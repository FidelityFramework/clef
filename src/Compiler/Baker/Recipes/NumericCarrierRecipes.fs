// SPDX-License-Identifier: MIT
/// One source-owned materialization of held carriers and their joint evidence.
module Clef.Compiler.Baker.Recipes.NumericCarrierRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph
open Clef.Compiler.Baker.Ingredients.Obligations
module Numeric = Clef.Compiler.Baker.Ingredients.NumericValues
module Boundary = Clef.Compiler.Baker.Ingredients.Boundaries
module RangeSources = Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources

let private scalarKind ty = Types.tryGetNTUKind ty |> Option.exists (function
    | NTUKind.NTUint _ | NTUKind.NTUuint _ | NTUKind.NTUbool | NTUKind.NTUchar
    | NTUKind.NTUfloat _ | NTUKind.NTUposit _ -> true
    | _ -> false)

let private declarationOnly graph =
    let rec collect seen id =
        if Set.contains id seen then seen else
        match graph.Nodes.TryFind id with
        | Some node -> List.fold collect (Set.add id seen) node.Children
        | None -> Set.add id seen
    graph.Edges |> List.fold (fun found edge ->
        match edge.Role with
        | EdgeRole.BoundaryDeclaration declaration -> collect found declaration.Binding
        | _ -> found) Set.empty

let private resultSite (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Binding _ | SemanticKind.PatternBinding _ | SemanticKind.Obligation _ -> false
    | _ -> true

let rec private kinds ty =
    let own = Types.tryGetNTUKind ty |> Option.toList
    let children =
        match applySubst ty with
        | NativeType.TApp(_, args) | NativeType.TTuple(args, _) -> args
        | NativeType.TFun(a, b) -> [a; b]
        | NativeType.TForall(_, body) | NativeType.TNativePtr body | NativeType.TByref(body, _) -> [body]
        | _ -> []
    own @ (children |> List.collect kinds)

/// Array element settlement shares the same range/representation owner. It is
/// computed in Baker, never reconstructed by a collection witness.
let private elementSlot (graph: SemanticGraph) (node: SemanticNode) =
    match applySubst node.Type with
    | NativeType.TApp(tc, [element]) when tc.NTUKind = Some NTUKind.NTUarray ->
        match StringByteStorage.element graph node.Id with
        | Some slot -> Some slot
        | None ->
            match Types.tryGetNTUKind element with
            | Some NTUKind.NTUbool -> Some SettledSlot.Bool
            | Some NTUKind.NTUchar -> Some SettledSlot.Char
            | Some kind when NTUKind.isInteger kind ->
                let key = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType element
                graph.ElementRanges.Value.TryFind key |> Option.bind (fun range ->
                    match range, RangeAnalysis.heldWidthOf graph range with
                    | ValueRange.Bounded _, Some bits when bits > 0 ->
                        let representation = RangeAnalysis.selectedRepresentationOf graph range
                        let covered =
                            match representation with
                            | Some representation -> Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources.declaredRange representation |> Option.exists (fun capacity -> ValueRange.contains capacity range)
                            | None -> graph.Platform |> Option.exists (fun context -> PlatformContext.substrateKind context = SubstrateKind.FPGA)
                        if covered then Some(SettledSlot.Integer(bits, representation |> Option.map _.Name)) else None
                    | _ -> None)
            | _ -> None
    | _ -> None

let elaborate (graph: SemanticGraph) =
    let enrichId = Elaboration.freshId ()
    let anchor = Boundary.anchor enrichId graph |> fun node -> { node with Metadata = node.Metadata.Remove "Baker.BoundaryOwned" } |> Numeric.markOwned
    let demand = OrdinaryDemand.project graph
    let declarations = declarationOnly graph
    let required = graph.Nodes |> Map.fold (fun ids id node ->
        if node.IsReachable && not (demand.DeferredOnly.Contains id) && not (declarations.Contains id) && scalarKind node.Type then Set.add id ids else ids) Set.empty
    let sourceReading = PlatformResolution.read graph
    let sourceCore = sourceReading.Platform |> Option.bind _.Core
    let select (node: SemanticNode) =
        let participants declaration = Set.ofList (anchor.Id :: node.Id :: (Option.toList declaration) @ (kindEdges node.Id node.Kind |> List.collect _.Sources))
        let fact slot range representation declaration =
            { Site = node.Id; Slot = slot; Range = range; Representation = representation; Declaration = declaration
              SourceType = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type; Obligations = []; Participants = participants declaration }
        match Types.tryGetNTUKind node.Type with
        | Some NTUKind.NTUbool -> Ok(fact SettledSlot.Bool ValueRange.boolean None None)
        | Some NTUKind.NTUchar -> Ok(fact SettledSlot.Char (ValueRange.bounded 0I 1114111I) None None)
        | Some kind when NTUKind.isInteger kind ->
            match node.ValueRange, RangeAnalysis.heldWidth graph node.Id with
            | Some(ValueRange.Bounded(lo, hi) as range), Some bits when lo <= hi && bits > 0 ->
                match RangeAnalysis.selectedRepresentation graph node.Id, sourceCore with
                | Some representation, Some core when sourceReading.Findings.IsEmpty ->
                    match core.Representations |> List.filter (fun declaration -> declaration.Representation = representation) with
                    | [declaration] when NumericRepresentation.isOffered representation && representation.Bits = bits ->
                        Ok(fact (SettledSlot.Integer(bits, Some representation.Name)) range (Some representation) (Some declaration.Node))
                    | _ -> Error "The held scalar has no unique matching offered representation declaration."
                | None, _ when graph.Platform |> Option.exists (fun context -> PlatformContext.substrateKind context = SubstrateKind.FPGA) ->
                    Ok(fact (SettledSlot.Integer(bits, None)) range None None)
                | _ -> Error "The held integer carrier lacks its source representation/declaration authority."
            | _ -> Error "The required integer carrier has no finite observable range and settled positive width."
        | Some(NTUKind.NTUfloat width) ->
            let selected =
                match width with
                | NTUWidth.Fixed bits when bits > 0 -> Some(bits, None)
                | NTUWidth.Resolved dimension -> sourceCore |> Option.bind (fun core ->
                    match core.Widths |> List.filter (fun declared -> declared.Name = WidthDimension.name dimension) with
                    | [declared] when declared.Bits > 0 -> Some(declared.Bits, Some declared.Node)
                    | _ -> None)
                | _ -> None
            match selected with
            | Some(bits, declaration) -> Ok(fact (SettledSlot.Real bits) (node.ValueRange |> Option.defaultValue ValueRange.Unbounded) None declaration)
            | None -> Error "The real scalar carrier has no unique source width declaration."
        | Some(NTUKind.NTUposit _) -> Error "The posit carrier requires its exact source format identity; IEEE width alone cannot authorize a posit representation."
        | _ -> Error "The required scalar carrier has no source settlement rule."
    let values, unresolved, proofs = required |> Set.fold (fun (values, unresolved, proofs) id ->
        match select graph.Nodes[id] with
        | Error reason -> values, Map.add id reason unresolved, proofs
        | Ok carrier ->
            match carrier.Slot, Numeric.coverage carrier with
            | SettledSlot.Integer _, Some body ->
                if Clef.Compiler.Baker.Ingredients.StringBytes.proofOutcome body <> BoundaryProofOutcome.Proven then
                    values, Map.add id "The selected scalar carrier does not cover its established source range." unresolved, proofs
                else
                    let node = obligationNode graph.Nodes[id] enrichId
                                   { Id = $"numeric_carrier_{NodeId.value id}"; Kind = "numeric-carrier-coverage"; Logic = "QF_LIA"
                                     Statement = "the held scalar carrier covers its exact source range under the retained source domain"
                                     Source = fmtRange graph.Nodes[id].Range; Refs = []; Body = body } |> Numeric.markOwned
                    let carrier = { carrier with Obligations = [node.Id] }
                    carrier :: values, unresolved, Enrichment.combine proofs { NewNodes = [node]; Annotated = []; NewEdges = Numeric.proofRows carrier node.Id body }
            | SettledSlot.Integer _, None -> values, Map.add id "The required scalar coverage obligation is unavailable." unresolved, proofs
            | _ -> carrier :: values, unresolved, proofs) ([], Map.empty, Enrichment.empty)
    let elements = graph.Nodes |> Map.toList |> List.choose (fun (id, node) -> elementSlot graph node |> Option.map (fun slot -> id, slot)) |> Map.ofList
    let elementTypes =
        graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
            match applySubst node.Type, elements.TryFind id with
            | NativeType.TApp(tc, [element]), Some slot when tc.NTUKind = Some NTUKind.NTUarray -> Some(Clef.Compiler.NativeTypedTree.TypeIdentities.ofType element, slot)
            | _ -> None)
        |> List.groupBy fst |> List.choose (fun (key, entries) ->
            match entries |> List.map snd |> List.distinct with [slot] -> Some(key, slot) | _ -> None) |> Map.ofList
    let declaredScalars =
        graph.Nodes |> Map.toList |> List.collect (fun (_, node) -> kinds node.Type) |> List.distinct |> List.choose (fun kind ->
            match RangeSources.declarationOfKind graph.Platform kind with
            | Some declared when declared.Bits > 0 -> Some(kind, SettledSlot.Integer(declared.Bits, Some declared.Repr))
            | _ -> None) |> Map.ofList
    let occurrenceRepresentations, typeRepresentations =
        Clef.Compiler.Baker.Ingredients.ValueRepresentations.settle graph (List.rev values) elements elementTypes declaredScalars
    let operationEnrichment, operations, operationFailures, operationRequired, operationProofs =
        NumericOperationRecipes.settle graph anchor.Id (values |> List.map (fun carrier -> carrier.Site, carrier) |> Map.ofList) required
    let operationMeets = operations |> List.map (fun operation -> operation.Site, Clef.Compiler.Baker.Ingredients.NumericOperations.meets operation) |> Map.ofList
    let unresolved = Map.fold (fun failures id reason -> Map.add id reason failures) unresolved operationFailures
    let unresolved = operationMeets |> Map.fold (fun failures site meets ->
        let previous = graph.Codata.Value.Meets.TryFind site |> Option.defaultValue []
        let combined = previous @ meets |> List.distinct
        if combined |> List.groupBy _.Operand |> List.exists (fun (_, sameActual) -> sameActual.Length > 1) then
            Map.add site "An operation's ordered occurrences demand contradictory adaptations for one actual identity." failures
        else failures) unresolved
    let indexSites =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.ContinuationDispatch(operand, _, _)
                when node.IsReachable && not(demand.DeferredOnly.Contains node.Id) && not(declarations.Contains node.Id) ->
                Some(node, operand)
            | _ -> None) |> Seq.toList
    let pointer = sourceCore |> Option.bind (fun core ->
        match core.Widths |> List.filter (fun width -> width.Name = "Pointer" && width.Bits > 0) with
        | [width] -> Some width
        | _ -> None)
    let bySite = values |> List.map (fun value -> value.Site, value) |> Map.ofList
    let indexEnrichment, indexTransports, unresolved =
        indexSites |> List.fold (fun (enrichment, transports, failures) (node, operand) ->
            let refuse reason = enrichment, transports, Map.add node.Id reason failures
            match pointer, bySite.TryFind operand with
            | Some width, Some carrier ->
                match carrier.Slot, carrier.Range with
                | (SettledSlot.Integer _ | SettledSlot.Bool | SettledSlot.Char), ValueRange.Bounded(lo, hi) when lo <= hi ->
                    let unsigned = lo >= 0I
                    let capacity = if unsigned then ValueRange.unsignedOf width.Bits else ValueRange.twosComplement width.Bits
                    if not(ValueRange.contains capacity carrier.Range) then
                        refuse "The dispatch selector range is not representable in the selected platform's index domain."
                    else
                        let minimum, maximum = match capacity with ValueRange.Bounded(a,b) -> a,b | _ -> invalidOp "Finite index capacity expected."
                        let body = ObligationBody.IntegerRepresentationCoverage(lo, hi, minimum, maximum)
                        let proof = obligationNode node enrichId
                                        { Id = $"numeric_index_{NodeId.value node.Id}"; Kind = "numeric-index-coverage"; Logic = "QF_LIA"
                                          Statement = "the exact dispatch selector range fits the declared platform index transport"
                                          Source = fmtRange node.Range; Refs = []; Body = body } |> Numeric.markOwned
                        let transport =
                            { Site = node.Id; Operand = operand; Carrier = carrier; PointerDeclaration = width.Node; PointerBits = width.Bits
                              Unsigned = unsigned; Capacity = capacity; Obligation = proof.Id
                              Participants = carrier.Participants |> Set.add node.Id |> Set.add width.Node }
                        let own = { NewNodes = [proof]; Annotated = []; NewEdges = Numeric.indexRows transport }
                        Enrichment.combine enrichment own, transport :: transports, failures
                | _ -> refuse "The dispatch selector lacks a finite source integer carrier for index transport."
            | _ -> refuse "The dispatch selector lacks its source carrier or selected platform Pointer declaration.")
            (Enrichment.empty, [], unresolved)
    let domain =
        { Premises = Numeric.premises graph; Platform = Boundary.platformPremise graph.Platform
          Roots = graph.DeclarationRoots; Escaping = graph.Escaping.Value; Layouts = graph.Layouts.Value
          Required = required; ResultSites = required |> Set.filter (fun id -> resultSite graph.Nodes[id])
          SourceTypes = Numeric.premises graph |> Map.map (fun _ premise -> premise.Shape.SourceType)
          Elements = elements; ElementTypes = elementTypes; DeclaredScalars = declaredScalars
          ElementRanges = graph.ElementRanges.Value; ByteRanges = Numeric.byteRanges graph
          ByteReadRanges = Numeric.byteReadRanges graph; ByteViews = Numeric.byteViews graph; StringExtents = Numeric.stringExtents graph
          OccurrenceRepresentations = occurrenceRepresentations; TypeRepresentations = typeRepresentations
          Operations = List.rev operations; OperationRequired = operationRequired
          OperationMeets = operationMeets; OperationProofs = operationProofs
          IndexTransports = List.rev indexTransports; IndexRequired = indexSites |> List.map (fst >> _.Id) |> Set.ofList
          Values = List.rev values; Unresolved = unresolved }
    Enrichment.combine (Enrichment.combine (Enrichment.combine proofs operationEnrichment) indexEnrichment)
        { NewNodes = [anchor]; Annotated = []
          NewEdges = Numeric.domainRow anchor.Id domain :: Numeric.domainRewrite anchor.Id domain :: (domain.Values |> List.map Numeric.carrierRow) }
