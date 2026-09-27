// SPDX-License-Identifier: MIT
/// Baker owns foreign declaration identity, scalar ABI and complete joint
/// call premises. Recipes return an enrichment; the nanopass folds it.
module Clef.Compiler.Baker.Recipes.BoundaryRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph
open Clef.Compiler.Baker.Ingredients.Obligations
module Declarations = PlatformResolution
module Ingredients = Clef.Compiler.Baker.Ingredients.Boundaries
module Bytes = Clef.Compiler.Baker.Ingredients.StringBytes

type private CheckedBuilder() =
    member _.Bind(value, next) = Result.bind next value
    member _.Return(value) = Ok value
    member _.ReturnFrom(value) = value
let private checked' = CheckedBuilder()

let private require condition message = if condition then Ok () else Error message
let private needed message = function Some value -> Ok value | None -> Error message
let private collect values =
    List.foldBack (fun value rest ->
        match value, rest with
        | Ok value, Ok rest -> Ok (value :: rest)
        | Error reason, _ | _, Error reason -> Error reason) values (Ok [])

let private field name fields = fields |> List.tryPick (fun (key, value) -> if key = name then Some value else None)
let private metadata name (node: SemanticNode) =
    match node.Metadata.TryFind name with Some (MetadataValue.String value) -> Some value | _ -> None

/// Follow only the actual callee's source references. A cycle or an unresolved
/// edge never acquires an external identity from a coincidentally matching name.
let private target = BoundaryDeclarations.target

/// Retain the exact source descriptor structure and referenced declaration
/// values. Parent/module nodes are participants, not recursively traversed.
let private declarationFacts (graph: SemanticGraph) root =
    let shape (node: SemanticNode) =
        let fact form text numbers references =
            Ok { Form = form; Text = text; Numbers = numbers; References = references
                 Children = node.Children; Parent = node.Parent
                 SourceType = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type }
        match node.Kind with
        | SemanticKind.RecordExpr(fields, copy) -> fact "record" (List.map fst fields) [] (List.map snd fields @ Option.toList copy)
        | SemanticKind.ArrayExpr values -> fact "array" [] [] values
        | SemanticKind.TupleExpr values -> fact "tuple" [] [] values
        | SemanticKind.UnionCase(name, index, value) -> fact "case" [name] [bigint index] (Option.toList value)
        | SemanticKind.DUConstruct(name, index, value, _) -> fact "settled-case" [name] [bigint index] (Option.toList value)
        | SemanticKind.Literal(NativeLiteral.String text) -> fact "string" [text] [] []
        | SemanticKind.Literal(NativeLiteral.Int(value, kind)) -> fact "integer" [string kind] [bigint value] []
        | SemanticKind.Literal(NativeLiteral.UInt(value, kind)) -> fact "unsigned-integer" [string kind] [bigint value] []
        | SemanticKind.Literal(NativeLiteral.Bool value) -> fact "boolean" [] [if value then 1I else 0I] []
        | SemanticKind.Literal NativeLiteral.Unit -> fact "unit" [] [] []
        | SemanticKind.VarRef(name, binding) -> fact "reference" [name] [] (Option.toList binding)
        | SemanticKind.Binding(name, mutable', recursive', _) -> fact "binding" [name] [if mutable' then 1I else 0I; if recursive' then 1I else 0I] node.Children
        | SemanticKind.TypeAnnotation(inner, _) -> fact "annotation" [] [] [inner]
        | SemanticKind.Quote(inner, _) -> fact "quotation" [] [] [inner]
        | SemanticKind.Application(callee, arguments) -> fact "application" [] [] (callee :: arguments)
        | SemanticKind.Intrinsic info -> fact "intrinsic" [string info.Module; info.Operation] [] []
        | _ -> Error $"Descriptor participant {NodeId.value node.Id} has no immutable boundary declaration premise."
    let rec visit facts id =
        if Map.containsKey id facts then Ok facts else
        match graph.Nodes.TryFind id with
        | None -> Error $"Descriptor participant {NodeId.value id} is absent from the source graph."
        | Some node -> checked' {
            let! value = shape node
            let next = value.References @ value.Children
            return! List.fold (fun state child -> state |> Result.bind (fun facts -> visit facts child)) (Ok (Map.add id value facts)) next }
    visit Map.empty root

let private typeRef graph typeId =
    Declarations.readTypeRef graph typeId
    |> Result.mapError _.Message
    |> Result.bind (function
        | Declarations.DeclaredTypeRef.Scalar scalar -> Ok (Some scalar)
        | Declarations.DeclaredTypeRef.Void -> Ok None
        | _ -> Error "This TypeRef requires a source-settled adapter beyond the scalar C contract.")

let private scalarRange = function
    | BoundaryScalar.Boolean -> ValueRange.boolean
    | BoundaryScalar.Integer(bits, true) -> ValueRange.twosComplement bits
    | BoundaryScalar.Integer(bits, false) -> ValueRange.unsignedOf bits

let private scalarBits = function BoundaryScalar.Boolean -> 1 | BoundaryScalar.Integer(bits, _) -> bits

let private supportedType scalar ty =
    match scalar, Types.tryGetNTUKind ty with
    | BoundaryScalar.Boolean, Some NTUKind.NTUbool -> true
    | BoundaryScalar.Integer _, Some (NTUKind.NTUint _)
    | BoundaryScalar.Integer _, Some (NTUKind.NTUuint _) -> true
    | _ -> false

let private sourceTypes (graph: SemanticGraph) ids =
    ids |> List.map (fun id ->
        match graph.Nodes.TryFind id with
        | Some node -> Ok (id, Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type)
        | _ -> Error "A scalar boundary participant has no source type identity.")
    |> collect |> Result.map Map.ofList

let private bindingPath = BoundaryDeclarations.bindingPath

let private readImport (graph: SemanticGraph) (descriptors: Declarations.Descriptors) (binding: SemanticNode) library symbol = checked' {
    let! scope = binding.Parent |> needed "The external binding has no source module owner."
    do! require (graph.Nodes.TryFind scope |> Option.exists (fun node -> match node.Kind with SemanticKind.ModuleDef(_, members) -> List.contains binding.Id members | _ -> false))
            "The external binding is not a structural member of its declared module occurrence."
    let! declarationPath, sourceFormals, body = bindingPath graph binding.Id
    let! descriptor =
        match descriptors.Functions |> List.filter (fun descriptor -> descriptor.Body = Some body) with
        | [descriptor] -> Ok descriptor
        | [] -> Error "The external binding has no matching FunctionDescriptor."
        | _ -> Error "The external binding has duplicate FunctionDescriptor declarations."
    let! _, fields = Declarations.recordOf graph descriptor.Node |> needed "The FunctionDescriptor no longer names a source record."
    let! callingId = field "CallingConvention" fields |> needed "The FunctionDescriptor has no declared calling convention."
    let! convention = Declarations.caseOf graph callingId |> Option.map (fun (_, name, _) -> name) |> needed "The calling convention is not a declared case."
    do! require (convention = "CDecl") $"Calling convention '{convention}' is not admitted by the scalar C contract."
    do! require (descriptor.CName = symbol) "FunctionDescriptor.CName disagrees with FidelityExtern.Symbol."
    do! require (descriptor.References.IsEmpty && descriptor.PointerReferences.IsEmpty && descriptor.RecordReferences.IsEmpty)
            "Reference arguments require source-settled boundary adapters; scalar C publication cannot substitute a pointer."
    let parameters =
        descriptor.Parameters |> List.map (fun (formal, declared) -> checked' {
            let! declared = declared |> needed "A boundary parameter has no admitted integer or boolean declaration."
            let! _, parameterFields = Declarations.recordOf graph declared.Node |> needed "A boundary parameter declaration is missing."
            let! passing = field "PassBy" parameterFields |> needed "A scalar boundary parameter must explicitly declare PassBy.Value."
            do! require (Declarations.caseOf graph passing |> Option.exists (fun (_, name, _) -> name = "Value"))
                    "A scalar boundary parameter must explicitly declare PassBy.Value."
            let! typeId = field "Type" parameterFields |> needed "A boundary parameter has no TypeRef."
            let! scalar = typeRef graph typeId
            let! scalar = scalar |> needed "Void is a result convention, not a boundary parameter."
            let! formalNode = graph.Nodes.TryFind formal |> needed "A boundary formal is absent from the source graph."
            do! require (supportedType scalar formalNode.Type) "A boundary formal's source kind disagrees with its declared scalar ABI."
            do! require (declared.Bits = scalarBits scalar && declared.Range = scalarRange scalar) "The descriptor's scalar range and TypeRef disagree."
            return formal, scalar }) |> collect
    let! parameters = parameters
    let retainedFormals = sourceFormals |> List.map (fun (_, _, id) -> id)
    let erasedUnitFormals =
        match sourceFormals, parameters with
        | [(_, ty, id)], [] when Types.tryGetNTUKind ty = Some NTUKind.NTUunit -> [id]
        | _ -> []
    do! require ((parameters |> List.map fst) @ erasedUnitFormals = retainedFormals)
            "The descriptor's formal order differs from its exact source function declaration."
    let! returnId = field "ReturnType" fields |> needed "The FunctionDescriptor has no ReturnType."
    let! result = typeRef graph returnId
    let! bodyNode = graph.Nodes.TryFind body |> needed "The external binding body is absent from the source graph."
    do! require (match result with Some scalar -> supportedType scalar bodyNode.Type | None -> Types.tryGetNTUKind bodyNode.Type = Some NTUKind.NTUunit)
            "The binding result's source kind disagrees with its declared boundary result."
    let descriptorBindings =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind, node.Children with
            | SemanticKind.Binding _, children when node.Parent = Some scope ->
                children |> List.tryLast |> Option.bind (Declarations.recordOf graph)
                |> Option.bind (fun (record, _) -> if record.Id = descriptor.Node then Some node.Id else None)
            | _ -> None) |> Set.ofSeq
    let! descriptorBinding =
        match Set.toList descriptorBindings with
        | [binding] -> Ok binding
        | _ -> Error "The FunctionDescriptor must retain exactly one source declaration binding."
    do! require (graph.Nodes.TryFind scope |> Option.exists (fun node -> match node.Kind with SemanticKind.ModuleDef(_, members) -> List.contains descriptorBinding members | _ -> false))
            "The FunctionDescriptor binding is not a member of its exact source module occurrence."
    let! facts = declarationFacts graph descriptorBinding
    let participants = Set.unionMany [facts |> Map.keys |> Set.ofSeq; descriptorBindings; Set.ofList (scope :: body :: retainedFormals @ declarationPath)]
    let! types = sourceTypes graph (body :: retainedFormals)
    return { Identity = descriptor.Node; Binding = binding.Id; Scope = scope; Library = library; Symbol = symbol
             CallingConvention = convention; DeclarationPath = declarationPath; Parameters = parameters; Result = result; Participants = participants; SourceTypes = types; DeclarationFacts = facts }
}

let private adaptation (graph: SemanticGraph) site operand sourceBits targetBits inputRange = checked' {
    let matches = graph.Codata.Value.Meets.TryFind site |> Option.defaultValue [] |> List.filter (fun meet -> meet.Operand = operand) |> List.distinct
    if sourceBits = targetBits then
        do! require matches.IsEmpty "An unchanged scalar boundary carries an inconsistent numeric meet."
        return None
    else
        let! meet = match matches with [meet] -> Ok meet | _ -> Error "The scalar boundary requires exactly one already-settled numeric meet."
        do! require (meet.Consumer = site && meet.From = sourceBits && meet.To = targetBits)
                "The source numeric meet disagrees with the exact boundary widths."
        do! require (match meet.Adapt with MeetKind.ExtendSigned | MeetKind.ExtendUnsigned -> sourceBits < targetBits | MeetKind.Truncate -> sourceBits > targetBits | _ -> false)
                "The numeric meet is not an integer adaptation for this scalar boundary."
        do! require (match meet.Adapt with
                     | MeetKind.ExtendUnsigned -> ValueRange.isNonNegative inputRange && ValueRange.contains (ValueRange.unsignedOf sourceBits) inputRange
                     | MeetKind.ExtendSigned -> not (ValueRange.isNonNegative inputRange) && ValueRange.contains (ValueRange.twosComplement sourceBits) inputRange
                     | MeetKind.Truncate -> true // Coverage is a separate joint proof obligation.
                     | _ -> false)
                "The numeric meet's signedness or truncation premise disagrees with the established input range."
        return Some meet
}

let private sourceWidth graph id scalar =
    match scalar with
    | BoundaryScalar.Boolean -> Ok 1
    | BoundaryScalar.Integer _ -> checked' {
        let! representation = RangeAnalysis.selectedRepresentation graph id |> needed "The scalar occurrence has no source-selected offered integer representation."
        do! require (NumericRepresentation.isOffered representation && (representation.Family = "int" || representation.Family = "uint"))
                "The scalar occurrence's selected representation is not an offered integer representation."
        do! require (RangeAnalysis.heldWidth graph id = Some representation.Bits)
                "The scalar occurrence's held width disagrees with its selected offered representation."
        return representation.Bits }

let private readCall (graph: SemanticGraph) (site: SemanticNode) callee args path (import: BoundaryImport) = checked' {
    do! require (site.Children = callee :: args) "The boundary application's ordered operands disagree with its source structural children."
    let operands, erased =
        match import.Parameters, args with
        | [], [unit] when graph.Nodes.TryFind unit |> Option.exists (fun node -> Types.tryGetNTUKind node.Type = Some NTUKind.NTUunit) -> [], [unit]
        | _ -> args, []
    do! require (operands.Length = import.Parameters.Length) "The external call does not supply exactly the declared ordered scalar arguments."
    let! arguments =
        List.zip operands import.Parameters |> List.map (fun (actual, (formal, abi)) -> checked' {
            let! node = graph.Nodes.TryFind actual |> needed "An actual boundary argument is absent from the source graph."
            do! require (supportedType abi node.Type) "An actual boundary argument's source kind disagrees with the declared formal."
            do! require (import.SourceTypes.TryFind formal = Some (Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type))
                    "The actual boundary argument does not retain its formal's native kind and dimension identity."
            let! range = match abi with BoundaryScalar.Boolean -> Ok ValueRange.boolean | _ -> node.ValueRange |> needed "The actual scalar argument lacks an established source range."
            let! sourceBits = sourceWidth graph actual abi
            let! meet = adaptation graph site.Id actual sourceBits (scalarBits abi) range
            return { Actual = actual; Formal = formal; Abi = abi; Adaptation = meet } }) |> collect
    let! resultAdaptation =
        match import.Result with
        | None -> checked' {
            do! require (Types.tryGetNTUKind site.Type = Some NTUKind.NTUunit) "A void foreign call cannot publish a non-unit source result."
            return None }
        | Some abi -> checked' {
            do! require (supportedType abi site.Type) "The call result's source kind disagrees with its boundary declaration."
            let! targetBits = sourceWidth graph site.Id abi
            return! adaptation graph site.Id site.Id (scalarBits abi) targetBits (scalarRange abi) }
    let! types = sourceTypes graph (site.Id :: args)
    return { Site = site.Id; Import = import.Identity; Callee = callee; Arguments = arguments; ErasedUnitArguments = erased
             Result = import.Result; ResultAdaptation = resultAdaptation
             Participants = Set.unionMany [import.Participants; path; Set.ofList (site.Id :: callee :: args)]
             SourceTypes = types }
}

type private IntrinsicDomain = {
    Views: BoundaryByteView list
    Extents: BoundaryStringExtent list
    Declarations: (NodeId * IntrinsicWriteImport) list
    Imports: IntrinsicWriteImport list
    Calls: IntrinsicWriteCall list
    Proofs: IntrinsicWriteProof list
    Enrichment: Enrichment
    Errors: (NodeId * Set<NodeId> * string) list
}

let private intrinsicWrites enrichId anchor (graph: SemanticGraph) =
    let views = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringByteView view -> Some view | _ -> None)
    let extents = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringExtent extent -> Some extent | _ -> None)
    let declarations = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.IntrinsicWriteAbi import -> Some(edge.Target, import) | _ -> None)
    let sourceEvidence = StringBorrowRecipes.evidence graph
    let retainedEvidence =
        (views |> List.collect (fun view -> [Bytes.viewRow view; Bytes.storageRow view])) @
        (extents |> List.map Bytes.extentRow) @ (declarations |> List.map (fun (site, import) -> Bytes.abiRow site import))
    let key (edge: Hyperedge) = edge.Role, edge.Sources, edge.Target
    let currentEvidence = (sourceEvidence |> List.map key |> List.sort) = (retainedEvidence |> List.map key |> List.sort)
    let unique message values = match values with [value] -> Ok value | _ -> Error message
    let range id = graph.Nodes.TryFind id |> Option.bind _.ValueRange |> needed "The intrinsic scalar lacks its established source range."
    let coverage input destination =
        match input, destination with
        | ValueRange.Bounded(lo, hi), ValueRange.Bounded(minimum, maximum) -> Ok(ObligationBody.IntegerRepresentationCoverage(lo, hi, minimum, maximum))
        | _ -> Error "The intrinsic coverage obligation requires finite source and destination ranges."
    let read (node: SemanticNode) callee args path = checked' {
        do! require currentEvidence "The complete byte-origin/formal/actual or intrinsic ABI premises changed after source numeric settlement."
        let! fd, buffer, count = match args with [fd; buffer; count] -> Ok(fd, buffer, count) | _ -> Error "Sys.write requires exactly fd, a bounded read-only byte view, and its explicit count."
        do! require (node.Children = callee :: args) "Sys.write's ordered operands differ from its source structural occurrence."
        let! import = declarations |> List.filter (fun (site, _) -> site = node.Id) |> List.map snd |> unique "Sys.write requires one selected source syscall endpoint, return contract, Register dimension and offered octet declaration before numeric settlement."
        let! view = views |> List.filter (fun view -> view.Site = buffer) |> unique "Sys.write requires a proved string.Bytes read-only borrow; this bounded slice admits only immutable program-resident string origins."
        let! extent = extents |> List.filter (fun extent -> extent.Site = count) |> unique "Sys.write's count must preserve the exact borrowed string's per-invocation Length relation."
        do! require (view.ExtentSource = extent.ExtentSource && view.StaticOrigins = extent.StaticOrigins && not view.StaticOrigins.IsEmpty)
                "Sys.write's buffer and count do not refer to the same per-invocation string extent and complete origin domain."
        do! require (view.Representation = import.ByteRepresentation) "The byte borrow and intrinsic ABI have different source-selected byte carriers."
        do! require (graph.Nodes[buffer].Kind = SemanticKind.StringByteBorrow view.Source && graph.Nodes[count].Kind = SemanticKind.FieldGet(extent.Source, "Length"))
                "The byte borrow or extent occurrence no longer retains its settled source operation."
        let readonlyUse = graph.Nodes.Values |> Seq.forall (fun consumer ->
            if not consumer.IsReachable || consumer.Id = buffer then true else
            let uses = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence consumer |> List.filter (fun edge -> List.contains buffer edge.Sources)
            uses.IsEmpty ||
            (match consumer.Kind, target graph (match consumer.Kind with SemanticKind.Application(fn, _) -> fn | _ -> consumer.Id) with
             | SemanticKind.Application(_, [_; actual; _]), Some({ Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Sys; Operation = "write" } }, _) when actual = buffer -> true
             | _ -> false))
        do! require readonlyUse "A read-only string byte borrow escapes the admitted write operand or has a mutable/unknown use."
        let! pool = graph.StaticStringPool |> needed "A byte borrow requires the settled immutable program string pool."
        let! storage = view.StaticOrigins |> Map.toList |> List.map (fun (origin, length) -> checked' {
            let! entry = pool.Entries |> List.filter (fun entry -> List.contains origin entry.NodeIds) |> unique "A string borrow origin has no unique program-resident immutable storage entry."
            do! require (bigint entry.Length = length && System.Text.Encoding.UTF8.GetByteCount entry.Content = entry.Length && entry.StorageLength = entry.Length + 1)
                    "The string borrow extent differs from its exact immutable storage entry."
            do! require (graph.Nodes.TryFind origin |> Option.exists (fun node -> node.Kind = SemanticKind.Literal(NativeLiteral.String entry.Content)))
                    "The program storage entry no longer belongs to the exact literal source bytes."
            return length, length, bigint entry.StorageLength }) |> collect
        let! fdRange = range fd
        let! countRange = range count
        let expectedCount = ValueRange.bounded (view.StaticOrigins.Values |> Seq.min) (view.StaticOrigins.Values |> Seq.max)
        do! require (countRange = expectedCount) "The scalar count range no longer matches the complete exact string extent domain."
        let! platform = Declarations.resolve graph |> needed "Sys.write lost its selected source platform description."
        let! result = platform.Returns |> List.filter (fun bound -> bound.Node = import.ReturnContract && bound.Endpoint = "write" && bound.AtMost = "count") |> unique "Sys.write lost its exact declared signed return bound."
        let! upper = match countRange with ValueRange.Bounded(_, hi) -> Ok hi | _ -> Error "The write count is not bounded."
        let returnRange = ValueRange.bounded result.Floor upper
        let! actualResult = range node.Id
        do! require (actualResult = returnRange) "Sys.write's result range differs from its source endpoint return contract."
        let! fdWidth = sourceWidth graph fd import.Fd
        let! countWidth = sourceWidth graph count import.Count
        let! resultWidth = sourceWidth graph node.Id import.Result
        let! fdMeet = adaptation graph node.Id fd fdWidth (scalarBits import.Fd) fdRange
        let! countMeet = adaptation graph node.Id count countWidth (scalarBits import.Count) countRange
        let! resultMeet = adaptation graph node.Id node.Id (scalarBits import.Result) resultWidth returnRange
        let! resultRepresentation = RangeAnalysis.selectedRepresentation graph node.Id |> Option.bind Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources.declaredRange |> needed "The write result has no offered representation range."
        let! fdProof = coverage fdRange (scalarRange import.Fd)
        let! countProof = coverage countRange (scalarRange import.Count)
        let! resultProof = coverage returnRange resultRepresentation
        let participants = Set.unionMany [path; import.Participants; view.Participants; extent.Participants; Set.ofList [anchor; node.Id; callee; fd; buffer; count; pool.DeclarationNode]]
        let call = { Site = node.Id; Import = import.Identity; Callee = callee; Fd = fd; Buffer = buffer; Count = count
                     FdAdaptation = fdMeet; CountAdaptation = countMeet; ResultAdaptation = resultMeet; Participants = participants }
        return import, call, [0, fdProof; 1, ObligationBody.StringBorrowBound storage; 2, countProof; -1, resultProof] }
    let evidenceErrors =
        if currentEvidence then [] else
        let participants = Set.unionMany ((views |> List.map _.Participants) @ (extents |> List.map _.Participants))
        [anchor,participants,"The complete string view, descriptor extent, actual/formal or intrinsic ABI evidence changed after source range settlement."]
    let initial = { Views = views; Extents = extents; Declarations = declarations; Imports = []; Calls = []; Proofs = []; Enrichment = Enrichment.empty; Errors = evidenceErrors }
    graph.Nodes |> Map.fold (fun state _ node ->
        match node.Kind with
        | SemanticKind.Application(callee, args) when node.IsReachable ->
            match target graph callee with
            | Some({ Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Sys; Operation = "write" } }, path) ->
                match read node callee args path with
                | Error reason -> { state with Errors = (node.Id, Set.union path (Set.ofList(node.Id :: args)), reason) :: state.Errors }
                | Ok(import, call, bodies) ->
                    let proofs, enrichment, errors = bodies |> List.fold (fun (proofs, enrichment, errors) (ordinal, body) ->
                        let info =
                            { Id = $"intrinsic_write_{NodeId.value node.Id}_{ordinal}"; Kind = "intrinsic-write-proof"; Logic = "QF_LIA"
                              Statement = "the exact ordered intrinsic write has covered scalars and a count-contained immutable borrow"
                              Source = fmtRange node.Range; Refs = []; Body = body }
                        let obligation = obligationNode node enrichId info |> Ingredients.markOwned
                        let proof = { Site = node.Id; Obligation = obligation.Id; Ordinal = ordinal; Body = body; Participants = call.Participants }
                        let errors = if Bytes.proofOutcome body = BoundaryProofOutcome.Proven then errors else (node.Id, call.Participants, "The intrinsic write obligation was refuted.") :: errors
                        proof :: proofs, Enrichment.combine enrichment { NewNodes = [obligation]; Annotated = []; NewEdges = Bytes.proofRows proof }, errors) (state.Proofs, state.Enrichment, state.Errors)
                    { state with Imports = import :: state.Imports; Calls = call :: state.Calls; Proofs = proofs; Enrichment = enrichment; Errors = errors }
            | _ -> state
        | _ -> state) initial

/// Late stage: all source ranges and ordinary numeric meets are already fixed.
/// The complete source domain records negative membership dependencies too.
let elaborate (graph: SemanticGraph) : Enrichment =
    let enrichId = Elaboration.freshId ()
    let anchor = Ingredients.anchor enrichId graph
    let intrinsic = intrinsicWrites enrichId anchor.Id graph
    let lengthComparisons = StringComparisonRecipes.lengthConstructions graph
    let lengthErrors = graph.Nodes.Values |> Seq.choose (fun node ->
        if node.Metadata.TryFind "Baker.StringLengthComparison" <> Some(MetadataValue.Bool true) then None else
        match lengthComparisons |> List.filter (fun fact -> fact.Site=node.Id) with
        | [fact] when StringComparisonRecipes.validLengthStructure graph fact -> None
        | _ -> Some(node.Id,Set.singleton node.Id,"The descriptor-only string comparison lost its exact zero-extent origin, actual/formal membership, or ordered source construction proof.")) |> Seq.toList
    let localViews, localReads, localSnapshots, localCopies, localErrors =
        let memory = Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication.project graph |> Result.toOption
        StringComparisonRecipes.constructions graph |> List.fold (fun (views,reads,snapshots,copies,errors) construction ->
            let participants = Set.ofList(construction.Site::construction.Left::construction.Right::construction.Members)
            let result = checked' {
                do! require (StringComparisonRecipes.validStructure graph construction) "The source string comparison lost its ordered length test, traversal, early exit or local result correspondence."
                let! memory = memory |> needed "A local string comparison borrow requires admitted memory access and bounds proofs."
                let! accesses = [construction.LeftView,construction.LeftRead; construction.RightView,construction.RightRead]
                                |> List.map (fun (view,frontier) -> checked' {
                    let! access =
                        match graph.Nodes.TryFind frontier with
                        | Some { Kind=SemanticKind.Sequential [_;continuation] } ->
                            memory.Operations.TryFind continuation |> Option.bind (function MemoryWitnessOperation.ArrayAccess fact -> Some fact | _ -> None)
                        | _ -> None
                        |> needed "The string comparison read lacks its exact guarded access continuation."
                    do! require (access.Buffer=view && access.Index=construction.Current && access.Value.IsNone && access.Bounds.Requirement.Frontier=frontier)
                            "The string comparison borrow is not read by its exact source guard and index occurrence."
                    let allowed = Set.ofList [access.Site;access.Bounds.Length]
                    let uses =
                        let source = graph.Nodes.Values |> Seq.collect Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence |> Seq.toList
                        source @ (graph.Edges |> List.filter (fun edge -> edge.Class=EdgeClass.Structural || edge.Class=EdgeClass.Reference))
                        |> List.filter (fun edge -> List.contains view edge.Sources && graph.Nodes.TryFind edge.Target |> Option.exists _.IsReachable)
                    do! require (not uses.IsEmpty && uses |> List.forall (fun edge -> allowed.Contains edge.Target))
                            "A local string comparison byte view escapes its exact read-only guarded uses."
                    let! byteView = intrinsic.Views |> List.filter (fun fact -> fact.Site=view) |> function [fact] -> Ok fact | _ -> Error "The local comparison lacks its single exact byte view."
                    do! require (byteView.ExtentSource=byteView.Source && byteView.Participants.IsSupersetOf participants)
                            "The local comparison view lost its complete actual and construction lifetime premises."
                    let! snapshots,copies,_ = StringViewRecipes.localLineage graph memory byteView.Source
                    return access,snapshots,copies }) |> collect
                return accesses }
            match result with
            | Ok accesses ->
                let localReads=accesses |> List.map(fun (read,_,_) -> read)
                let localSnapshots=accesses |> List.collect(fun (_,facts,_) -> facts)
                let localCopies=accesses |> List.collect(fun (_,_,facts) -> facts)
                Set.add construction.LeftView (Set.add construction.RightView views),localReads@reads,localSnapshots@snapshots,localCopies@copies,errors
            | Error reason -> views,reads,snapshots,copies,(construction.Site,participants,reason)::errors) (Set.empty,[],[],[],[])
    let intrinsic =
        let errors = graph.Nodes |> Map.fold (fun errors _ node ->
            match node.Kind with
            | SemanticKind.StringByteBorrow _ when node.IsReachable && not (localViews.Contains node.Id) && not (intrinsic.Calls |> List.exists (fun call -> call.Buffer = node.Id)) ->
                (node.Id, Set.singleton node.Id, "A string.Bytes borrow requires complete intrinsic write-use or local guarded comparison lifetime proofs.") :: errors
            | _ -> errors) intrinsic.Errors
        { intrinsic with Errors = lengthErrors @ localErrors @ errors }
    let descriptors = Declarations.readDescriptors graph
    let runtime = Declarations.read graph
    let runtimeContract = checked' {
        do! require runtime.Findings.IsEmpty "The selected source platform runtime has unresolved declaration or project consistency findings."
        let! platform = runtime.Platform |> needed "A reachable C import requires a resolved source PlatformDescription."
        let! core = platform.Core |> needed "A reachable C import requires a declared TargetCore.Runtime."
        do! require (Declarations.runtimeModel core = Some RuntimeModel.Libc) "A reachable C import requires source TargetCore.Runtime libc; startup or project defaults do not establish library availability."
        return () }
    let initialErrors = intrinsic.Errors @ (descriptors.Findings |> List.map (fun finding -> finding.Node, Set.singleton finding.Node, finding.Message))
    let imports, calls, errors = graph.Nodes |> Map.fold (fun (imports, calls, errors) _ node ->
        match node.Kind with
        | SemanticKind.Application(callee, args) when node.IsReachable ->
            match target graph callee with
            | Some (binding, path) when BoundaryDeclarations.isExternal binding ->
                let participants = Set.union path (Set.ofList (node.Id :: args))
                let result = checked' {
                    let! library = metadata "FidelityExtern.Library" binding |> needed "FidelityExtern.Library is missing."
                    let! symbol = metadata "FidelityExtern.Symbol" binding |> needed "FidelityExtern.Symbol is missing."
                    do! require (not (System.String.IsNullOrWhiteSpace symbol)) "FidelityExtern.Symbol must name an external declaration."
                    do! runtimeContract
                    do! require (library = "c") "This C library requires a source-settled link/load contract beyond the admitted libc boundary."
                    let! import = readImport graph descriptors binding library symbol
                    // Every import/call cites the complete domain premise,
                    // including selected-runtime and negative membership facts.
                    let import = { import with Participants = Set.add anchor.Id import.Participants }
                    let! call = readCall graph node callee args path import
                    return import, call }
                match result with
                | Ok (import, call) -> Map.add import.Identity import imports, Map.add node.Id call calls, errors
                | Error reason -> imports, calls, (node.Id, participants, reason) :: errors
            | Some ({ Kind = SemanticKind.Intrinsic info }, path) when info.Module = IntrinsicModule.Sys ->
                if info.Operation = "write" then imports, calls, errors else
                imports, calls, (node.Id, Set.union path (Set.ofList (node.Id :: args)),
                    $"Intrinsic/system boundary Sys.{info.Operation} requires CCS/Baker intrinsic boundary settlement (Layer 1); its source-owned operand and ABI contract is unsettled, and runtime or startup defaults cannot supply it.") :: errors
            | _ -> imports, calls, errors
        | _ -> imports, calls, errors) (Map.empty, Map.empty, initialErrors)
    let errors =
        imports.Values |> Seq.groupBy _.Symbol |> Seq.fold (fun errors (_, declarations) ->
            match Seq.toList declarations with
            | first :: rest -> rest |> List.fold (fun errors other ->
                let reason =
                    if first.Library <> other.Library || first.CallingConvention <> other.CallingConvention ||
                       List.map snd first.Parameters <> List.map snd other.Parameters || first.Result <> other.Result then
                        "The same imported symbol has inconsistent library or scalar ABI declarations."
                    else "The same imported symbol has multiple source declaration identities; source reconciliation is required."
                (other.Identity, Set.union first.Participants other.Participants, reason) :: errors) errors
            | [] -> errors) errors
    let leaves = imports.Values |> Seq.map _.Binding |> Set.ofSeq
    let rec declarationNodes pending found errors =
        match pending with
        | [] -> found, errors
        | id :: rest when Set.contains id found -> declarationNodes rest found errors
        | id :: rest ->
            match graph.Nodes.TryFind id with
            | Some node -> declarationNodes (node.Children @ rest) (Set.add id found) errors
            | None -> declarationNodes rest found ((id, Set.add id leaves, "A structural participant of an external declaration leaf is absent.") :: errors)
    let declarationInventory, errors = declarationNodes (Set.toList leaves) Set.empty errors
    let declarationOnly = Set.difference declarationInventory leaves
    let errors = graph.Nodes |> Map.fold (fun errors _ node ->
        if not node.IsReachable || declarationInventory.Contains node.Id then errors else
        Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence node |> List.fold (fun errors edge ->
            if edge.Class <> EdgeClass.Structural && edge.Class <> EdgeClass.Reference then errors else
            edge.Sources |> List.fold (fun errors source ->
                if declarationOnly.Contains source then
                    (node.Id, Set.ofList [node.Id; source], "An external declaration placeholder participant has an executable use outside its declaration leaf.") :: errors
                else errors) errors) errors) errors
    let proofs, errors = calls |> Map.fold (fun (enrichment, errors) _ call ->
        let argumentRanges = call.Arguments |> List.mapi (fun ordinal operand ->
            let input = match operand.Abi with BoundaryScalar.Boolean -> ValueRange.boolean | _ -> graph.Nodes[operand.Actual].ValueRange |> Option.defaultValue ValueRange.Unbounded
            ordinal, operand.Actual, input, scalarRange operand.Abi)
        let resultRange = call.Result |> Option.toList |> List.map (fun abi ->
            let destination =
                match abi with
                | BoundaryScalar.Boolean -> ValueRange.boolean
                | _ -> RangeAnalysis.selectedRepresentation graph call.Site
                       |> Option.bind Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources.declaredRange
                       |> Option.defaultValue ValueRange.Unbounded
            -1, call.Site, scalarRange abi, destination)
        argumentRanges @ resultRange |> List.fold (fun (enrichment, errors) (ordinal, operand, input, destination) ->
            match Ingredients.coverage enrichId graph call ordinal operand input destination with
            | Error reason -> enrichment, (call.Site, call.Participants, reason) :: errors
            | Ok (proof, _, outcome) ->
                let errors = if outcome = BoundaryProofOutcome.Proven then errors else
                                (call.Site, call.Participants, "The boundary range obligation is refuted: source range is not covered by its declared destination.") :: errors
                Enrichment.combine enrichment proof, errors) (enrichment, errors)) (Enrichment.empty, errors)
    let domain =
        { Premises = Ingredients.premises graph; Platform = Ingredients.platformPremise graph.Platform; Meets = graph.Codata.Value.Meets
          Declarations = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryDeclaration declaration -> Some declaration | _ -> None)
          Imports = Map.keys imports |> Seq.toList; Calls = Map.keys calls |> Seq.toList
          ByteViews = intrinsic.Views; StringExtents = intrinsic.Extents; IntrinsicDeclarations = intrinsic.Declarations
          StringComparisons = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringComparisonConstruction negated -> Some(edge.Target,negated,edge.Sources) | _ -> None)
          StringLengthComparisons = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringLengthComparison negated -> Some(edge.Target,negated,edge.Sources) | _ -> None)
          StringComparisonReads = localReads
          StringComparisonSnapshots = List.distinct localSnapshots
          StringComparisonCopies = List.distinct localCopies
          IntrinsicImports = List.distinct intrinsic.Imports; IntrinsicCalls = intrinsic.Calls; IntrinsicProofs = intrinsic.Proofs
          StringStorage = Bytes.storagePremise graph
          DeclarationLeaves = leaves; DeclarationOnly = declarationOnly
          Links = imports.Values |> Seq.map _.Library |> Set.ofSeq; Failures = List.rev errors }
    let sources = Map.keys domain.Premises |> Seq.toList
    let rows =
        [Ingredients.row (EdgeRole.BoundaryDomain domain) 0 sources anchor.Id
         { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = sources; Target = anchor.Id }]
        @ (imports.Values |> Seq.map Ingredients.importRow |> Seq.toList)
        @ (calls.Values |> Seq.collect (fun call -> Ingredients.callRow call :: Ingredients.operandRows call) |> Seq.toList)
        @ (domain.IntrinsicImports |> List.map Bytes.importRow)
        @ (domain.IntrinsicCalls |> List.collect Bytes.callRows)
    Enrichment.combine (Enrichment.combine { NewNodes = [anchor]; Annotated = []; NewEdges = rows } proofs) intrinsic.Enrichment
