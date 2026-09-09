// SPDX-License-Identifier: MIT

/// Obligation Elaboration -- Pass 5.
///
/// The pass: discover the subjects obligations are stated over (reachable
/// string literals, String.concat2 sites, the Sys.readline site), read the
/// declared platform the program was cross-compiled with, apply the Baker
/// obligation recipes, and fold the result into the graph. The recipes and
/// their ingredients live in Baker; this module only orchestrates.
///
/// Runs after final reachability, over the saturated graph: the layout
/// obligation needs the complete reachable literal set, and no obligation is
/// minted for a dead literal. Under the saturation lattice this becomes a rule
/// that fires when its sources are Saturated; today it is a fixed position.
///
/// Pure: `elaborate` projects an Enrichment; `foldIn` returns a new graph.
module Clef.Compiler.Nanopass.ObligationElaboration

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration
open Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.Baker.Ingredients.Obligations
module Recipes = Clef.Compiler.Baker.Recipes.ObligationRecipes
module RangeAnalysis = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis
module MappedBindings = Clef.Compiler.PSGSaturation.SemanticGraph.MappedBindings
module MappedSpans = Clef.Compiler.PSGSaturation.SemanticGraph.MappedSpans

//=============================================================================
// SUBJECT DISCOVERY
//=============================================================================

/// Every reachable string literal: entry-unit strings first in source order,
/// then library strings, distinct by content -- exactly the set the emission
/// places.
let private reachableLiterals (graph: SemanticGraph) : (string * SemanticNode) list =
    let entryFile =
        match graph.DeclarationRoots with
        | (entryId, _) :: _ -> SemanticGraph.tryGetNode entryId graph |> Option.map (fun n -> n.Range.File) |> Option.defaultValue ""
        | [] -> ""
    graph.Nodes
    |> Map.toList
    |> List.map snd
    |> List.filter (fun n -> n.IsReachable)
    |> List.choose (fun n ->
        match n.Kind with
        | SemanticKind.Literal (NativeLiteral.String s) -> Some (s, n)
        | _ -> None)
    |> List.sortBy (fun (_, n) -> (if n.Range.File = entryFile then 0 else 1), n.Range.File, n.Range.Start.Line, n.Range.Start.Column)
    |> List.distinctBy fst

let rec private intrinsicOf (graph: SemanticGraph) (id: NodeId) : IntrinsicInfo option =
    match SemanticGraph.tryGetNode id graph with
    | Some ({ Kind = SemanticKind.Intrinsic info } : SemanticNode) -> Some info
    | Some ({ Kind = SemanticKind.TypeAnnotation (inner, _) } : SemanticNode) -> intrinsicOf graph inner
    | _ -> None

let private literalOperand (graph: SemanticGraph) (id: NodeId) : (int * string) option =
    match SemanticGraph.tryGetNode id graph with
    | Some ({ Kind = SemanticKind.Literal (NativeLiteral.String s) } : SemanticNode) -> Some (byteLength s, s)
    | _ -> None

/// Reachable applications of a named intrinsic, in source order.
let private intrinsicSites (graph: SemanticGraph) (m: IntrinsicModule) (op: string) : (SemanticNode * NodeId list) list =
    graph.Nodes
    |> Map.toList
    |> List.map snd
    |> List.filter (fun n -> n.IsReachable)
    |> List.choose (fun n ->
        match n.Kind with
        | SemanticKind.Application (funcId, args) ->
            match intrinsicOf graph funcId with
            | Some info when info.Module = m && info.Operation = op -> Some (n, args)
            | _ -> None
        | _ -> None)
    |> List.sortBy (fun (n, _) -> n.Range.File, n.Range.Start.Line, n.Range.Start.Column)

/// concat2 sites with their operands, named and uniquified in source order.
let private concatSites (graph: SemanticGraph) =
    intrinsicSites graph IntrinsicModule.String "concat2"
    |> List.choose (fun (site, args) ->
        match args with
        | [ leftId; rightId ] ->
            let left, right = literalOperand graph leftId, literalOperand graph rightId
            let baseSlug =
                match right, left with
                | Some (_, c), _ | _, Some (_, c) -> sprintf "concat_%s" (slug c)
                | None, None -> "concat_dynamic"
            Some (baseSlug, (site, leftId, rightId, left, right))
        | _ -> None)
    |> uniquify

/// Measured arithmetic and comparison sites, including formal measure
/// variables. Missing numeric facts never become dimensionless defaults.
let private dimensionalSites (graph: SemanticGraph) =
    let dimension (node: SemanticNode) =
        // buildResult has already resolved graph types. Re-reading the global
        // inference store here would couple retained snapshots to later checks.
        match node.Type with
        | NativeType.TNum (_, dim) -> Some dim
        | _ -> None
    let ruleFor = function
        | "op_Multiply" -> Some DimensionalRule.Product
        | "op_Division" -> Some DimensionalRule.Quotient
        | "op_Addition" | "op_Subtraction" | "op_Modulus" -> Some DimensionalRule.SameDimension
        | "op_LessThan" | "op_GreaterThan" | "op_LessThanOrEqual"
        | "op_GreaterThanOrEqual" | "op_Equality" | "op_Inequality" -> Some DimensionalRule.Comparison
        | _ -> None
    let measured dim = not (Map.isEmpty dim.Bases && Map.isEmpty dim.Vars)
    graph.Nodes
    |> Map.toList
    |> List.map snd
    |> List.filter (fun n -> n.IsReachable)
    |> List.sortBy (fun n -> n.Range.File, n.Range.Start.Line, n.Range.Start.Column, n.Id)
    |> List.choose (fun site ->
        match site.Kind with
        | SemanticKind.Application (funcId, [ leftId; rightId ]) ->
            match intrinsicOf graph funcId, SemanticGraph.tryGetNode leftId graph, SemanticGraph.tryGetNode rightId graph with
            | Some info, Some left, Some right when info.Module = IntrinsicModule.Operators ->
                match ruleFor info.Operation, dimension left, dimension right with
                | Some rule, Some leftDim, Some rightDim ->
                    let resultDim = if rule = DimensionalRule.Comparison then None else dimension site
                    if (rule = DimensionalRule.Comparison || Option.isSome resultDim)
                       && List.exists measured (leftDim :: rightDim :: Option.toList resultDim) then
                        Some ("dimension_" + info.Operation, (site, left, right, rule, leftDim, rightDim, resultDim))
                    else None
                | _ -> None
            | _ -> None
        | _ -> None)
    |> uniquify

/// Dimensional leaves are immutable graph facts. Paths preserve type shape
/// and nominal constructor ownership; no inference cells are read here.
let rec private dimensionsAt path ty : (string * Dimension) list =
    let at suffix = dimensionsAt (path + suffix)
    match ty with
    | NativeType.TNum (_, dimension) -> [path + ".numeric", dimension]
    | NativeType.TMeasure dimension -> [path + ".measure", dimension]
    | NativeType.TFun (domain, result) -> at ".domain" domain @ at ".result" result
    | NativeType.TTuple (elements, isStruct) ->
        elements |> List.mapi (fun i element -> at (sprintf ".tuple(%b)[%d]" isStruct i) element) |> List.concat
    | NativeType.TApp (constructor, arguments) ->
        arguments |> List.mapi (fun i argument -> at (sprintf ".type(%A,%A)[%d]" constructor.Module constructor.Name i) argument) |> List.concat
    | NativeType.TAnon (fields, isStruct) ->
        fields |> List.collect (fun (name, field) -> at (sprintf ".record(%b)[%A]" isStruct name) field)
    | NativeType.TUnion (constructor, cases) ->
        cases |> List.collect (fun case ->
            case.Fields |> List.mapi (fun i (_, field) ->
                at (sprintf ".union(%A,%A).case[%d].field[%d]" constructor.Module constructor.Name case.Index i) field) |> List.concat)
    | NativeType.TByref (element, kind) -> at (sprintf ".byref(%A)" kind) element
    | NativeType.TNativePtr element -> at ".pointer" element
    | NativeType.TLazy element -> at ".lazy" element
    | NativeType.TSeq element -> at ".seq" element
    | NativeType.TSeqEnumerator element -> at ".enumerator" element
    | NativeType.TList element -> at ".list" element
    | NativeType.TMap (key, value) -> at ".mapKey" key @ at ".mapValue" value
    | NativeType.TSet element -> at ".set" element
    // Generic signatures must have been instantiated at their occurrence.
    // Unresolved/error types contribute no fabricated dimensional leaves.
    | NativeType.TForall _ | NativeType.TVar _ | NativeType.TError _ -> []

let private applicationSites (graph: SemanticGraph) =
    let rec definitionOf id =
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.VarRef (_, Some definition) } when Map.containsKey definition graph.Nodes -> Some definition
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> definitionOf inner
        | _ -> None
    let rec signature arguments ty =
        match arguments, ty with
        | [], remainder -> Some ([], remainder)
        | _ :: rest, NativeType.TFun (domain, result) ->
            signature rest result |> Option.map (fun (domains, remainder) -> domain :: domains, remainder)
        | _ -> None
    let compare path expected actual =
        let expected = dimensionsAt path expected |> Map.ofList
        let actual = dimensionsAt path actual |> Map.ofList
        Set.union (expected |> Map.keys |> Set.ofSeq) (actual |> Map.keys |> Set.ofSeq)
        |> Set.toList |> List.map (fun position -> position, Map.tryFind position expected, Map.tryFind position actual)
    let relevant (_, expected, actual) =
        match expected, actual with
        | Some left, Some right ->
            [left; right] |> List.exists (fun dim -> not (Map.isEmpty dim.Bases && Map.isEmpty dim.Vars))
        | _ -> true
    graph.Nodes |> Map.toList |> List.map snd
    |> List.filter (fun node -> node.IsReachable)
    |> List.sortBy (fun node -> node.Range.File, node.Range.Start.Line, node.Range.Start.Column, node.Id)
    |> List.choose (fun site ->
        match site.Kind with
        | SemanticKind.Application (calleeId, argumentIds) when not argumentIds.IsEmpty && (intrinsicOf graph calleeId).IsNone ->
            match SemanticGraph.tryGetNode calleeId graph with
            | Some callee ->
                let arguments = argumentIds |> List.choose (fun id -> SemanticGraph.tryGetNode id graph)
                match signature argumentIds callee.Type with
                | Some (domains, result) when arguments.Length = argumentIds.Length ->
                    let comparisons =
                        List.map3 (fun i expected (actual: SemanticNode) -> compare (sprintf "argument %d" (i + 1)) expected actual.Type)
                            [0 .. arguments.Length - 1] domains arguments
                        |> List.concat
                    let comparisons = comparisons @ compare "result" result site.Type
                    if List.exists relevant comparisons then
                        Some ("dimension_application", (site, callee, arguments, definitionOf calleeId, comparisons))
                    else None
                | _ -> None
            | None -> None
        | _ -> None)
    |> uniquify

//=============================================================================
// THE PASS
//=============================================================================

let private entrySubject (graph: SemanticGraph) =
    let entryBinding (node: SemanticNode) =
        match node.Kind with
        | SemanticKind.Binding (_, _, _, Some DeclRoot.EntryPoint)
        | SemanticKind.Binding ("main", _, _, None) -> Some node
        | _ -> None
    graph.DeclarationRoots
    |> List.collect (fun (id, kind) ->
        if kind <> DeclRoot.EntryPoint then []
        else
            match SemanticGraph.tryGetNode id graph with
            | Some { Kind = SemanticKind.ModuleDef (_, members) } ->
                members |> List.choose (fun id -> SemanticGraph.tryGetNode id graph |> Option.bind entryBinding)
            | Some node -> entryBinding node |> Option.toList
            | None -> [])
    |> List.distinctBy (fun node -> node.Id)
    |> function [node] -> Some node | _ -> None

/// Project the obligation enrichment from the saturated graph.
let elaborate (graph: SemanticGraph) : Enrichment =
    let platform = resolve graph
    let rodata = platform |> Option.bind (spaceNamed "rodata")
    let enrichId = freshId ()
    let literals = reachableLiterals graph
    let namedLiterals = literals |> List.map (fun (c, n) -> slug c, (c, n)) |> uniquify
    let readln =
        match platform |> Option.bind (fun p -> bufferNamed "consoleReadln" p |> Option.map (fun b -> p, b)) with
        | Some (p, b) -> intrinsicSites graph IntrinsicModule.Sys "readline" |> List.map (fun (site, _) -> Recipes.readln p b enrichId site)
        | None -> []
    Enrichment.concat
        [ namedLiterals |> List.map (Recipes.literal rodata enrichId) |> Enrichment.concat
          concatSites graph |> List.map (Recipes.concat enrichId) |> Enrichment.concat
          dimensionalSites graph |> List.map (Recipes.dimensional enrichId) |> Enrichment.concat
          applicationSites graph |> List.map (Recipes.application enrichId) |> Enrichment.concat
          Enrichment.concat readln ]

/// The integer range pass has already settled each literal's enclosure and
/// selection. This observer consumes those facts and the selected declaration.
let private elaborateIntegers (graph: SemanticGraph) (core: DeclaredCore option) (enrichId: int) : Enrichment * Diagnostic list =
    let sites =
        graph.Nodes |> Map.toList |> List.map snd
        |> List.filter (fun node -> node.IsReachable && (Types.tryGetNTUKind node.Type |> Option.exists NTUKind.isInteger))
        |> List.choose (fun node ->
            match node.Kind with
            | SemanticKind.Literal (NativeLiteral.Int (value, _)) -> Some ("integer_literal", (node, bigint value))
            | SemanticKind.Literal (NativeLiteral.UInt (value, _)) -> Some ("integer_literal", (node, bigint value))
            | _ -> None)
        |> uniquify
    let integer (text: string) =
        match System.Numerics.BigInteger.TryParse(text, System.Globalization.NumberStyles.AllowLeadingSign, System.Globalization.CultureInfo.InvariantCulture) with
        | true, value -> Some value
        | _ -> None
    let results = sites |> List.map (fun (name, (site, value)) ->
        let error code message =
            { Severity = NativeDiagnosticSeverity.Error; Code = code; Message = message
              Range = site.Range; RelatedNodes = [site.Id]; Reachability = ReachabilityContext.Reachable }
        match site.ValueRange with
        | Some (ValueRange.Bounded (lower, upper)) ->
            let range = Recipes.integerLiteral enrichId name site value lower upper
            let rangeErrors =
                if lower <= value && value <= upper then []
                else [error "CCS8012" (sprintf "The analysed range [%A, %A] does not contain integer literal %A." lower upper value)]
            let selected = RangeAnalysis.selectedRepresentation graph site.Id
            match selected, core with
            | None, None -> range, rangeErrors
            | None, Some _ when graph.Platform |> Option.exists (fun context -> PlatformContext.substrateKind context = SubstrateKind.FPGA) -> range, rangeErrors
            | None, Some _ -> range, rangeErrors @ [error "CCS8204" "No platform representation was selected for this analysed integer literal."]
            | Some _, None -> range, rangeErrors @ [error "CCS8206" "The selected integer representation has no source platform declaration."]
            | Some selected, Some core ->
                match core.Representations |> List.filter (fun declared -> declared.Representation.Name = selected.Name) with
                | [declared] when declared.Representation = selected && NumericRepresentation.isOffered selected ->
                    match integer selected.MinMagnitude, integer selected.MaxMagnitude with
                    | Some minimum, Some maximum when minimum <= maximum ->
                        let coverage = Recipes.integerCoverage enrichId (name + "_coverage") site lower upper declared minimum maximum
                        let coverageErrors =
                            if minimum <= lower && lower <= upper && upper <= maximum then []
                            else [error "CCS8012" (sprintf "The analysed integer range [%A, %A] is outside the declared bounds of selected representation %s." lower upper selected.Name)]
                        Enrichment.combine range coverage, rangeErrors @ coverageErrors
                    | _ -> range, rangeErrors @ [error "CCS8206" (sprintf "Cannot read ordered integer bounds for selected representation %s." selected.Name)]
                | [] -> range, rangeErrors @ [error "CCS8204" (sprintf "Selected integer representation %s has no matching platform declaration." selected.Name)]
                | [_] -> range, rangeErrors @ [error "CCS8206" (sprintf "Selected integer representation %s disagrees with its source declaration." selected.Name)]
                | _ -> range, rangeErrors @ [error "CCS8208" (sprintf "Multiple platform declarations name selected integer representation %s." selected.Name)]
        | _ -> Enrichment.empty, [error "CCS8011" (sprintf "Integer literal %A has no finite analysed range for proof dispatch." value)])
    results |> List.map fst |> Enrichment.concat, results |> List.collect snd

/// Obligations requiring settled platform facts run after range/placement.
/// This first real-valued slice seeds source singleton ranges and checks the
/// current concrete literal representation; real-expression selection remains
/// a separate range-analysis responsibility.
let elaborateSettled (graph: SemanticGraph) : Enrichment * Diagnostic list =
    let core = resolve graph |> Option.bind (fun platform -> platform.Core)
    let enrichId = freshId ()
    let sites =
        graph.Nodes |> Map.toList |> List.map snd
        |> List.filter (fun node -> node.IsReachable)
        |> List.choose (fun node ->
            match node.Kind, Map.tryFind "Numeric.RealLiteral" node.Metadata with
            | SemanticKind.Literal (NativeLiteral.Float(_, NTUKind.NTUfloat (NTUWidth.Fixed bits))), Some (MetadataValue.RealLiteral(source, value)) ->
                Some ("real_literal", (node, source, value, bits))
            | _ -> None)
        |> uniquify
    let enrichments, diagnostics =
        sites |> List.map (fun (name, (site, source, value, bits)) ->
            let point = Recipes.realLiteral enrichId (name, (site, source, value))
            let error code message =
                { Severity = NativeDiagnosticSeverity.Error; Code = code; Message = message
                  Range = site.Range; RelatedNodes = [site.Id]; Reachability = ReachabilityContext.Reachable }
            match core with
            | None -> point, [] // No representation commitment without a platform declaration.
            | Some core ->
                let candidates = core.Representations |> List.filter (fun declared ->
                    declared.Representation.Family = "ieee" && declared.Representation.Bits = bits
                    && NumericRepresentation.isOffered declared.Representation)
                match candidates with
                | [declared] ->
                    let representation = declared.Representation
                    match ExactRational.tryParseDecimal representation.MinMagnitude, ExactRational.tryParseDecimal representation.MaxMagnitude with
                    | Ok minimum, Ok maximum ->
                        let coverage = Recipes.realCoverage enrichId site (name + "_coverage") source value declared minimum maximum
                        let le a b = a.Numerator * b.Denominator <= b.Numerator * a.Denominator
                        let diagnostics =
                            if le minimum value && le value maximum then []
                            else [error "CCS8012" (sprintf "The exact source value %s is outside the declared finite bounds of %s." source representation.Name)]
                        Enrichment.combine point coverage, diagnostics
                    | _ -> point, [error "CCS8206" (sprintf "Cannot read exact real bounds for declared representation %s." representation.Name)]
                | [] -> point, [error "CCS8204" (sprintf "The platform does not offer the current literal's IEEE representation (%d bits)." bits)]
                | _ -> point, [error "CCS8208" (sprintf "Multiple platform declarations describe the current literal's IEEE representation (%d bits)." bits)])
        |> List.unzip
    let integers, integerDiagnostics = elaborateIntegers graph core enrichId
    let mapped =
        graph.Nodes.Values |> Seq.choose (fun site ->
            match site.Kind with
            | SemanticKind.Application (callee, arguments) when site.IsReachable ->
                MappedBindings.tryFindCall graph callee |> Option.bind (fun mapping ->
                    if arguments.Length <> mapping.Parameters.Length then None
                    else
                        match MappedSpans.ofMapping graph mapping with
                        | Ok model ->
                            let sources = mapping.Node :: mapping.AcquireBinding :: mapping.ReleaseBinding :: arguments @ MappedSpans.declarationSources graph mapping
                            Some (Recipes.mappedElementSpan enrichId site sources model)
                        | Result.Error _ -> None) // Declaration/lowering diagnostics reject malformed mapped contracts.
            | _ -> None) |> Seq.toList |> Enrichment.concat
    let layout =
        match graph.StaticStringPool with
        | Some pool ->
            pool.Entries |> List.collect (fun item -> item.NodeIds)
            |> List.tryPick (fun id -> SemanticGraph.tryGetNode id graph)
            |> Option.map (fun subject -> Recipes.staticStorageLayout enrichId (entrySubject graph) subject pool)
            |> Option.defaultValue Enrichment.empty
        | None -> Enrichment.empty
    Enrichment.concat [Enrichment.concat enrichments; integers; layout; mapped], List.concat diagnostics @ integerDiagnostics

/// Project every obligation hyperedge onto its source nodes as an
/// `Obligation.Anchors` annotation: the hyperedge's consequence on alpha (PHG
/// paper 2.4a). Derived from F after the recipes have minted it, so a node
/// constrained by several obligations carries all of their anchors and no
/// recipe has to know about another. Declaration nodes are annotated too;
/// they are never emitted, and they are constrained.
let private projectAnchors (e: Enrichment) (graph: SemanticGraph) : SemanticNode list =
    let obligationId (target: NodeId) =
        e.NewNodes |> List.tryPick (fun n ->
            match n.Kind with
            | SemanticKind.Obligation info when n.Id = target -> Some info.Id
            | _ -> None)
    let anchorsBySource =
        e.NewEdges
        |> List.filter (fun edge -> edge.Class = EdgeClass.Obligation)
        |> List.fold (fun (acc: Map<NodeId, string list>) edge ->
            match obligationId edge.Target with
            | Some anchor ->
                edge.Sources |> List.fold (fun acc src ->
                    let existing = Map.tryFind src acc |> Option.defaultValue []
                    Map.add src (existing @ [ anchor ]) acc) acc
            | None -> acc) Map.empty
    // Annotate over the already-annotated form of a node where one exists
    // (the readln site carries Buffer.* too), else over the graph's node.
    let current (id: NodeId) =
        e.Annotated |> List.tryFind (fun n -> n.Id = id)
        |> Option.orElse (SemanticGraph.tryGetNode id graph)
    anchorsBySource
    |> Map.toList
    |> List.choose (fun (id, anchors) ->
        current id |> Option.map (fun n ->
            let existing =
                match Map.tryFind ObligationMetadata.Anchors n.Metadata with
                | Some (MetadataValue.StringList values) -> values
                | _ -> []
            { n with Metadata = n.Metadata |> Map.add ObligationMetadata.Anchors (MetadataValue.StringList (List.distinct (existing @ anchors))) }))

/// Fold the enrichment into the graph: annotated nodes replace their originals
/// by id, obligation nodes join V, their hyperedges join F, and every source
/// of an obligation edge carries its anchors.
let foldIn (e: Enrichment) (graph: SemanticGraph) : SemanticGraph =
    graph
    |> SemanticGraph.addNodes e.Annotated
    |> SemanticGraph.addNodes (projectAnchors e graph)
    |> SemanticGraph.addNodes e.NewNodes
    |> SemanticGraph.addEdges e.NewEdges
