namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module SequenceOwnership = Clef.Compiler.Nanopass.SequenceOwnership

// Delimiter ownership is not a cut ordinal, segment plan, or frame proof.
module private SequenceOwners =
    let check source =
        let prelude = "module Dimensions\n[<Measure>] type m\n[<Measure>] type s\n"
        match parseAndCheck (prelude + source + "\n[<EntryPoint>]\nlet main _ = ignore outer; 0\n") "sequence-ownership.clef" with
        | Success result ->
            DimensionalCases.noErrors result
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Error _ -> true | _ -> false)
            result.Graph
        | CheckFailure result -> failwithf "Expected admitted ownership source: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed ownership source: %A" errors

    let isOwnership (edge: Hyperedge) = edge.Class = EdgeClass.Suspension && edge.Role = EdgeRole.Delimiter
    let edges (graph: SemanticGraph) = graph.Edges |> List.filter isOwnership
    let owners (graph: SemanticGraph) = graph.Nodes.Values |> Seq.filter (fun node ->
        match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false) |> Seq.toList
    let cuts (graph: SemanticGraph) = graph.Nodes.Values |> Seq.filter (fun node ->
        match node.Kind with SemanticKind.Yield _ | SemanticKind.YieldBang _ -> true | _ -> false) |> Seq.toList

    let owner name (graph: SemanticGraph) =
        let binding = graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.Binding (actual, _, _, _) -> actual = name | _ -> false)
        let rec value id =
            let node = graph.Nodes[id]
            match node.Kind with
            | SemanticKind.TypeAnnotation (inner, _) -> value inner
            | SemanticKind.Sequential items -> value (List.last items)
            | SemanticKind.SeqExpr _ -> node
            | kind -> failwithf "Expected sequence value of %s: %A" name kind
        value (List.last binding.Children)

    let owned (graph: SemanticGraph) (owner: SemanticNode) =
        edges graph |> List.filter (fun edge -> edge.Sources.Head = owner.Id) |> List.map (fun edge -> graph.Nodes[edge.Target])

    let assertComplete (graph: SemanticGraph) =
        let relations = edges graph
        for cut in cuts graph do
            let relation = relations |> List.filter (fun edge -> edge.Target = cut.Id) |> Assert.Single
            Assert.Equal(0, relation.Ordinal)
            match relation.Sources with
            | [ownerId; generatorId] ->
                match graph.Nodes[ownerId].Kind, graph.Nodes[generatorId].Kind with
                | SemanticKind.SeqExpr (actual, _), SemanticKind.Lambda (_, _, _, _, LambdaContext.SeqGenerator) -> Assert.Equal(actual, generatorId)
                | kinds -> failwithf "Cut lost its actual owner and generator participants: %A" kinds
            | sources -> failwithf "Ownership relation has an unexpected participant set: %A" sources
        Assert.Equal((cuts graph).Length, relations.Length)

    let edgeFields (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
    let range: SourceRange =
        { File = "malformed-sequence.clef"; Start = { Line = 3; Column = 4 }; End = { Line = 3; Column = 22 } }

    let malformed scenario =
        let builder = NodeBuilder()
        let create kind ty children = builder.Create(kind, ty, range, children = children)
        let seqType = Types.mkSeqType Types.boolType
        let value = create (SemanticKind.Literal (NativeLiteral.Bool true)) Types.boolType []
        let cut = create (SemanticKind.Yield value.Id) Types.unitType [value.Id]
        let addOwner () =
            let pointerType = NativeType.TNativePtr seqType
            let parameter = create (SemanticKind.PatternBinding "_seq_ptr") pointerType []
            let generator = create (SemanticKind.Lambda (["_seq_ptr", pointerType, parameter.Id], cut.Id, [], None, LambdaContext.SeqGenerator)) (NativeType.TFun(pointerType, Types.boolType)) [parameter.Id; cut.Id]
            create (SemanticKind.SeqExpr (generator.Id, [])) seqType [generator.Id]
        match scenario with
        | "missing-generator" ->
            // Keep the cut owned so the only defect is the other missing generator.
            addOwner () |> ignore
            let missing = NodeId.fresh()
            create (SemanticKind.SeqExpr (missing, [])) seqType [missing] |> ignore
        | "orphan-cut" -> ()
        | "multiply-owned" -> addOwner () |> ignore; addOwner () |> ignore
        | other -> failwithf "Unknown malformed graph scenario: %s" other
        builder.Build [], cut.Id

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceOwnership")>]
type SequenceOwnershipCases() =
    [<Fact>]
    member _.``Nested sequence values own their cuts independently``() =
        let graph = SequenceOwners.check """
let outer = seq {
    let inner = seq {
        let mutable hidden = 0
        yield hidden
    }
    yield 2
}
"""
        SequenceOwners.assertComplete graph
        let outer, inner = SequenceOwners.owner "outer" graph, SequenceOwners.owner "inner" graph
        let outerCut = SequenceOwners.owned graph outer |> Assert.Single
        let innerCut = SequenceOwners.owned graph inner |> Assert.Single
        Assert.NotEqual(outerCut.Id, innerCut.Id)
        match outerCut.Kind with
        | SemanticKind.Yield value ->
            match graph.Nodes[value].Kind with
            | SemanticKind.Literal (NativeLiteral.Int (2L, _)) -> ()
            | kind -> failwithf "Outer owner acquired an inner cut: %A" kind
        | kind -> failwithf "Expected outer yield: %A" kind

    [<Theory>]
    [<InlineData("fun () -> seq { yield true }")>]
    [<InlineData("lazy (seq { yield true })")>]
    member _.``Ordinary deferred boundaries do not donate their nested sequence cuts``(expression: string) =
        let graph = SequenceOwners.check ("let outer = seq {\n    let deferred = " + expression + "\n    yield 2\n}")
        SequenceOwners.assertComplete graph
        let outer = SequenceOwners.owner "outer" graph
        let inner = SequenceOwners.owners graph |> List.filter (fun node -> node.Id <> outer.Id) |> Assert.Single
        let outerCut = SequenceOwners.owned graph outer |> Assert.Single
        let innerCut = SequenceOwners.owned graph inner |> Assert.Single
        Assert.NotEqual(outerCut.Id, innerCut.Id)
        DimensionalCases.same (Types.mkSeqType Types.intType) outer.Type
        DimensionalCases.same (Types.mkSeqType Types.boolType) inner.Type

    [<Theory>]
    [<InlineData("let outer = seq { yield! seq { yield 1 } }")>]
    [<InlineData("let input = seq { yield 1 }\nlet outer = seq { yield! input }")>]
    member _.``Delegation is an outer cut while delegated yields retain their own owner``(source: string) =
        let graph = SequenceOwners.check source
        SequenceOwners.assertComplete graph
        let outer = SequenceOwners.owner "outer" graph
        let delegated = SequenceOwners.owned graph outer |> Assert.Single
        match delegated.Kind with SemanticKind.Yield _ -> () | kind -> failwithf "Delegation has no elaborated outer yield: %A" kind
        let inner = SequenceOwners.owners graph |> List.filter (fun owner -> owner.Id <> outer.Id) |> Assert.Single
        let cut = SequenceOwners.owned graph inner |> Assert.Single
        match cut.Kind with SemanticKind.Yield _ -> () | kind -> failwithf "Expected the delegated sequence's own cut: %A" kind

    [<Theory>]
    [<InlineData("Seq.map (fun (_: int<m>) -> 2<s>) (seq { yield 1<m> })", 1)>]
    [<InlineData("Seq.filter (fun (value: int<m>) -> value > 0<m>) (seq { yield 1<m> })", 1)>]
    [<InlineData("Seq.collect (fun (_: int<m>) -> seq { yield 2<s> }) (seq { yield 1<m> })", 1)>]
    [<InlineData("Seq.append (seq { yield 1<m> }) (seq { yield 2<m> })", 2)>]
    member _.``Baker producer cuts belong to the generated sequence rather than its inputs``(expression: string, count: int) =
        let graph = SequenceOwners.check ("let outer = " + expression)
        SequenceOwners.assertComplete graph
        let outer = SequenceOwners.owner "outer" graph
        let cuts = SequenceOwners.owned graph outer
        Assert.Equal(count, cuts.Length)
        for cut in cuts do
            match cut.Kind with
            | SemanticKind.Yield _ -> ()
            | kind -> failwithf "Unexpected producer cut: %A" kind

    [<Theory>]
    [<InlineData(true)>]
    [<InlineData(false)>]
    member _.``Ownership enrichment preserves guarded cuts and surrounding effects without segmentation``(guarded: bool) =
        let middle = if guarded then "    if false then yield 1\n    if true then yield 2\n    if gate () then yield 3\n" else ""
        let graph = SequenceOwners.check ("let mutable trace = 0\nlet gate () = trace = 0\nlet outer: seq<int> = seq {\n    trace <- 1\n" + middle + "    trace <- 2\n}")
        SequenceOwners.assertComplete graph
        let owner = SequenceOwners.owner "outer" graph
        Assert.Equal((if guarded then 3 else 0), (SequenceOwners.owned graph owner).Length)
        Assert.Equal(2, graph.Nodes.Values |> Seq.filter (fun node -> match node.Kind with SemanticKind.Set _ -> true | _ -> false) |> Seq.length)
        let stripped = { graph with Edges = graph.Edges |> List.filter (SequenceOwners.isOwnership >> not) }
        let enrichment, diagnostics = SequenceOwnership.elaborate stripped
        Assert.Empty diagnostics
        let updated = SequenceOwnership.foldIn enrichment stripped
        Assert.Same(graph.Nodes, updated.Nodes)
        Assert.Equal<(EdgeClass * EdgeRole * int * NodeId list * NodeId) list>(graph.Edges |> List.map SequenceOwners.edgeFields |> List.sort, updated.Edges |> List.map SequenceOwners.edgeFields |> List.sort)

    [<Theory>]
    [<InlineData("missing-generator")>]
    [<InlineData("orphan-cut")>]
    [<InlineData("multiply-owned")>]
    member _.``Malformed ownership is diagnosed without inventing an ambiguous delimiter``(scenario: string) =
        let graph, cut = SequenceOwners.malformed scenario
        let normalized, diagnostics = SequenceOwnership.normalize graph
        let diagnostic = diagnostics |> List.filter (fun diagnostic ->
            diagnostic.Code = "CCS8402" && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error) |> Assert.Single
        Assert.Equal<SourceRange>(SequenceOwners.range, diagnostic.Range)
        Assert.Same(graph.Nodes, normalized.Nodes)
        if scenario <> "missing-generator" then
            Assert.DoesNotContain(SequenceOwners.edges normalized, fun edge -> edge.Target = cut)

    [<Fact>]
    member _.``Normalization is idempotent and retracts stale ownership while preserving proof relations``() =
        let graph = SequenceOwners.check "let outer = seq { yield 1 }"
        let owner = SequenceOwners.owner "outer" graph
        let cut = SequenceOwners.owned graph owner |> Assert.Single
        let stale = { Sources = [owner.Id; owner.Id]; Target = cut.Id; Class = EdgeClass.Suspension; Role = EdgeRole.Delimiter; Ordinal = 99 }
        let withStale = { graph with Edges = stale :: graph.Edges }
        let corrected, diagnostics = SequenceOwnership.normalize withStale
        Assert.Empty diagnostics
        SequenceOwners.assertComplete corrected
        let repeated, diagnostics = SequenceOwnership.normalize corrected
        Assert.Empty diagnostics
        Assert.Equal<(EdgeClass * EdgeRole * int * NodeId list * NodeId) list>(corrected.Edges |> List.map SequenceOwners.edgeFields, repeated.Edges |> List.map SequenceOwners.edgeFields)
        Assert.Same(graph.Nodes, corrected.Nodes)
        let otherEdges = graph.Edges |> List.filter (SequenceOwners.isOwnership >> not)
        Assert.Contains(otherEdges, fun edge -> edge.Class = EdgeClass.Obligation)
        let replacement = { cut with Kind = SemanticKind.Literal NativeLiteral.Unit; Type = Types.unitType; Children = [] }
        let changed = { corrected with Nodes = Map.add cut.Id replacement corrected.Nodes }
        let retracted, diagnostics = SequenceOwnership.normalize changed
        Assert.Empty diagnostics
        Assert.Empty(SequenceOwners.edges retracted)
        Assert.Equal<(EdgeClass * EdgeRole * int * NodeId list * NodeId) list>(otherEdges |> List.map SequenceOwners.edgeFields, retracted.Edges |> List.map SequenceOwners.edgeFields)
        Assert.Same(changed.Nodes, retracted.Nodes)
        Assert.Equal(99, withStale.Edges.Head.Ordinal)
