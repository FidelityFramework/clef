namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module FiniteCells = Clef.Compiler.PSGSaturation.SemanticGraph.FiniteCellRanges
module CellRanges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis

module private FiniteCellFixture =
    let check source =
        match parseAndCheck ("module FiniteCells\n" + source) "finite-cells.clef" with
        | Success result | CheckFailure result ->
            Assert.Empty(result.Diagnostics |> List.filter (fun diagnostic -> Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error))
            result.Graph
        | ParseFailure errors -> failwithf "%A" errors

    let source = """
let mutable state = 0
let record digit = state <- state * 10 + digit
let twice digit =
    record digit
    record digit
[<EntryPoint>]
let main _ =
    twice 1
    record 2
    state <- 0
    record 4
    state
"""
    let cell (graph: SemanticGraph) = graph.Nodes.Values |> Seq.filter (fun node ->
        node.IsReachable && match node.Kind with SemanticKind.Binding("state", true, _, _) -> true | _ -> false) |> Assert.Single
    let proof graph = FiniteCells.recognize graph |> Assert.Single
    let analyze graph = CellRanges.run graph.Platform graph |> fst
    let obligations (graph: SemanticGraph) = graph.Nodes.Values |> Seq.filter (fun node ->
        match node.Kind with SemanticKind.Obligation info -> info.Kind = "finite-cell-effects" | _ -> false) |> Seq.toList

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "FiniteCellRanges")>]
type FiniteCellRangeCases() =
    [<Fact>]
    member _.``Repeated acyclic invocations multiply activation counts rather than count syntax`` () =
        let graph = FiniteCellFixture.check FiniteCellFixture.source
        let proof = FiniteCellFixture.proof graph
        Assert.Equal(5I, proof.Certificate.MaximumIterations)
        Assert.Equal<bigint list>([1I; 4I], proof.Writes |> List.map _.MaximumActivations |> List.sort)
        Assert.Equal<bigint list>([44444I; 1I], proof.Certificate.Upper)
        Assert.Equal(Some(ValueRange.Bounded(0I, 44444I)), (FiniteCellFixture.cell graph).ValueRange)
        Assert.Contains((FiniteCellFixture.cell graph).Id, proof.Participants)
        for write in proof.Writes do
            Assert.Contains(write.Store, proof.Participants)
            Assert.Contains(write.Value, proof.Participants)

    [<Fact>]
    member _.``Signed affine updates retain every possible ordering prefix`` () =
        let graph = FiniteCellFixture.check """
let mutable state = -2
let update delta = state <- state * -3 + delta
[<EntryPoint>]
let main _ =
    update -5
    update 7
    state
"""
        let proof = FiniteCellFixture.proof graph
        Assert.Equal(2I, proof.Certificate.MaximumIterations)
        Assert.Equal<bigint list>([46I; 1I], proof.Certificate.Upper)
        match (FiniteCellFixture.cell graph).ValueRange with
        | Some(ValueRange.Bounded(lo, hi)) -> Assert.True(lo >= -46I && hi <= 46I)
        | actual -> failwithf "Expected finite signed enclosure, got %A" actual

    [<Theory>]
    [<InlineData("loop")>]
    [<InlineData("recursion")>]
    [<InlineData("callback")>]
    [<InlineData("unknown-update")>]
    member _.``Unproved repetition or nonaffine writers cannot retain a finite proof`` defect =
        let body =
            match defect with
            | "loop" -> "while true do record 1\n    state"
            | "recursion" -> "repeat 2\n    state"
            | "callback" -> "Seq.iter record (seq { yield 1 })\n    state"
            | _ -> "state <- state * state\n    state"
        let recursive = if defect = "recursion" then "let rec repeat x = record x; repeat x\n" else ""
        let graph = FiniteCellFixture.check (
            "let mutable state = 0\nlet record digit = state <- state * 10 + digit\n" + recursive +
            "[<EntryPoint>]\nlet main _ =\n    " + body + "\n")
        Assert.Empty(FiniteCells.recognize graph)

    [<Fact>]
    member _.``Startup authority and source type edits retract the current conclusion`` () =
        let graph = FiniteCellFixture.check FiniteCellFixture.source
        FiniteCellFixture.proof graph |> ignore
        let removed = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramInitialization) }
        Assert.Empty(FiniteCells.recognize removed)
        let cell = FiniteCellFixture.cell graph
        let changed = { graph with Nodes = graph.Nodes.Add(cell.Id, { cell with Type = Types.boolType }) }
        Assert.Empty(FiniteCells.recognize changed)
        Assert.Empty(FiniteCellFixture.obligations (FiniteCells.settle [] changed))
        FiniteCellFixture.proof graph |> ignore

    [<Fact>]
    member _.``Contradictory current reference rows invalidate the proof even with old ranges`` () =
        let graph = FiniteCellFixture.check FiniteCellFixture.source
        let proof = FiniteCellFixture.proof graph
        let reference = graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.VarRef(_, Some source) -> source = proof.Cell | _ -> false)
        let wrong = { Class = EdgeClass.Reference; Role = EdgeRole.Definition; Ordinal = 0
                      Sources = [proof.Writes.Head.Value]; Target = reference.Id }
        let changed = { graph with Edges = wrong :: graph.Edges }
        Assert.Empty(FiniteCells.recognize changed)
        Assert.Empty(FiniteCellFixture.obligations (FiniteCellFixture.analyze changed))

    [<Fact>]
    member _.``Unchanged settlement retains exact certificate identity and joint participants`` () =
        let graph = FiniteCellFixture.check FiniteCellFixture.source
        let before = FiniteCellFixture.obligations graph |> Assert.Single
        let refreshed = FiniteCellFixture.analyze graph
        let after = FiniteCellFixture.obligations refreshed |> Assert.Single
        Assert.Equal(before.Id, after.Id)
        let proof = FiniteCellFixture.proof refreshed
        let row = refreshed.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains && edge.Target = after.Id) |> Assert.Single
        Assert.Equal<Set<NodeId>>(proof.Participants, Set.ofList row.Sources)

    [<Fact>]
    member _.``Ordinary affine bounds do not impersonate dimensional compatibility`` () =
        let graph = FiniteCellFixture.check """
[<Measure>] type m
let mutable state = 0<m>
let record delta = state <- state * 10 + delta
[<EntryPoint>]
let main _ =
    record 2<m>
    if state = 2<m> then 0 else 1
"""
        let proof = FiniteCellFixture.proof graph
        Assert.Equal(2I, proof.Certificate.Upper.Head)
        let factor = graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Literal(NativeLiteral.Int(10L, _)) -> true | _ -> false)
        let changed = { graph with Nodes = graph.Nodes.Add(factor.Id, { factor with Type = graph.Nodes[proof.Cell].Type }) }
        Assert.Empty(FiniteCells.recognize changed)

    [<Fact>]
    member _.``Shared formal occurrences cannot select the last implementation owner`` () =
        let graph = FiniteCellFixture.check FiniteCellFixture.source
        FiniteCellFixture.proof graph |> ignore
        let implementation = graph.Nodes.Values |> Seq.find (fun node ->
            match node.IsReachable, node.Kind with
            | true, SemanticKind.Lambda(parameters, _, _, _, _) -> parameters |> List.exists (fun (name, _, _) -> name = "digit")
            | _ -> false)
        let other = { implementation with Id = NodeId.fresh(); Parent = None }
        let changed = { graph with Nodes = graph.Nodes.Add(other.Id, other) }
        Assert.Empty(FiniteCells.recognize changed)

    [<Fact>]
    member _.``An independent reference to the entry invalidates single activation authority`` () =
        let graph = FiniteCellFixture.check FiniteCellFixture.source
        FiniteCellFixture.proof graph |> ignore
        let startup = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read graph |> Option.get
        let source = graph.Nodes[startup.EntryBinding]
        let escaped = { source with Id = NodeId.fresh(); Kind = SemanticKind.VarRef("entry", Some startup.EntryBinding)
                                    Children = []; Parent = None }
        let changed = { graph with Nodes = graph.Nodes.Add(escaped.Id, escaped) }
        Assert.Empty(FiniteCells.recognize changed)
