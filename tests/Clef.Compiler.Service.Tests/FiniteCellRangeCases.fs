namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module FiniteCells = Clef.Compiler.PSGSaturation.SemanticGraph.FiniteCellRanges
module CellRanges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis

module private FiniteCellFixture =
    let private parse source =
        parseAndCheck ("module FiniteCells\n" + source) "finite-cells.clef"

    let check source =
        match parse source with
        | Success result | CheckFailure result ->
            Assert.Empty(result.Diagnostics |> List.filter (fun diagnostic -> Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error))
            result.Graph
        | ParseFailure errors -> failwithf "%A" errors

    let rejected recursive source =
        match parse source with
        | CheckFailure result ->
            let message subject owner =
                sprintf "The range of '%s' in '%s' cannot be observed; bound it with a comparison, a modulus or a clamp" subject owner
            let shift = if recursive then 1 else 0
            let expected =
                [ message "state" "__clef_program_entry", 2, 12, 2, 17
                  message "the result of '*'" "record", 3, 28, 3, 38
                  message "main" "main", 6 + shift, 4, 7 + shift, 9
                  message "main …" "__clef_program_entry", 4 + shift, 0, 4 + shift, 0 ]
            let actual = CheckResult.errors result |> List.map (fun diagnostic ->
                Assert.Equal("CCS8011", diagnostic.Code)
                Assert.Equal("finite-cells.clef", diagnostic.Range.File)
                let node = result.Graph.Nodes[Assert.Single diagnostic.RelatedNodes]
                Assert.True(node.IsReachable)
                Assert.True((node.Range = diagnostic.Range), "The refusal must identify its actual source node")
                Assert.True(node.ValueRange |> Option.exists (ValueRange.isObservable >> not), "The rejected source node must remain nonobservable")
                diagnostic.Message, diagnostic.Range.Start.Line, diagnostic.Range.Start.Column,
                diagnostic.Range.End.Line, diagnostic.Range.End.Column)
            Assert.Equal<(string * int * int * int * int) list>(List.sort expected, List.sort actual)
            result.Graph
        | result -> failwithf "Expected the four located finite-cell source refusals: %A" result

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
        let source =
            "let mutable state = 0\nlet record digit = state <- state * 10 + digit\n" + recursive +
            "[<EntryPoint>]\nlet main _ =\n    " + body + "\n"
        let graph =
            if defect = "unknown-update" then FiniteCellFixture.check source
            else FiniteCellFixture.rejected (defect = "recursion") source
        Assert.Empty(FiniteCells.recognize graph)
        if defect <> "unknown-update" then
            Assert.Empty(FiniteCellFixture.obligations graph)
            Assert.True((FiniteCellFixture.cell graph).ValueRange |> Option.exists (ValueRange.isObservable >> not))

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

open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module private LocalFiniteCellFixture =
    module Incidence = Clef.Compiler.Baker.Ingredients.Closures
    module Initialization = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization

    let statements = "    let mutable state = 0\n    state <- state + 1\n    state <- state + 2\n    state\n"
    let source = "[<EntryPoint>]\nlet main _ =\n" + statements
    let repeated = "let run () =\n" + statements + "[<EntryPoint>]\nlet main _ = run () + run ()\n"

    let check source activations =
        let graph = FiniteCellFixture.check source
        let cell = FiniteCellFixture.cell graph
        let startup = Initialization.read graph |> Option.get
        Assert.DoesNotContain(cell.Id, startup.ValueBindings)
        let proof = FiniteCellFixture.proof graph
        Assert.Equal(cell.Id, proof.Cell)
        Assert.Equal(2, proof.Writes.Length)
        Assert.Equal<bigint list>([activations; activations], proof.Writes |> List.map _.MaximumActivations |> List.sort)
        Assert.Equal(2I * activations, proof.Certificate.MaximumIterations)
        Assert.Equal<bigint list>([4I * activations; 1I], proof.Certificate.Upper)
        let initializer = Assert.Single cell.Children
        Assert.Contains(initializer, proof.Participants)
        Assert.Contains(cell.Id, proof.Participants)
        Assert.Contains(startup.EntryLambda, proof.Participants)
        match cell.ValueRange with
        | Some(ValueRange.Bounded(lower, upper)) -> Assert.True(lower >= 0I && upper <= 4I * activations)
        | actual -> failwithf "The local cell must have a proved finite source range: %A" actual
        let obligation = FiniteCellFixture.obligations graph |> Assert.Single
        let row = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains && edge.Target = obligation.Id) |> Assert.Single
        Assert.Equal<Set<NodeId>>(proof.Participants, Set.ofList row.Sources)
        graph, proof

    let replace (graph: SemanticGraph) (node: SemanticNode) =
        let edges =
            graph.Edges |> List.filter (fun edge ->
                edge.Target <> node.Id || (edge.Class <> EdgeClass.Structural && edge.Class <> EdgeClass.Reference))
        { graph with Nodes = graph.Nodes.Add(node.Id, node)
                     Edges = edges @ Incidence.structuralIncidence node }

    let prepend graph (added: SemanticNode list) action =
        let startup = Initialization.read graph |> Option.get
        let body = graph.Nodes[startup.OriginalBody]
        let values = match body.Kind with SemanticKind.Sequential values -> values | _ -> failwith "Missing entry sequence"
        let nodes = added |> List.fold (fun nodes node -> Map.add node.Id node nodes) graph.Nodes
        let changed = { graph with Nodes = nodes; Edges = graph.Edges @ (added |> List.collect Incidence.structuralIncidence) }
        let ordered = action :: values
        let changed = replace changed { body with Kind = SemanticKind.Sequential ordered; Children = ordered }
        Assert.True((Initialization.read changed).IsSome, "This mutation must preserve startup authority")
        changed

    let refused graph =
        let fresh = FiniteCells.recognize graph
        Assert.Empty fresh
        let refreshed = FiniteCells.settle fresh graph
        Assert.Empty(FiniteCellFixture.obligations refreshed)
        Assert.DoesNotContain(refreshed.Edges, fun edge -> edge.Role = EdgeRole.FiniteCellRange)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "FiniteCellRanges")>]
type LocalFiniteCellRangeCases() =
    [<Fact>]
    member _.``A local cell retains its declaration activation and every finite writer`` () =
        LocalFiniteCellFixture.check LocalFiniteCellFixture.source 1I |> ignore

    [<Fact>]
    member _.``A local cell in a twice called ordinary function counts both activations`` () =
        let graph, proof = LocalFiniteCellFixture.check LocalFiniteCellFixture.repeated 2I
        let run = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding("run", false, _, _) -> true | _ -> false) |> Assert.Single
        let implementation = Assert.Single run.Children
        Assert.Contains(implementation, proof.Participants)

    [<Fact>]
    member _.``A repeated store occurrence enlarges the local cell certificate`` () =
        let graph, original = LocalFiniteCellFixture.check LocalFiniteCellFixture.source 1I
        let store = original.Writes.Head.Store
        let parent = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Sequential values -> List.contains store values | _ -> false) |> Assert.Single
        let values = match parent.Kind with SemanticKind.Sequential values -> values | _ -> failwith "Missing store scope"
        Assert.Equal(1, values |> List.filter ((=) store) |> List.length)
        let repeated = values |> List.collect (fun value -> if value = store then [value; value] else [value])
        let changed = LocalFiniteCellFixture.replace graph { parent with Kind = SemanticKind.Sequential repeated; Children = repeated }
        Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read changed).IsSome)
        let fresh = FiniteCellFixture.proof changed
        Assert.Equal(3I, fresh.Certificate.MaximumIterations)
        Assert.Equal<bigint list>([1I; 2I], fresh.Writes |> List.map _.MaximumActivations |> List.sort)
        Assert.Equal<bigint list>([6I; 1I], fresh.Certificate.Upper)
        let renewed = FiniteCells.settle [fresh] changed
        let obligation = FiniteCellFixture.obligations renewed |> Assert.Single
        match obligation.Kind with
        | SemanticKind.Obligation info -> Assert.Equal(ObligationBody.FiniteLinearRecurrence fresh.Certificate, info.Body)
        | _ -> failwith "Missing replacement finite-cell obligation"
        Assert.NotEqual((FiniteCellFixture.obligations graph |> Assert.Single).Id, obligation.Id)
        LocalFiniteCellFixture.check LocalFiniteCellFixture.source 1I |> ignore

    [<Fact>]
    member _.``Unbounded repeated initialization retracts a local cell despite finite writer sites`` () =
        let graph, proof = LocalFiniteCellFixture.check LocalFiniteCellFixture.source 1I
        let cell = graph.Nodes[proof.Cell]
        let builder = NodeBuilder()
        let condition = builder.Create(SemanticKind.Literal(NativeLiteral.Bool true), Types.boolType, cell.Range)
        let unit = builder.Create(SemanticKind.Literal NativeLiteral.Unit, Types.unitType, cell.Range)
        // The very same declaration also appears in an unproved loop; no
        // writer occurrence is added or moved. A finite write count alone
        // must not authorize unbounded allocation/initialization of this cell.
        let body = builder.Create(SemanticKind.Sequential [cell.Id; unit.Id], Types.unitType, cell.Range)
        let loop = builder.Create(SemanticKind.WhileLoop(condition.Id, body.Id), Types.unitType, cell.Range)
        let changed = LocalFiniteCellFixture.prepend graph (builder.Nodes.Values |> Seq.toList) loop.Id
        let sets (current: SemanticGraph) = current.Nodes.Values |> Seq.choose (fun node ->
            match node.IsReachable, node.Kind with true, SemanticKind.Set _ -> Some node.Id | _ -> None) |> Set.ofSeq
        Assert.Equal<Set<NodeId>>(sets graph, sets changed)
        LocalFiniteCellFixture.refused changed

    [<Theory>]
    [<InlineData("capture")>]
    [<InlineData("address")>]
    [<InlineData("lowered-address")>]
    member _.``A captured or address exposed local cell cannot retain finite ordinary authority`` defect =
        let graph, proof = LocalFiniteCellFixture.check LocalFiniteCellFixture.source 1I
        let cell = graph.Nodes[proof.Cell]
        let builder = NodeBuilder()
        let extra =
            if defect = "capture" then
                let formal = builder.Create(SemanticKind.PatternBinding "unused", Types.unitType, cell.Range)
                let body = builder.Create(SemanticKind.Literal NativeLiteral.Unit, Types.unitType, cell.Range)
                let capture = { Name = "state"; Type = cell.Type; IsMutable = true; SourceNodeId = Some cell.Id }
                builder.Create(SemanticKind.Lambda(["unused", Types.unitType, formal.Id], body.Id, [capture], None, LambdaContext.RegularClosure),
                               NativeType.TFun(Types.unitType, Types.unitType), cell.Range)
            elif defect = "lowered-address" then
                builder.Create(SemanticKind.CellAddress cell.Id, NativeType.TByref(cell.Type, ByrefKind.InOut), cell.Range)
            else
                let read = builder.Create(SemanticKind.VarRef("state", Some cell.Id), cell.Type, cell.Range)
                builder.Create(SemanticKind.AddressOf(read.Id, true), NativeType.TByref(cell.Type, ByrefKind.InOut), cell.Range)
        let changed = LocalFiniteCellFixture.prepend graph (builder.Nodes.Values |> Seq.toList) extra.Id
        LocalFiniteCellFixture.refused changed

    [<Fact>]
    member _.``Finite writer counts do not authorize a local use before its initialization`` () =
        let graph, proof = LocalFiniteCellFixture.check LocalFiniteCellFixture.source 1I
        let scope = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Sequential values -> List.contains proof.Cell values | _ -> false) |> Assert.Single
        let values = match scope.Kind with SemanticKind.Sequential values -> values | _ -> failwith "Missing declaration scope"
        let reordered = (values |> List.filter ((<>) proof.Cell)) @ [proof.Cell]
        let changed = LocalFiniteCellFixture.replace graph { scope with Kind = SemanticKind.Sequential reordered; Children = reordered }
        Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read changed).IsSome)
        LocalFiniteCellFixture.refused changed
