namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module FiniteCells = Clef.Compiler.PSGSaturation.SemanticGraph.FiniteCellRanges
module CellRanges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis
module RepresentationRanges = Clef.Compiler.Nanopass.RepresentationRanges

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
            let diagnostics = CheckResult.errors result
            let actual = diagnostics |> List.map (fun diagnostic ->
                Assert.Equal("CCS8011", diagnostic.Code)
                Assert.Equal("finite-cells.clef", diagnostic.Range.File)
                let primary, related =
                    match diagnostic.RelatedNodes with
                    | primary :: related -> primary, related
                    | [] -> failwith "The refusal must retain its primary source endpoint"
                let baseMessage =
                    if related.IsEmpty then diagnostic.Message
                    else
                        Assert.True(recursive, "Only the recursive fixture admits merged invocation provenance")
                        let parts = diagnostic.Message.Split([| "; its retained range support includes merged invocation contexts " |], System.StringSplitOptions.None)
                        Assert.Equal(2, parts.Length)
                        let facts = result.Graph.RangeContextFacts |> Option.get
                        Assert.False(System.String.IsNullOrWhiteSpace parts[1])
                        let rows = facts.Invocations |> List.groupBy _.Context |> List.collect (fun (_, rows) ->
                            if (rows |> List.map _.Caller |> List.distinct).Length > 1 then rows else [])
                        Assert.All(related, fun id ->
                            Assert.True(rows |> List.exists (fun row -> row.Call = id || row.Target = id), "Every added endpoint must belong to a retained merged invocation"))
                        Assert.True(facts.Reads.ContainsKey(RangeContext.Shared, primary), "The refusal must retain its source range reads")
                        parts[0]
                if not recursive then Assert.Single diagnostic.RelatedNodes |> ignore
                let node = result.Graph.Nodes[primary]
                Assert.True(node.IsReachable)
                Assert.True((node.Range = diagnostic.Range), "The refusal must identify its actual source node")
                Assert.True(node.ValueRange |> Option.exists (ValueRange.isObservable >> not), "The rejected source node must remain nonobservable")
                baseMessage, diagnostic.Range.Start.Line, diagnostic.Range.Start.Column,
                diagnostic.Range.End.Line, diagnostic.Range.End.Column)
            Assert.Equal<(string * int * int * int * int) list>(List.sort expected, List.sort actual)
            if recursive then
                let facts = result.Graph.RangeContextFacts |> Option.get
                Assert.True(facts.Invocations |> List.exists (fun row ->
                    match result.Graph.Nodes[row.Call].Kind with
                    | SemanticKind.Application(callee, _) ->
                        match result.Graph.Nodes[callee].Kind with
                        | SemanticKind.VarRef("repeat", _) ->
                            diagnostics |> List.exists (fun diagnostic ->
                                (diagnostic.RelatedNodes.Tail |> List.contains row.Call) &&
                                (diagnostic.RelatedNodes.Tail |> List.contains row.Target))
                        | _ -> false
                    | _ -> false), "The recursive refusal must identify the retained repeat call and its target")
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

    // Introduce a representation-preserving, independently typed transport of
    // the initializer. Its new dependency invalidates the old inventory,
    // while its current source meaning earns exactly the original recurrence.
    let annotateInitializer (graph: SemanticGraph) =
        let binding = cell graph
        let initializer = graph.Nodes[Assert.Single binding.Children]
        let annotation =
            { initializer with Id = NodeId.fresh(); Parent = Some binding.Id
                               Kind = SemanticKind.TypeAnnotation(initializer.Id, initializer.Type)
                               Children = [initializer.Id]; Metadata = Map.empty; ValueRange = None }
        let binding = { binding with Children = [annotation.Id] }
        let edges =
            graph.Edges |> List.filter (fun edge ->
                edge.Target <> binding.Id ||
                (edge.Class <> EdgeClass.Structural && edge.Class <> EdgeClass.Reference))
            |> List.map (fun edge ->
                // Carry the exact initializer correspondence through the same
                // typed transport, preserving startup order and authority.
                match edge.Role, edge.Sources with
                | EdgeRole.ProgramInitializer, [owner; cell; value; entry]
                    when cell = binding.Id && value = initializer.Id ->
                    { edge with Sources = [owner; cell; annotation.Id; entry] }
                | EdgeRole.ProgramValueIntent, [entry; spine; value]
                    when edge.Target = binding.Id && value = initializer.Id ->
                    { edge with Sources = [entry; spine; annotation.Id] }
                | _ -> edge)
        { graph with Nodes = graph.Nodes.Add(annotation.Id, annotation).Add(binding.Id, binding)
                     Edges = edges @ (Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence binding) @
                             (Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence annotation) }, annotation.Id

module internal FiniteCellRepresentationFixture =
    let annotateInitializer graph = FiniteCellFixture.annotateInitializer graph

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "FiniteCellRanges")>]
type FiniteCellRepresentationCases() =
    [<Fact>]
    member _.``Representation renewal earns new participants from current source without held ranges`` () =
        let original = FiniteCellFixture.check FiniteCellFixture.source
        Assert.True(FiniteCells.evidenceCurrent original)
        let previous = FiniteCellFixture.proof original
        let changed, annotation = FiniteCellFixture.annotateInitializer original
        let current = FiniteCellFixture.proof changed
        Assert.Equal(previous.Cell, current.Cell)
        Assert.Equal<FiniteCells.Write list>(previous.Writes, current.Writes)
        Assert.Equal(previous.Certificate, current.Certificate)
        Assert.DoesNotContain(annotation, previous.Participants)
        Assert.Contains(annotation, current.Participants)
        Assert.False(FiniteCells.evidenceCurrent changed)
        // Remove all cached arithmetic annotations: only current source
        // recognition may earn the replacement proof and its dependency rows.
        let unannotated = { changed with Nodes = changed.Nodes |> Map.map (fun _ node -> { node with ValueRange = None }) }
        let renewed = RepresentationRanges.preserve original unannotated
        Assert.True(FiniteCells.evidenceCurrent renewed)
        Assert.All(renewed.Nodes.Values, fun node -> Assert.True(node.ValueRange.IsNone))
        let proof = FiniteCellFixture.obligations renewed |> Assert.Single
        let originalProof = FiniteCellFixture.obligations unannotated |> Assert.Single
        Assert.Same(originalProof, proof)
        let constraintRow = renewed.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains && edge.Target = proof.Id) |> Assert.Single
        Assert.Equal<Set<NodeId>>(current.Participants, Set.ofList constraintRow.Sources)
        Assert.All(renewed.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.FiniteCellRange), fun edge ->
            Assert.Equal<Set<NodeId>>(current.Participants, Set.ofList edge.Sources))
        Assert.Same(renewed, RepresentationRanges.preserve renewed renewed)
        Assert.True(FiniteCells.evidenceCurrent original)

    [<Fact>]
    member _.``Representation renewal cannot repair an invalid starting certificate`` () =
        let original = FiniteCellFixture.check FiniteCellFixture.source
        let proof = FiniteCellFixture.obligations original |> Assert.Single
        let stale =
            { original with
                Edges = original.Edges |> List.filter (fun edge ->
                    edge.Role <> EdgeRole.Constrains || edge.Target <> proof.Id) }
        let changed, _ = FiniteCellFixture.annotateInitializer stale
        Assert.False(FiniteCells.evidenceCurrent stale)
        Assert.Same(changed, RepresentationRanges.preserve stale changed)
        Assert.False(FiniteCells.evidenceCurrent changed)

    [<Fact>]
    member _.``Representation renewal refuses changed recurrence meaning`` () =
        let original = FiniteCellFixture.check FiniteCellFixture.source
        let initializer = original.Nodes[Assert.Single((FiniteCellFixture.cell original).Children)]
        let literal =
            match initializer.Kind with
            | SemanticKind.Literal(NativeLiteral.Int(_, width)) -> NativeLiteral.Int(1L, width)
            | kind -> failwithf "Missing literal initializer: %A" kind
        let replacement = { initializer with Kind = SemanticKind.Literal literal }
        let changed = { original with Nodes = original.Nodes.Add(initializer.Id, replacement) }
        let fresh = FiniteCellFixture.proof changed
        Assert.NotEqual((FiniteCellFixture.proof original).Certificate, fresh.Certificate)
        Assert.Same(changed, RepresentationRanges.preserve original changed)
        Assert.False(FiniteCells.evidenceCurrent changed)

    [<Fact>]
    member _.``Representation renewal refuses an additional activation of the same store`` () =
        let original = FiniteCellFixture.check """
[<EntryPoint>]
let main _ =
    let mutable state = 0
    state <- state + 1
    state <- state + 2
    state
"""
        let previous = FiniteCellFixture.proof original
        let store = previous.Writes.Head.Store
        let parent = original.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Sequential values -> List.contains store values | _ -> false) |> Assert.Single
        let values = match parent.Kind with SemanticKind.Sequential values -> values | _ -> failwith "Missing store activation sequence"
        let repeated = values |> List.collect (fun value -> if value = store then [value; value] else [value])
        let parent = { parent with Kind = SemanticKind.Sequential repeated; Children = repeated }
        let edges = original.Edges |> List.filter (fun edge ->
            edge.Target <> parent.Id || (edge.Class <> EdgeClass.Structural && edge.Class <> EdgeClass.Reference))
        let changed =
            { original with
                Nodes = original.Nodes.Add(parent.Id, parent)
                Edges = edges @ Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence parent }
        let fresh = FiniteCellFixture.proof changed
        Assert.NotEqual<FiniteCells.Write list>(previous.Writes, fresh.Writes)
        Assert.NotEqual(previous.Certificate, fresh.Certificate)
        Assert.Same(changed, RepresentationRanges.preserve original changed)
        Assert.False(FiniteCells.evidenceCurrent changed)

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
    [<Theory>]
    [<InlineData(1)>]
    [<InlineData(2)>]
    member _.``Captured affine stores retain the logical cell and count every ordinary invocation`` (count: int) =
        let calls = String.replicate count "    bump ()\n"
        let graph = FiniteCellFixture.check (
            "[<EntryPoint>]\nlet main _ =\n    let mutable state = 0\n    let bump () = state <- state + 1\n" + calls + "    state\n")
        let proof = FiniteCellFixture.proof graph
        let writer = Assert.Single proof.Writes
        Assert.Equal(bigint count, writer.MaximumActivations)
        Assert.Equal(bigint count, proof.Certificate.MaximumIterations)
        Assert.Equal<bigint list>([bigint count; 1I], proof.Certificate.Upper)
        match graph.Nodes[writer.Store].Kind with
        | SemanticKind.EnvironmentWrite(_, cell, value) ->
            Assert.Equal(proof.Cell, cell)
            Assert.Equal(writer.Value, value)
        | actual -> failwithf "Expected the original writer after environment realization: %A" actual
        Assert.True(FiniteCells.evidenceCurrent graph)
        let original = FiniteCellFixture.obligations graph |> Assert.Single
        let renewed = FiniteCellFixture.analyze graph
        Assert.Equal(original.Id, (FiniteCellFixture.obligations renewed |> Assert.Single).Id)

    [<Theory>]
    [<InlineData("mode")>]
    [<InlineData("cell")>]
    [<InlineData("formal")>]
    [<InlineData("order")>]
    member _.``Captured finite proof refuses changed cell formation formal or initialization order`` defect =
        let graph = FiniteCellFixture.check """
[<EntryPoint>]
let main _ =
    let mutable state = 0
    let bump () = state <- state + 1
    bump ()
    state
"""
        let proof = FiniteCellFixture.proof graph
        Assert.True(FiniteCells.evidenceCurrent graph)
        let cell = graph.Nodes[proof.Cell]
        let changed =
            match defect with
            | "mode" ->
                let edges =
                    graph.Edges |> List.map (fun edge ->
                        match edge.Role, edge.Sources with
                        | EdgeRole.EnvironmentCapture true, [_; slot; _] when slot = cell.Id ->
                            { edge with Role = EdgeRole.EnvironmentCapture false }
                        | _ -> edge)
                { graph with Edges = edges }
            | "cell" ->
                let edges =
                    graph.Edges |> List.map (fun edge ->
                        match edge.Role, edge.Sources with
                        | EdgeRole.EnvironmentCapture true, [owner; slot; _] when slot = cell.Id ->
                            { edge with Sources = [owner; slot; Assert.Single cell.Children] }
                        | _ -> edge)
                { graph with Edges = edges }
            | "formal" ->
                { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.EnvironmentFormal) }
            | _ ->
                let sequence = graph.Nodes.Values |> Seq.find (fun node ->
                    match node.Kind with SemanticKind.Sequential values -> List.contains cell.Id values | _ -> false)
                let values = match sequence.Kind with SemanticKind.Sequential values -> values | _ -> []
                let reordered = List.filter ((<>) cell.Id) values @ [cell.Id]
                let sequence = { sequence with Kind = SemanticKind.Sequential reordered; Children = reordered }
                let edges = graph.Edges |> List.filter (fun edge ->
                    edge.Target <> sequence.Id || (edge.Class <> EdgeClass.Structural && edge.Class <> EdgeClass.Reference))
                { graph with Nodes = graph.Nodes.Add(sequence.Id, sequence)
                             Edges = edges @ Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence sequence }
        Assert.Empty(FiniteCells.recognize changed)
        Assert.False(FiniteCells.evidenceCurrent changed)
        Assert.Empty(FiniteCellFixture.obligations (FiniteCells.settle [] changed))

    [<Theory>]
    [<InlineData("loop")>]
    [<InlineData("recursive")>]
    [<InlineData("callback")>]
    member _.``Captured cells refuse unbounded recursive or unknown callback activations`` defect =
        let declaration, invocation =
            match defect with
            | "recursive" -> "let rec bump () = state <- state + 1; bump ()", "bump ()"
            | "callback" -> "let bump () = state <- state + 1", "Seq.iter bump (seq { yield () })"
            | _ -> "let bump () = state <- state + 1", "while true do bump ()"
        let source =
            "module CapturedFiniteRefusal\n[<EntryPoint>]\nlet main _ =\n    let mutable state = 0\n    " +
            declaration + "\n    " + invocation + "\n    state\n"
        let result =
            match parseAndCheck source "captured-finite-refusal.clef" with
            | Success result | CheckFailure result -> result
            | ParseFailure errors -> failwithf "%A" errors
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8011")
        Assert.Empty(FiniteCells.recognize result.Graph)
        Assert.Empty(FiniteCellFixture.obligations result.Graph)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "FiniteCellRanges")>]
type FiniteMutableCallbackCases() =
    [<Fact>]
    member _.``Finite callback alternatives retain snapshot identity and every shared cell writer`` () =
        let graph = FiniteCellFixture.check """
[<EntryPoint>]
let main _ =
    let mutable calls = 0
    let mutable callback = fun (_: bool) -> calls <- calls + 1; true
    let saved = callback
    callback <- fun (_: bool) -> calls <- calls + 2; false
    ignore (saved true)
    ignore (callback false)
    calls
"""
        let cell = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Binding("calls", true, _, _) -> true | _ -> false) |> Assert.Single
        let bound = FiniteCells.recognize graph |> List.filter (fun bound -> bound.Cell = cell.Id) |> Assert.Single
        Assert.Equal(2, bound.Writes.Length)
        Assert.All(bound.Writes, fun writer -> Assert.True(writer.MaximumActivations > 0I))
        Assert.True(ValueRange.isObservable (FiniteCells.range bound))
        Assert.True(ValueRange.isObservable (cell.ValueRange |> Option.get))
        for writer in bound.Writes do
            Assert.Contains(writer.Store, bound.Participants)
            Assert.True(ValueRange.isObservable (graph.Nodes[writer.Value].ValueRange |> Option.get))
        Assert.True(FiniteCells.evidenceCurrent graph)

    [<Fact>]
    member _.``A retained dormant callback contributes zero only through current ordinary inactivity`` () =
        let graph = FiniteCellFixture.check """
[<EntryPoint>]
let main _ =
    let mutable calls = 0
    let dormant = fun (_: bool) -> calls <- calls + 100; true
    let active = fun (_: bool) -> calls <- calls + 1; true
    ignore dormant
    ignore (active true)
    calls
"""
        let cell = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Binding("calls", true, _, _) -> true | _ -> false) |> Assert.Single
        let bound = FiniteCells.recognize graph |> List.filter (fun bound -> bound.Cell = cell.Id) |> Assert.Single
        let dormant = bound.Writes |> List.filter (fun writer -> writer.Offset = 100I) |> Assert.Single
        let active = bound.Writes |> List.filter (fun writer -> writer.Offset = 1I) |> Assert.Single
        Assert.Equal(0I, dormant.MaximumActivations)
        Assert.Equal(1I, active.MaximumActivations)
        let reading = Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.analyze graph
        let proof = reading.Inactivity.Values |> Seq.filter (fun proof -> proof.Excluded.Contains dormant.Store) |> Assert.Single
        Assert.Contains(proof.Implementation, bound.Participants)
        Assert.True(Set.isSubset (Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.inactivityParticipants proof) bound.Participants)
        let external = { graph with DeclarationRoots = (proof.Implementation, DeclRoot.HardwareModule) :: graph.DeclarationRoots }
        Assert.DoesNotContain(FiniteCells.recognize external, fun bound -> bound.Cell = cell.Id)
        Assert.True(FiniteCells.evidenceCurrent graph)

    [<Fact>]
    member _.``A reachable call in a dormant implementation is accounted by its current excluded call census``() =
        let graph =
            FiniteCellFixture.check
                """
[<EntryPoint>]
let main _ =
    let mutable calls = 0
    let active = fun (_: bool) -> calls <- calls + 1; true
    let dormant = fun (_: bool) -> active true
    ignore dormant
    ignore (active true)
    calls
"""

        let cell =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                match node.Kind with
                | SemanticKind.Binding("calls", true, _, _) -> true
                | _ -> false)
            |> Assert.Single

        let bound =
            FiniteCells.recognize graph
            |> List.filter (fun bound -> bound.Cell = cell.Id)
            |> Assert.Single

        let writer = Assert.Single bound.Writes
        Assert.Equal(1I, writer.MaximumActivations)

        let inactivity =
            (Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.analyze graph).Inactivity

        let proof =
            inactivity.Values
            |> Seq.filter (fun proof -> not proof.Calls.IsEmpty)
            |> Assert.Single

        let site = Assert.Single proof.Calls
        Assert.True(graph.Nodes[site].IsReachable)
        Assert.Contains(site, proof.Excluded)

        match graph.Nodes[site].Kind with
        | SemanticKind.Application _ -> ()
        | kind -> failwithf "The excluded occurrence must retain its call identity: %A" kind

        let ingress =
            Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.analyze graph

        Assert.Equal(Some proof.Implementation, Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.tryExecutionOwner ingress site)
        Assert.Contains(site, bound.Participants)
        Assert.True(Set.isSubset proof.Calls bound.Participants)
        Assert.True(FiniteCells.evidenceCurrent graph)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "FiniteSequenceCallbacks")>]
type FiniteSequenceCallbackCases() =
    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Fresh finite consumers bound callback writes and count each acquisition separately`` twice =
        let body =
            """
[<EntryPoint>]
let main _ =
    let mutable calls = 0
    let observe (_: int) = calls <- calls + 1
    let input = seq { yield 1; yield 2; yield 3 }
    Seq.iter observe input
"""

        let source =
            body + (if twice then "    Seq.iter observe input\n" else "") + "    calls\n"

        let graph = FiniteCellFixture.check source

        let cell =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                match node.Kind with
                | SemanticKind.Binding("calls", true, _, _) -> true
                | _ -> false)
            |> Assert.Single

        let bound =
            FiniteCells.recognize graph
            |> List.filter (fun bound -> bound.Cell = cell.Id)
            |> Assert.Single

        let writer = Assert.Single bound.Writes
        Assert.Equal((if twice then 6I else 3I), writer.MaximumActivations)

        let pulls =
            Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes.currentPulls graph

        Assert.Equal((if twice then 2 else 1), pulls.Length)
        Assert.True(graph.Platform.IsNone)

        let sourceOnly =
            { graph with
                Codata = lazy (failwith "Source pulls must not require frame or layout evidence")
            }

        Assert.Equal<Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes.Pull list>(
            pulls,
            Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes.sourcePulls sourceOnly
        )

        for pull in pulls do
            Assert.Equal(3I, pull.Pulls.MaximumPulls)
            Assert.True(Set.isSubset (Set.ofList pull.Participants) bound.Participants)

        Assert.True(FiniteCells.evidenceCurrent graph)

    [<Fact>]
    member _.``An unaccounted iterator use retracts the callback activation bound``() =
        let graph =
            FiniteCellFixture.check
                """
[<EntryPoint>]
let main _ =
    let mutable calls = 0
    let observe (_: int) = calls <- calls + 1
    Seq.iter observe (seq { yield 1; yield 2 })
    calls
"""

        let pull =
            Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes.currentPulls graph
            |> Assert.Single

        let cell =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                match node.Kind with
                | SemanticKind.Binding("calls", true, _, _) -> true
                | _ -> false)
            |> Assert.Single

        Assert.Contains(FiniteCells.recognize graph, fun bound -> bound.Cell = cell.Id)

        let extra =
            {
                Class = EdgeClass.Reference
                Role = EdgeRole.Argument
                Sources = [ pull.Enumerator ]
                Target = pull.Owner
                Ordinal = 99
            }

        let changed =
            { graph with
                Edges = extra :: graph.Edges
            }

        Assert.Empty(Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes.currentPulls changed)
        Assert.DoesNotContain(FiniteCells.recognize changed, fun bound -> bound.Cell = cell.Id)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "FiniteFoldCallbacks")>]
type FiniteFoldCallbackCases() =
    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``A demanded program binding retains a finite fold state through an exact callable return`` factory =
        let body =
            if factory then
                "let seed () = 0\nlet folder () = fun (state: int) (_: int) -> state + 1\nlet observed = Seq.fold (folder ()) (seed ()) (seq { yield 1; yield 2 })\n"
            else
                "let observed = Seq.fold (fun (state: int) (_: int) -> state + 1) 0 (seq { yield 1; yield 2 })\n"

        let graph =
            FiniteCellFixture.check (body + "[<EntryPoint>]\nlet main _ = if observed = 2 then 0 else 1\n")

        let cell =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                match node.Kind with
                | SemanticKind.Binding(name, true, _, _) -> name.StartsWith "__seq_accumulator_"
                | _ -> false)
            |> Assert.Single

        let proof =
            FiniteCells.recognize graph
            |> List.filter (fun proof -> proof.Cell = cell.Id)
            |> Assert.Single

        let write = Assert.Single proof.Writes
        Assert.Equal(2I, write.MaximumActivations)
        Assert.Equal(1I, write.Scale)
        Assert.Equal(1I, write.Offset)
        Assert.Equal<bigint list>([ 2I; 1I ], proof.Certificate.Upper)

        let pull =
            Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes.sourcePulls graph
            |> Assert.Single

        Assert.Equal(2I, pull.Pulls.MaximumPulls)
        Assert.True(Set.isSubset (Set.ofList pull.Participants) proof.Participants)
        Assert.True(FiniteCells.evidenceCurrent graph)

    [<Fact>]
    member _.``A nested fold region requires the current program initializer value intent``() =
        let graph =
            FiniteCellFixture.check
                "let observed = Seq.fold (fun (state: int) (_: int) -> state + 1) 0 (seq { yield 1; yield 2 })\n[<EntryPoint>]\nlet main _ = if observed = 2 then 0 else 1\n"

        let observed =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                match node.Kind with
                | SemanticKind.Binding("observed", _, _, _) -> true
                | _ -> false)
            |> Assert.Single

        Assert.Single(Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes.sourcePulls graph)
        |> ignore

        let changed =
            { graph with
                Edges =
                    graph.Edges
                    |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramValueIntent || edge.Target <> observed.Id)
            }

        Assert.Empty(Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes.sourcePulls changed)

        Assert.DoesNotContain(
            FiniteCells.recognize changed,
            fun proof -> proof.Writes |> List.exists (fun write -> write.MaximumActivations = 2I)
        )

    [<Fact>]
    member _.``A dormant binding value does not create a demanded fold execution region``() =
        let graph =
            FiniteCellFixture.check
                "let dormant () =\n    let observed = Seq.fold (fun (state: int) (_: int) -> state + 1) 0 (seq { yield 1; yield 2 })\n    observed\nlet discard (_: unit -> int) = 0\n[<EntryPoint>]\nlet main _ = discard dormant\n"

        Assert.Empty(Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes.sourcePulls graph)

        Assert.DoesNotContain(
            FiniteCells.recognize graph,
            fun proof ->
                match graph.Nodes[proof.Cell].Kind with
                | SemanticKind.Binding(name, _, _, _) -> name.StartsWith "__seq_accumulator_"
                | _ -> false
        )

    [<Fact>]
    member _.``An external callable placeholder cannot supply a finite fold affine return``() =
        let graph =
            FiniteCellFixture.check
                "let folder (state: int) (_: int) = state + 1\nlet observed = Seq.fold folder 0 (seq { yield 1; yield 2 })\n[<EntryPoint>]\nlet main _ = if observed = 2 then 0 else 1\n"

        let cell =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                match node.Kind with
                | SemanticKind.Binding(name, true, _, _) -> name.StartsWith "__seq_accumulator_"
                | _ -> false)
            |> Assert.Single

        Assert.Single(FiniteCells.recognize graph |> List.filter (fun proof -> proof.Cell = cell.Id))
        |> ignore

        let folder =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                match node.Kind with
                | SemanticKind.Binding("folder", false, _, _) -> true
                | _ -> false)
            |> Assert.Single

        let foreign =
            { folder with
                Metadata = folder.Metadata.Add("FidelityExtern.Symbol", MetadataValue.String "folder")
            }

        let changed =
            { graph with
                Nodes = graph.Nodes.Add(folder.Id, foreign)
            }

        let declaration =
            (Clef.Compiler.Baker.Recipes.BoundaryDeclarations.elaborate changed).NewEdges
            |> List.choose (fun edge ->
                match edge.Role with
                | EdgeRole.BoundaryDeclaration declaration when declaration.Binding = folder.Id -> Some declaration
                | _ -> None)
            |> Assert.Single

        Assert.NotEmpty declaration.Formals
        Assert.DoesNotContain(FiniteCells.recognize changed, fun proof -> proof.Cell = cell.Id)
