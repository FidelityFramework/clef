namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.NativeTypedTree.NativeTypes
module SequenceControl = Clef.Compiler.Baker.Recipes.SequenceControlRecipes

// These assertions inspect finite control incidence and live identities. They
// do not interpret source programs or claim a target frame implementation.
module private Control =
    let check source =
        match parseAndCheck ("module SequenceControl\n" + source + "\n[<EntryPoint>]\nlet main _ = ignore outer; 0\n") "sequence-control.clef" with
        | Success result -> DimensionalCases.noErrors result; result.Graph
        | CheckFailure result -> failwithf "Expected admitted control source: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed control source: %A" errors

    let owners (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false) |> Seq.toList

    let compose graph owner =
        match SequenceControl.forOwner graph owner with
        | Ok control -> control
        | Error residual -> failwithf "Expected complete local contracts: %A" residual

    let reachable (control: SequenceControl.Control) start =
        let rec visit seen = function
            | [] -> seen
            | label :: rest when Set.contains label seen -> visit seen rest
            | label :: rest ->
                let following = control.Steps[label].Successors |> List.filter (fun arc -> arc.Transfer <> EvaluationTransfer.Resume) |> List.map _.Target
                visit (Set.add label seen) (following @ rest)
        visit Set.empty [start]

    let cutWithLiteral (graph: SemanticGraph) (control: SequenceControl.Control) value =
        control.Steps.Values |> Seq.filter (fun step ->
            match step.Instruction with
            | SequenceControl.Instruction.Suspend(payload, _) ->
                match graph.Nodes[payload].Kind with SemanticKind.Literal(NativeLiteral.Int(actual, _)) -> actual = value | _ -> false
            | _ -> false) |> Assert.Single

    let resume (control: SequenceControl.Control) (cut: SequenceControl.Step) =
        match cut.Instruction with
        | SequenceControl.Instruction.Suspend(_, state) ->
            Assert.True(state > 0)
            let successor = Assert.Single cut.Successors
            Assert.Equal(EvaluationTransfer.Resume, successor.Transfer)
            Assert.Equal(successor.Target, control.ResumeEntries[state])
            successor.Target
        | instruction -> failwithf "Expected suspension: %A" instruction

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node -> match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false) |> Assert.Single

    let evaluated (control: SequenceControl.Control) labels =
        labels |> Set.toList |> List.choose (fun label ->
            match control.Steps[label].Instruction with SequenceControl.Instruction.Evaluate id -> Some id | _ -> None) |> Set.ofList

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceControl")>]
type SequenceControlCases() =
    [<Fact>]
    member _.``Payload effects finish before suspension and following effects start at its resume entry``() =
        let graph = Control.check "let mutable trace = 0\nlet outer = seq { trace <- 1; yield (trace <- 2; trace); trace <- 3 }"
        let control = Control.compose graph (Control.owners graph |> Assert.Single)
        let cut = control.Steps.Values |> Seq.filter (fun step -> match step.Instruction with SequenceControl.Instruction.Suspend _ -> true | _ -> false) |> Assert.Single
        let assignments =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.Set(_, value) ->
                    match graph.Nodes[value].Kind with
                    | SemanticKind.Literal(NativeLiteral.Int(marker, _)) -> Some(marker, node.Id)
                    | _ -> None
                | _ -> None)
            |> Map.ofSeq
        let initial = Control.reachable control control.Entry
        Assert.Contains(cut.Label, initial)
        let before = Control.evaluated control initial
        Assert.Contains(assignments[1L], before)
        Assert.Contains(assignments[2L], before)
        Assert.DoesNotContain(assignments[3L], before)
        let after = Control.reachable control (Control.resume control cut) |> Control.evaluated control
        Assert.Contains(assignments[3L], after)
        Assert.DoesNotContain(assignments[1L], after)
        Assert.DoesNotContain(assignments[2L], after)
        Assert.Equal(control.Entry, control.ResumeEntries[0])

    [<Fact>]
    member _.``Live across facts preserve the needed immutable binding and exclude completed temporaries``() =
        let graph = Control.check "let outer = seq {\n    let saved = 17\n    let discarded = 23\n    ignore discarded\n    yield 1\n    yield saved\n}"
        let control = Control.compose graph (Control.owners graph |> Assert.Single)
        let first = Control.cutWithLiteral graph control 1L
        let saved, discarded = Control.binding "saved" graph, Control.binding "discarded" graph
        Assert.Contains(saved.Id, control.LiveAcross[first.Label])
        Assert.DoesNotContain(discarded.Id, control.LiveAcross[first.Label])
        for initializer in saved.Children @ discarded.Children do Assert.DoesNotContain(initializer, control.LiveAcross[first.Label])
        let final = control.Steps.Values |> Seq.filter (fun step ->
            match step.Instruction with SequenceControl.Instruction.Suspend _ -> step.Label <> first.Label | _ -> false) |> Assert.Single
        Assert.Empty(control.LiveAcross[final.Label])
        Assert.Contains(saved.Id, control.LiveAtEntry[Control.resume control first])

    [<Fact>]
    member _.``Resuming a loop reaches its original guard and keeps its captured condition live``() =
        let graph = Control.check "let produce (running: bool) = seq { while running do yield 1 }\nlet outer = produce false"
        let control = Control.compose graph (Control.owners graph |> Assert.Single)
        let cut = Control.cutWithLiteral graph control 1L
        let branch = control.Steps.Values |> Seq.filter (fun step -> match step.Instruction with SequenceControl.Instruction.Branch _ -> true | _ -> false) |> Assert.Single
        Assert.Contains(branch.Label, Control.reachable control (Control.resume control cut))
        let guard = match branch.Instruction with SequenceControl.Instruction.Branch guard -> guard | _ -> failwith "branch"
        let declaration = match graph.Nodes[guard].Kind with SemanticKind.VarRef(_, Some source) -> source | kind -> failwithf "Expected captured guard: %A" kind
        Assert.Contains(declaration, control.LiveAcross[cut.Label])
        Assert.Contains(branch.Successors, fun arc -> arc.Transfer = EvaluationTransfer.WhenFalse)
        Assert.Contains(branch.Successors, fun arc -> arc.Transfer = EvaluationTransfer.WhenTrue)

    [<Fact>]
    member _.``A conditional cut and its bypass rejoin the same following continuation``() =
        let graph = Control.check "let produce (gate: bool) = seq {\n    if gate then yield 1\n    yield 2\n}\nlet outer = produce false"
        let control = Control.compose graph (Control.owners graph |> Assert.Single)
        let first, second = Control.cutWithLiteral graph control 1L, Control.cutWithLiteral graph control 2L
        let branch = control.Steps.Values |> Seq.filter (fun step -> match step.Instruction with SequenceControl.Instruction.Branch _ -> true | _ -> false) |> Assert.Single
        let yes = branch.Successors |> List.filter (fun arc -> arc.Transfer = EvaluationTransfer.WhenTrue) |> Assert.Single
        let no = branch.Successors |> List.filter (fun arc -> arc.Transfer = EvaluationTransfer.WhenFalse) |> Assert.Single
        Assert.Contains(first.Label, Control.reachable control yes.Target)
        Assert.DoesNotContain(second.Label, Control.reachable control yes.Target)
        Assert.Contains(second.Label, Control.reachable control no.Target)
        Assert.DoesNotContain(first.Label, Control.reachable control no.Target)
        Assert.Contains(second.Label, Control.reachable control (Control.resume control first))

    [<Fact>]
    member _.``Deferred values capture source identities without composing their bodies into outer execution``() =
        let graph = Control.check "let produce () = seq {\n    let seed = 17\n    let inner = seq { yield seed }\n    let callback = fun () -> seed\n    let delayed = lazy seed\n    yield seed\n}\nlet outer = produce ()"
        let value name = graph.Nodes[Assert.Single (Control.binding name graph).Children]
        let inner = value "inner"
        let owner = Control.owners graph |> List.filter (fun node -> node.Id <> inner.Id) |> Assert.Single
        let control = Control.compose graph owner
        let seed = Control.binding "seed" graph
        for formation in [inner; value "callback"; value "delayed"] do
            let step = control.Steps.Values |> Seq.filter (fun step -> step.Instruction = SequenceControl.Instruction.Evaluate formation.Id) |> Assert.Single
            Assert.Contains(seed.Id, step.Uses)
            let body =
                match formation.Kind with
                | SemanticKind.SeqExpr(body, _) | SemanticKind.LazyExpr(body, _) | SemanticKind.Lambda(_, body, _, _, _) -> body
                | kind -> failwithf "Expected deferred value: %A" kind
            Assert.DoesNotContain(control.Steps.Values, fun step -> step.Origin = body)
        let nested = Control.compose graph inner
        Assert.NotEqual(control.Owner, nested.Owner)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Missing or pending local contracts produce a residual instead of invented control``(pending: bool) =
        let graph = Control.check "let outer = seq { yield 1 }"
        let owner = Control.owners graph |> Assert.Single
        let root = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.EvaluationRoot && edge.Sources.Head = owner.Id) |> Assert.Single
        let missing = graph.Edges |> List.filter (fun edge ->
            not (edge.Class = EdgeClass.Evaluation && edge.Target = root.Target && edge.Role <> EdgeRole.EvaluationRoot))
        let edges =
            if pending then
                { Class = EdgeClass.Evaluation; Role = EdgeRole.EvaluationPending EvaluationResidual.InvalidShape
                  Sources = [owner.Id]; Target = root.Target; Ordinal = 0 } :: missing
            else missing
        let changed = { graph with Edges = edges }
        match SequenceControl.forOwner changed owner with
        | Ok _ -> failwith "Incomplete local facts produced a continuation graph"
        | Error residual ->
            Assert.Equal(owner.Id, residual.Owner)
            Assert.Equal(root.Target, residual.Site)
            Assert.Contains((if pending then "pending" else "Missing"), residual.Reason)
        Assert.Same(graph.Nodes, changed.Nodes)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Shared effectful operands reuse one dominating producer within an evaluation epoch``(inLoop: bool) =
        let source =
            "let mutable calls = 0\nlet make () = calls <- 1; 7\nlet mutable running = true\nlet outer = seq {\n    "
            + (if inLoop then "while running do\n        " else "")
            + "yield Option.defaultValue (make ()) None\n}"
        let graph = Control.check source
        let control = Control.compose graph (Control.owners graph |> Assert.Single)
        let call =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                match node.Kind with
                | SemanticKind.Application(callee, _) ->
                    match graph.Nodes[callee].Kind with
                    | SemanticKind.VarRef("make", _) -> true
                    | _ -> false
                | _ -> false)
            |> Assert.Single
        let producer = control.Steps.Values |> Seq.filter (fun step -> step.Instruction = SequenceControl.Instruction.Evaluate call.Id) |> Assert.Single
        let reuse = control.ReuseOrigins |> Map.toList |> List.filter (fun (label, _) -> control.Steps[label].Origin = call.Id)
        Assert.NotEmpty reuse
        for label, origin in reuse do
            Assert.Equal(producer.Label, origin)
            Assert.Equal(SequenceControl.Instruction.Pass, control.Steps[label].Instruction)
            Assert.Contains(call.Id, control.AssignedAtEntry[label])
        if inLoop then
            let cut = control.Steps.Values |> Seq.filter (fun step -> match step.Instruction with SequenceControl.Instruction.Suspend _ -> true | _ -> false) |> Assert.Single
            Assert.Contains(producer.Label, Control.reachable control (Control.resume control cut))
            Assert.DoesNotContain(call.Id, control.AssignedAtEntry[producer.Label])

    [<Fact>]
    member _.``A use with no capture declaration or preceding local initialization blocks a control plan``() =
        let graph = Control.check "let outer = seq { let saved = 17 in yield saved }"
        let owner = Control.owners graph |> Assert.Single
        let binding = Control.binding "saved" graph
        let useNode = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.VarRef(_, Some declaration) -> declaration = binding.Id | _ -> false) |> Assert.Single
        let missing = { binding with Id = NodeId.fresh(); Kind = SemanticKind.PatternBinding "uninitialized"; Children = []; Parent = None }
        let altered = { useNode with Kind = SemanticKind.VarRef("uninitialized", Some missing.Id) }
        let changed = { graph with Nodes = graph.Nodes |> Map.add missing.Id missing |> Map.add useNode.Id altered }
        match SequenceControl.forOwner changed owner with
        | Ok _ -> failwith "An uninitialized local use acquired a frame/control plan"
        | Error residual ->
            Assert.Equal(useNode.Id, residual.Site)
            Assert.Contains("definite initialization", residual.Reason)
        Assert.Same(graph.Nodes[useNode.Id], useNode)
