namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module SequenceEvaluation = Clef.Compiler.Nanopass.SequenceEvaluation

// Local demand and control incidence precedes global demand composition,
// dominance, segmentation and frame settlement. No test executes a graph.
module private Evaluation =
    let check source =
        let source = "module Evaluation\n[<Measure>] type m\n" + source + "\n[<EntryPoint>]\nlet main _ = ignore outer; 0\n"
        match parseAndCheck source "sequence-evaluation.clef" with
        | Success result ->
            DimensionalCases.noErrors result
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Error _ -> true | _ -> false)
            result.Graph
        | CheckFailure result -> failwithf "Expected admitted source: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed source: %A" errors

    let owners (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false) |> Seq.toList

    let root (graph: SemanticGraph) (owner: SemanticNode) =
        match owner.Kind with
        | SemanticKind.SeqExpr (generator, _) ->
            match graph.Nodes[generator].Kind with
            | SemanticKind.Lambda (_, body, _, _, LambdaContext.SeqGenerator) ->
                let edge = graph.Edges |> List.filter (fun edge ->
                    edge.Class = EdgeClass.Evaluation && edge.Role = EdgeRole.EvaluationRoot && edge.Sources.Head = owner.Id) |> Assert.Single
                Assert.Equal<NodeId list>([owner.Id; generator], edge.Sources)
                Assert.Equal(body, edge.Target)
                body
            | kind -> failwithf "Missing generator: %A" kind
        | kind -> failwithf "Missing owner: %A" kind

    let relations (graph: SemanticGraph) owner target =
        graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Evaluation && edge.Target = target && edge.Sources.Head = owner)

    let flow graph owner target fromPort toPort transfer =
        let matching = relations graph owner target |> List.filter (fun edge ->
            edge.Role = EdgeRole.EvaluationFlow(fromPort, toPort, transfer))
        let edge = Assert.Single matching
        Assert.Equal(owner, edge.Sources.Head)
        Assert.All(edge.Sources, fun participant -> Assert.True(graph.Nodes.ContainsKey participant))

    let noFlow graph owner target predicate =
        Assert.DoesNotContain(relations graph owner target, fun edge ->
            match edge.Role with EdgeRole.EvaluationFlow (before, after, transfer) -> predicate before after transfer | _ -> false)

    let operands graph owner target expected =
        let actual = relations graph owner target |> List.choose (fun edge ->
            match edge.Role, edge.Sources with
            | EdgeRole.EvaluationOperand access, [actualOwner; operand] ->
                Assert.Equal(owner, actualOwner)
                Some (edge.Ordinal, access, operand)
            | EdgeRole.EvaluationOperand _, sources -> failwithf "Operand participant set changed: %A" sources
            | _ -> None) |> List.sortBy (fun (slot, _, _) -> slot)
        Assert.Equal<(int * EvaluationAccess * NodeId) list>(expected, actual)

    let linear graph owner target inputs =
        operands graph owner target (inputs |> List.mapi (fun slot id -> slot, EvaluationAccess.Value, id))
        match inputs with
        | [] -> flow graph owner target EvaluationPort.Entry EvaluationPort.Ready EvaluationTransfer.Continue
        | _ ->
            flow graph owner target EvaluationPort.Entry (EvaluationPort.OperandEntry 0) EvaluationTransfer.Continue
            for slot in 0 .. inputs.Length - 2 do
                flow graph owner target (EvaluationPort.OperandExit slot) (EvaluationPort.OperandEntry (slot + 1)) EvaluationTransfer.Continue
            flow graph owner target (EvaluationPort.OperandExit (inputs.Length - 1)) EvaluationPort.Ready EvaluationTransfer.Continue

    let ownedNodes (graph: SemanticGraph) owner =
        graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Evaluation && edge.Sources.Head = owner)
        |> List.map _.Target |> Set.ofList |> Set.toList |> List.map (fun id -> graph.Nodes[id])

    let sequential (graph: SemanticGraph) owner id =
        match graph.Nodes[id].Kind with
        | SemanticKind.Sequential inputs ->
            linear graph owner id inputs
            flow graph owner id EvaluationPort.Ready EvaluationPort.Exit EvaluationTransfer.Continue
            inputs
        | kind -> failwithf "Expected ordered source expressions: %A" kind

    let suspend (graph: SemanticGraph) owner cut =
        match graph.Nodes[cut].Kind with
        | SemanticKind.Yield payload ->
            linear graph owner cut [payload]
            flow graph owner cut EvaluationPort.Ready EvaluationPort.Exit EvaluationTransfer.Resume
            noFlow graph owner cut (fun before after transfer ->
                before = EvaluationPort.Ready && after = EvaluationPort.Exit && transfer = EvaluationTransfer.Continue)
            payload
        | kind -> failwithf "Expected suspension site: %A" kind

    let assignment (graph: SemanticGraph) owner id =
        match graph.Nodes[id].Kind with
        | SemanticKind.Set (target, value) ->
            operands graph owner id [0, EvaluationAccess.Storage, target; 1, EvaluationAccess.Value, value]
            flow graph owner id EvaluationPort.Entry (EvaluationPort.OperandEntry 1) EvaluationTransfer.Continue
            flow graph owner id (EvaluationPort.OperandExit 1) EvaluationPort.Ready EvaluationTransfer.Continue
            flow graph owner id EvaluationPort.Ready EvaluationPort.Exit EvaluationTransfer.Continue
            noFlow graph owner id (fun before after _ ->
                before = EvaluationPort.OperandEntry 0 || before = EvaluationPort.OperandExit 0 ||
                after = EvaluationPort.OperandEntry 0 || after = EvaluationPort.OperandExit 0)
        | kind -> failwithf "Expected assignment: %A" kind

    let backedge (graph: SemanticGraph) owner id =
        match graph.Nodes[id].Kind with
        | SemanticKind.WhileLoop (guard, body) ->
            operands graph owner id [0, EvaluationAccess.Value, guard; 1, EvaluationAccess.Value, body]
            flow graph owner id EvaluationPort.Entry (EvaluationPort.OperandEntry 0) EvaluationTransfer.Continue
            flow graph owner id (EvaluationPort.OperandExit 0) (EvaluationPort.OperandEntry 1) EvaluationTransfer.WhenTrue
            flow graph owner id (EvaluationPort.OperandExit 0) EvaluationPort.Ready EvaluationTransfer.WhenFalse
            flow graph owner id (EvaluationPort.OperandExit 1) (EvaluationPort.OperandEntry 0) EvaluationTransfer.Continue
            flow graph owner id EvaluationPort.Ready EvaluationPort.Exit EvaluationTransfer.Continue
            guard, body
        | kind -> failwithf "Expected repeated guard and body: %A" kind

    let edgeFields (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target

    let incomplete scenario =
        let builder = NodeBuilder()
        let range: SourceRange = { File = "incomplete-evaluation.clef"; Start = { Line = 1; Column = 0 }; End = { Line = 1; Column = 10 } }
        let create kind ty = builder.Create(kind, ty, range)
        let yes = create (SemanticKind.Literal(NativeLiteral.Bool true)) Types.boolType
        let unitValue = create (SemanticKind.Literal NativeLiteral.Unit) Types.unitType
        let kind, residual =
            match scenario with
            | "missing-operand" -> SemanticKind.Sequential [NodeId.fresh()], EvaluationResidual.MissingOperand
            | "invalid-target" -> SemanticKind.Set(yes.Id, yes.Id), EvaluationResidual.InvalidShape
            | "match" -> SemanticKind.Match(yes.Id, []), EvaluationResidual.MatchSelection
            | "exception" -> SemanticKind.TryFinally(unitValue.Id, unitValue.Id), EvaluationResidual.ExceptionFlow
            | other -> failwithf "Unknown incomplete contract: %s" other
        let body = create kind Types.unitType
        let sequenceType = Types.mkSeqType Types.boolType
        let pointerType = NativeType.TNativePtr sequenceType
        let formal = create (SemanticKind.PatternBinding "_seq_ptr") pointerType
        let generator = create (SemanticKind.Lambda(["_seq_ptr", pointerType, formal.Id], body.Id, [], None, LambdaContext.SeqGenerator)) (NativeType.TFun(pointerType, Types.boolType))
        let owner = create (SemanticKind.SeqExpr(generator.Id, [])) sequenceType
        builder.Build [], owner.Id, body.Id, residual

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceEvaluation")>]
type SequenceEvaluationCases() =
    [<Fact>]
    member _.``Source assignments and payload evaluation keep their local order across a suspension``() =
        let graph = Evaluation.check "let mutable trace = 0\nlet outer = seq { trace <- 1; yield (trace <- 2; trace); trace <- 3 }"
        let owner = Evaluation.owners graph |> Assert.Single
        let body = Evaluation.root graph owner
        let first = Evaluation.sequential graph owner.Id body
        Assert.Equal(2, first.Length)
        Evaluation.assignment graph owner.Id first[0]
        let remaining = Evaluation.sequential graph owner.Id first[1]
        Assert.Equal(2, remaining.Length)
        let payload = Evaluation.suspend graph owner.Id remaining[0]
        let payloadInputs = Evaluation.sequential graph owner.Id payload
        Assert.Equal(2, payloadInputs.Length)
        Evaluation.assignment graph owner.Id payloadInputs[0]
        Evaluation.assignment graph owner.Id remaining[1]
        match graph.Nodes[payloadInputs[1]].Kind with SemanticKind.VarRef _ -> () | kind -> failwithf "Lost payload read: %A" kind

    [<Theory>]
    [<InlineData("true")>]
    [<InlineData("false")>]
    [<InlineData("gate")>]
    member _.``Conditional flow retains guard effects and both local joins without claiming feasibility``(guard: string) =
        let graph = Evaluation.check ("let mutable trace = 0\nlet produce (gate: bool) = seq {\n    if (trace <- 1; " + guard + ") then\n        trace <- 2\n        yield 3\n        trace <- 4\n    else\n        trace <- 5\n    trace <- 6\n}\nlet outer = produce false")
        let owner = Evaluation.owners graph |> Assert.Single
        let body = Evaluation.root graph owner
        let ordered = Evaluation.sequential graph owner.Id body
        Assert.Equal(2, ordered.Length)
        Evaluation.assignment graph owner.Id ordered[1]
        let conditional = ordered[0]
        match graph.Nodes[conditional].Kind with
        | SemanticKind.IfThenElse (condition, yes, Some no) ->
            Evaluation.operands graph owner.Id conditional [0, EvaluationAccess.Value, condition; 1, EvaluationAccess.Value, yes; 2, EvaluationAccess.Value, no]
            Evaluation.flow graph owner.Id conditional EvaluationPort.Entry (EvaluationPort.OperandEntry 0) EvaluationTransfer.Continue
            Evaluation.flow graph owner.Id conditional (EvaluationPort.OperandExit 0) (EvaluationPort.OperandEntry 1) EvaluationTransfer.WhenTrue
            Evaluation.flow graph owner.Id conditional (EvaluationPort.OperandExit 0) (EvaluationPort.OperandEntry 2) EvaluationTransfer.WhenFalse
            for slot in [1; 2] do Evaluation.flow graph owner.Id conditional (EvaluationPort.OperandExit slot) EvaluationPort.Ready EvaluationTransfer.Continue
            Evaluation.flow graph owner.Id conditional EvaluationPort.Ready EvaluationPort.Exit EvaluationTransfer.Continue
            let guardInputs = Evaluation.sequential graph owner.Id condition
            Evaluation.assignment graph owner.Id guardInputs[0]
            let yesInputs = Evaluation.sequential graph owner.Id yes
            let following = Evaluation.sequential graph owner.Id yesInputs[1]
            Evaluation.suspend graph owner.Id following[0] |> ignore
            Evaluation.assignment graph owner.Id following[1]
            Evaluation.assignment graph owner.Id no
        | kind -> failwithf "Conditional structure changed: %A" kind

    [<Fact>]
    member _.``Loop completion returns to the whole effectful guard and keeps its false exit``() =
        let graph = Evaluation.check "let mutable trace = 0\nlet produce running = seq {\n    trace <- 1\n    while (trace <- 2; running) do\n        trace <- 3\n        yield 4\n        trace <- 5\n    trace <- 6\n}\nlet outer = produce false"
        let owner = Evaluation.owners graph |> Assert.Single
        let loop = Evaluation.ownedNodes graph owner.Id |> List.filter (fun node -> match node.Kind with SemanticKind.WhileLoop _ -> true | _ -> false) |> Assert.Single
        let guard, body = Evaluation.backedge graph owner.Id loop.Id
        let guardInputs = Evaluation.sequential graph owner.Id guard
        Evaluation.assignment graph owner.Id guardInputs[0]
        let bodyInputs = Evaluation.sequential graph owner.Id body
        Evaluation.assignment graph owner.Id bodyInputs[0]
        let remaining = Evaluation.sequential graph owner.Id bodyInputs[1]
        Evaluation.suspend graph owner.Id remaining[0] |> ignore
        Evaluation.assignment graph owner.Id remaining[1]

    [<Fact>]
    member _.``An effectful empty sequence still has root and ordered completion relations``() =
        let graph = Evaluation.check "let mutable trace = 0\nlet outer: seq<int> = seq { trace <- 1; trace <- 2 }"
        let owner = Evaluation.owners graph |> Assert.Single
        let body = Evaluation.root graph owner
        let inputs = Evaluation.sequential graph owner.Id body
        Assert.Equal(2, inputs.Length)
        inputs |> List.iter (Evaluation.assignment graph owner.Id)
        Assert.DoesNotContain(Evaluation.ownedNodes graph owner.Id, fun node -> match node.Kind with SemanticKind.Yield _ -> true | _ -> false)

    [<Fact>]
    member _.``Deferred formation records capture identity without demanding its body in the outer owner``() =
        let graph = Evaluation.check "let produce (seed: int<m>) = seq {\n    let inner = seq { yield seed }\n    let callback = fun () -> seed\n    let delayed = lazy seed\n    yield seed\n}\nlet outer = produce 1<m>"
        let binding name = graph.Nodes.Values |> Seq.find (fun node -> match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
        let formation name = graph.Nodes[Assert.Single (binding name).Children]
        let inner = formation "inner"
        let owner = Evaluation.owners graph |> List.filter (fun node -> node.Id <> inner.Id) |> Assert.Single
        Evaluation.root graph owner |> ignore
        Evaluation.root graph inner |> ignore
        for node in [inner; formation "callback"; formation "delayed"] do
            Evaluation.linear graph owner.Id node.Id []
            Evaluation.flow graph owner.Id node.Id EvaluationPort.Ready EvaluationPort.Exit EvaluationTransfer.Continue
            let body, captures =
                match node.Kind with
                | SemanticKind.SeqExpr(body, captures) | SemanticKind.LazyExpr(body, captures) -> body, captures
                | SemanticKind.Lambda(_, body, captures, _, _) -> body, captures
                | kind -> failwithf "Expected deferred source value: %A" kind
            Assert.NotEmpty captures
            Assert.Empty(Evaluation.relations graph owner.Id body)
            for index, capture in List.indexed captures do
                let captureEdge = Evaluation.relations graph owner.Id node.Id |> List.filter (fun edge -> edge.Role = EdgeRole.EvaluationCapture && edge.Ordinal = index) |> Assert.Single
                Assert.Equal<NodeId list>([owner.Id; Option.get capture.SourceNodeId], captureEdge.Sources)

    [<Fact>]
    member _.``Filter consumers demand the same bound current value without scheduling another initializer``() =
        let graph = Evaluation.check "let outer = Seq.filter (fun (value: int<m>) -> value > 0<m>) (seq { yield 1<m> })"
        let owner = Evaluation.owners graph |> List.find (fun owner ->
            match graph.Nodes[Evaluation.root graph owner].Kind with SemanticKind.Sequential _ -> true | _ -> false)
        let loop = Evaluation.ownedNodes graph owner.Id |> List.filter (fun node -> match node.Kind with SemanticKind.WhileLoop _ -> true | _ -> false) |> Assert.Single
        let _, body = Evaluation.backedge graph owner.Id loop.Id
        let inputs = Evaluation.sequential graph owner.Id body
        match inputs with
        | [binding; current; conditional] ->
            match graph.Nodes[current].Kind with
            | SemanticKind.VarRef(_, Some definition) -> Assert.Equal(binding, definition)
            | kind -> failwithf "Lost bound current read: %A" kind
            Evaluation.linear graph owner.Id current []
            let predicate, yielded =
                match graph.Nodes[conditional].Kind with SemanticKind.IfThenElse(predicate, yes, _) -> predicate, yes | kind -> failwithf "Missing filter guard: %A" kind
            Assert.Equal(current, Evaluation.suspend graph owner.Id yielded)
            let demands = graph.Edges |> List.filter (fun edge ->
                edge.Class = EdgeClass.Evaluation && edge.Role = EdgeRole.EvaluationOperand EvaluationAccess.Value && edge.Sources = [owner.Id; current])
            Assert.Equal<Set<NodeId>>(Set.ofList [body; predicate; yielded], demands |> List.map _.Target |> Set.ofList)
        | other -> failwithf "Current binding does not dominate its local uses: %A" other

    [<Fact>]
    member _.``Delegation iteration has local backedges and resumption without absorbing the inner owner``() =
        let graph = Evaluation.check "let outer = seq { yield! (seq { yield 1 }); yield 2 }"
        let origin = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.DelegationOrigin) |> Assert.Single
        let delimiter = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Delimiter && edge.Target = origin.Target) |> Assert.Single
        let owner = graph.Nodes[delimiter.Sources.Head]
        let loop = Evaluation.ownedNodes graph owner.Id |> List.filter (fun node -> match node.Kind with SemanticKind.WhileLoop _ -> true | _ -> false) |> Assert.Single
        Evaluation.backedge graph owner.Id loop.Id |> ignore
        Evaluation.suspend graph owner.Id origin.Target |> ignore
        let inner = Evaluation.owners graph |> List.filter (fun node -> node.Id <> owner.Id) |> Assert.Single
        Evaluation.linear graph owner.Id inner.Id []
        let innerBody = Evaluation.root graph inner
        Assert.Empty(Evaluation.relations graph owner.Id innerBody)
        Evaluation.suspend graph inner.Id innerBody |> ignore

    [<Fact>]
    member _.``Evaluation enrichment preserves the DAG and other proofs while replacing stale projection facts``() =
        let graph = Evaluation.check "let outer = seq { yield 1 }"
        let owner = Evaluation.owners graph |> Assert.Single
        let cut = Evaluation.root graph owner
        let unrelated = graph.Edges |> List.filter (fun edge -> edge.Class <> EdgeClass.Evaluation)
        Assert.Contains(unrelated, fun edge -> edge.Class = EdgeClass.Obligation)
        let stripped = { graph with Edges = unrelated }
        let enrichment = SequenceEvaluation.elaborate stripped
        Assert.Empty enrichment.NewNodes
        Assert.Empty enrichment.Annotated
        let settled = SequenceEvaluation.foldIn enrichment stripped
        Assert.Same(graph.Nodes, settled.Nodes)
        let stale = { Class = EdgeClass.Evaluation; Role = EdgeRole.EvaluationFlow(EvaluationPort.Ready, EvaluationPort.Exit, EvaluationTransfer.Continue); Sources = [owner.Id]; Target = cut; Ordinal = 99 }
        let updated = SequenceEvaluation.normalize { settled with Edges = stale :: settled.Edges }
        Assert.Same(graph.Nodes, updated.Nodes)
        Evaluation.suspend updated owner.Id cut |> ignore
        Assert.DoesNotContain(updated.Edges, fun edge -> edge.Class = EdgeClass.Evaluation && edge.Ordinal = 99)
        Assert.Equal<(EdgeClass * EdgeRole * int * NodeId list * NodeId) list>(unrelated |> List.map Evaluation.edgeFields, updated.Edges |> List.filter (fun edge -> edge.Class <> EdgeClass.Evaluation) |> List.map Evaluation.edgeFields)
        let repeated = SequenceEvaluation.normalize updated
        Assert.Same(updated.Nodes, repeated.Nodes)
        Assert.Equal<(EdgeClass * EdgeRole * int * NodeId list * NodeId) list>(updated.Edges |> List.map Evaluation.edgeFields, repeated.Edges |> List.map Evaluation.edgeFields)

    [<Theory>]
    [<InlineData("missing-operand")>]
    [<InlineData("invalid-target")>]
    [<InlineData("match")>]
    [<InlineData("exception")>]
    member _.``Incomplete local contracts retain explicit residuals without invented successful flow``(scenario: string) =
        let graph, owner, body, residual = Evaluation.incomplete scenario
        let settled = SequenceEvaluation.normalize graph
        Assert.Same(graph.Nodes, settled.Nodes)
        let pending = Evaluation.relations settled owner body |> List.filter (fun edge -> edge.Role = EdgeRole.EvaluationPending residual) |> Assert.Single
        Assert.Equal(owner, pending.Sources.Head)
        Evaluation.noFlow settled owner body (fun _ _ _ -> true)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``A yield needs one actual delimiter before it can carry a resumption transfer``(ambiguous: bool) =
        let graph = Evaluation.check "let inner = seq { yield 1 }\nlet outer = seq { yield! inner }"
        let delimiters = graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Suspension && edge.Role = EdgeRole.Delimiter)
        Assert.Equal(2, delimiters.Length)
        let original, rival = delimiters[0], delimiters[1]
        Assert.NotEqual(original.Sources.Head, rival.Sources.Head)
        let changed =
            if ambiguous then { graph with Edges = { rival with Target = original.Target } :: graph.Edges }
            else
                let remaining = graph.Edges |> List.filter (fun edge ->
                    not (edge.Class = EdgeClass.Suspension && edge.Role = EdgeRole.Delimiter && edge.Target = original.Target))
                { graph with Edges = remaining }
        let settled = SequenceEvaluation.normalize changed
        Assert.Same(changed.Nodes, settled.Nodes)
        let relations = Evaluation.relations settled original.Sources.Head original.Target
        Assert.Single(relations |> List.filter (fun edge -> edge.Role = EdgeRole.EvaluationPending EvaluationResidual.InvalidShape)) |> ignore
        Evaluation.noFlow settled original.Sources.Head original.Target (fun _ _ _ -> true)

    [<Fact>]
    member _.``A deferred capture without source identity remains an incomplete formation contract``() =
        let graph = Evaluation.check "let produce (seed: int<m>) = seq {\n    let callback = fun () -> seed\n    yield seed\n}\nlet outer = produce 1<m>"
        let owner = Evaluation.owners graph |> Assert.Single
        let closure = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Lambda(_, _, _ :: _, _, LambdaContext.RegularClosure) -> true | _ -> false) |> Assert.Single
        let replacement, body =
            match closure.Kind with
            | SemanticKind.Lambda(parameters, body, capture :: captures, enclosing, context) ->
                Assert.True capture.SourceNodeId.IsSome
                { closure with Kind = SemanticKind.Lambda(parameters, body, { capture with SourceNodeId = None } :: captures, enclosing, context) }, body
            | _ -> failwith "Expected captured closure"
        let changed = { graph with Nodes = Map.add closure.Id replacement graph.Nodes }
        let settled = SequenceEvaluation.normalize changed
        Assert.Same(changed.Nodes, settled.Nodes)
        let relations = Evaluation.relations settled owner.Id closure.Id
        Assert.Single(relations |> List.filter (fun edge -> edge.Role = EdgeRole.EvaluationPending EvaluationResidual.MissingOperand)) |> ignore
        Assert.DoesNotContain(relations, fun edge -> edge.Role = EdgeRole.EvaluationCapture)
        Evaluation.noFlow settled owner.Id closure.Id (fun _ _ _ -> true)
        Assert.Empty(Evaluation.relations settled owner.Id body)
