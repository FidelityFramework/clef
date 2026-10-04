namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module FlowCarriers = Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers
module FlowOrigins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
module Flows = Clef.Compiler.PSGSaturation.SemanticGraph.CallableFlows

module private CallableFlowFixture =
    let demand graph =
        let graph = Clef.Compiler.Nanopass.OrdinaryDemand.normalize graph
        match Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.tryRead graph with
        | Ok _ -> graph
        | Result.Error failures -> failwithf "Expected current ordinary-demand premises before callable flow settlement: %A" failures

    let create () =
        let builder = NodeBuilder()
        let callbackType = NativeType.TFun(Types.boolType, Types.boolType)
        let named name value =
            let argument = builder.Create(SemanticKind.PatternBinding "input", Types.boolType, dummyRange)
            let body = builder.Create(SemanticKind.Literal(NativeLiteral.Bool value), Types.boolType, dummyRange)
            let code = builder.Create(SemanticKind.Lambda(["input", Types.boolType, argument.Id], body.Id,
                                                        [], None, LambdaContext.RegularClosure), callbackType, dummyRange)
            let binding = builder.Create(SemanticKind.Binding(name, false, false, None), callbackType, dummyRange, children = [code.Id])
            builder.SetParent(argument.Id, code.Id)
            builder.SetParent(body.Id, code.Id)
            builder.SetParent(code.Id, binding.Id)
            builder.Create(SemanticKind.VarRef(name, Some binding.Id), callbackType, dummyRange)
        let first, second = named "first" true, named "second" false
        let callback = builder.Create(SemanticKind.PatternBinding "callback", callbackType, dummyRange)
        let read = builder.Create(SemanticKind.VarRef("callback", Some callback.Id), callbackType, dummyRange)
        let value = builder.Create(SemanticKind.Literal(NativeLiteral.Bool true), Types.boolType, dummyRange)
        let body = builder.Create(SemanticKind.Application(read.Id, [value.Id]), Types.boolType, dummyRange)
        let higherType = NativeType.TFun(callbackType, Types.boolType)
        let higher = builder.Create(SemanticKind.Lambda(["callback", callbackType, callback.Id], body.Id,
                                                      [], None, LambdaContext.RegularClosure), higherType, dummyRange)
        let binding = builder.Create(SemanticKind.Binding("higher", false, false, None), higherType, dummyRange, children = [higher.Id])
        builder.SetParent(higher.Id, binding.Id)
        builder.SetParent(callback.Id, higher.Id)
        builder.SetParent(body.Id, higher.Id)
        builder.SetParent(read.Id, body.Id)
        let call actual =
            let reference = builder.Create(SemanticKind.VarRef("higher", Some binding.Id), higherType, dummyRange)
            builder.Create(SemanticKind.Application(reference.Id, [actual]), Types.boolType, dummyRange)
        let firstCall, secondCall = call first.Id, call second.Id
        let opaque = builder.Create(SemanticKind.PatternBinding "opaque", callbackType, dummyRange)
        let unit = builder.Create(SemanticKind.PatternBinding "unit", Types.unitType, dummyRange)
        let spine = builder.Create(SemanticKind.Sequential [firstCall.Id; secondCall.Id], Types.boolType, dummyRange)
        let entryType = NativeType.TFun(Types.unitType, Types.boolType)
        let entry = builder.Create(SemanticKind.Lambda(["unit", Types.unitType, unit.Id], spine.Id,
                                                     [], None, LambdaContext.RegularClosure), entryType, dummyRange)
        let main = builder.Create(SemanticKind.Binding("main", false, false, Some DeclRoot.EntryPoint), entryType, dummyRange, children = [entry.Id])
        builder.SetParent(entry.Id, main.Id)
        let raw, startupErrors = Clef.Compiler.Nanopass.ProgramInitialization.normalize [main.Id] (builder.Build [main.Id, DeclRoot.EntryPoint])
        Assert.Empty startupErrors
        Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read raw).IsSome)
        // This raw fixture owns the upstream stages normally run by checking.
        let raw = demand raw
        let carriers, errors = FlowCarriers.settle { Layouts = Map.empty; Origins = Map.empty; Known = Map.empty } raw
        Assert.Empty errors
        let inputs: Flows.Inputs =
            { Carriers = carriers; Joins = Map.empty; Layouts = Map.empty
              SequenceFlows = Map.empty; SequenceFamilies = Map.empty }
        let flows, residuals = Flows.settle inputs { raw with Codata = lazy (failwith "Premature Codata force") }
        Assert.Empty residuals
        let codata = { raw.Codata.Value with CallableCarriers = carriers; CallableFlows = flows }
        { raw with Codata = lazy codata }, inputs, callback.Id, read.Id, [first.Id; second.Id], [firstCall.Id; secondCall.Id], opaque.Id

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "CallableFlow")>]
type CallableFlowCases() =
    [<Fact>]
    member _.``Eager callable actual retains its demand marker in complete ingress and value flow`` () =
        let original, _, formal, _, alternatives, calls, _ = CallableFlowFixture.create ()
        let actual, callId = List.head alternatives, List.head calls
        let markerId = NodeId.fresh()
        let marker = { original.Nodes[actual] with Id = markerId; Kind = SemanticKind.EagerExpr actual; Children = [actual]; Parent = Some callId }
        let call = original.Nodes[callId]
        let call =
            match call.Kind with
            | SemanticKind.Application(callee, [previous]) when previous = actual ->
                { call with Kind = SemanticKind.Application(callee, [markerId]); Children = [callee; markerId] }
            | _ -> failwith "Expected one original callable actual"
        let edges = original.Edges |> List.map (fun edge ->
            if edge.Target = callId && edge.Class = EdgeClass.Structural then
                { edge with Sources = edge.Sources |> List.map (fun source -> if source = actual then markerId else source) }
            else edge)
        let graph =
            { original with Nodes = original.Nodes.Add(markerId, marker).Add(callId, call)
                            Edges = edges @ kindEdges markerId marker.Kind }
            |> Clef.Compiler.Nanopass.EagerDemand.normalize
            |> CallableFlowFixture.demand
        let ingress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.analyze graph
        let evidence = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.tryEvidence ingress formal |> Option.get
        Assert.Contains(markerId, evidence.Participants)
        Assert.Contains(evidence.Calls, fun row -> row.Site = callId && List.head row.Arguments = markerId)
        let carriers, errors = FlowCarriers.settle { Layouts = Map.empty; Origins = Map.empty; Known = Map.empty } graph
        Assert.Empty errors
        let inputs: Flows.Inputs =
            { Carriers = carriers; Joins = Map.empty; Layouts = Map.empty; SequenceFlows = Map.empty; SequenceFamilies = Map.empty }
        let flows, errors = Flows.settle inputs graph
        Assert.Empty errors
        Assert.Equal<NodeId list>((markerId :: List.tail alternatives) |> List.sort, flows[formal].Alternatives)
        Assert.Contains(markerId, flows[formal].Dependencies[formal])
        Assert.Equal(markerId, carriers[markerId].Occurrence)
        Assert.Equal(carriers[actual].Implementation, carriers[markerId].Implementation)
        Assert.Contains(graph.Edges, fun edge ->
            edge.Target = callId && edge.Role = EdgeRole.EagerDemand EagerFrontier.Actual && List.contains markerId edge.Sources)
        for changed in [{ marker with Children = [] }; { marker with Type = Types.boolType }; { marker with IsReachable = false }] do
            let invalid = { graph with Nodes = graph.Nodes.Add(markerId, changed) }
            Assert.False(Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.allowsOccurrence
                             (Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.analyze invalid) formal)
        Assert.Equal(SemanticKind.EagerExpr actual, graph.Nodes[markerId].Kind)

    [<Fact>]
    member _.``Higher-order formal keeps every exact actual and complete call without inventing a storage frontier`` () =
        let graph, _, formal, read, alternatives, calls, _ = CallableFlowFixture.create ()
        for occurrence in [formal; read] do
            let flow = graph.Codata.Value.CallableFlows[occurrence]
            Assert.Equal<NodeId list>(alternatives |> List.sort, flow.Alternatives)
            Assert.Equal<NodeId list>(calls |> List.sort, flow.Calls |> List.map _.Call |> List.sort)
            Assert.Equal<NodeId list>(alternatives, flow.Dependencies[formal])
            Assert.True(Flows.validate graph flow)
        Assert.Equal<NodeId list>([formal], graph.Codata.Value.CallableFlows[read].Dependencies[read])
        Assert.Empty graph.Codata.Value.CallableJoins
        Assert.Empty graph.Codata.Value.MutableCallableStorage

    [<Theory>]
    [<InlineData("opaque-actual")>]
    [<InlineData("partial-call")>]
    [<InlineData("redirected-alias")>]
    member _.``Changed actual invocation or alias retracts the retained complete boundary`` defect =
        let graph, _, formal, read, _, calls, opaque = CallableFlowFixture.create ()
        for occurrence in [formal; read] do
            Assert.True(Flows.validate graph graph.Codata.Value.CallableFlows[occurrence])
        let changed =
            match defect with
            | "redirected-alias" ->
                let node = graph.Nodes[read]
                { graph with Nodes = graph.Nodes.Add(read, { node with Kind = SemanticKind.VarRef("opaque", Some opaque) }) }
            | _ ->
                let node = graph.Nodes[List.last calls]
                match node.Kind with
                | SemanticKind.Application(callee, _) ->
                    let args = if defect = "partial-call" then [] else [opaque]
                    { graph with Nodes = graph.Nodes.Add(node.Id, { node with Kind = SemanticKind.Application(callee, args); Children = callee :: args }) }
                | _ -> failwith "Missing fixture application"
        // Refresh only demand evidence; retain the old callable flow to test
        // that its complete call/alias boundary is rejected after this edit.
        let changed = CallableFlowFixture.demand changed
        Assert.False(Flows.validate changed graph.Codata.Value.CallableFlows[read])
        if defect <> "redirected-alias" then Assert.False(Flows.validate changed graph.Codata.Value.CallableFlows[formal])

    [<Fact>]
    member _.``A known partial alternative is not a complete invocation even beside a complete target`` () =
        let builder = NodeBuilder()
        let boolean name = builder.Create(SemanticKind.PatternBinding name, Types.boolType, dummyRange)
        let x, y, a, b = boolean "x", boolean "y", boolean "a", boolean "b"
        let unary = NativeType.TFun(Types.boolType, Types.boolType)
        let binary = NativeType.TFun(Types.boolType, unary)
        let nested = builder.Create(SemanticKind.Lambda(["y", Types.boolType, y.Id], y.Id, [], None, LambdaContext.RegularClosure), unary, dummyRange)
        builder.SetMetadata(nested.Id, ClosureMetadata.LambdaExpression, MetadataValue.Bool true)
        let returned = builder.Create(SemanticKind.Lambda(["x", Types.boolType, x.Id], nested.Id, [], None, LambdaContext.RegularClosure), binary, dummyRange)
        let flat = builder.Create(SemanticKind.Lambda(["a", Types.boolType, a.Id; "b", Types.boolType, b.Id], b.Id,
                                                    [], None, LambdaContext.RegularClosure), binary, dummyRange)
        let condition = boolean "condition"
        let choose = builder.Create(SemanticKind.IfThenElse(condition.Id, returned.Id, Some flat.Id), binary, dummyRange)
        let call = builder.Create(SemanticKind.Application(choose.Id, [condition.Id]), unary, dummyRange)
        let graph = builder.Build []
        let resolved = (FlowOrigins.resolve graph).Calls[call.Id]
        Assert.False resolved.Unknown
        Assert.False resolved.Complete
        Assert.Equal(returned.Id, (Assert.Single resolved.Targets).Lambda)
        Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments.tryImplementation graph call.Id).IsNone)

    [<Fact>]
    member _.``Stateless callbacks used through a formal with several targets become plain code`` () =
        let result = DimensionalCases.check """
let higher (callback: bool -> bool) = callback true
let first = higher (fun value -> value)
let second = higher (fun value -> not value)
"""
        DimensionalCases.noErrors result
        let marked = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            (match node.Kind with SemanticKind.Lambda _ -> true | _ -> false) &&
            (node.Metadata.TryFind ClosureMetadata.RequiresClosurePair = Some(MetadataValue.Bool true) ||
             node.Metadata.TryFind ClosureMetadata.LambdaExpression = Some(MetadataValue.Bool true)))
        Assert.Empty marked

// These tests exercise source callable origins, not closure residence or native
// admission. The raw controls use the same typed DU guard as ResultRecipes.
module private CallableResultOriginFixture =
    type Model =
        { Graph: SemanticGraph
          Call: NodeId
          First: NodeId
          Fallback: NodeId
          Constructor: NodeId
          ErrorPayload: NodeId
          ExpectedTag: NodeId }

    let create mode =
        let builder = NodeBuilder()
        let callable = NativeType.TFun(Types.boolType, Types.boolType)
        let resultType =
            NativeType.TApp(Clef.Compiler.NativeTypedTree.Expressions.Types.resultTycon,
                            [callable; Types.boolType])
        let pendingFactory =
            if mode = "late-factory" then
                let ty = NativeType.TFun(Types.unitType, resultType)
                let read = builder.Create(SemanticKind.PatternBinding "lateFactory", ty, dummyRange)
                let binding = builder.Create(SemanticKind.Binding("lateFactory", false, false, None), ty, dummyRange)
                Some(read, binding, ty)
            else None
        // These identifiers precede their producing constructor. Their facts
        // arrive on a later fixed-point pass, not in the first map traversal.
        let delayedRead = builder.Create(SemanticKind.PatternBinding "delayed", resultType, dummyRange)
        let delayedBinding = builder.Create(SemanticKind.Binding("delayed", false, false, None), resultType, dummyRange)
        let functionValue name result =
            let parameter = builder.Create(SemanticKind.PatternBinding name, Types.boolType, dummyRange)
            let body = builder.Create(SemanticKind.Literal(NativeLiteral.Bool result), Types.boolType, dummyRange)
            let code =
                builder.Create(SemanticKind.Lambda([name, Types.boolType, parameter.Id], body.Id,
                                                  [], None, LambdaContext.RegularClosure), callable, dummyRange)
            builder.SetParent(parameter.Id, code.Id)
            builder.SetParent(body.Id, code.Id)
            code
        let first = functionValue "firstArgument" true
        let fallback = functionValue "fallbackArgument" false
        let errorPayload = builder.Create(SemanticKind.Literal(NativeLiteral.Bool false), Types.boolType, dummyRange)
        let okValue = builder.Create(SemanticKind.DUConstruct("Ok", 0, Some first.Id, None), resultType, dummyRange)
        let errorValue = builder.Create(SemanticKind.DUConstruct("Error", 1, Some errorPayload.Id, None), resultType, dummyRange)
        let opaque = builder.Create(SemanticKind.PatternBinding "opaqueResult", resultType, dummyRange)
        let condition = builder.Create(SemanticKind.PatternBinding "condition", Types.boolType, dummyRange)
        builder.CompleteNode(delayedRead.Id, SemanticKind.VarRef("delayed", Some delayedBinding.Id), []) |> ignore
        let delayedValue =
            if mode = "cycle" then delayedRead.Id
            elif mode = "alias" then okValue.Id
            else errorValue.Id
        builder.CompleteNode(delayedBinding.Id, delayedBinding.Kind, [delayedValue]) |> ignore
        let input =
            match mode with
            | "known" -> okValue
            | "mixed" ->
                builder.Create(SemanticKind.IfThenElse(condition.Id, okValue.Id, Some errorValue.Id), resultType, dummyRange)
            | "opaque" ->
                builder.Create(SemanticKind.IfThenElse(condition.Id, okValue.Id, Some opaque.Id), resultType, dummyRange)
            | "late" ->
                builder.Create(SemanticKind.IfThenElse(condition.Id, okValue.Id, Some delayedRead.Id), resultType, dummyRange)
            | "cycle" -> builder.Nodes[delayedRead.Id]
            | "alias" -> builder.Nodes[delayedRead.Id]
            | "late-factory" ->
                let read, binding, factoryType = Option.get pendingFactory
                let formal = builder.Create(SemanticKind.PatternBinding "factoryUnit", Types.unitType, dummyRange)
                let factory =
                    builder.Create(SemanticKind.Lambda(["factoryUnit", Types.unitType, formal.Id], okValue.Id,
                                                      [], None, LambdaContext.RegularClosure), factoryType, dummyRange)
                builder.SetParent(formal.Id, factory.Id)
                builder.CompleteNode(read.Id, SemanticKind.VarRef("lateFactory", Some binding.Id), []) |> ignore
                builder.CompleteNode(binding.Id, binding.Kind, [factory.Id]) |> ignore
                let unitValue = builder.Create(SemanticKind.Literal NativeLiteral.Unit, Types.unitType, dummyRange)
                let invocation = builder.Create(SemanticKind.Application(read.Id, [unitValue.Id]), resultType, dummyRange)
                builder.Create(SemanticKind.IfThenElse(condition.Id, okValue.Id, Some invocation.Id), resultType, dummyRange)
            | other -> failwithf "Unexpected origin fixture mode: %s" other
        let tag = builder.Create(SemanticKind.DUGetTag(input.Id, resultType), Types.int8Type, dummyRange)
        let expected =
            builder.Create(SemanticKind.Literal(NativeLiteral.Int(0L, NTUKind.NTUint(NTUWidth.Fixed 8))),
                           Types.int8Type, dummyRange)
        let equality =
            builder.Create(SemanticKind.Intrinsic
                { Module = IntrinsicModule.Operators; Operation = "op_Equality"
                  Category = IntrinsicCategory.Comparison; FullName = "op_Equality" },
                NativeType.TFun(Types.int8Type, NativeType.TFun(Types.int8Type, Types.boolType)), dummyRange)
        let guard = builder.Create(SemanticKind.Application(equality.Id, [tag.Id; expected.Id]), Types.boolType, dummyRange)
        let payload = builder.Create(SemanticKind.DUEliminate(input.Id, 0, "Ok", callable), callable, dummyRange)
        let choice = builder.Create(SemanticKind.IfThenElse(guard.Id, payload.Id, Some fallback.Id), callable, dummyRange)
        let actual = builder.Create(SemanticKind.Literal(NativeLiteral.Bool true), Types.boolType, dummyRange)
        let call = builder.Create(SemanticKind.Application(choice.Id, [actual.Id]), Types.boolType, dummyRange)
        { Graph = builder.Build []; Call = call.Id; First = first.Id; Fallback = fallback.Id
          Constructor = okValue.Id; ErrorPayload = errorPayload.Id; ExpectedTag = expected.Id }

    let targets (resolved: FlowOrigins.ResolvedCall) =
        resolved.Targets |> List.map _.Lambda |> Set.ofList

    let complete expected (resolved: FlowOrigins.ResolvedCall) =
        Assert.False resolved.Unknown
        Assert.True resolved.Complete
        Assert.Equal<Set<NodeId>>(Set.ofList expected, targets resolved)

    let source ok =
        let constructor = if ok then "Ok first" else "Error false"
        let text =
            "module CallableResultOrigins\n" +
            "let first (value: bool) = value\n" +
            "let fallback (value: bool) = false\n" +
            "let input () : Result<bool -> bool, bool> = " + constructor + "\n" +
            "let observed = Result.defaultValue fallback (input ()) true\n" +
            "[<EntryPoint>]\nlet main _ = if observed = first true then 0 else 1\n"
        let result =
            match Clef.Compiler.NativeService.parseAndCheck text "callable-result-origins.clef" with
            | Clef.Compiler.NativeService.Success result
            | Clef.Compiler.NativeService.CheckFailure result -> result
            | Clef.Compiler.NativeService.ParseFailure errors -> failwithf "Unexpected source parse refusal: %A" errors
        let graph = result.Graph
        let choices =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.IfThenElse(guard, yes, Some no) when node.IsReachable ->
                    match graph.Nodes[yes].Kind with
                    | SemanticKind.DUEliminate(input, 0, "Ok", callable) ->
                        match callable with
                        | NativeType.TFun _ ->
                            match graph.Nodes[guard].Kind with
                            | SemanticKind.Application(compare, [tag; expected]) ->
                                match graph.Nodes[compare].Kind, graph.Nodes[tag].Kind, graph.Nodes[expected].Kind with
                                | SemanticKind.Intrinsic info, SemanticKind.DUGetTag(original, carrier),
                                  SemanticKind.Literal(NativeLiteral.Int(0L, _)) ->
                                    Assert.Equal(IntrinsicModule.Operators, info.Module)
                                    Assert.Equal("op_Equality", info.Operation)
                                    Assert.Equal(input, original)
                                    DimensionalCases.same graph.Nodes[input].Type carrier
                                    Some(node.Id, no)
                                | kinds -> failwithf "Result lost its canonical typed tag guard: %A" kinds
                            | kind -> failwithf "Result lost its canonical guard application: %A" kind
                        | _ -> None
                    | _ -> None
                | _ -> None)
            |> Seq.toList
        let choice, fallback = Assert.Single choices
        let call =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                node.IsReachable &&
                match node.Kind with
                | SemanticKind.Application(callee, [_]) -> callee = choice
                | _ -> false)
            |> Assert.Single
        let named name =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                node.IsReachable &&
                match node.Kind with
                | SemanticKind.Binding(actual, false, _, _) -> actual = name || actual.EndsWith("." + name)
                | _ -> false)
            |> Assert.Single
        result, call.Id, (named "first").Id, fallback

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "CallableFlow")>]
type CallableResultOriginCases() =
    [<Fact>]
    member _.``A late same-tag factory cannot leave a second target beside a final branch selection`` () =
        let model = CallableResultOriginFixture.create "late-factory"
        let reference =
            model.Graph.Nodes.Values
            |> Seq.filter (fun node ->
                match node.Kind with SemanticKind.VarRef("lateFactory", Some _) -> true | _ -> false)
            |> Assert.Single
        let binding =
            match reference.Kind with
            | SemanticKind.VarRef(_, Some binding) -> model.Graph.Nodes[binding]
            | _ -> failwith "Expected the exact late factory reference"
        let implementation = Assert.Single binding.Children
        Assert.True(NodeId.value reference.Id < NodeId.value binding.Id)
        Assert.True(NodeId.value binding.Id < NodeId.value implementation)
        let current = FlowOrigins.resolveCallableBranches model.Graph
        let observation = (Assert.Single current.Branches).Value
        let alternative = Assert.Single observation.Alternatives
        Assert.Equal(model.Constructor, alternative.Constructor)
        Assert.Equal(0, alternative.Tag)
        // The late call returns the same Ok constructor. A final singleton
        // branch observation must agree with the surviving callable facts.
        CallableResultOriginFixture.complete [model.First] current.Calls[model.Call]
        Assert.Empty current.FirstBoundaries[model.Call].UnknownOrigins

    [<Theory>]
    [<InlineData(true)>]
    [<InlineData(false)>]
    member _.``Known Result case selects exactly its source callable with complete origins`` (ok: bool) =
        let result, call, first, fallback = CallableResultOriginFixture.source ok
        let origins = FlowOrigins.resolveCallableBranches result.Graph
        let expectedValue, declaration =
            if ok then
                let payload =
                    result.Graph.Nodes.Values
                    |> Seq.choose (fun node ->
                        match node.Kind with
                        | SemanticKind.DUConstruct("Ok", 0, Some payload, None) when node.IsReachable -> Some payload
                        | _ -> None)
                    |> Assert.Single
                payload, first
            else
                let declaration =
                    result.Graph.Nodes.Values
                    |> Seq.filter (fun node ->
                        node.IsReachable &&
                        match node.Kind with
                        | SemanticKind.Binding(name, false, _, _) -> name = "fallback" || name.EndsWith(".fallback")
                        | _ -> false)
                    |> Assert.Single
                fallback, declaration.Id
        // Stored source functions are eta-expanded. The constructor payload
        // (or exact fallback arm) owns that implementation, not the original
        // named lambda. Verify the wrapper's source call independently of the
        // resolver whose selected target is under test.
        let code, parameters, body, captures = CallableTestContracts.shape result.Graph expectedValue
        Assert.Empty captures
        let _, _, formal = Assert.Single parameters
        match result.Graph.Nodes[body].Kind with
        | SemanticKind.Application(callee, [argument]) ->
            CallableTestContracts.referenceTo result.Graph declaration callee
            CallableTestContracts.referenceTo result.Graph formal argument
        | kind -> failwithf "Stored Result callable lost exact source forwarding: %A" kind
        CallableResultOriginFixture.complete [code.Id] origins.Calls[call]
        Assert.Empty origins.FirstBoundaries[call].UnknownOrigins
        // The direct-reader assertion runs even when source checking reported
        // the old defect; successful resolution must not waive other errors.
        DimensionalCases.noErrors result

    [<Fact>]
    member _.``Default callable resolution keeps conservative joins without branch observations`` () =
        let model = CallableResultOriginFixture.create "known"
        let conservative = FlowOrigins.resolve model.Graph
        CallableResultOriginFixture.complete [model.First; model.Fallback] conservative.Calls[model.Call]
        Assert.Empty conservative.Branches
        let finalReading = FlowOrigins.resolveCallableBranches model.Graph
        CallableResultOriginFixture.complete [model.First] finalReading.Calls[model.Call]
        Assert.Single finalReading.Branches |> ignore

    [<Theory>]
    [<InlineData("wrong-binding-type")>]
    [<InlineData("missing-binding-value")>]
    [<InlineData("contradictory-binding-edge")>]
    member _.``Malformed intermediate transport cannot authorize a callable branch`` (mutation: string) =
        let model = CallableResultOriginFixture.create "alias"
        let baseline = FlowOrigins.resolveCallableBranches model.Graph
        CallableResultOriginFixture.complete [model.First] baseline.Calls[model.Call]
        Assert.Single baseline.Branches |> ignore
        let binding =
            model.Graph.Nodes.Values
            |> Seq.filter (fun node ->
                match node.Kind with SemanticKind.Binding("delayed", false, _, _) -> true | _ -> false)
            |> Assert.Single
        let changed =
            match mutation with
            | "wrong-binding-type" ->
                { model.Graph with Nodes = model.Graph.Nodes.Add(binding.Id, { binding with Type = Types.boolType }) }
            | "missing-binding-value" ->
                { model.Graph with Nodes = model.Graph.Nodes.Add(binding.Id, { binding with Children = [] }) }
            | "contradictory-binding-edge" ->
                let wrong = Hyperedge.edge1 EdgeClass.Structural EdgeRole.Attached 0 model.ErrorPayload binding.Id
                { model.Graph with Edges = wrong :: model.Graph.Edges }
            | other -> failwithf "Unexpected transport mutation: %s" other
        let current = FlowOrigins.resolveCallableBranches changed
        Assert.True current.Calls[model.Call].Unknown
        Assert.False current.Calls[model.Call].Complete
        Assert.Empty current.Branches

    [<Fact>]
    member _.``Mixed known Result constructors retain both complete callable alternatives`` () =
        let model = CallableResultOriginFixture.create "mixed"
        let origins = FlowOrigins.resolveCallableBranches model.Graph
        CallableResultOriginFixture.complete [model.First; model.Fallback] origins.Calls[model.Call]
        Assert.Empty origins.FirstBoundaries[model.Call].UnknownOrigins

    [<Fact>]
    member _.``Known Result beside an opaque alternative cannot become complete callable evidence`` () =
        let model = CallableResultOriginFixture.create "opaque"
        let origins = FlowOrigins.resolveCallableBranches model.Graph
        let call = origins.Calls[model.Call]
        Assert.True call.Unknown
        Assert.False call.Complete
        Assert.Equal<Set<NodeId>>(Set.ofList [model.First; model.Fallback], CallableResultOriginFixture.targets call)
        Assert.NotEmpty origins.FirstBoundaries[model.Call].UnknownOrigins

    [<Fact>]
    member _.``An opposing Result constructor arriving on a later pass widens callable selection`` () =
        let model = CallableResultOriginFixture.create "late"
        let origins = FlowOrigins.resolveCallableBranches model.Graph
        CallableResultOriginFixture.complete [model.First; model.Fallback] origins.Calls[model.Call]
        Assert.Empty origins.FirstBoundaries[model.Call].UnknownOrigins

    [<Fact>]
    member _.``An empty Result origin cycle cannot establish a callable branch selection`` () =
        let model = CallableResultOriginFixture.create "cycle"
        let origins = FlowOrigins.resolveCallableBranches model.Graph
        let call = origins.Calls[model.Call]
        Assert.True call.Unknown
        Assert.False call.Complete
        Assert.Equal<Set<NodeId>>(Set.singleton model.Fallback, CallableResultOriginFixture.targets call)
        Assert.NotEmpty origins.FirstBoundaries[model.Call].UnknownOrigins

    [<Theory>]
    [<InlineData("guard-tag")>]
    [<InlineData("constructor-tag")>]
    member _.``Current guard or constructor edits retract a prior exact Result callable selection`` (mutation: string) =
        let model = CallableResultOriginFixture.create "known"
        let model =
            { model with
                Graph =
                    { model.Graph with
                        Edges = kindEdges model.Constructor model.Graph.Nodes[model.Constructor].Kind } }
        let before = FlowOrigins.resolveCallableBranches model.Graph
        CallableResultOriginFixture.complete [model.First] before.Calls[model.Call]
        let changed =
            match mutation with
            | "guard-tag" ->
                let node = model.Graph.Nodes[model.ExpectedTag]
                let kind =
                    match node.Kind with
                    | SemanticKind.Literal(NativeLiteral.Int(_, representation)) ->
                        SemanticKind.Literal(NativeLiteral.Int(1L, representation))
                    | other -> failwithf "Expected source guard tag literal: %A" other
                { model.Graph with Nodes = model.Graph.Nodes.Add(node.Id, { node with Kind = kind }) }
            | "constructor-tag" ->
                let node = model.Graph.Nodes[model.Constructor]
                let changed =
                    { node with
                        Kind = SemanticKind.DUConstruct("Error", 1, Some model.ErrorPayload, None)
                        Children = [model.ErrorPayload] }
                let edges =
                    model.Graph.Edges
                    |> List.filter (fun edge -> edge.Target <> node.Id || edge.Class <> EdgeClass.Structural)
                { model.Graph with
                    Nodes = model.Graph.Nodes.Add(node.Id, changed)
                    Edges = edges @ kindEdges node.Id changed.Kind }
            | other -> failwithf "Unexpected mutation: %s" other
        Assert.Equal<NodeId list>(model.Graph.Nodes |> Map.keys |> Seq.toList, changed.Nodes |> Map.keys |> Seq.toList)
        let after = FlowOrigins.resolveCallableBranches changed
        CallableResultOriginFixture.complete [model.Fallback] after.Calls[model.Call]
        Assert.Empty after.FirstBoundaries[model.Call].UnknownOrigins
        Assert.DoesNotContain(model.First, CallableResultOriginFixture.targets after.Calls[model.Call])

    [<Fact>]
    member _.``Contradictory current constructor incidence cannot authorize a Result branch selection`` () =
        let model = CallableResultOriginFixture.create "known"
        let constructor = model.Graph.Nodes[model.Constructor]
        let original =
            { model.Graph with Edges = kindEdges constructor.Id constructor.Kind }
        CallableResultOriginFixture.complete [model.First] (FlowOrigins.resolveCallableBranches original).Calls[model.Call]
        let changedConstructor =
            { constructor with
                Kind = SemanticKind.DUConstruct("Error", 1, Some model.ErrorPayload, None)
                Children = [model.ErrorPayload] }
        // Deliberately retain the old recorded Payload incidence. This differs
        // from a legitimate constructor edit, which changes all source facts.
        let changed = { original with Nodes = original.Nodes.Add(constructor.Id, changedConstructor) }
        let retained = Assert.Single changed.Edges
        Assert.Equal(EdgeClass.Structural, retained.Class)
        Assert.Equal(EdgeRole.Payload, retained.Role)
        Assert.Equal<NodeId list>([model.First], retained.Sources)
        Assert.Equal<NodeId list>([model.ErrorPayload], changed.Nodes[model.Constructor].Children)
        let origins = FlowOrigins.resolveCallableBranches changed
        Assert.True origins.Calls[model.Call].Unknown
        Assert.False origins.Calls[model.Call].Complete
        Assert.NotEmpty origins.FirstBoundaries[model.Call].UnknownOrigins

module BranchAuthorityRecipe = Clef.Compiler.Baker.Recipes.CallableBranchRecipes
module BranchAuthoritySettlement = Clef.Compiler.Nanopass.CallableBranchSettlement

module private CallableBranchAuthorityFixture =
    let refusal =
        "Callable branch authority is missing or differs from the current whole-revision origin census; Baker branch settlement is required."

    let current graph =
        match BranchAuthorityRecipe.validate graph with
        | Result.Ok authority -> authority
        | Result.Error failures -> failwithf "Expected current branch authority: %A" failures

    let refused graph =
        match BranchAuthorityRecipe.validate graph with
        | Result.Ok _ -> failwith "Stale whole-revision branch authority was accepted"
        | Result.Error failures ->
            Assert.Contains(failures, fun failure -> failure.Reason = refusal)

    let settle graph =
        let settled, carrierResiduals, flowResiduals = BranchAuthoritySettlement.normalize graph
        Assert.Empty carrierResiduals
        Assert.Empty flowResiduals
        Assert.NotEmpty (current settled).Observations
        settled

    let create () =
        let model = CallableResultOriginFixture.create "known"
        let builder = NodeBuilder()
        let resultType = model.Graph.Nodes[model.Constructor].Type
        let condition = builder.Create(SemanticKind.PatternBinding "condition", Types.boolType, dummyRange)
        // The two identical arms make this transport complete without needing
        // a guard fact. The final callable choice is a separate canonical tag test.
        let transport =
            builder.Create(SemanticKind.IfThenElse(condition.Id, model.Constructor, Some model.Constructor),
                           resultType, dummyRange)
        let binding =
            builder.Create(SemanticKind.Binding("resultInput", false, false, None), resultType,
                           dummyRange, children = [transport.Id])
        let read = builder.Create(SemanticKind.VarRef("resultInput", Some binding.Id), resultType, dummyRange)
        builder.SetParent(condition.Id, transport.Id)
        builder.SetParent(transport.Id, binding.Id)
        let nodes =
            model.Graph.Nodes
            |> Map.map (fun _ node ->
                match node.Kind with
                | SemanticKind.DUGetTag(subject, carrier) when subject = model.Constructor ->
                    { node with Kind = SemanticKind.DUGetTag(read.Id, carrier); Children = [read.Id] }
                | SemanticKind.DUEliminate(subject, index, name, payload) when subject = model.Constructor ->
                    { node with Kind = SemanticKind.DUEliminate(read.Id, index, name, payload); Children = [read.Id] }
                | _ -> node)
        let nodes = builder.Nodes |> Map.fold (fun state id node -> Map.add id node state) nodes
        let graph = { model.Graph with Nodes = nodes } |> CallableFlowFixture.demand
        model, transport.Id, graph

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "CallableFlow")>]
type CallableBranchAuthorityCases() =
    [<Fact>]
    member _.``Final callable settlement preserves source identities and conservative early origins`` () =
        let model, _, graph = CallableBranchAuthorityFixture.create ()
        CallableResultOriginFixture.complete [model.First; model.Fallback] (FlowOrigins.resolve graph).Calls[model.Call]
        let settled = CallableBranchAuthorityFixture.settle graph
        CallableResultOriginFixture.complete [model.First] (FlowOrigins.resolveCallableBranches settled).Calls[model.Call]
        CallableResultOriginFixture.complete [model.First; model.Fallback] (FlowOrigins.resolve settled).Calls[model.Call]
        Assert.Same(graph.Nodes, settled.Nodes)
        Assert.Same(graph.Edges, settled.Edges)
        Assert.Same(graph.DeclarationRoots, settled.DeclarationRoots)
        Assert.Same(graph.Codata.Value.CallableJoins, settled.Codata.Value.CallableJoins)
        Assert.Same(graph.Codata.Value.MutableCallableStorage, settled.Codata.Value.MutableCallableStorage)
        let authority = CallableBranchAuthorityFixture.current settled
        Assert.Equal(CallableBranchScope.WholeRevision, authority.Scope)
        let row = authority.Observations |> Map.toList |> Assert.Single |> snd
        let direct =
            [ ParticipantRole.BranchChoice, row.Choice
              ParticipantRole.BranchGuard, row.Guard
              ParticipantRole.BranchOperator, row.Operator
              ParticipantRole.BranchTagRead, row.TagRead
              ParticipantRole.BranchSubject, row.Subject
              ParticipantRole.BranchLiteral, row.Literal
              ParticipantRole.BranchTrueArm, row.TrueArm
              ParticipantRole.BranchFalseArm, row.FalseArm
              ParticipantRole.BranchSelectedArm, row.SelectedArm ]
            |> List.map (fun (role, node) ->
                { Node = node; Role = role; Ordinal = 0; Group = row.Choice } : Participant)
        let alternatives =
            row.Alternatives
            |> List.mapi (fun ordinal alternative ->
                { Node = alternative.Constructor; Role = ParticipantRole.BranchConstructor
                  Ordinal = ordinal; Group = row.Choice }
                :: (alternative.Payloads
                    |> List.mapi (fun position payload ->
                        { Node = payload; Role = ParticipantRole.BranchPayload
                          Ordinal = position; Group = alternative.Constructor })))
            |> List.concat
        Assert.Equal<Participant list>(direct @ alternatives, row.Participants)
        let selected = row.Participants |> List.filter (fun occurrence -> occurrence.Role = ParticipantRole.BranchSelectedArm) |> Assert.Single
        Assert.Equal(row.TrueArm, selected.Node)
        Assert.Equal(2, row.Participants |> List.filter (fun occurrence -> occurrence.Node = row.TrueArm) |> List.length)
        Assert.Contains(model.Call, authority.CallUses)

    [<Theory>]
    [<InlineData("missing-observation")>]
    [<InlineData("wrong-arm")>]
    [<InlineData("missing-call-use")>]
    member _.``Missing or altered stored branch authority cannot be reconstructed by its reader`` (mutation: string) =
        let model, _, raw = CallableBranchAuthorityFixture.create ()
        let graph = CallableBranchAuthorityFixture.settle raw
        let authority = CallableBranchAuthorityFixture.current graph
        let key, row = authority.Observations |> Map.toList |> Assert.Single
        let changedAuthority =
            match mutation with
            | "missing-observation" -> { authority with Observations = Map.empty }
            | "wrong-arm" ->
                Assert.Equal(row.TrueArm, row.SelectedArm)
                { authority with Observations = authority.Observations.Add(key, { row with SelectedArm = row.FalseArm }) }
            | "missing-call-use" -> { authority with CallUses = authority.CallUses.Remove model.Call }
            | other -> failwithf "Unexpected authority mutation: %s" other
        let changed = { graph with Codata = lazy { graph.Codata.Value with CallableBranches = changedAuthority } }
        Assert.Same(graph.Nodes, changed.Nodes)
        Assert.Same(graph.Edges, changed.Edges)
        CallableBranchAuthorityFixture.refused changed
        Assert.Equal<CallableBranchAuthority>(changedAuthority, changed.Codata.Value.CallableBranches)
        Assert.Equal<CallableBranchAuthority>(authority, CallableBranchAuthorityFixture.current graph)

    [<Fact>]
    member _.``Opaque origin outside recorded participants withdraws whole-revision branch authority`` () =
        let model, transportId, raw = CallableBranchAuthorityFixture.create ()
        let graph = CallableBranchAuthorityFixture.settle raw
        let authority = CallableBranchAuthorityFixture.current graph
        let row = authority.Observations |> Map.toList |> Assert.Single |> snd
        let participantNodes = row.Participants |> List.collect (fun occurrence -> [occurrence.Node; occurrence.Group]) |> Set.ofList
        Assert.DoesNotContain(transportId, participantNodes)
        let before = FlowOrigins.resolveCallableBranches graph
        CallableResultOriginFixture.complete [model.First] before.Calls[model.Call]
        let transport = graph.Nodes[transportId]
        let builder = NodeBuilder()
        let opaque = builder.Create(SemanticKind.PatternBinding "newOpaqueResult", transport.Type, dummyRange)
        let changedTransport =
            match transport.Kind with
            | SemanticKind.IfThenElse(condition, yes, Some _) ->
                { transport with Kind = SemanticKind.IfThenElse(condition, yes, Some opaque.Id)
                                 Children = [condition; yes; opaque.Id] }
            | other -> failwithf "Expected immutable alternative transport: %A" other
        let changed = { graph with Nodes = graph.Nodes.Add(transportId, changedTransport).Add(opaque.Id, opaque) }
        Assert.DoesNotContain(opaque.Id, participantNodes)
        for id in participantNodes do Assert.Same(graph.Nodes[id], changed.Nodes[id])
        let after = FlowOrigins.resolveCallableBranches changed
        Assert.Equal<Set<NodeId>>(before.Calls |> Map.keys |> Set.ofSeq, after.Calls |> Map.keys |> Set.ofSeq)
        Assert.True after.Calls[model.Call].Unknown
        Assert.False after.Calls[model.Call].Complete
        Assert.Equal<Set<NodeId>>(Set.ofList [model.First; model.Fallback], CallableResultOriginFixture.targets after.Calls[model.Call])
        Assert.Empty after.Branches
        CallableBranchAuthorityFixture.refused changed
        Assert.Equal<CallableBranchAuthority>(authority, changed.Codata.Value.CallableBranches)
        Assert.Equal<CallableBranchAuthority>(authority, CallableBranchAuthorityFixture.current graph)

module private CallableAbsentPayloadFixture =
    type Model = {
        Graph: SemanticGraph
        Call: NodeId
        First: NodeId
        Fallback: NodeId
        Constructor: NodeId
        Projection: NodeId
        Reference: NodeId
        Opaque: NodeId
        ActiveName: string
        ActiveTag: int
    }

    let create union mode =
        let builder = NodeBuilder()
        let callable = NativeType.TFun(Types.boolType, Types.boolType)
        let functionValue name =
            let parameter = builder.Create(SemanticKind.PatternBinding name, Types.boolType, dummyRange)
            let read = builder.Create(SemanticKind.VarRef(name, Some parameter.Id), Types.boolType, dummyRange)
            builder.Create(SemanticKind.Lambda([name, Types.boolType, parameter.Id], read.Id,
                                              [], None, LambdaContext.RegularClosure), callable, dummyRange)
        let first, fallback = functionValue "first", functionValue "fallback"
        let error = builder.Create(SemanticKind.Literal(NativeLiteral.Bool false), Types.boolType, dummyRange)
        let carrier, absentName, absentTag, absentPayload, activeName, activeTag =
            if union = "option" then
                NativeType.TApp(Types.optionTyCon, [callable]), "None", 0, None, "Some", 1
            else
                NativeType.TApp(Clef.Compiler.NativeTypedTree.Expressions.Types.resultTycon, [callable; Types.boolType]),
                "Error", 1, Some error.Id, "Ok", 0
        let absent = builder.Create(SemanticKind.DUConstruct(absentName, absentTag, absentPayload, None), carrier, dummyRange)
        let active = builder.Create(SemanticKind.DUConstruct(activeName, activeTag, Some first.Id, None), carrier, dummyRange)
        let opaque = builder.Create(SemanticKind.PatternBinding "opaque", carrier, dummyRange)
        let condition = builder.Create(SemanticKind.PatternBinding "condition", Types.boolType, dummyRange)
        let input =
            match mode with
            | "mixed" -> builder.Create(SemanticKind.IfThenElse(condition.Id, absent.Id, Some active.Id), carrier, dummyRange)
            | "opaque" -> builder.Create(SemanticKind.IfThenElse(condition.Id, absent.Id, Some opaque.Id), carrier, dummyRange)
            | _ -> absent
        let inputBinding = builder.Create(SemanticKind.Binding("input", false, false, None), carrier, dummyRange, children = [input.Id])
        let reference = builder.Create(SemanticKind.VarRef("input", Some inputBinding.Id), carrier, dummyRange)
        let projection = builder.Create(SemanticKind.DUEliminate(reference.Id, activeTag, activeName, callable), callable, dummyRange)
        let alias = builder.Create(SemanticKind.Binding("projected", false, false, None), callable, dummyRange, children = [projection.Id])
        let aliasRead = builder.Create(SemanticKind.VarRef("projected", Some alias.Id), callable, dummyRange)
        let choice = builder.Create(SemanticKind.IfThenElse(condition.Id, aliasRead.Id, Some fallback.Id), callable, dummyRange)
        let argument = builder.Create(SemanticKind.Literal(NativeLiteral.Bool true), Types.boolType, dummyRange)
        let call = builder.Create(SemanticKind.Application(choice.Id, [argument.Id]), Types.boolType, dummyRange)
        { Graph = builder.Build []; Call = call.Id; First = first.Id; Fallback = fallback.Id
          Constructor = absent.Id; Projection = projection.Id; Reference = reference.Id; Opaque = opaque.Id
          ActiveName = activeName; ActiveTag = activeTag }

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "CallableFlow")>]
type CallableAbsentPayloadCases() =
    // Width Inference §6 distinguishes unreachable computations from missing
    // observations. NTU Types §3.2 joins the actual call-site alternatives.
    [<Theory>]
    [<InlineData("option")>]
    [<InlineData("result")>]
    member _.``A proved absent callable payload stays empty through aliases without obscuring its fallback`` union =
        let model = CallableAbsentPayloadFixture.create union "absent"
        for resolve in [FlowOrigins.resolve; FlowOrigins.resolveCallableBranches] do
            let current = resolve model.Graph
            CallableResultOriginFixture.complete [model.Fallback] current.Calls[model.Call]
            Assert.Empty current.FirstBoundaries[model.Call].UnknownOrigins
        // Rechecking the same identifiers after a legitimate case edit must
        // discover the new payload, rather than retain the earlier emptiness.
        let constructor = model.Graph.Nodes[model.Constructor]
        let changed =
            { constructor with Kind = SemanticKind.DUConstruct(model.ActiveName, model.ActiveTag, Some model.First, None)
                               Children = [model.First] }
        let graph =
            { model.Graph with Nodes = model.Graph.Nodes.Add(changed.Id, changed)
                               Edges = model.Graph.Edges |> List.filter (fun edge -> edge.Target <> changed.Id) }
        CallableResultOriginFixture.complete [model.First; model.Fallback] (FlowOrigins.resolve graph).Calls[model.Call]
        CallableResultOriginFixture.complete [model.Fallback] (FlowOrigins.resolve model.Graph).Calls[model.Call]

    [<Theory>]
    [<InlineData("option", "mixed")>]
    [<InlineData("result", "mixed")>]
    [<InlineData("option", "opaque")>]
    [<InlineData("result", "opaque")>]
    member _.``Empty alternatives never suppress actual payloads or opaque alternatives`` (union, mode) =
        let model = CallableAbsentPayloadFixture.create union mode
        let current = FlowOrigins.resolve model.Graph
        if mode = "mixed" then
            CallableResultOriginFixture.complete [model.First; model.Fallback] current.Calls[model.Call]
            Assert.Empty current.FirstBoundaries[model.Call].UnknownOrigins
        else
            Assert.True current.Calls[model.Call].Unknown
            Assert.False current.Calls[model.Call].Complete
            Assert.Equal<Set<NodeId>>(Set.singleton model.Fallback, CallableResultOriginFixture.targets current.Calls[model.Call])
            Assert.NotEmpty current.FirstBoundaries[model.Call].UnknownOrigins

    [<Theory>]
    [<InlineData("option")>]
    [<InlineData("result")>]
    member _.``Malformed constructor projection or alias cannot mint absent payload evidence`` union =
        let model = CallableAbsentPayloadFixture.create union "absent"
        CallableResultOriginFixture.complete [model.Fallback] (FlowOrigins.resolve model.Graph).Calls[model.Call]
        let constructor, projection, reference = model.Graph.Nodes[model.Constructor], model.Graph.Nodes[model.Projection], model.Graph.Nodes[model.Reference]
        let malformedConstructor =
            match constructor.Kind with
            | SemanticKind.DUConstruct(_, tag, payload, fields) ->
                { constructor with Kind = SemanticKind.DUConstruct("wrong-case", tag, payload, fields) }
            | _ -> failwith "Expected native constructor"
        let malformedPayload =
            match constructor.Kind with
            | SemanticKind.DUConstruct(name, tag, _, fields) ->
                { constructor with Kind = SemanticKind.DUConstruct(name, tag, Some model.First, fields); Children = [model.First] }
            | _ -> failwith "Expected native constructor"
        let malformedProjection =
            { projection with Kind = SemanticKind.DUEliminate(model.Reference, model.ActiveTag, "wrong-case", projection.Type) }
        let mutations =
            [ malformedConstructor; malformedPayload; malformedProjection
              { projection with Children = [] }
              { projection with Type = NativeType.TFun(Types.unitType, Types.boolType) }
              { reference with Kind = SemanticKind.VarRef("opaque", Some model.Opaque) }
              { constructor with IsReachable = false } ]
        for changed in mutations do
            let graph = { model.Graph with Nodes = model.Graph.Nodes.Add(changed.Id, changed) }
            let current = FlowOrigins.resolve graph
            Assert.True(current.Calls[model.Call].Unknown, sprintf "Incorrect empty proof after %A" changed.Kind)
            Assert.False current.Calls[model.Call].Complete
            Assert.NotEmpty current.FirstBoundaries[model.Call].UnknownOrigins
