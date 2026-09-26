namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module FlowCarriers = Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers
module FlowOrigins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
module Flows = Clef.Compiler.PSGSaturation.SemanticGraph.CallableFlows

module private CallableFlowFixture =
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
