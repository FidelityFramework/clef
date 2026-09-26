namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module Ingress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress
module IngressOrigins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
module IngressInitialization = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization

module private CallableIngressFixture =
    type Fixture = {
        Graph: SemanticGraph
        Code: NodeId
        Binding: NodeId
        Formal: NodeId
        Alias: NodeId
        Read: NodeId
        Actuals: NodeId list
        Calls: NodeId list
        Opaque: NodeId
    }

    let create () =
        let builder = NodeBuilder()
        let callable = NativeType.TFun(Types.boolType, Types.boolType)
        let named name value =
            let argument = builder.Create(SemanticKind.PatternBinding "input", Types.boolType, dummyRange)
            let body = builder.Create(SemanticKind.Literal(NativeLiteral.Bool value), Types.boolType, dummyRange)
            let code = builder.Create(SemanticKind.Lambda(["input", Types.boolType, argument.Id], body.Id,
                                                        [], None, LambdaContext.RegularClosure), callable, dummyRange)
            let binding = builder.Create(SemanticKind.Binding(name, false, false, None), callable, dummyRange, children = [code.Id])
            builder.SetParent(code.Id, binding.Id)
            builder.Create(SemanticKind.VarRef(name, Some binding.Id), callable, dummyRange)
        let first, second = named "first" true, named "second" false
        let formal = builder.Create(SemanticKind.PatternBinding "callback", callable, dummyRange)
        let parameter = builder.Create(SemanticKind.PatternBinding "value", Types.boolType, dummyRange)
        let reference = builder.Create(SemanticKind.VarRef("callback", Some formal.Id), callable, dummyRange)
        let alias = builder.Create(SemanticKind.Binding("saved", false, false, None), callable, dummyRange, children = [reference.Id])
        let read = builder.Create(SemanticKind.VarRef("saved", Some alias.Id), callable, dummyRange)
        let body = builder.Create(SemanticKind.Application(read.Id, [parameter.Id]), Types.boolType, dummyRange)
        let spine = builder.Create(SemanticKind.Sequential [alias.Id; body.Id], Types.boolType, dummyRange)
        let higherType = NativeType.TFun(callable, NativeType.TFun(Types.boolType, Types.boolType))
        let higher = builder.Create(SemanticKind.Lambda(["callback", callable, formal.Id; "value", Types.boolType, parameter.Id], spine.Id,
                                                      [], None, LambdaContext.RegularClosure), higherType, dummyRange)
        let binding = builder.Create(SemanticKind.Binding("higher", false, false, None), higherType, dummyRange, children = [higher.Id])
        builder.SetParent(higher.Id, binding.Id)
        let call actual =
            let reference = builder.Create(SemanticKind.VarRef("higher", Some binding.Id), higherType, dummyRange)
            let value = builder.Create(SemanticKind.Literal(NativeLiteral.Bool false), Types.boolType, dummyRange)
            builder.Create(SemanticKind.Application(reference.Id, [actual; value.Id]), Types.boolType, dummyRange)
        let firstCall, secondCall = call first.Id, call second.Id
        let opaque = builder.Create(SemanticKind.PatternBinding "opaque", callable, dummyRange)
        let unit = builder.Create(SemanticKind.PatternBinding "unit", Types.unitType, dummyRange)
        let entryBody = builder.Create(SemanticKind.Sequential [firstCall.Id; secondCall.Id], Types.boolType, dummyRange)
        let entryType = NativeType.TFun(Types.unitType, Types.boolType)
        let entry = builder.Create(SemanticKind.Lambda(["unit", Types.unitType, unit.Id], entryBody.Id,
                                                     [], None, LambdaContext.RegularClosure), entryType, dummyRange)
        let main = builder.Create(SemanticKind.Binding("main", false, false, Some DeclRoot.EntryPoint), entryType, dummyRange, children = [entry.Id])
        let graph, errors = Clef.Compiler.Nanopass.ProgramInitialization.normalize [main.Id] (builder.Build [main.Id, DeclRoot.EntryPoint])
        Assert.Empty errors
        Assert.True((IngressInitialization.read graph).IsSome)
        { Graph = graph; Code = higher.Id; Binding = binding.Id; Formal = formal.Id; Alias = alias.Id; Read = read.Id
          Actuals = [first.Id; second.Id]; Calls = [firstCall.Id; secondCall.Id]; Opaque = opaque.Id }

    let changeCall fixture arguments =
        let node = fixture.Graph.Nodes[List.last fixture.Calls]
        match node.Kind with
        | SemanticKind.Application(callee, previous) ->
            let next = arguments previous
            { fixture.Graph with Nodes = fixture.Graph.Nodes.Add(node.Id, { node with Kind = SemanticKind.Application(callee, next); Children = callee :: next }) }
        | _ -> failwith "Expected fixture call"

    let denied graph fixture =
        let reading = Ingress.analyze graph
        for occurrence in [fixture.Formal; fixture.Alias; fixture.Read] do
            Assert.False(Ingress.allowsOccurrence reading occurrence, sprintf "Unexpected closed ingress at %A" occurrence)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "CallableIngress")>]
type CallableIngressCases() =
    [<Fact>]
    member _.``Closed executable ingress retains exact formal actual and call identities without forcing codata`` () =
        let fixture = CallableIngressFixture.create ()
        let graph = { fixture.Graph with Codata = lazy (failwith "Ingress forced downstream codata") }
        let reading = Ingress.analyze graph
        let initialization = IngressInitialization.read graph |> Option.get
        for occurrence in [fixture.Formal; fixture.Alias; fixture.Read] do
            let proof = Ingress.tryEvidence reading occurrence |> Option.get
            Assert.Equal(Some initialization.EntryLambda, proof.Entry)
            Assert.Contains(fixture.Formal, proof.Formals)
            Assert.Contains(fixture.Code, proof.Implementations)
            let rows = proof.Calls |> List.filter (fun row -> row.Implementation = fixture.Code) |> List.sortBy _.Site
            Assert.Equal<NodeId list>(fixture.Calls |> List.sort, rows |> List.map _.Site)
            Assert.Equal<NodeId list>(fixture.Actuals, rows |> List.map (fun row -> List.head row.Arguments))
            Assert.All(rows, fun row -> Assert.Equal(fixture.Formal, List.head row.Parameters))

    [<Fact>]
    member _.``Removing the startup proof retracts formal aliases while direct code values remain known`` () =
        let fixture = CallableIngressFixture.create ()
        Assert.True(Ingress.allowsOccurrence (Ingress.analyze fixture.Graph) fixture.Read)
        let graph = { fixture.Graph with Edges = fixture.Graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramInitialization) }
        CallableIngressFixture.denied graph fixture
        let reading = Ingress.analyze graph
        Assert.True(Ingress.allowsOccurrence reading fixture.Code)
        for actual in fixture.Actuals do Assert.True(Ingress.allowsOccurrence reading actual)
        Assert.True(Ingress.allowsOccurrence (Ingress.analyze fixture.Graph) fixture.Read)

    [<Theory>]
    [<InlineData("partial")>]
    [<InlineData("opaque")>]
    member _.``Every actual invocation must remain complete and known`` defect =
        let fixture = CallableIngressFixture.create ()
        let changed = CallableIngressFixture.changeCall fixture (fun previous ->
            if defect = "partial" then [List.head previous] else fixture.Opaque :: List.tail previous)
        CallableIngressFixture.denied changed fixture

    [<Theory>]
    [<InlineData("entry")>]
    [<InlineData("hardware")>]
    [<InlineData("kernel")>]
    [<InlineData("binding")>]
    member _.``Externally rooted higher order declarations cannot infer closed ingress from observed callers`` flavor =
        let fixture = CallableIngressFixture.create ()
        let root = match flavor with "hardware" -> DeclRoot.HardwareModule | "kernel" -> DeclRoot.KernelModule | _ -> DeclRoot.EntryPoint
        let changed =
            if flavor = "binding" then
                let node = fixture.Graph.Nodes[fixture.Binding]
                { fixture.Graph with Nodes = fixture.Graph.Nodes.Add(node.Id, { node with Kind = SemanticKind.Binding("higher", false, false, Some root) }) }
            else { fixture.Graph with DeclarationRoots = (fixture.Binding, root) :: fixture.Graph.DeclarationRoots }
        CallableIngressFixture.denied changed fixture

    [<Theory>]
    [<InlineData("mutable")>]
    [<InlineData("opaque-argument")>]
    [<InlineData("unclassified-reference")>]
    member _.``Additional escape uses retract the entire incoming proof`` defect =
        let fixture = CallableIngressFixture.create ()
        let builder = NodeBuilder()
        let higherType = fixture.Graph.Nodes[fixture.Binding].Type
        let changed =
            match defect with
            | "mutable" ->
                builder.Create(SemanticKind.Binding("escaped", true, false, None), higherType, dummyRange, children = [fixture.Binding]) |> ignore
                { fixture.Graph with Nodes = builder.Nodes |> Map.fold (fun nodes id node -> Map.add id node nodes) fixture.Graph.Nodes }
            | "opaque-argument" ->
                let external = builder.Create(SemanticKind.PatternBinding "external", NativeType.TFun(higherType, Types.unitType), dummyRange)
                builder.Create(SemanticKind.Application(external.Id, [fixture.Binding]), Types.unitType, dummyRange) |> ignore
                { fixture.Graph with Nodes = builder.Nodes |> Map.fold (fun nodes id node -> Map.add id node nodes) fixture.Graph.Nodes }
            | _ ->
                let edge = { Sources = [fixture.Binding]; Target = fixture.Opaque; Class = EdgeClass.Reference; Role = EdgeRole.Definition; Ordinal = 0 }
                { fixture.Graph with Edges = edge :: fixture.Graph.Edges }
        CallableIngressFixture.denied changed fixture

    [<Fact>]
    member _.``A known complete target does not authorize an omitted partial alternative`` () =
        let fixture = CallableIngressFixture.create ()
        let resolution = IngressOrigins.resolve fixture.Graph
        let last = List.last fixture.Calls
        let original = resolution.Calls[last]
        Assert.True original.Complete
        Assert.False original.Unknown
        let changed = { resolution with Calls = resolution.Calls.Add(last, { original with Complete = false }) }
        let reading = Ingress.analyzeWith fixture.Graph changed
        for occurrence in [fixture.Formal; fixture.Alias; fixture.Read] do Assert.False(Ingress.allowsOccurrence reading occurrence)

    [<Fact>]
    member _.``Promoted references retain their original formal ingress obligation`` () =
        let result = DimensionalCases.check """
let callback (value: bool) = value
let higher (operation: bool -> bool) (value: bool) = operation value
[<EntryPoint>]
let main _ = if higher callback true then 0 else 1
"""
        DimensionalCases.noErrors result
        let formal = result.Graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.PatternBinding "operation" -> true | _ -> false)
        let sourceDeclaration = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments.trySourceDeclaration result.Graph
        let references = result.Graph.Nodes.Values |> Seq.filter (fun node -> sourceDeclaration node.Id = Some formal.Id) |> Seq.toList
        Assert.NotEmpty references
        let reading = Ingress.analyze result.Graph
        for reference in references do Assert.True(Ingress.allowsOccurrence reading reference.Id)
        let openGraph = { result.Graph with Edges = result.Graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramInitialization) }
        let openReading = Ingress.analyze openGraph
        for reference in references do Assert.False(Ingress.allowsOccurrence openReading reference.Id)
        let malformedEdges = result.Graph.Edges |> List.map (fun edge ->
            if edge.Role = EdgeRole.CallableReferenceOrigin && references |> List.exists (fun reference -> reference.Id = edge.Target)
            then { edge with Sources = [formal.Id] } else edge)
        let malformed = { result.Graph with Edges = malformedEdges }
        let malformedReading = Ingress.analyze malformed
        for reference in references do Assert.False(Ingress.allowsOccurrence malformedReading reference.Id)

    [<Fact>]
    member _.``Returned callable captures keep both factory inputs and their closed invocation chain`` () =
        let result = DimensionalCases.check """
let yes (_: bool) = true
let no (_: bool) = false
let compose (f: bool -> bool) (g: bool -> bool) = fun value -> g (f value)
[<EntryPoint>]
let main _ =
    let first = compose yes no
    let second = compose no yes
    if first true || second false then 0 else 1
"""
        DimensionalCases.noErrors result
        let graph = result.Graph
        let formals = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.PatternBinding "f" | SemanticKind.PatternBinding "g" -> true | _ -> false) |> Seq.toList
        Assert.Equal(2, formals.Length)
        let resolution = IngressOrigins.resolve graph
        let reading = Ingress.analyzeWith graph resolution
        for formal in formals do
            let proof = Ingress.tryEvidence reading formal.Id |> Option.get
            let supplied = resolution.ParameterInputs[formal.Id]
            Assert.Equal(2, supplied.Length)
            for site, actual in supplied do
                Assert.Contains(proof.Calls, fun call -> call.Site = site && List.contains actual call.Arguments)
            Assert.Contains(formal.Id, proof.Formals)
        let openGraph = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramInitialization) }
        let openReading = Ingress.analyze openGraph
        for formal in formals do Assert.False(Ingress.allowsOccurrence openReading formal.Id)
