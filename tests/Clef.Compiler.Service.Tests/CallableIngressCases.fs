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
    member _.``Source shape readers share complete formal ingress with retained participants`` () =
        let fixture = CallableIngressFixture.create ()
        let resolution = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve fixture.Graph
        let reading = Ingress.analyzeWith fixture.Graph resolution
        let ingress = Ingress.closedFormalInputs fixture.Graph resolution reading fixture.Formal |> Option.get
        Assert.Equal<(NodeId * NodeId) list>(resolution.ParameterInputs[fixture.Formal],ingress.Inputs)
        Assert.Contains(fixture.Formal,ingress.Participants)
        Assert.True(Set.isSubset ingress.Closure.Participants ingress.Participants)
        for site, actual in ingress.Inputs do
            Assert.Contains(site,ingress.Participants)
            Assert.Contains(actual,ingress.Participants)

    [<Theory>]
    [<InlineData("entry")>]
    [<InlineData("hardware")>]
    [<InlineData("kernel")>]
    member _.``A retained actual argument census cannot authorize externally rooted formal shapes`` flavor =
        let fixture = CallableIngressFixture.create ()
        let root = match flavor with "hardware" -> DeclRoot.HardwareModule | "kernel" -> DeclRoot.KernelModule | _ -> DeclRoot.EntryPoint
        let graph = { fixture.Graph with DeclarationRoots = (fixture.Binding,root) :: fixture.Graph.DeclarationRoots }
        let resolution = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
        Assert.NotEmpty resolution.ParameterInputs[fixture.Formal]
        let reading = Ingress.analyzeWith graph resolution
        Assert.True((Ingress.closedFormalInputs graph resolution reading fixture.Formal).IsNone)

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

module private LazyIngressFixture =
    let create () =
        let result = DimensionalCases.check """
let observe (value: bool) = value
[<EntryPoint>]
let main _ =
    let left = lazy (observe false)
    let right = lazy (observe true)
    let alias = left
    let first = Lazy.force alias
    let second = Lazy.force right
    let repeated = Lazy.force left
    if first || repeated then 1 elif second then 0 else 1
"""
        DimensionalCases.noErrors result
        let graph = result.Graph
        let formal = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && node.Kind = SemanticKind.PatternBinding "value") |> Assert.Single
        graph, formal.Id

    let inputs graph formal =
        let resolution = IngressOrigins.resolve graph
        Ingress.closedFormalInputs graph resolution (Ingress.analyzeWith graph resolution) formal

    let admitted graph formal =
        let inputs = inputs graph formal |> Option.defaultWith (fun () -> failwith "Lazy thunk callers have no closed formal ingress")
        Assert.Equal(2, inputs.Inputs.Length)
        inputs

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "CallableIngress")>]
type LazyCallableIngressCases() =
    [<Fact>]
    member _.``Lazy thunk ingress retains both actuals and the complete formation and force participants`` () =
        let graph, formal = LazyIngressFixture.create ()
        let graph = { graph with Codata = lazy (failwith "Source ingress must not force downstream codata") }
        let inputs = LazyIngressFixture.admitted graph formal
        let rows = graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.LazyInstance || edge.Role = EdgeRole.LazyMemoization)
        Assert.Equal(5, rows.Length)
        for row in rows do
            for participant in row.Target :: row.Sources do Assert.Contains(participant, inputs.Participants)
        let values = inputs.Inputs |> List.map (fun (_, actual) ->
            match graph.Nodes[actual].Kind with SemanticKind.Literal(NativeLiteral.Bool value) -> value | _ -> failwith "Expected exact Boolean actual") |> Set.ofList
        Assert.Equal<Set<bool>>(Set.ofList [false; true], values)

    [<Theory>]
    [<InlineData("missing-instance")>]
    [<InlineData("duplicate-instance")>]
    [<InlineData("missing-force")>]
    [<InlineData("force-order")>]
    [<InlineData("formation-children")>]
    [<InlineData("extra-reference")>]
    [<InlineData("extra-invocation")>]
    [<InlineData("escaping-descriptor")>]
    member _.``Lazy thunk ingress refuses incomplete protocols and unexplained uses`` defect =
        let graph, formal = LazyIngressFixture.create ()
        LazyIngressFixture.admitted graph formal |> ignore

        let settlement = Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues.settle graph
        Assert.Empty settlement.Residuals
        let force = settlement.Forces.Values |> Seq.head
        let instance = settlement.Instances[force.Formation]
        let row = graph.Edges |> List.find (fun edge -> edge.Role = EdgeRole.LazyInstance && edge.Target = instance.Formation)
        let changed =
            match defect with
            | "missing-instance" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.LazyInstance || edge.Target <> instance.Formation) }
            | "duplicate-instance" -> { graph with Edges = row :: graph.Edges }
            | "missing-force" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.LazyMemoization || edge.Target <> force.Site) }
            | "force-order" ->
                let branch = graph.Nodes[force.UncachedBranch]
                let actions = [force.ResultBinding; force.Publication; force.ResultStore; List.last branch.Children]
                { graph with Nodes = graph.Nodes.Add(branch.Id, { branch with Kind = SemanticKind.Sequential actions; Children = actions }) }
            | "formation-children" ->
                let formation = graph.Nodes[instance.Formation]
                { graph with Nodes = graph.Nodes.Add(formation.Id, { formation with Children = [] }) }
            | "extra-reference" ->
                let edge = { Sources = [instance.Thunk]; Target = formal; Class = EdgeClass.Reference; Role = EdgeRole.Definition; Ordinal = 0 }
                { graph with Edges = edge :: graph.Edges }
            | "escaping-descriptor" ->
                let builder = NodeBuilder()
                let descriptor = graph.Nodes[instance.Formation]
                let consumer = builder.Create(SemanticKind.PatternBinding "unknown_consumer", NativeType.TFun(descriptor.Type, Types.unitType), dummyRange)
                let call = builder.Create(SemanticKind.Application(consumer.Id, [descriptor.Id]), Types.unitType, dummyRange)
                let initialization = IngressInitialization.read graph |> Option.get
                let body = graph.Nodes[initialization.OriginalBody]
                let actions = match body.Kind with SemanticKind.Sequential actions -> call.Id :: actions | _ -> failwith "Missing source entry sequence"
                let nodes = builder.Nodes |> Map.fold (fun nodes id node -> Map.add id node nodes) graph.Nodes
                { graph with Nodes = nodes.Add(body.Id, { body with Kind = SemanticKind.Sequential actions; Children = actions }) }
            | _ ->
                // The extra invocation is live in the entry body and uses the
                // very same known thunk and argument as an admitted force.
                let invocation = graph.Nodes[force.Invocation]
                let id = NodeId.fresh()
                let initialization = IngressInitialization.read graph |> Option.get
                let body = graph.Nodes[initialization.OriginalBody]
                let actions = match body.Kind with SemanticKind.Sequential actions -> id :: actions | _ -> failwith "Missing source entry sequence"
                { graph with Nodes = graph.Nodes.Add(id, { invocation with Id = id }).Add(body.Id, { body with Kind = SemanticKind.Sequential actions; Children = actions }) }
        Assert.True((IngressInitialization.read changed).IsSome, "The mutation must preserve startup authority")
        if defect = "extra-invocation" then
            Assert.Empty((Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues.settle changed).Residuals)
            Assert.True((IngressOrigins.resolve changed).Calls.Count > (IngressOrigins.resolve graph).Calls.Count)
        if defect = "escaping-descriptor" then
            Assert.Empty((Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues.settle changed).Residuals)
        Assert.True((LazyIngressFixture.inputs changed formal).IsNone, defect)
        LazyIngressFixture.admitted graph formal |> ignore

    [<Fact>]
    member _.``Array extent admission requires its own lazy protocol freshness authority`` () =
        for deferred in [false; true] do
            let body =
                if deferred then "    let delayed = lazy (length [| true; false |])\n    if Lazy.force delayed = 2 then 0 else 1\n"
                else "    if length [| true; false |] = 2 then 0 else 1\n"
            let result = DimensionalCases.check ("let length (values: bool array) = values.Length\n[<EntryPoint>]\nlet main _ =\n" + body)
            let graph = result.Graph
            let formal = graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && node.Kind = SemanticKind.PatternBinding "values") |> Assert.Single
            let resolution = IngressOrigins.resolve graph
            let inputs = Clef.Compiler.Baker.Ingredients.FormalDemand.reader graph resolution formal.Id |> Option.get
            let extent = Clef.Compiler.Baker.Ingredients.ArrayShapes.reader graph formal.Id
            if deferred then
                Assert.NotEmpty inputs.UsedLazyForces
                Assert.True(extent.IsNone, "An owner without lazy relation freshness must not retain this newly closed extent")
            else
                DimensionalCases.noErrors result
                Assert.Empty inputs.UsedLazyForces
                let extent = extent |> Option.get
                Assert.Equal<Clef.Compiler.Baker.Ingredients.ArrayShapes.Length list>([Clef.Compiler.Baker.Ingredients.ArrayShapes.Length.Constant 2I], extent.Sources)
