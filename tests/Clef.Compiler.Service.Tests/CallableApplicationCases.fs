namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module StagedEnvironments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments

module private CallableApplication =
    let check source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        result.Graph

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Binding (actual, _, _, _) -> actual = name || actual.EndsWith("." + name)
            | _ -> false)

    // Follow value-preserving wrappers, without crossing an application boundary.
    let rec value (graph: SemanticGraph) id =
        let node = graph.Nodes[id]
        match node.Kind with
        | SemanticKind.Binding _ -> value graph (List.last node.Children)
        | SemanticKind.TypeAnnotation (inner, _) -> value graph inner
        | SemanticKind.Sequential nodes -> value graph (List.last nodes)
        | _ -> node

    let sameType expected actual =
        let actual = applySubst actual
        Assert.False(hasUnboundVars actual, formatType actual)
        Assert.Equal(formatType expected, formatType actual)

    let option payload = NativeType.TApp(Types.optionTyCon, [payload])

    let lambda (graph: SemanticGraph) (binding: SemanticNode) =
        let node = value graph binding.Id
        let code, parameters, body, _ = CallableTestContracts.shape graph node.Id
        code, parameters, body

    // Assert two actual calls, with the first call's function result as the
    // second callee. A matching final source type alone cannot establish this.
    let stages (graph: SemanticGraph) root firstResult finalResult =
        let outer = value graph root
        match outer.Kind with
        | SemanticKind.Application (intermediate, finalArguments) ->
            let intermediate, finalArguments =
                match StagedEnvironments.callEnvironments graph |> Map.tryFind outer.Id with
                | Some(ordinal, environment) ->
                    Assert.Equal(environment, finalArguments[ordinal])
                    let source =
                        match graph.Nodes[environment].Kind with
                        | SemanticKind.EnvironmentReference source -> source
                        | kind -> failwithf "A staged captured call lost its actual result environment: %A" kind
                    let carrier = StagedEnvironments.tryKnown graph source |> Option.get
                    Assert.Equal(Some carrier.Implementation, StagedEnvironments.tryImplementation graph intermediate)
                    source, finalArguments |> List.indexed |> List.choose (fun (index, argument) -> if index = ordinal then None else Some argument)
                | None -> intermediate, finalArguments
            let finalArgument = Assert.Single finalArguments
            sameType finalResult outer.Type
            let inner = value graph intermediate
            match inner.Kind with
            | SemanticKind.Application (original, initialArguments) ->
                let initialArgument = Assert.Single initialArguments
                sameType firstResult inner.Type
                outer, inner, original, initialArgument, finalArgument
            | kind -> failwithf "The returned function is not produced by a separate call: %A" kind
        | kind -> failwithf "Expected application of the returned function, got %A" kind

    let referenceTo (graph: SemanticGraph) expected id =
        CallableTestContracts.referenceTo graph expected (value graph id).Id

    let namedCall (graph: SemanticGraph) expected id =
        match (value graph id).Kind with
        | SemanticKind.Application (callee, _) ->
            match (value graph callee).Kind with
            | SemanticKind.VarRef (name, _) ->
                Assert.True(name = expected || name.EndsWith("." + expected), name)
            | kind -> failwithf "Expected call to %s, got callee %A" expected kind
        | kind -> failwithf "Expected call to %s, got %A" expected kind

/// expressions.md:2897–2908 distinguishes actual parameters from arguments to a
/// returned function; C-01 §14.3 requires matching definitions/calls/returns.
/// These source-level gates inspect those relationships after ordinary checking,
/// independently of the implementation pass or its private provenance analysis.
[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "CallableApplications")>]
type CallableApplicationTests() =
    [<Fact>]
    member _.``A bare Option operation calls its returned closure at a separate boundary``() =
        let graph = CallableApplication.check """
let map: (int -> bool) -> int option -> bool option = Option.map
let observed = map (fun value -> value > 0) (Some 7)
[<EntryPoint>]
let main _ = if Option.get observed then 0 else 1
"""
        let map = CallableApplication.binding "map" graph
        let _, parameters, body = CallableApplication.lambda graph map
        Assert.Single parameters |> ignore
        let residual = NativeType.TFun(CallableApplication.option Types.intType, CallableApplication.option Types.boolType)
        CallableApplication.sameType residual graph.Nodes[body].Type
        let observed = CallableApplication.binding "observed" graph
        let _, _, original, _, _ =
            CallableApplication.stages graph observed.Id residual (CallableApplication.option Types.boolType)
        CallableApplication.referenceTo graph map.Id original

    [<Fact>]
    member _.``A generic higher order parameter preserves the supplied callable boundary``() =
        let graph = CallableApplication.check """
let invoke2 (work: 'a -> 'b -> 'c) (first: 'a) (second: 'b) : 'c = work first second
let map: (int -> bool) -> int option -> bool option = Option.map
let observed = invoke2 map (fun value -> value > 0) (Some 7)
[<EntryPoint>]
let main _ = if Option.get observed then 0 else 1
"""
        let helper = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Binding (name, _, _, _) -> name.StartsWith("invoke2__mono")
            | _ -> false) |> Assert.Single
        let _, parameters, body = CallableApplication.lambda graph helper
        Assert.Equal(3, parameters.Length)
        let _, _, work = parameters[0]
        let _, _, first = parameters[1]
        let _, _, second = parameters[2]
        let residual = NativeType.TFun(CallableApplication.option Types.intType, CallableApplication.option Types.boolType)
        let _, _, original, firstArgument, secondArgument =
            CallableApplication.stages graph body residual (CallableApplication.option Types.boolType)
        CallableApplication.referenceTo graph work original
        CallableApplication.referenceTo graph first firstArgument
        CallableApplication.referenceTo graph second secondArgument

    [<Fact>]
    member _.``Explicit get of a function consumes one option before invoking its payload``() =
        let graph = CallableApplication.check """
let get = Option.get<(int -> int)>
let work: int -> int = fun value -> value + 2
let observed = get (Some work) 3
[<EntryPoint>]
let main _ = if observed = 5 then 0 else 1
"""
        let payload = NativeType.TFun(Types.intType, Types.intType)
        let get = CallableApplication.binding "get" graph
        let _, parameters, body = CallableApplication.lambda graph get
        let _, parameterType, _ = Assert.Single parameters
        CallableApplication.sameType (CallableApplication.option payload) parameterType
        CallableApplication.sameType payload graph.Nodes[body].Type
        let observed = CallableApplication.binding "observed" graph
        let _, _, original, optionArgument, payloadArgument =
            CallableApplication.stages graph observed.Id payload Types.intType
        CallableApplication.referenceTo graph get.Id original
        CallableApplication.sameType (CallableApplication.option payload) graph.Nodes[optionArgument].Type
        CallableApplication.sameType Types.intType graph.Nodes[payloadArgument].Type

    [<Fact>]
    member _.``Staged calls preserve each original supplied computation and the returned callable identity``() =
        let graph = CallableApplication.check """
let mutable trace: int = 0
let makeMapper () : int -> bool =
    trace <- trace * 10 + 1
    fun value -> value > 0
let makeOption () : int option =
    trace <- trace * 10 + 2
    Some 7
let map: (int -> bool) -> int option -> bool option = Option.map
let observed = map (makeMapper ()) (makeOption ())
[<EntryPoint>]
let main _ = if Option.get observed && trace = 12 then 0 else 1
"""
        let observed = CallableApplication.binding "observed" graph
        let root = graph.Nodes[List.last observed.Children]
        let residual = NativeType.TFun(CallableApplication.option Types.intType, CallableApplication.option Types.boolType)
        let outer, inner, original, mapperArgument, optionArgument =
            CallableApplication.stages graph root.Id residual (CallableApplication.option Types.boolType)
        Assert.Equal(outer.Id, root.Id)
        Assert.Equal<NodeId list>([original; mapperArgument], inner.Children)
        match outer.Kind, StagedEnvironments.callEnvironments graph |> Map.tryFind outer.Id with
        | SemanticKind.Application(code, arguments), Some(ordinal, environment) ->
            Assert.Equal<NodeId list>(code :: arguments, outer.Children)
            Assert.Equal(environment, arguments[ordinal])
            Assert.Equal(SemanticKind.EnvironmentReference inner.Id, graph.Nodes[environment].Kind)
            Assert.Equal<NodeId list>([inner.Id], graph.Nodes[environment].Children)
            let known = StagedEnvironments.tryKnown graph inner.Id |> Option.get
            Assert.Equal(Some known.Implementation, StagedEnvironments.tryImplementation graph code)
            Assert.Equal<NodeId list>([optionArgument], arguments |> List.indexed |> List.choose (fun (index, value) -> if index = ordinal then None else Some value))
        | SemanticKind.Application _, None -> Assert.Equal<NodeId list>([inner.Id; optionArgument], outer.Children)
        | _ -> failwith "The returned callable must retain its actual call and source result environment"
        CallableApplication.referenceTo graph (CallableApplication.binding "map" graph).Id original
        for name, argument in ["makeMapper", mapperArgument; "makeOption", optionArgument] do
            CallableApplication.namedCall graph name argument
            let declaration = CallableApplication.binding name graph
            let calls = graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable &&
                match node.Kind with
                | SemanticKind.Application(callee, _) ->
                    match graph.Nodes[callee].Kind with
                    | SemanticKind.VarRef(_, Some target) -> target = declaration.Id
                    | _ -> false
                | _ -> false) |> Seq.toList
            Assert.Equal(argument, (Assert.Single calls).Id)
        // Ordinary arguments retain shared computation identities. This gate
        // does not authorize forcing them before either application boundary;
        // the owning default-demand/explicit-eager gates establish demand.
        Assert.DoesNotContain(graph.Nodes.Values, fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Sequential ids -> List.contains mapperArgument ids || List.contains optionArgument ids
            | _ -> false)

    [<Fact>]
    member _.``Eager actuals to a returned callable cannot precede formation of that callable``() =
        let graph = CallableApplication.check """
let mutable trace: int = 0
let mark value = trace <- trace * 10 + value; value
let make first =
    trace <- trace * 10 + 2
    fun second -> first + second
[<EntryPoint>]
let main _ = make (eager (mark 1)) (eager (mark 3))
"""
        let entry = CallableApplication.binding "main" graph
        let _, _, body = CallableApplication.lambda graph entry
        let outer, inner, _, first, second =
            CallableApplication.stages graph body (NativeType.TFun(Types.intType, Types.intType)) Types.intType
        let demand owner =
            graph.Edges
            |> List.filter (fun edge ->
                edge.Target = owner && edge.Class = EdgeClass.Demand && edge.Role = EdgeRole.EagerDemand EagerFrontier.Actual)
            |> Assert.Single
        let firstDemand, secondDemand = demand inner.Id, demand outer.Id
        Assert.Equal(first, firstDemand.Sources.Head)
        Assert.Equal(second, secondDemand.Sources.Head)
        Assert.Equal(inner.Id, List.last secondDemand.Sources)
        Assert.Equal(0, secondDemand.Ordinal)
        let environmentOrdinal, environment = StagedEnvironments.callEnvironments graph |> Map.find outer.Id
        let physicalCallee, physicalArguments =
            match outer.Kind with SemanticKind.Application(callee, arguments) -> callee, arguments | _ -> failwith "Expected settled outer call"
        Assert.Equal(environment, physicalArguments[environmentOrdinal])
        Assert.Equal(SemanticKind.EnvironmentReference inner.Id, graph.Nodes[environment].Kind)
        let known = StagedEnvironments.tryKnown graph inner.Id |> Option.get
        let convention =
            graph.Edges |> List.filter (fun edge ->
                edge.Role = EdgeRole.EnvironmentFormal && edge.Sources = [known.EnvironmentOwner; known.Implementation]) |> Assert.Single
        for participant in [physicalCallee; environment; inner.Id; known.EnvironmentOwner; convention.Target] do
            Assert.Contains(participant, secondDemand.Sources)
        Assert.DoesNotContain(second, firstDemand.Sources)
        Assert.DoesNotContain(graph.Nodes.Values, fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Sequential ids -> List.contains first ids || List.contains second ids
            | _ -> false)
        for defect in ["missing-convention"; "environment-type"; "environment-incidence"; "environment-origin"] do
            let changed =
                match defect with
                | "missing-convention" ->
                    let edges =
                        graph.Edges |> List.filter (fun edge ->
                            not (edge.Role = EdgeRole.EnvironmentFormal && edge.Target = convention.Target))
                    { graph with Edges = edges }
                | _ ->
                    let current = graph.Nodes[environment]
                    let changed =
                        match defect with
                        | "environment-type" -> { current with Type = Types.boolType }
                        | "environment-incidence" -> { current with Children = [] }
                        | _ -> { current with Kind = SemanticKind.EnvironmentReference physicalCallee; Children = [physicalCallee] }
                    { graph with Nodes = graph.Nodes.Add(environment, changed) }
            let refreshed = Clef.Compiler.Nanopass.EagerDemand.normalize changed
            Assert.DoesNotContain(refreshed.Edges, fun edge ->
                edge.Target = outer.Id && edge.Role = EdgeRole.EagerDemand EagerFrontier.Actual)
            Assert.Contains(refreshed.Edges, fun edge -> edge.Target = outer.Id && edge.Role = EdgeRole.EagerDemandPending)

    [<Theory>]
    [<InlineData("option", "Some staged", "Option.get chosen")>]
    [<InlineData("record", "{ Work = staged }", "chosen.Work")>]
    [<InlineData("tuple", "(staged, 0)", "fst chosen")>]
    member _.``An opaque aggregate alternative prevents guessing its callable boundary``(carrier: string, aggregate: string, projection: string) =
        // Indexing has no resident aggregate origin in this analysis. Joining
        // that value with a known constructor must retain the unknown path.
        let template = """
type Holder = { Work: int -> int -> int }
let staged (first: int) : int -> int = fun second -> first + second
let stored = [| AGGREGATE |]
let opaque = stored.[0]
let chosen = if true then AGGREGATE else opaque
let work = PROJECTION
let observed = work 3 4
[<EntryPoint>]
let main _ = if observed = 7 then 0 else 1
"""
        let source = template.Replace("AGGREGATE", aggregate).Replace("PROJECTION", projection)
        let graph = CallableApplication.check source
        let opaque = CallableApplication.binding "opaque" graph
        match (CallableApplication.value graph opaque.Id).Kind with
        | SemanticKind.IndexGet _ -> ()
        | kind -> failwithf "Expected an opaque indexed %s, got %A" carrier kind
        let chosen = CallableApplication.binding "chosen" graph
        match (CallableApplication.value graph chosen.Id).Kind with
        | SemanticKind.IfThenElse (_, _, Some alternative) ->
            CallableApplication.referenceTo graph opaque.Id alternative
        | kind -> failwithf "Expected both %s alternatives to remain resident, got %A" carrier kind
        let work = CallableApplication.binding "work" graph
        let observed = CallableApplication.binding "observed" graph
        match (CallableApplication.value graph observed.Id).Kind with
        | SemanticKind.Application (callee, arguments) ->
            CallableApplication.referenceTo graph work.Id callee
            Assert.Equal(2, arguments.Length)
            CallableApplication.sameType Types.intType graph.Nodes[observed.Id].Type
        | kind -> failwithf "An opaque %s cannot establish a staged callable boundary: %A" carrier kind

    [<Fact>]
    member _.``An immutable callable alias range excludes unrelated compatible functions``() =
        let graph = CallableApplication.check """
[<EntryPoint>]
let main _ =
    let increment = fun value -> value + 1
    let unrelated = fun value -> value + 1000
    let selected = increment
    let observed = selected 7
    let other = unrelated 3000
    ignore other
    observed
"""
        Assert.Equal(Some(ValueRange.point 8I), (CallableApplication.binding "observed" graph).ValueRange)
        Assert.Equal(Some(ValueRange.point 4000I), (CallableApplication.binding "other" graph).ValueRange)

    [<Fact>]
    member _.``Returned callable supplies retain both actual parameter frontiers``() =
        let graph = CallableApplication.check """
let make initial = fun increment -> initial + increment
[<EntryPoint>]
let main _ =
    let next = make 7
    let observed = next 300
    observed
"""
        Assert.Equal(Some(ValueRange.point 307I), (CallableApplication.binding "observed" graph).ValueRange)

    [<Fact>]
    member _.``A known callable beside an opaque input cannot establish a bounded result``() =
        let graph = CallableApplication.check """
let consume (opaque: int -> int) flag =
    let selected = if flag then opaque else (fun value -> value + 1)
    let observed = selected 7
    observed
[<EntryPoint>]
let main _ = ignore consume; 0
"""
        Assert.Equal(Some ValueRange.Unbounded, (CallableApplication.binding "observed" graph).ValueRange)
