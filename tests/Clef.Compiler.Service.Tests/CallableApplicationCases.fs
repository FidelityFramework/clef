namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

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
        match node.Kind with
        | SemanticKind.Lambda (parameters, body, _, _, _) -> node, parameters, body
        | kind -> failwithf "Expected a resident lambda, got %A" kind

    // Assert two actual calls, with the first call's function result as the
    // second callee. A matching final source type alone cannot establish this.
    let stages (graph: SemanticGraph) root firstResult finalResult =
        let outer = value graph root
        match outer.Kind with
        | SemanticKind.Application (intermediate, finalArguments) ->
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
        match (value graph id).Kind with
        | SemanticKind.VarRef (_, Some definition) -> Assert.Equal(expected, definition)
        | kind -> failwithf "Expected a reference to resident binding %A, got %A" expected kind

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
    member _.``Supplied expressions are evaluated in order before either staged call``() =
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
        match root.Kind with
        | SemanticKind.Sequential ordered ->
            Assert.Equal(outer.Id, List.last ordered)
            let prefix = ordered |> List.take (ordered.Length - 1)
            let mapperPosition = prefix |> List.findIndex ((=) mapperArgument)
            let optionPosition = prefix |> List.findIndex ((=) optionArgument)
            Assert.True(mapperPosition < optionPosition, "Supplied expressions changed order")
            Assert.Equal(1, prefix |> List.filter ((=) mapperArgument) |> List.length)
            Assert.Equal(1, prefix |> List.filter ((=) optionArgument) |> List.length)
            Assert.DoesNotContain(inner.Id, prefix)
            Assert.True(prefix |> List.contains original, "The callee must be evaluated before application")
            CallableApplication.namedCall graph "makeMapper" mapperArgument
            CallableApplication.namedCall graph "makeOption" optionArgument
        | kind -> failwithf "The staged calls have no eager supplied-expression prefix: %A" kind

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
