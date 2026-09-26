namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

module private RecursiveInstances =
    let check body = LazyResidenceFixture.programWith (Some("module RecursiveInstances\n" + body))

    let declarations (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(_, false, true, _) -> true | _ -> false) |> Seq.toList

    let assertReferences (graph: SemanticGraph) =
        for node in graph.Nodes.Values do
            for child in node.Children do Assert.True(graph.Nodes.ContainsKey child, $"Missing child {child} of {node.Id}")
            match node.Kind with
            | SemanticKind.VarRef(_, Some target) -> Assert.True(graph.Nodes.ContainsKey target, $"Missing definition {target} of {node.Id}")
            | SemanticKind.ModuleDef(_, members) ->
                for memberId in members do Assert.True(graph.Nodes.ContainsKey memberId)
            | _ -> ()

    let code (graph: SemanticGraph) (declaration: SemanticNode) =
        match graph.Nodes[Assert.Single declaration.Children].Kind with
        | SemanticKind.Lambda(parameters, body, _, _, _) -> parameters, body
        | kind -> failwithf "Expected recursive code, got %A" kind

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "RecursiveInstantiations")>]
type RecursiveInstantiationCases() =
    [<Fact>]
    member _.``Nested recursive accumulator specializes its complete declaration and self references``() =
        let graph = RecursiveInstances.check """let fibonacciTail (n: int) : int =
    let rec loop a b count =
        if count <= 0 then a else loop b (a + b) (count - 1)
    loop 0 1 n
[<EntryPoint>]
let main _ = fibonacciTail 10
"""
        RecursiveInstances.assertReferences graph
        let declaration = RecursiveInstances.declarations graph |> Assert.Single
        Assert.False(hasUnboundVars declaration.Type)
        let parameters, body = RecursiveInstances.code graph declaration
        Assert.Equal(3, parameters.Length)
        for _, ty, id in parameters do
            Assert.Equal(Types.intType, applySubst ty)
            Assert.Equal(applySubst ty, applySubst graph.Nodes[id].Type)
        Assert.Equal(Types.intType, applySubst graph.Nodes[body].Type)
        Assert.Contains(graph.Nodes.Values, fun node ->
            match node.Kind with
            | SemanticKind.Sequential values -> values |> List.contains declaration.Id
            | _ -> false)
        let calls = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.VarRef("loop", Some target) -> target = declaration.Id | _ -> false) |> Seq.toList
        Assert.Equal(2, calls.Length)
        for call in calls do Assert.Equal(applySubst declaration.Type, applySubst call.Type)

    [<Fact>]
    member _.``Mutual recursive instances retain all peer declarations at each inferred native type``() =
        let graph = RecursiveInstances.check """let rec keep n value = if n = 0 then value else again (n - 1) value
and again n value = keep n value
[<EntryPoint>]
let main _ =
    let number = keep 2 7
    let enabled = keep 3 true
    if enabled then number else 0
"""
        RecursiveInstances.assertReferences graph
        let declarations = RecursiveInstances.declarations graph
        Assert.Equal(4, declarations.Length)
        let results = declarations |> List.map (fun declaration ->
            let _, body = RecursiveInstances.code graph declaration
            Assert.False(hasUnboundVars declaration.Type)
            applySubst graph.Nodes[body].Type)
        Assert.Equal(2, results |> List.filter ((=) Types.intType) |> List.length)
        Assert.Equal(2, results |> List.filter ((=) Types.boolType) |> List.length)
        for declaration in declarations do
            let uses = graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && match node.Kind with SemanticKind.VarRef(_, Some target) -> target = declaration.Id | _ -> false) |> Seq.toList
            Assert.NotEmpty uses
            for useSite in uses do Assert.Equal(applySubst declaration.Type, applySubst useSite.Type)

    [<Fact>]
    member _.``Recursive generic calls infer distinct compound dimensions without changing their result types``() =
        let graph = RecursiveInstances.check """[<Measure>] type m
[<Measure>] type s
let rec keep n value = if n = 0 then value else keep (n - 1) value
[<EntryPoint>]
let main _ =
    let velocity = keep 2 7<m/s>
    let inverse = keep 3 11<s/m>
    if velocity = 7<m/s> && inverse = 11<s/m> then 0 else 1
"""
        RecursiveInstances.assertReferences graph
        let declarations = RecursiveInstances.declarations graph
        Assert.Equal(2, declarations.Length)
        let results = declarations |> List.map (fun declaration ->
            let _, body = RecursiveInstances.code graph declaration
            Assert.False(hasUnboundVars declaration.Type)
            Assert.Empty(freeMeasureVars declaration.Type)
            applySubst graph.Nodes[body].Type)
        Assert.NotEqual(results[0], results[1])
        for declaration in declarations do
            let calls = graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && match node.Kind with SemanticKind.VarRef("keep", Some target) -> target = declaration.Id | _ -> false) |> Seq.toList
            Assert.Equal(2, calls.Length)
            for call in calls do Assert.Equal(applySubst declaration.Type, applySubst call.Type)
