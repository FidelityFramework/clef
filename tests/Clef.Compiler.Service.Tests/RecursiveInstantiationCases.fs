namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module TailSourceRanges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis

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

    let tailSource seedA seedB count guard step =
        "module RecursiveInstances\nlet fibonacciTail (n: int) : int =\n" +
        "    let rec loop a b count =\n" +
        "        if " + guard + " then a else loop b (a + b) (count " + step + ")\n" +
        sprintf "    loop %d %d n\n[<EntryPoint>]\nlet main _ = if fibonacciTail %s >= 0 then 0 else 1\n" seedA seedB count

    let certificates (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Obligation { Id = name; Body = ObligationBody.FiniteLinearRecurrence model } when name.StartsWith("tail_linear_") -> Some model
            | _ -> None) |> Seq.toList

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "RecursiveInstantiations")>]
type RecursiveInstantiationCases() =
    [<Theory>]
    [<InlineData(0, 1, 10, 55, 89)>]
    [<InlineData(1, 1, 9, 55, 89)>]
    [<InlineData(1, 2, 8, 55, 89)>]
    member _.``Closed tail entry tuples certify simultaneous Fibonacci parameters``(a: int, b: int, count: int, upperA: int, upperB: int) =
        let source = RecursiveInstances.tailSource a b (string count) "count <= 0" "- 1"
        let result = LazyResidenceFixture.checkProgramWithCapacity 1024 (Some source)
        DimensionalCases.noErrors result
        let models = RecursiveInstances.certificates result.Graph
        Assert.Contains(models, fun model ->
            model.InitialUpper = [bigint a; bigint b] && model.MaximumIterations = bigint count &&
            model.CoefficientUpper = [[0I; 1I]; [1I; 1I]] && model.Upper = [bigint upperA; bigint upperB])

    [<Fact>]
    member _.``Zero tail trips retain the initial value without inventing a transition``() =
        let source = RecursiveInstances.tailSource 0 1 "0" "count <= 0" "- 1"
        let result = LazyResidenceFixture.checkProgramWithCapacity 1024 (Some source)
        DimensionalCases.noErrors result
        let inactive = TailSourceRanges.tailInactiveOccurrences result.Graph
        Assert.NotEmpty inactive
        for node in result.Graph.Nodes.Values do
            match node.Kind with
            | SemanticKind.Lambda(parameters, _, _, _, _) ->
                for _, _, formal in parameters do Assert.DoesNotContain(formal, inactive)
            | _ -> ()
        for model in RecursiveInstances.certificates result.Graph do
            Assert.Equal(0I, model.MaximumIterations)
            Assert.Equal<bigint list>([0I; 1I], model.Upper)

    [<Theory>]
    [<InlineData("absent")>]
    [<InlineData("stale")>]
    member _.``Zero tail inactivity requires the current complete numeric producer receipt`` defect =
        let source = RecursiveInstances.tailSource 0 1 "0" "count <= 0" "- 1"
        let result = LazyResidenceFixture.checkProgramWithCapacity 1024 (Some source)
        DimensionalCases.noErrors result
        Assert.NotEmpty(TailSourceRanges.tailInactiveOccurrences result.Graph)
        let facts = result.Graph.RangeContextFacts |> Option.get
        let changed =
            match defect with
            | "absent" -> { result.Graph with RangeContextFacts = None }
            | _ -> { result.Graph with RangeContextFacts = Some { facts with Premises = Map.empty } }
        Assert.Empty(TailSourceRanges.tailInactiveOccurrences changed)

    [<Fact>]
    member _.``A live tail entry keeps the shared continuing call and ABI roles committed``() =
        let source = (RecursiveInstances.tailSource 0 1 "10" "count <= 0" "- 1")
                        .Replace("fibonacciTail 10 >= 0", "fibonacciTail 0 >= 0 && fibonacciTail 10 >= 0")
        let result = LazyResidenceFixture.checkProgramWithCapacity 1024 (Some source)
        DimensionalCases.noErrors result
        Assert.Empty(TailSourceRanges.tailInactiveOccurrences result.Graph)
        Assert.Contains(RecursiveInstances.certificates result.Graph, fun model -> model.MaximumIterations = 10I)

    [<Fact>]
    member _.``Finite tail transition state retains its exact measured dimension``() =
        let source = (RecursiveInstances.tailSource 0 1 "10" "count <= 0" "- 1")
                        .Replace("module RecursiveInstances", "module RecursiveInstances\n[<Measure>] type m")
                        .Replace("(n: int) : int", "(n: int) : int<m>")
                        .Replace("loop 0 1 n", "loop 0<m> 1<m> n")
                        .Replace(">= 0 then", ">= 0<m> then")
        let result = LazyResidenceFixture.checkProgramWithCapacity 1024 (Some source)
        DimensionalCases.noErrors result
        Assert.NotEmpty(RecursiveInstances.certificates result.Graph)
        let declaration = RecursiveInstances.declarations result.Graph |> Assert.Single
        let parameters, _ = RecursiveInstances.code result.Graph declaration
        Assert.Contains("<m>", formatType (let _, ty, _ = parameters[0] in applySubst ty))
        Assert.Contains("<m>", formatType (let _, ty, _ = parameters[1] in applySubst ty))
        Assert.Equal(Types.intType, (let _, ty, _ = parameters[2] in applySubst ty))

    [<Theory>]
    [<InlineData("count = 0", "- 1")>]
    [<InlineData("count <= 0", "+ 1")>]
    [<InlineData("count <= 0", "- 0")>]
    member _.``Nonpositive or unproved tail progress remains a numeric source refusal``(guard, step) =
        let source = RecursiveInstances.tailSource 0 1 "10" guard step
        let result = LazyResidenceFixture.checkProgramWithCapacity 1024 (Some source)
        Assert.Empty(RecursiveInstances.certificates result.Graph)
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8011")

    [<Fact>]
    member _.``An unbounded tail entry counter cannot seed a finite certificate``() =
        let source = (RecursiveInstances.tailSource 0 1 "count" "count <= 0" "- 1")
                        .Replace("let main _ =", "let main (count: int) =")
        let result = LazyResidenceFixture.checkProgramWithCapacity 1024 (Some source)
        Assert.Empty(RecursiveInstances.certificates result.Graph)
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8011")

    [<Theory>]
    [<InlineData("nonlinear")>]
    [<InlineData("nontail")>]
    member _.``A finite counter alone cannot certify an unrelated recursive transition`` defect =
        let source = RecursiveInstances.tailSource 1 2 "10" "count <= 0" "- 1"
        let source =
            match defect with
            | "nonlinear" -> source.Replace("(a + b)", "(a * b)")
            | _ -> source.Replace("else loop b", "else 1 + loop b")
        let result = LazyResidenceFixture.checkProgramWithCapacity 1024 (Some source)
        Assert.Empty(RecursiveInstances.certificates result.Graph)
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8011")

    [<Fact>]
    member _.``A changed tail entry tuple replaces the old enclosure``() =
        let run count =
            let source = RecursiveInstances.tailSource 0 1 (string count) "count <= 0" "- 1"
            let result = LazyResidenceFixture.checkProgramWithCapacity 1024 (Some source)
            DimensionalCases.noErrors result
            RecursiveInstances.certificates result.Graph
        Assert.Contains(run 10, fun model -> model.MaximumIterations = 10I && model.Upper = [55I; 89I])
        let changed = run 11
        Assert.Contains(changed, fun model -> model.MaximumIterations = 11I && model.Upper = [89I; 144I])
        Assert.DoesNotContain(changed, fun model -> model.MaximumIterations = 10I)

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
