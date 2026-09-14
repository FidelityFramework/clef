namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private OptionValues =
    let check source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Intrinsic info -> info.Module = IntrinsicModule.Option
            | _ -> false)
        result

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "OptionOperations")>]
type OptionValueTests() =
    [<Fact>]
    member _.``A bare Option alias specializes independently across payload types and measures``() =
        let result = OptionValues.check """
[<EntryPoint>]
let main _ =
    let map = Option.map
    let enabled = map (fun (x: int) -> x > 0) (Some 1)
    let speed = map (fun (x: int<m>) -> x / 2<s>) (Some 12<m>)
    if Option.get enabled && Option.get speed = 6<m/s> then 0 else 1
"""
        let aliases = result.Graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Binding (name, _, _, _) when name.StartsWith("map__mono") -> Some node
            | _ -> None) |> Seq.toList
        Assert.Equal(2, aliases.Length)
        Assert.All(aliases, fun node -> Assert.True(node.IsReachable))
        for node in result.Graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable) do
            for child in node.Children do
                Assert.True(result.Graph.Nodes.ContainsKey child, $"Dangling child {child} of {node.Id}")

    [<Fact>]
    member _.``Explicit Option type arguments still select the declared scheme for a bare value``() =
        let result = OptionValues.check """
let map = Option.map<int, int<m>>
let present = Option.isSome<int<m>>
let get = Option.get<int<m>>
let value = map (fun x -> x * 1<m>) (Some 3)
[<EntryPoint>]
let main _ = if present value && get value = 3<m> then 0 else 1
"""
        let measured = DimensionalCases.measuredInt DimensionalCases.metre
        let option = NativeType.TApp(Types.optionTyCon, [measured])
        DimensionalCases.same (NativeType.TFun(option, measured)) (DimensionalCases.bindingType "get" result)

    [<Fact>]
    member _.``A bare Option get with function payload retains its single option parameter``() =
        let result = OptionValues.check """
let get: (int -> int) option -> (int -> int) = Option.get
let callback = get (Some (fun x -> x + 2))
[<EntryPoint>]
let main _ = if callback 3 = 5 then 0 else 1
"""
        let payload = NativeType.TFun(Types.intType, Types.intType)
        let option = NativeType.TApp(Types.optionTyCon, [payload])
        let getClosures =
            result.Graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind, node.Type with
                | SemanticKind.Lambda (parameters, _, _, _, _), NativeType.TFun (domain, _) when domain = option -> Some parameters
                | _ -> None)
            |> Seq.toList
        Assert.NotEmpty getClosures
        Assert.All(getClosures, fun parameters -> Assert.Single parameters |> ignore)

    [<Fact>]
    member _.``Direct get applies remaining arguments to its extracted function payload``() =
        let result = OptionValues.check """
let first = Option.get (Some (fun value -> value + 2)) 3
let typed = Option.get<(int -> int)> (Some (fun value -> value + 3)) 4
let staged = Option.get (Some (fun first -> fun second -> first + second)) 2 3
[<EntryPoint>]
let main _ = if first = 5 && typed = 7 && staged = 5 then 0 else 1
"""
        let graph = result.Graph
        let extractedCalls =
            graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable &&
                match node.Kind with
                | SemanticKind.Application (callee, [_]) ->
                    match graph.Nodes[callee].Kind with
                    | SemanticKind.DUEliminate _ -> true
                    | _ -> false
                | _ -> false) |> Seq.toList
        Assert.Equal(3, extractedCalls.Length)
