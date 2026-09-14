namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private PipeEvaluation =
    let check expression =
        let result = DimensionalCases.check ("""
let first () : int = 4
let second () : int = 7
let add (left: int) (right: int) = left + right
let observed = """ + expression + "\n[<EntryPoint>]\nlet main _ = observed\n")
        DimensionalCases.noErrors result
        result

    let value (result: CheckResult) =
        let binding = result.Graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with
            | SemanticKind.Binding ("observed", _, _, _) -> true
            | _ -> false)
        result.Graph.Nodes[binding.Children.Head]

    let arguments (result: CheckResult) (node: SemanticNode) =
        match node.Kind with
        | SemanticKind.Application (functionId, args) ->
            match result.Graph.Nodes[functionId].Kind with
            | SemanticKind.Application _ | SemanticKind.Sequential _ ->
                failwith "Sequencing prevented the call from saturating"
            | _ -> args
        | kind -> failwithf "Expected a saturated application, got %A" kind

    let assertCall name (result: CheckResult) nodeId =
        match result.Graph.Nodes[nodeId].Kind with
        | SemanticKind.Application (functionId, _) ->
            match result.Graph.Nodes[functionId].Kind with
            | SemanticKind.VarRef (actual, _) -> Assert.True(actual = name || actual.EndsWith("." + name), actual)
            | kind -> failwithf "Expected a reference to %s, got %A" name kind
        | kind -> failwithf "Expected a call to %s, got %A" name kind

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "PipeEvaluation")>]
type PipeEvaluationTests() =
    [<Fact>]
    member _.``Forward pipe preserves its operand before the right function arguments``() =
        let result = PipeEvaluation.check "first () |> add (second ())"
        match (PipeEvaluation.value result).Kind with
        | SemanticKind.Sequential [operand; call] ->
            PipeEvaluation.assertCall "first" result operand
            let args = PipeEvaluation.arguments result result.Graph.Nodes[call]
            Assert.Equal(2, args.Length)
            PipeEvaluation.assertCall "second" result args[0]
            Assert.Equal(operand, args[1])
        | kind -> failwithf "Forward pipe lost its prerequisite: %A" kind

    [<Theory>]
    [<InlineData("add (first ()) (second ())")>]
    [<InlineData("add (first ()) <| second ()")>]
    member _.``Direct and backward applications keep ordinary argument order``(expression: string) =
        let result = PipeEvaluation.check expression
        let args = PipeEvaluation.arguments result (PipeEvaluation.value result)
        Assert.Equal(2, args.Length)
        PipeEvaluation.assertCall "first" result args[0]
        PipeEvaluation.assertCall "second" result args[1]

    [<Fact>]
    member _.``A piped partial call still saturates when another argument follows``() =
        let result = PipeEvaluation.check "(first () |> add) (second ())"
        match (PipeEvaluation.value result).Kind with
        | SemanticKind.Sequential [operand; call] ->
            PipeEvaluation.assertCall "first" result operand
            let args = PipeEvaluation.arguments result result.Graph.Nodes[call]
            Assert.Equal(2, args.Length)
            Assert.Equal(operand, args[0])
            PipeEvaluation.assertCall "second" result args[1]
        | kind -> failwithf "Partial pipe did not retain its prerequisite: %A" kind

    [<Fact>]
    member _.``Nested right pipes preserve both operands in source order``() =
        let result = PipeEvaluation.check "first () |> (second () |> add)"
        match (PipeEvaluation.value result).Kind with
        | SemanticKind.Sequential [outerOperand; innerOperand; call] ->
            PipeEvaluation.assertCall "first" result outerOperand
            PipeEvaluation.assertCall "second" result innerOperand
            let args = PipeEvaluation.arguments result result.Graph.Nodes[call]
            Assert.Equal<NodeId list>([innerOperand; outerOperand], args)
        | kind -> failwithf "Nested pipe changed prerequisite order: %A" kind

    [<Fact>]
    member _.``Chained Option pipes and piped partial intrinsics still decompose``() =
        let result = DimensionalCases.check """
let chained = Some 4 |> Option.map (fun x -> x + 2) |> Option.filter (fun x -> x > 0)
let partial = ((fun (x: int) -> x + 1) |> Option.map) (Some 4)
[<EntryPoint>]
let main _ = Option.get chained + Option.get partial
"""
        DimensionalCases.noErrors result
        let expected = NativeType.TApp(Types.optionTyCon, [Types.intType])
        DimensionalCases.same expected (DimensionalCases.bindingType "chained" result)
        DimensionalCases.same expected (DimensionalCases.bindingType "partial" result)
        let reachable = result.Graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable) |> Seq.toList
        Assert.NotEmpty reachable
        Assert.DoesNotContain(reachable, fun node ->
            match node.Kind with
            | SemanticKind.Intrinsic info when info.Module = IntrinsicModule.Option -> true
            | _ -> false)
