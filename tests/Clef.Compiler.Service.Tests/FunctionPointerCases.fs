namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeService
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

module private CallbackCases =
    let check source =
        match parseAndCheck ("module Callbacks\n" + source) "callbacks.clef" with
        | Success result | CheckFailure result -> result
        | ParseFailure errors -> failwithf "Parse failed: %A" errors
    let plans (graph: SemanticGraph) = graph.Codata.Value.FunctionPointers |> Map.values |> Seq.toList

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "FunctionPointers")>]
type FunctionPointerTests() =
    [<Fact>]
    member _.``Retaining diagnostics never serializes inference cells as JSON object keys``() =
        let result = DimensionalCases.check "let measured (x: float<'u>) = x\n"
        let nodes = result.Graph.Nodes |> Map.values |> Seq.toList
        let recipe : Clef.Compiler.Nanopass.Recipe.Recipe = {
            OriginalNodeId = nodes.Head.Id; ReplacementRootId = nodes.Head.Id
            NewNodes = nodes; ElaborationKind = "Baker"; ElaborationSource = "native callback\n\"entry\"" }
        let diagnostics : Clef.Compiler.Nanopass.Recipe.RecipeDiagnostic list = [
            { NodeId = nodes.Head.Id; ElaborationKind = "Baker"; Result = Clef.Compiler.Nanopass.Recipe.RecipeCreated recipe }
            { NodeId = nodes.Head.Id; ElaborationKind = "Baker"; Result = Clef.Compiler.Nanopass.Recipe.NotApplicable "reason" } ]
        use artifact = System.Text.Json.JsonDocument.Parse(Clef.Compiler.Nanopass.Serialization.serializeDiagnostics diagnostics)
        Assert.Equal(2, artifact.RootElement.GetArrayLength())
        Assert.Equal(nodes.Length, artifact.RootElement[0].GetProperty("Result").GetProperty("RecipeCreated").GetProperty("newNodeCount").GetInt32())

    [<Fact>]
    member _.``Native address retains its named declaration and full invocation``() =
        let result = CallbackCases.check """
let add (a: int) (b: int) : int = a + b
let apply (pointer: FnPtr<int -> int -> int>) (a: int) (b: int) = FnPtr.invoke pointer a b
[<EntryPoint>]
let main _ =
    let pointer: FnPtr<int -> int -> int> = FnPtr.ofFunction add
    apply pointer 40 2
"""
        DimensionalCases.noErrors result
        let plans = CallbackCases.plans result.Graph
        let address = plans |> List.choose (function FunctionPointerPlan.Address (symbol, lambda) -> Some (symbol, lambda) | _ -> None)
        Assert.Single(address) |> ignore
        let symbol, lambda = address.Head
        Assert.Equal("Callbacks.add", symbol)
        Assert.True(result.Graph.Nodes[lambda].IsReachable)
        match plans |> List.choose (function FunctionPointerPlan.Invoke (_, args, parameters, _) -> Some (args, parameters) | _ -> None) with
        | [args, parameters] -> Assert.Equal(2, args.Length); Assert.Equal(2, parameters.Length)
        | invocations -> failwithf "Expected one full native invocation, got %A" invocations

    [<Theory>]
    [<InlineData("let offset = 7\n    let captured x = x + offset\n    FnPtr.ofFunction captured")>]
    [<InlineData("FnPtr.ofFunction (fun (x: int) -> x)")>]
    member _.``Native address refuses implicit closure erasure``(body: string) =
        let result = CallbackCases.check ("[<EntryPoint>]\nlet main _ =\n    " + body + "\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096")
        Assert.DoesNotContain(CallbackCases.plans result.Graph, function FunctionPointerPlan.Address _ -> true | _ -> false)

    [<Fact>]
    member _.``Unsupported annotated entry is rejected before native emission``() =
        let result = CallbackCases.check """
let add : int -> int -> int = fun a b -> a + b
[<EntryPoint>]
let main _ = FnPtr.invoke (FnPtr.ofFunction add) 40 2
"""
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096")
        Assert.DoesNotContain(CallbackCases.plans result.Graph, function FunctionPointerPlan.Address _ -> true | _ -> false)

    [<Fact>]
    member _.``Partial callback invocation cannot masquerade as a native call``() =
        let result = CallbackCases.check """
let add (a: int) (b: int) : int = a + b
[<EntryPoint>]
let main _ = FnPtr.invoke (FnPtr.ofFunction add) 40
"""
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096")
        Assert.DoesNotContain(CallbackCases.plans result.Graph, function FunctionPointerPlan.Invoke _ -> true | _ -> false)
