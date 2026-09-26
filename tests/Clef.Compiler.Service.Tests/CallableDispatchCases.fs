namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module DispatchEnvironments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "CallableDispatch")>]
type CallableDispatchCases() =
    [<Fact>]
    member _.``A closed captured formal supplied only by one pure code leaf needs no fabricated environment`` () =
        let result = DimensionalCases.check """
let retain (callback: bool -> bool) = fun value -> callback value
[<EntryPoint>]
let main _ =
    let callback = fun (value: bool) -> value
    let retained = retain callback
    if retained true then 0 else 1
"""
        DimensionalCases.noErrors result
        let graph = result.Graph
        let retained =
            graph.Nodes.Values |> Seq.filter (fun node ->
                match node.Kind with SemanticKind.Binding("retained", false, _, _) -> true | _ -> false) |> Assert.Single
        let implementation = DispatchEnvironments.tryImplementation graph retained.Id
        Assert.True(implementation.IsSome)
        let code = graph.Nodes[implementation.Value]
        match code.Kind with
        | SemanticKind.Lambda(_, _, captures, _, _) -> Assert.Empty captures
        | _ -> failwith "The returned pure callback lost its actual code declaration."
        Assert.True((DispatchEnvironments.tryKnown graph retained.Id).IsNone)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Stateless code promotion preserves the original effectful factory demand identity`` demanded =
        let useValue = if demanded then "made true" else "ignoreArgument made"
        let prefix = """
let ignoreArgument (_: bool -> bool) = false
[<EntryPoint>]
let main _ =
    let mutable effects = 0
    let factory () = effects <- effects + 1; fun (value: bool) -> value
    let made = factory ()
    if """
        let source = prefix + useValue + " then effects else 0\n"
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        let graph = result.Graph
        let made =
            graph.Nodes.Values |> Seq.filter (fun node ->
                match node.Kind with SemanticKind.Binding("made", false, _, _) -> true | _ -> false) |> Assert.Single
        let initializer = graph.Nodes[Assert.Single made.Children]
        Assert.True(match initializer.Kind with SemanticKind.Application _ -> true | _ -> false)
        let reads =
            graph.Nodes.Values |> Seq.filter (fun node ->
                match node.Kind with SemanticKind.VarRef("made", _) -> true | _ -> false) |> Seq.toList
        Assert.NotEmpty reads
        for read in reads do
            match read.Kind with
            | SemanticKind.VarRef(_, Some declaration) -> Assert.Equal(made.Id, declaration)
            | _ -> failwith "The factory-result read lost its original source binding."
        // The source graph retains one factory initializer. This checks demand
        // identity in both contexts, not an eager execution/counting policy.
        Assert.Single(made.Children) |> ignore

    [<Fact>]
    member _.``Returned composition retains each finite stateless callback through a real immutable environment`` () =
        let result = DimensionalCases.check """
let compose (first: bool -> bool) (second: bool -> bool) = fun value -> first (second value)
[<EntryPoint>]
let main _ =
    let positive = compose (fun value -> value) (fun value -> not value)
    let negative = compose (fun value -> not value) (fun value -> value)
    if positive true = negative false then 0 else 1
"""
        DimensionalCases.noErrors result
        let graph = result.Graph
        let bindings =
            graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && match node.Kind with SemanticKind.Binding(name, _, _, _) -> name = "positive" || name = "negative" | _ -> false) |> Seq.toList
        Assert.Equal(2, bindings.Length)
        for binding in bindings do
            let callable = DispatchEnvironments.tryKnown graph binding.Id
            Assert.True(callable.IsSome, "Returned composition needs one real code/environment schema and its own actual instance.")
        let legacy =
            graph.Nodes.Values |> Seq.filter (fun node ->
                match node.IsReachable, node.Kind with
                | true, SemanticKind.Lambda(_, _, captures, _, _) -> captures |> List.exists (fun capture -> match capture.Type with NativeType.TFun _ -> true | _ -> false)
                | _ -> false)
        Assert.Empty legacy

    [<Fact>]
    member _.``An open composition declaration does not close its input family from observed library callers`` () =
        let result = DimensionalCases.check """
let compose (first: bool -> bool) (second: bool -> bool) = fun value -> first (second value)
let positive = compose (fun value -> value) (fun value -> not value)
let negative = compose (fun value -> not value) (fun value -> value)
"""
        DimensionalCases.noErrors result
        Assert.Empty(Clef.Compiler.PSGSaturation.SemanticGraph.CallableDispatch.plans result.Graph)
        Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read result.Graph).IsNone)
        let ingress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.analyze result.Graph
        let formals =
            result.Graph.Nodes.Values |> Seq.filter (fun node ->
                match node.Kind with SemanticKind.PatternBinding name -> name = "first" || name = "second" | _ -> false) |> Seq.toList
        Assert.NotEmpty formals
        for formal in formals do
            Assert.False(Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.allowsOccurrence ingress formal.Id)
