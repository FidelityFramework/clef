namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module SequenceResidence = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence

module private Residence =
    let check source =
        match parseAndCheck ("module Residence\n" + source) "sequence-residence.clef" with
        | Success result -> DimensionalCases.noErrors result; result.Graph
        | CheckFailure result -> failwithf "Expected admitted source: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed source: %A" errors

    let owners (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false) |> Seq.toList

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
        |> Assert.Single

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceResidence")>]
type SequenceResidenceCases() =
    [<Fact>]
    member _.``Literal sequence and two local enumerators have one bounded ordinary activation``() =
        let graph = Residence.check """
[<EntryPoint>]
let main _ =
    let values = seq { yield true; yield false }
    for value in values do ignore value
    for value in values do ignore value
    0
"""
        // Parent is a convenience projection, not residence authority.
        let graph = { graph with Nodes = graph.Nodes |> Map.map (fun _ node -> { node with Parent = None }) }
        let reading = SequenceResidence.analyze graph
        Assert.Empty reading.Unresolved
        Assert.Equal(3, reading.Sites.Count)
        Assert.All(reading.Sites.Values, fun residence -> Assert.Equal(EscapeKind.StackScoped, residence))
        Assert.True(reading.Sites.ContainsKey((Residence.owners graph |> Assert.Single).Id))

    [<Fact>]
    member _.``Returning factory and its consumer iterator do not borrow the departed activation``() =
        let graph = Residence.check """
let produce () = seq { yield true }
[<EntryPoint>]
let main _ =
    let values = produce ()
    for value in values do ignore value
    0
"""
        let reading = SequenceResidence.analyze graph
        let owner = Residence.owners graph |> Assert.Single
        Assert.False(reading.Sites.ContainsKey owner.Id)
        Assert.Contains(reading.Unresolved, fun residual -> residual.Site = owner.Id && match residual.Reason with SequenceResidence.ResidualReason.ReturnsFrom _ -> true | _ -> false)
        Assert.Contains(reading.Unresolved, fun residual -> match residual.Reason with SequenceResidence.ResidualReason.FactoryResult _ -> true | _ -> false)

    [<Fact>]
    member _.``Delegation iterator in a generator has no ordinary stack lifetime proof across pulls``() =
        let graph = Residence.check """
[<EntryPoint>]
let main _ =
    let inner = seq { yield true }
    let outer = seq { yield! inner }
    for value in outer do ignore value
    0
"""
        let reading = SequenceResidence.analyze graph
        let deferred = reading.Unresolved |> List.filter (fun residual ->
            match residual.Reason with SequenceResidence.ResidualReason.DeferredActivation _ -> true | _ -> false)
        Assert.NotEmpty deferred
        Assert.Contains(deferred, fun residual -> match graph.Nodes[residual.Site].Kind with SemanticKind.Application _ -> true | _ -> false)
        for residual in deferred do Assert.False(reading.Sites.ContainsKey residual.Site)

    [<Fact>]
    member _.``An allocation shared structurally by two function activations remains ambiguous``() =
        let graph = Residence.check """
let first () =
    let firstValues = seq { yield true }
    ignore firstValues
    0
let second () =
    let secondValues = seq { yield false }
    ignore secondValues
    0
[<EntryPoint>]
let main _ = first () + second ()
"""
        let first, second = Residence.binding "firstValues" graph, Residence.binding "secondValues" graph
        let shared = Assert.Single first.Children
        // Both initializers have the same seq<bool> type. The shared identity
        // deliberately has two containment paths, regardless of its Parent.
        let second = { second with Children = [shared] }
        let graph = { graph with Nodes = graph.Nodes.Add(second.Id, second) }
        let reading = SequenceResidence.analyze graph
        Assert.False(reading.Sites.ContainsKey shared)
        Assert.Contains(reading.Unresolved, fun residual -> residual.Site = shared && match residual.Reason with SequenceResidence.ResidualReason.AmbiguousActivation owners -> owners.Length = 2 | _ -> false)

    [<Fact>]
    member _.``A sequence retained by a closure requires a separate capture region proof``() =
        let graph = Residence.check """
[<EntryPoint>]
let main _ =
    let values = seq { yield true }
    let consume = fun () -> for value in values do ignore value
    consume ()
    0
"""
        let reading = SequenceResidence.analyze graph
        let owner = Residence.owners graph |> Assert.Single
        Assert.False(reading.Sites.ContainsKey owner.Id)
        Assert.Contains(reading.Unresolved, fun residual -> residual.Site = owner.Id)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Captured templates retain finite covered residence through repeated and nested enumeration`` nested =
        let middle = if nested then "    let middle = seq { yield! input }\n    let outer = seq { yield! middle; yield! middle }\n" else "    let outer = seq { yield! input; yield! input }\n"
        let graph = Residence.check (
            "[<EntryPoint>]\nlet main _ =\n    let mutable shared = true\n    let input = seq { yield shared; shared <- false; yield shared }\n" + middle +
            "    for value in outer do ignore value\n    for value in outer do ignore value\n    0\n")
        let graph = { graph with Nodes = graph.Nodes |> Map.map (fun _ node -> { node with Parent = None }) }
        let reading = SequenceResidence.analyzeWithRegions graph Map.empty Map.empty
        Assert.Empty reading.Unresolved
        Assert.Equal((if nested then 5 else 4), reading.Sites.Count) // Templates + two independent outer iterators.
        Assert.Equal((if nested then 3 else 2), reading.Regions.Count)
        Assert.Equal((if nested then 2 else 1), reading.Evidence.Length)
        for edge in reading.Evidence do
            Assert.Equal(EdgeRole.SequenceTemplateBorrow, edge.Role)
            Assert.Equal(EdgeClass.Provenance, edge.Class)
            match edge.Sources with
            | [allocation; covering; declaration; generator] ->
                Assert.True(reading.Sites.ContainsKey allocation)
                Assert.True(reading.Sites.ContainsKey edge.Target)
                match graph.Nodes[covering].Kind with
                | SemanticKind.Lambda(_, _, _, _, LambdaContext.SeqGenerator) -> failwith "Expected the ordinary covering activation"
                | SemanticKind.Lambda _ -> ()
                | _ -> failwith "Covering activation is not a callable"
                match graph.Nodes[edge.Target].Kind with
                | SemanticKind.SeqExpr(actualGenerator, captures) ->
                    Assert.Equal(generator, actualGenerator)
                    Assert.Contains(captures, fun capture -> capture.SourceNodeId = Some declaration && not capture.IsMutable)
                | _ -> failwith "Borrow target is not its capturing constructor"
                match graph.Nodes[generator].Kind with
                | SemanticKind.Lambda(_, _, repeatedCaptures, _, LambdaContext.SeqGenerator) ->
                    Assert.Contains(repeatedCaptures, fun capture -> capture.SourceNodeId = Some declaration)
                | _ -> failwith "Borrow has no exact generator"
            | sources -> failwithf "Missing finite residence participants: %A" sources

    [<Theory>]
    [<InlineData("return")>]
    [<InlineData("store")>]
    [<InlineData("opaque")>]
    member _.``Capturing templates with an escaping or opaque use cannot lend their source residence`` escape =
        let useValue =
            match escape with
            | "return" -> "    outer\n"
            | "store" -> "    (outer, true)\n"
            | _ -> "    sink outer\n    ()\n"
        let argument = if escape = "opaque" then "(sink: seq<bool> -> unit)" else "()"
        let graph = Residence.check (
            "let make " + argument + " =\n    let input = seq { yield true }\n    let outer = seq { yield! input }\n" + useValue +
            "[<EntryPoint>]\nlet main _ = ignore make; 0\n")
        let allocation = Assert.Single (Residence.binding "input" graph).Children
        let reading = SequenceResidence.analyzeWithRegions graph Map.empty Map.empty
        Assert.False(reading.Sites.ContainsKey allocation)
        Assert.Contains(reading.Unresolved, fun residual -> residual.Site = allocation)
        Assert.DoesNotContain(reading.Evidence, fun edge -> List.head edge.Sources = allocation)

    [<Fact>]
    member _.``Unknown captured input cannot acquire an allocation region from its lexical owner``() =
        let graph = Residence.check "let consume (input: seq<bool>) =\n    let outer = seq { yield! input }\n    for value in outer do ignore value\n[<EntryPoint>]\nlet main _ = ignore consume; 0\n"
        let reading = SequenceResidence.analyzeWithRegions graph Map.empty Map.empty
        Assert.Contains(reading.Unresolved, fun residual ->
            match residual.Reason with SequenceResidence.ResidualReason.UnknownInputRegion _ -> true | _ -> false)
        Assert.Empty reading.Evidence

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Missing or shared constructor ownership cannot certify a generator capture`` shared =
        let graph = Residence.check "[<EntryPoint>]\nlet main _ =\n    let input = seq { yield true }\n    let outer = seq { yield! input }\n    for value in outer do ignore value\n    0\n"
        let input = Assert.Single (Residence.binding "input" graph).Children
        let outer = graph.Nodes[Assert.Single (Residence.binding "outer" graph).Children]
        let nodes =
            if shared then
                let duplicate = { outer with Id = NodeId.fresh(); Parent = None }
                graph.Nodes.Add(duplicate.Id, duplicate)
            else graph.Nodes.Remove outer.Id
        let reading = SequenceResidence.analyzeWithRegions { graph with Nodes = nodes } Map.empty Map.empty
        Assert.False(reading.Sites.ContainsKey input)
        Assert.Contains(reading.Unresolved, fun residual -> residual.Site = input)
        Assert.Empty reading.Evidence
