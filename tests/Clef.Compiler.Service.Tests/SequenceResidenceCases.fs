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

    let activated source =
        let graph = check source
        let owner = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.ModuleDef("Residence", _) -> true | _ -> false) |> Assert.Single
        let graph, diagnostics = Clef.Compiler.Nanopass.ProgramInitialization.normalize [owner.Id] graph
        Assert.Empty diagnostics
        Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable graph

    let preparedBorrow () =
        let graph = activated """
let retain (input: seq<bool>) = seq { yield! input }
[<EntryPoint>]
let main _ =
    let input = seq { yield true; yield false }
    let held = retain input
    for value in held do ignore value
    0
"""
        let prepared = Clef.Compiler.Nanopass.SequenceFactoryResults.prepare graph graph.Codata.Value.Curry
        Assert.Empty prepared.Unresolved
        Assert.NotEmpty prepared.FactoryCalls
        prepared

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceResidence")>]
type SequenceResidenceCases() =
    [<Fact>]
    member _.``Returned sequence and callable environments share the complete deferred use proof``() =
        let graph = Residence.activated """
[<EntryPoint>]
let main _ =
    let offset = 7
    let callback = fun value -> value + offset
    let storedMap = Seq.map callback
    let first = storedMap (seq { yield 1 })
    let mapOperation = Seq.map
    let second = mapOperation callback (seq { yield 2 })
    for value in first do ignore value
    for value in second do ignore value
    0
"""
        let graph, curry = Clef.Compiler.Nanopass.EnvironmentFactoryResults.prepare graph graph.Codata.Value.Curry
        Assert.Contains(graph.Edges, fun edge -> edge.Role = EdgeRole.EnvironmentResultCall)
        let prepared = Clef.Compiler.Nanopass.SequenceFactoryResults.prepare graph curry
        Assert.Empty prepared.Unresolved
        Assert.Equal(2, prepared.FactoryCalls.Count)
        let graph = prepared.Graph
        let reading = SequenceResidence.analyzeWithRegions graph prepared.Destinations prepared.FactoryCalls
        Assert.Empty reading.Unresolved
        Assert.All(prepared.FactoryCalls.Values, fun allocation -> Assert.True(reading.Sites.ContainsKey allocation))
        let callableRequirements = graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.SequenceResultCapture &&
            match graph.Nodes[edge.Sources[0]].Type with NativeType.TFun _ -> true | _ -> false)
        Assert.Equal(2, callableRequirements.Length)
        let requirement = callableRequirements.Head
        let slot, allocation = requirement.Sources[0], requirement.Sources[7]
        let changed =
            { graph with Edges = Hyperedge.edge1 EdgeClass.Reference EdgeRole.Symbol 0 slot requirement.Target :: graph.Edges }
        let refused = SequenceResidence.analyzeWithRegions changed prepared.Destinations prepared.FactoryCalls
        Assert.False(refused.Sites.ContainsKey allocation)
        Assert.Contains(refused.Unresolved, fun item -> item.Site = allocation)

    [<Fact>]
    member _.``Known callable input retains its environment through complete formal consumption``() =
        let graph = Residence.activated """
let prepare (callback: int -> int) = Seq.map callback
[<EntryPoint>]
let main _ =
    let offset = 7
    let callback = fun value -> value + offset
    let mapped = prepare callback (seq { yield 1 })
    for value in mapped do ignore value
    0
"""
        let graph, curry = Clef.Compiler.Nanopass.EnvironmentFactoryResults.prepare graph graph.Codata.Value.Curry
        let prepared = Clef.Compiler.Nanopass.SequenceFactoryResults.prepare graph curry
        Assert.Empty prepared.Unresolved
        let graph = prepared.Graph
        let reading = SequenceResidence.analyzeEnvironmentsPrepared graph prepared.Destinations prepared.FactoryCalls
        Assert.NotEmpty reading.Sites
        Assert.Empty reading.Unresolved
        let borrows = reading.Evidence |> List.filter (fun edge ->
            edge.Role = EdgeRole.SequenceInputBorrow &&
            match graph.Nodes[edge.Sources[2]].Type with NativeType.TFun _ -> true | _ -> false)
        let borrow = Assert.Single borrows
        let allocation, formal = borrow.Sources[0], borrow.Sources[3]
        Assert.True(reading.Sites.ContainsKey allocation)
        let changed =
            { graph with Edges = Hyperedge.edge1 EdgeClass.Reference EdgeRole.Symbol 0 formal borrow.Target :: graph.Edges }
        let refused = SequenceResidence.analyzeEnvironmentsPrepared changed prepared.Destinations prepared.FactoryCalls
        Assert.False(refused.Sites.ContainsKey allocation)
        Assert.Contains(refused.Unresolved, fun item -> item.Site = allocation)

    [<Fact>]
    member _.``Complete ordinary inputs carry actual regions through all formal uses``() =
        let graph = Residence.activated """
let consume (input: seq<bool>) =
    for value in input do ignore value
[<EntryPoint>]
let main _ =
    let supplied = seq { yield true; yield false }
    consume supplied
    consume supplied
    0
"""
        let graph = { graph with Nodes = graph.Nodes |> Map.map (fun _ node -> { node with Parent = None }) }
        let reading = SequenceResidence.analyzeWithRegions graph Map.empty Map.empty
        Assert.Empty reading.Unresolved
        let borrows = reading.Evidence |> List.filter (fun edge -> edge.Role = EdgeRole.SequenceInputBorrow)
        Assert.Equal(2, borrows.Length)
        for edge in borrows do
            match edge.Sources, graph.Nodes[edge.Target].Kind with
            | [allocation; covering; actual; formal; implementation], SemanticKind.Application(_, arguments) ->
                Assert.True(reading.Sites.ContainsKey allocation)
                Assert.Contains(actual, arguments)
                let parameters = match graph.Nodes[implementation].Kind with SemanticKind.Lambda(parameters, _, _, _, _) -> parameters | _ -> failwith "Missing called activation"
                let ordinal = parameters |> List.findIndex (fun (_, _, parameter) -> parameter = formal)
                Assert.Equal(actual, arguments[ordinal])
                Assert.NotEqual(covering, implementation)
            | other -> failwithf "Incomplete input borrow: %A" other
        let formal = borrows.Head.Sources[3]
        let consumer = graph.Nodes.Values |> Seq.find (fun node -> node.IsReachable && match node.Kind with SemanticKind.Literal _ -> true | _ -> false)
        let changed = { graph with Edges = Hyperedge.edge1 EdgeClass.Reference EdgeRole.Symbol 0 formal consumer.Id :: graph.Edges }
        let refused = SequenceResidence.analyzeWithRegions changed Map.empty Map.empty
        Assert.Contains(refused.Unresolved, fun item -> item.Reason = SequenceResidence.ResidualReason.UnsupportedConsumer consumer.Id)
        Assert.DoesNotContain(refused.Evidence, fun edge -> edge.Role = EdgeRole.SequenceInputBorrow)

    [<Fact>]
    member _.``Returned sequence borrow requires caller destination and complete input lifetime``() =
        let prepared = Residence.preparedBorrow ()
        let graph = { prepared.Graph with Nodes = prepared.Graph.Nodes |> Map.map (fun _ node -> { node with Parent = None }) }
        let reading = SequenceResidence.analyzeWithRegions graph prepared.Destinations prepared.FactoryCalls
        Assert.Empty reading.Unresolved
        Assert.All(prepared.FactoryCalls.Values, fun allocation -> Assert.True(reading.Sites.ContainsKey allocation))
        Assert.Contains(reading.Evidence, fun edge -> edge.Role = EdgeRole.SequenceInputBorrow)
        Assert.Contains(reading.Evidence, fun edge -> edge.Role = EdgeRole.SequenceTemplateBorrow && prepared.Destinations.ContainsKey edge.Target)

    [<Theory>]
    [<InlineData("missing")>]
    [<InlineData("actual")>]
    [<InlineData("formal")>]
    [<InlineData("allocation")>]
    [<InlineData("unrelated-proof")>]
    member _.``Prepared result capture requirements are revalidated before lifetime admission`` damage =
        let prepared = Residence.preparedBorrow ()
        let requirement = prepared.Graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequenceResultCapture) |> Assert.Single
        let allocation = requirement.Sources[7]
        let replacement =
            match damage with
            | "actual" -> Some { requirement with Sources = requirement.Sources |> List.mapi (fun i value -> if i = 5 then requirement.Sources[6] else value) }
            | "formal" -> Some { requirement with Sources = requirement.Sources |> List.mapi (fun i value -> if i = 3 then prepared.Destinations[requirement.Target] else value) }
            | "allocation" -> Some { requirement with Sources = requirement.Sources |> List.mapi (fun i value -> if i = 7 then requirement.Target else value) }
            | _ -> None
        let identity (edge: Hyperedge) = edge.Class, edge.Role, edge.Sources, edge.Target, edge.Ordinal
        let edges = prepared.Graph.Edges |> List.filter (fun edge -> identity edge <> identity requirement)
        let edges = Option.toList replacement @ edges
        let edges =
            if damage = "unrelated-proof" then
                { requirement with Role = EdgeRole.SequenceInputBorrow; Sources = [allocation; allocation; allocation; allocation; allocation] } :: edges
            else edges
        let graph = { prepared.Graph with Edges = edges }
        let reading = SequenceResidence.analyzeWithRegions graph prepared.Destinations prepared.FactoryCalls
        Assert.False(reading.Sites.ContainsKey allocation)
        Assert.Contains(reading.Unresolved, fun item ->
            item.Site = allocation && match item.Reason with SequenceResidence.ResidualReason.MissingResultCapture _ -> true | _ -> false)

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
