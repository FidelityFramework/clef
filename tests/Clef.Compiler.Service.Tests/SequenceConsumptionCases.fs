namespace Clef.Compiler.Service.Tests

open System
open System.IO
open System.Text.Json
open System.Text.RegularExpressions
open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.Infrastructure
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module SequenceConsumption = Clef.Compiler.Nanopass.SequenceConsumption

module private Consumption =
    let prelude = "module Consumption\n[<Measure>] type m\n[<Measure>] type s\n"
    let check body =
        let directory = Path.Combine(Path.GetTempPath(), "clef-sequence-consumption-" + Guid.NewGuid().ToString("N"))
        let previous = PhaseConfig.getConfig ()
        Directory.CreateDirectory directory |> ignore
        try
            PhaseConfig.enableArtifacts directory [1]
            let result =
                match parseAndCheck (prelude + body) "sequence-consumption.clef" with
                | Success result -> result
                | CheckFailure result -> failwithf "Expected admitted consumption: %A" result.Diagnostics
                | ParseFailure errors -> failwithf "Expected parsed consumption: %A" errors
            DimensionalCases.noErrors result
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
                node.IsReachable && match node.Kind with SemanticKind.ForEach _ | SemanticKind.Error _ -> true | _ -> false)
            use document = JsonDocument.Parse(File.ReadAllText(Path.Combine(directory, "01_psg0.json")))
            let raw = document.RootElement.GetProperty("nodes").EnumerateArray()
                      |> Seq.map (fun node -> node.GetProperty("id").GetInt32(), node.Clone()) |> Map.ofSeq
            result.Graph, raw
        finally
            PhaseConfig.setConfig previous
            Directory.Delete(directory, true)

    let rawKind (node: JsonElement) =
        node.GetProperty("kind").GetString() |> Option.ofObj |> Option.defaultWith (fun () -> failwith "Missing raw node kind")
    let rawLoops (raw: Map<int, JsonElement>) =
        raw |> Map.toList |> List.choose (fun (id, node) ->
            let kind = rawKind node
            if kind.StartsWith("ForEach") then
                let ids = Regex.Matches(kind, @"NodeId\s+(\d+)") |> Seq.cast<Match> |> Seq.map (fun matched -> NodeId(Int32.Parse matched.Groups[1].Value)) |> Seq.toList
                match ids with
                | [formal; collection; body] -> Some (NodeId id, formal, collection, body)
                | _ -> failwithf "ForEach omitted its exact source formal: %s" kind
            else None)

    let call modl operation (graph: SemanticGraph) id =
        match graph.Nodes[id].Kind with
        | SemanticKind.Application(callee, arguments) ->
            match graph.Nodes[callee].Kind with
            | SemanticKind.Intrinsic info when info.Module = modl && info.Operation = operation -> Some arguments
            | _ -> None
        | _ -> None

    let verify (graph: SemanticGraph) (raw: Map<int, JsonElement>) (site, formal, collection, body) =
        Assert.StartsWith("PatternBinding", rawKind raw[NodeId.value formal])
        let binding = graph.Nodes[formal]
        match binding.Kind with SemanticKind.Binding(_, false, false, _) -> () | kind -> failwithf "Lost immutable iteration binding: %A" kind
        let iteration =
            match graph.Nodes[site].Kind with
            | SemanticKind.Sequential [iteration] -> iteration
            | kind -> failwithf "ForEach source identity was not retained: %A" kind
        let enumBinding, loop =
            match graph.Nodes[iteration].Kind with
            | SemanticKind.Sequential [binding; loop] -> binding, loop
            | kind -> failwithf "Collection initialization lost its outer scope: %A" kind
        let initialization = Assert.Single graph.Nodes[enumBinding].Children
        Assert.Equal<NodeId list>([collection], call IntrinsicModule.Seq "getEnumerator" graph initialization |> Option.get)
        let guard, loopBody =
            match graph.Nodes[loop].Kind with SemanticKind.WhileLoop(guard, body) -> guard, body | kind -> failwithf "Expected pull loop: %A" kind
        let enumerationRef = Assert.Single (call IntrinsicModule.SeqEnumerator "moveNext" graph guard |> Option.get)
        match graph.Nodes[enumerationRef].Kind with
        | SemanticKind.VarRef(_, Some source) -> Assert.Equal(enumBinding, source)
        | kind -> failwithf "Loop did not use retained enumeration: %A" kind
        match graph.Nodes[loopBody].Kind with
        | SemanticKind.Sequential [currentBinding; current; action] ->
            let currentCall = Assert.Single graph.Nodes[currentBinding].Children
            Assert.True((call IntrinsicModule.SeqEnumerator "current" graph currentCall).IsSome)
            Assert.Equal<NodeId list>([current], binding.Children)
            match graph.Nodes[current].Kind with
            | SemanticKind.VarRef(_, Some source) -> Assert.Equal(currentBinding, source)
            | kind -> failwithf "Iteration binding lost current snapshot: %A" kind
            Assert.Equal(SemanticKind.Sequential [formal; body], graph.Nodes[action].Kind)
        | kind -> failwithf "Body is not preceded by one current snapshot: %A" kind
        match graph.Nodes[collection].Type with
        | NativeType.TSeq element -> DimensionalCases.same element binding.Type
        | ty -> failwithf "Collection lost admitted sequence type: %A" ty
        site, formal, collection, body, enumBinding, loop

    let reject code (marked: string) =
        let first, last = marked.IndexOf('«'), marked.IndexOf('»')
        let before, selected = marked.Substring(0, first), marked.Substring(first + 1, last - first - 1)
        let position (text: string) =
            let lines = text.Split('\n')
            { Line = lines.Length; Column = (Array.last lines).Length }
        let file = "sequence-consumption-negative.clef"
        let range = { File = file; Start = position (prelude + before); End = position (prelude + before + selected) }
        match parseAndCheck (prelude + marked.Replace("«", "").Replace("»", "")) file with
        | CheckFailure result ->
            Assert.True(CheckResult.hasErrors result)
            let diagnostic = result.Diagnostics |> List.filter (fun diagnostic ->
                diagnostic.Code = code && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error) |> Assert.Single
            Assert.Equal<SourceRange>(range, diagnostic.Range)
        | Success result -> failwithf "Invalid consumption reached successful checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected located %s: %A" code errors

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceConsumption")>]
type SequenceConsumptionCases() =
    [<Theory>]
    [<InlineData("seq { yield 1<m> }", "item")>]
    [<InlineData("seq { yield 0.25<1/m> }", "item")>]
    [<InlineData("seq { yield () }", "item")>]
    [<InlineData("seq { yield (fun (value: int<m>) -> value) }", "item")>]
    [<InlineData("(seq { () }: seq<int<m>>)", "_")>]
    member _.``Sequence elements initialize a real immutable source declaration for each successful pull``(source: string, name: string) =
        let useValue = if name = "_" then "()" else "ignore item"
        let graph, raw = Consumption.check ("[<EntryPoint>]\nlet main _ =\n    for " + name + " in " + source + " do " + useValue + "\n    0\n")
        let loop = Consumption.rawLoops raw |> Assert.Single
        let _, formal, _, _, _, _ = Consumption.verify graph raw loop
        let references = graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with SemanticKind.VarRef("item", definition) -> Some definition | _ -> None) |> Seq.toList
        if name <> "_" then
            Assert.NotEmpty references
            Assert.All(references, fun definition -> Assert.Equal(Some formal, definition))
        let repeated = SequenceConsumption.normalize graph
        Assert.Same(graph, repeated)

    [<Fact>]
    member _.``Nested same-name iteration declarations retain separate exact reference identities``() =
        let graph, raw = Consumption.check """
[<EntryPoint>]
let main _ =
    for item in seq { yield 1<m> } do
        ignore item
        for item in seq { yield true } do
            ignore item
        ignore item
    0
"""
        let loops = Consumption.rawLoops raw
        Assert.Equal(2, loops.Length)
        let verified = loops |> List.map (Consumption.verify graph raw)
        let formals = verified |> List.map (fun (_, formal, _, _, _, _) -> formal) |> Set.ofList
        Assert.Equal(2, formals.Count)
        let uses = graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with SemanticKind.VarRef("item", Some definition) -> Some definition | _ -> None) |> Seq.toList
        Assert.Equal(formals, Set.ofList uses)
        Assert.Equal(3, uses.Length)

    [<Fact>]
    member _.``A loop closure captures the same declaration that receives its current snapshot``() =
        let graph, raw = Consumption.check """
[<EntryPoint>]
let main _ =
    for item in seq { yield 1<m> } do
        let read = fun () -> item
        ignore read
    0
"""
        let _, formal, _, _, _, _ = Consumption.verify graph raw (Consumption.rawLoops raw |> Assert.Single)
        let capture =
            graph.Nodes.Values
            |> Seq.collect (fun node ->
                match node.Kind with
                | SemanticKind.Lambda(_, _, captures, _, LambdaContext.RegularClosure) -> captures
                | _ -> [])
            |> Seq.filter (fun capture -> capture.SourceNodeId = Some formal)
            |> Assert.Single
        Assert.False capture.IsMutable
        DimensionalCases.same graph.Nodes[formal].Type capture.Type

    [<Fact>]
    member _.``Effectful collection formation stays outside repeated pulls and preceding the following effect``() =
        let graph, raw = Consumption.check """
[<EntryPoint>]
let main _ =
    let mutable trace = 0
    for item in (trace <- 1; seq { yield 2 }) do
        trace <- item
    trace <- 3
    0
"""
        let _, _, collection, _, enumBinding, loop = Consumption.verify graph raw (Consumption.rawLoops raw |> Assert.Single)
        let operandEffects =
            match graph.Nodes[collection].Kind with SemanticKind.Sequential [effect; _] -> effect | kind -> failwithf "Lost collection evaluation: %A" kind
        let rec descendants seen id =
            if Set.contains id seen then seen
            else graph.Nodes[id].Children |> List.fold descendants (Set.add id seen)
        Assert.Contains(operandEffects, descendants Set.empty enumBinding)
        Assert.DoesNotContain(operandEffects, descendants Set.empty loop)

    [<Theory>]
    [<InlineData("[<EntryPoint>]\nlet main _ =\n    «for item in 1 do ()»\n    0\n", "CCS8003")>]
    [<InlineData("[<EntryPoint>]\nlet main _ =\n    «for item in seq { yield 1 } do item»\n    0\n", "CCS8003")>]
    [<InlineData("[<EntryPoint>]\nlet main _ =\n    for item in seq { yield 1 } do item <- «2»\n    0\n", "CCS8009")>]
    [<InlineData("[<EntryPoint>]\nlet main _ =\n    for item in seq { yield 1<m> } do «(fun (_: int<s>) -> ()) item»\n    0\n", "CCS8040")>]
    [<InlineData("[<EntryPoint>]\nlet main _ =\n    «for (left, right) in seq { yield (1, 2) } do ()»\n    0\n", "CCS8401")>]
    member _.``Sequence iteration rejects invalid source and body contracts at their source premise``(source: string, code: string) =
        Consumption.reject code source
