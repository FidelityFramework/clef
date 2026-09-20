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

module private LoopBindings =
    let prelude = "module LoopBindings\n"

    /// Inspect the actual pre-Baker phase alongside the returned typed graph.
    /// No alternate checker or reconstructed graph stands in for either phase.
    let check source =
        let directory = Path.Combine(Path.GetTempPath(), "clef-loop-bindings-" + Guid.NewGuid().ToString("N"))
        let previous = PhaseConfig.getConfig ()
        Directory.CreateDirectory directory |> ignore
        try
            PhaseConfig.enableArtifacts directory [1]
            let result =
                match parseAndCheck (prelude + source) "loop-bindings.clef" with
                | Success result -> result
                | CheckFailure result -> failwithf "Loop binding failed checking: %A" result.Diagnostics
                | ParseFailure errors -> failwithf "Loop binding failed parsing: %A" errors
            DimensionalCases.noErrors result
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
                node.IsReachable && match node.Kind with SemanticKind.Error _ -> true | _ -> false)
            use document = JsonDocument.Parse(File.ReadAllText(Path.Combine(directory, "01_psg0.json")))
            let raw = document.RootElement.GetProperty("nodes").EnumerateArray()
                      |> Seq.map (fun node -> node.GetProperty("id").GetInt32(), node.Clone()) |> Map.ofSeq
            result, raw
        finally
            PhaseConfig.setConfig previous
            Directory.Delete(directory, true)

    let rawKind (raw: Map<int, JsonElement>) id =
        raw[NodeId.value id].GetProperty("kind").GetString()
        |> Option.ofObj |> Option.defaultWith (fun () -> failwith "Raw phase omitted the node kind")
    let rawChildren (raw: Map<int, JsonElement>) id =
        raw[NodeId.value id].GetProperty("children").EnumerateArray() |> Seq.map (fun child -> child.GetInt32()) |> Seq.toList
    let rawDefinition raw id =
        let matched = Regex.Match(rawKind raw id, @"Some\s*\(NodeId\s+(\d+)\)")
        Assert.True(matched.Success, sprintf "Raw reference lost its definition: %s" (rawKind raw id))
        Int32.Parse matched.Groups[1].Value

    let descendants (nodes: Map<NodeId, SemanticNode>) root =
        let rec visit seen id =
            if Set.contains id seen then seen
            else nodes[id].Children |> List.fold visit (Set.add id seen)
        visit Set.empty root

    let reference (nodes: Map<NodeId, SemanticNode>) id =
        match nodes[id].Kind with
        | SemanticKind.VarRef (_, Some definition) -> definition
        | kind -> failwithf "Expected a resolved read of the existing binding: %A" kind

    let loopBinding (result: CheckResult) raw (loop: SemanticNode) =
        let nodes = result.Graph.Nodes
        match loop.Kind with
        | SemanticKind.WhileLoop (guard, body) ->
            let source =
                match nodes[body].Kind with
                | SemanticKind.Sequential (source :: _) -> nodes[source]
                | kind -> failwithf "Loop body does not establish its iteration value first: %A" kind
            match source.Kind with
            | SemanticKind.Binding ("index", false, false, _) -> ()
            | kind -> failwithf "Source iteration binding is not immutable: %A" kind
            let read = Assert.Single source.Children
            let counter = nodes[reference nodes read]
            match counter.Kind with
            | SemanticKind.Binding (name, true, false, _) -> Assert.NotEqual<string>("index", name)
            | kind -> failwithf "Iteration value is not read from a distinct hidden counter: %A" kind
            Assert.NotEqual(source.Id, counter.Id)
            Assert.DoesNotContain(counter.Id, descendants nodes body)
            Assert.StartsWith("Binding (\"index\", false,", rawKind raw source.Id)
            Assert.Equal<int list>(source.Children |> List.map NodeId.value, rawChildren raw source.Id)
            Assert.Equal(NodeId.value counter.Id, rawDefinition raw read)
            let guardReads = descendants nodes guard |> Set.toList |> List.choose (fun id ->
                match nodes[id].Kind with SemanticKind.VarRef (_, Some definition) -> Some definition | _ -> None)
            Assert.Contains(counter.Id, guardReads)
            Assert.DoesNotContain(source.Id, guardReads)
            source.Id, counter.Id, body
        | kind -> failwithf "Expected the settled counted while loop: %A" kind

    let captureFor name (result: CheckResult) =
        let binding = result.Graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.Binding (actual, _, _, _) -> actual = name | _ -> false)
        match result.Graph.Nodes[Assert.Single binding.Children].Kind with
        | SemanticKind.Lambda (_, _, captures, _, _) ->
            captures |> List.filter (fun capture -> capture.Name = "index") |> Assert.Single
        | kind -> failwithf "Expected a source closure retaining its iteration value: %A" kind

    let reject (marked: string) =
        let start, finish = marked.IndexOf('«'), marked.IndexOf('»')
        Assert.True(start >= 0 && finish > start)
        let before, span = marked.Substring(0, start), marked.Substring(start + 1, finish - start - 1)
        let position (text: string) =
            let lines = text.Split('\n')
            { Line = lines.Length; Column = (Array.last lines).Length }
        let file = "loop-binding-negative.clef"
        let expected = { File = file; Start = position (prelude + before); End = position (prelude + before + span) }
        match parseAndCheck (prelude + marked.Replace("«", "").Replace("»", "")) file with
        | CheckFailure result ->
            Assert.True(CheckResult.hasErrors result)
            let matches = result.Diagnostics |> List.filter (fun diagnostic ->
                diagnostic.Code = "CCS8009" && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)
            Assert.True(matches.Length = 1, sprintf "Expected one immutable assignment error: %A" result.Diagnostics)
            let diagnostic = Assert.Single matches
            Assert.Contains("not found or not mutable", diagnostic.Message)
            Assert.Equal<SourceRange>(expected, diagnostic.Range)
        | Success result -> failwithf "Assignment to an iteration binding reached successful checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected located immutable assignment rejection: %A" errors

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "LoopBindings")>]
type LoopBindingCases() =
    [<Theory>]
    [<InlineData("index = 1 to 3")>]
    [<InlineData("index = 3 downto 1")>]
    [<InlineData("index in 1 .. 3")>]
    member _.``Raw and saturated loops separate source values from the mutable counter``(header: string) =
        let result, raw = LoopBindings.check $"""
[<EntryPoint>]
let main _ =
    for {header} do
        let sample = fun () -> index
        ignore (sample ())
    0
"""
        let nodes = result.Graph.Nodes
        let loop = nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.WhileLoop _ -> true | _ -> false) |> Assert.Single
        let source, counter, body = LoopBindings.loopBinding result raw loop
        let reads = nodes.Values |> Seq.choose (fun node ->
            match node.Kind with SemanticKind.VarRef ("index", Some definition) -> Some (node.Id, definition) | _ -> None) |> Seq.toList
        Assert.NotEmpty reads
        for id, definition in reads do
            Assert.Equal(source, definition)
            Assert.Equal(NodeId.value source, LoopBindings.rawDefinition raw id)
        let sets = LoopBindings.descendants nodes body |> Set.toList |> List.choose (fun id ->
            match nodes[id].Kind with SemanticKind.Set (target, _) -> Some target | _ -> None)
        let target = Assert.Single sets
        Assert.Equal(counter, LoopBindings.reference nodes target)
        Assert.Equal(NodeId.value counter, LoopBindings.rawDefinition raw target)
        let capture = LoopBindings.captureFor "sample" result
        Assert.False capture.IsMutable
        Assert.Equal(Some source, capture.SourceNodeId)

    [<Fact>]
    member _.``Nested same-name loops preserve separate iteration values and capture origins``() =
        let result, raw = LoopBindings.check """
[<EntryPoint>]
let main _ =
    for index = 1 to 2 do
        let outerSample = fun () -> index
        for index in 3 .. 4 do
            let innerSample = fun () -> index
            ignore (innerSample ())
        ignore (outerSample ())
    0
"""
        let nodes = result.Graph.Nodes
        let loops = nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.WhileLoop _ -> true | _ -> false) |> Seq.toList
        Assert.Equal(2, loops.Length)
        let identities = loops |> List.map (LoopBindings.loopBinding result raw)
        let sourceIds = identities |> List.map (fun (source, _, _) -> source) |> Set.ofList
        let counterIds = identities |> List.map (fun (_, counter, _) -> counter) |> Set.ofList
        Assert.Equal(2, sourceIds.Count)
        Assert.Equal(2, counterIds.Count)
        Assert.Empty(Set.intersect sourceIds counterIds)
        let outerCapture = LoopBindings.captureFor "outerSample" result
        let innerCapture = LoopBindings.captureFor "innerSample" result
        Assert.NotEqual(outerCapture.SourceNodeId, innerCapture.SourceNodeId)
        for capture in [outerCapture; innerCapture] do
            Assert.False capture.IsMutable
            Assert.Contains(capture.SourceNodeId |> Option.get, sourceIds)
        for node in nodes.Values do
            match node.Kind with
            | SemanticKind.VarRef ("index", Some definition) -> Assert.Contains(definition, sourceIds)
            | SemanticKind.Set (target, _) -> Assert.Contains(LoopBindings.reference nodes target, counterIds)
            | _ -> ()

    [<Theory>]
    [<InlineData("index = 1 to 3")>]
    [<InlineData("index = 3 downto 1")>]
    [<InlineData("index in 1 .. 3")>]
    member _.``Source assignment to an iteration binding is rejected at the assigned value``(header: string) =
        LoopBindings.reject $"""
[<EntryPoint>]
let main _ =
    for {header} do
        index <- «9»
    0
"""

    [<Fact>]
    member _.``Nested closure cannot assign the captured immutable iteration value``() =
        LoopBindings.reject """
[<EntryPoint>]
let main _ =
    for index = 1 to 3 do
        let change = fun () -> index <- «9»
        change ()
    0
"""
