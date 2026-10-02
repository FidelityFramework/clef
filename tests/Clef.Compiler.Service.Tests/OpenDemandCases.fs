// Normative: clef-lang-spec/spec/{inference-name-resolution,program-hypergraph}.md
namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module OpenDemandCases =
    let private check files =
        let inputs =
            files |> List.map (fun (file, source) ->
                match parseStringWithDefaults source file with
                | ParseSuccess input -> input
                | ParseError errors -> failwithf "Open-demand fixture did not parse at %s: %A" file errors)
        // Dependencies are visible to resolution. Only the application owns
        // program startup; the fixtures contain no eager dependency effects.
        let result = checkParsedInputsWithPlatformAndSources inputs None (Set.singleton "OpenClient.clef")
        let errors = result.Diagnostics |> List.filter (fun diagnostic -> diagnostic.Severity = NativeDiagnosticSeverity.Error)
        if not errors.IsEmpty then failwithf "Open-demand fixture was not admitted: %A" errors
        result.Graph

    let private declarations (graph: SemanticGraph) =
        graph.Nodes.Values
        |> Seq.collect (fun node ->
            match node.Kind with SemanticKind.ModuleDef(_, members) -> members | _ -> [])
        |> Set.ofSeq

    let private binding file name (graph: SemanticGraph) =
        let members = declarations graph
        graph.Nodes.Values
        |> Seq.filter (fun node ->
            members.Contains node.Id && node.Range.File = file
            && match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
        |> Assert.Single

    let private liveIn file (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node -> node.Range.File = file && node.IsReachable) |> Seq.toList

    let private liveDeclarations file (graph: SemanticGraph) =
        let members = declarations graph
        liveIn file graph
        |> List.choose (fun node ->
            match node.Kind with
            | SemanticKind.Binding(name, _, _, _) when members.Contains node.Id -> Some name
            | _ -> None)
        |> Set.ofList

    let private application opens body =
        "module OpenClient\n" + opens + "\n[<EntryPoint>]\nlet main _ = " + body + "\n"

    let private library =
        "module OpenLibrary\n"
        + "let leaf (value: int) = value + 1\n"
        + "let selected (value: int) = leaf value\n"
        + "let dormantLeaf (value: int) = value - 1\n"
        + "let dormant (value: int) = dormantLeaf value\n"

    let private checkLibrary librarySource opens body =
        check ["OpenLibrary.clef", librarySource; "OpenClient.clef", application opens body]

    let private requireReference file line name expectedFile (graph: SemanticGraph) =
        let expected = binding expectedFile name graph
        let references =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.VarRef(_, Some target)
                    when node.IsReachable && node.Range.File = file && node.Range.Start.Line = line
                         && (match graph.Nodes[target].Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false) ->
                    Some target
                | _ -> None)
            |> Seq.toList
        Assert.Equal<NodeId list>([expected.Id], references)
        Assert.True(expected.IsReachable, "The consumed declaration was not demanded")

    let tests = [
        "An unused open does not activate pure library declarations", fun () ->
            let absent = checkLibrary library "// open OpenLibrary" "0"
            let opened = checkLibrary library "open OpenLibrary" "0"
            for graph in [absent; opened] do
                // Require resident source declarations so empty reachability
                // cannot pass merely because the library was not checked.
                Assert.NotEmpty(graph.Nodes.Values |> Seq.filter (fun node -> node.Range.File = "OpenLibrary.clef"))
                Assert.Empty(liveIn "OpenLibrary.clef" graph)
                for name in ["leaf"; "selected"; "dormantLeaf"; "dormant"] do
                    Assert.False((binding "OpenLibrary.clef" name graph).IsReachable)
            Assert.Equal(liveIn "OpenClient.clef" absent |> List.length, liveIn "OpenClient.clef" opened |> List.length)

        "A resolved use demands its declaration closure without dormant siblings", fun () ->
            let graph = checkLibrary library "open OpenLibrary" "selected 2"
            Assert.Equal<Set<string>>(Set.ofList ["leaf"; "selected"], liveDeclarations "OpenLibrary.clef" graph)
            requireReference "OpenClient.clef" 4 "selected" "OpenLibrary.clef" graph
            requireReference "OpenLibrary.clef" 3 "leaf" "OpenLibrary.clef" graph
            for line in [4; 5] do
                Assert.DoesNotContain(liveIn "OpenLibrary.clef" graph, fun node -> node.Range.Start.Line = line)

        "Adding and removing an open replaces the consumed unqualified binding", fun () ->
            let providers = [
                "Earlier.clef", "module Earlier\nlet choose (value: int) = value + 1\nlet unusedEarlier (value: int) = value - 1\n"
                "Later.clef", "module Later\nlet choose (value: int) = value + 2\nlet unusedLater (value: int) = value - 2\n" ]
            let run laterOpen =
                check (providers @ [("OpenClient.clef", application ("open Earlier\n" + laterOpen) "choose 2")])
            for laterOpen, expected, withdrawn in [
                "// open Later", "Earlier.clef", "Later.clef"
                "open Later", "Later.clef", "Earlier.clef"
                "// open Later", "Earlier.clef", "Later.clef" ] do
                let graph = run laterOpen
                requireReference "OpenClient.clef" 5 "choose" expected graph
                Assert.Equal<Set<string>>(Set.singleton "choose", liveDeclarations expected graph)
                Assert.Empty(liveIn withdrawn graph)

        "Growth of an unused library region does not enlarge the demanded declaration set", fun () ->
            let expanded =
                library + ([1..64] |> List.map (fun index -> $"let extra{index} (value: int) = value + {index}\n") |> String.concat "")
            let original = checkLibrary library "open OpenLibrary" "selected 2"
            let grown = checkLibrary expanded "open OpenLibrary" "selected 2"
            Assert.True(grown.Nodes.Count > original.Nodes.Count, "The dependency-growth control did not add retained source nodes")
            Assert.Equal<Set<string>>(liveDeclarations "OpenLibrary.clef" original, liveDeclarations "OpenLibrary.clef" grown)
            Assert.Equal(liveIn "OpenLibrary.clef" original |> List.length, liveIn "OpenLibrary.clef" grown |> List.length)
            Assert.DoesNotContain(liveIn "OpenLibrary.clef" grown, fun node -> node.Range.Start.Line > 5)
    ]

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "OpenDemand")>]
type OpenDemandTests() =
    static member Cases = OpenDemandCases.tests |> Seq.map (fun (name, _) -> [| box name |])

    [<Theory; MemberData(nameof OpenDemandTests.Cases)>]
    member _.``Open visibility and executable demand``(name: string) =
        OpenDemandCases.tests |> List.find (fun (testName, _) -> testName = name) |> snd |> fun test -> test ()
