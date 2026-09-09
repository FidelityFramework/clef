namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module LocalUnusedSupport =
    let check owned source =
        let input =
            match parseStringWithDefaults source "Local.clef" with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Parse failed: %A" errors
        checkParsedInputsWithPlatformAndSources [input] None owned
    let own source = check (Set.singleton "Local.clef") source
    let warnings result = result.Diagnostics |> List.filter Diagnostic.isUnnecessary

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "LocalUnused")>]
type LocalUnusedTests() =
    [<Fact>]
    member _.``Unused measured locals warn at their names``() =
        let result = LocalUnusedSupport.own "module Local\n[<Measure>] type m\n[<Measure>] type s\n[<EntryPoint>]\nlet main _ =\n    let distance = 12<m>\n    let elapsed = 3<s>\n    0\n"
        DimensionalCases.noErrors result
        let warnings = LocalUnusedSupport.warnings result
        Assert.Equal(2, warnings.Length)
        for line, name in [6, "distance"; 7, "elapsed"] do
            let warning = warnings |> List.find (fun warning -> warning.Range.Start.Line = line)
            Assert.Equal("CCS8500", warning.Code)
            Assert.Equal(8, warning.Range.Start.Column)
            Assert.Equal(8 + name.Length, warning.Range.End.Column)

    [<Fact>]
    member _.``Resolved dimensional use clears warnings while unused values keep their range facts``() =
        let source useValues =
            "module Local\n[<Measure>] type m\n[<Measure>] type s\n[<EntryPoint>]\nlet main _ =\n    let distance = 12<m>\n    let elapsed = 3<s>\n    "
            + (if useValues then "if distance / elapsed > 0<m/s> then 0 else 1\n" else "0\n")
        let unused = LocalUnusedSupport.own (source false)
        DimensionalCases.noErrors unused
        for name, expected in ["distance", 12I; "elapsed", 3I] do
            let node = unused.Graph.Nodes.Values |> Seq.find (fun node ->
                match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
            Assert.Equal(Some (ValueRange.point expected), node.ValueRange)
            Assert.True(node.IsReachable, "Unused-value reporting removed the source binding")
        let used = LocalUnusedSupport.own (source true)
        DimensionalCases.noErrors used
        Assert.Empty(LocalUnusedSupport.warnings used)

    [<Fact>]
    member _.``Shadowed locals count references by declaration identity``() =
        let result = LocalUnusedSupport.own "module Local\n[<Measure>] type m\n[<EntryPoint>]\nlet main _ =\n    let distance = 12<m>\n    let distance = 24<m>\n    if distance > 0<m> then 0 else 1\n"
        DimensionalCases.noErrors result
        let warning = Assert.Single(LocalUnusedSupport.warnings result)
        Assert.Equal(5, warning.Range.Start.Line)
        let target = result.Graph.Nodes[warning.RelatedNodes.Head]
        Assert.Equal(Some (ValueRange.point 12I), target.ValueRange)

    [<Fact>]
    member _.``A nested function capture is a use of the local value``() =
        let result = LocalUnusedSupport.own "module Local\n[<Measure>] type m\n[<EntryPoint>]\nlet main _ =\n    let distance = 12<m>\n    let exceeds () = distance > 0<m>\n    if exceeds () then 0 else 1\n"
        DimensionalCases.noErrors result
        Assert.Empty(LocalUnusedSupport.warnings result)

    [<Fact>]
    member _.``Unused reporting preserves scope and substitution exemptions``() =
        let source = "module Local\nlet publicValue = 42\n[<Literal>]\nlet constant = 7\n[<EntryPoint>]\nlet main _ =\n    let _reserved = 12\n    let mutable state = 3\n    let inline identity value = value\n    let inline unusedInline value = value\n    identity constant\n"
        let own = LocalUnusedSupport.own source
        DimensionalCases.noErrors own
        Assert.Empty(LocalUnusedSupport.warnings own)
        let dependency = LocalUnusedSupport.check Set.empty "module Local\n[<EntryPoint>]\nlet main _ =\n    let unused = 12\n    0\n"
        DimensionalCases.noErrors dependency
        Assert.Empty(LocalUnusedSupport.warnings dependency)
        let library = LocalUnusedSupport.own "module Local\nlet publicApi parameter =\n    let unused = 12\n    0\n"
        DimensionalCases.noErrors library
        Assert.Empty(LocalUnusedSupport.warnings library)

    [<Fact>]
    member _.``Unused effectful initializer retains its effect and warns only on the name``() =
        let result = LocalUnusedSupport.own "module Local\n[<EntryPoint>]\nlet main _ =\n    let mutable state = 0\n    let ignored = state <- 1\n    state\n"
        DimensionalCases.noErrors result
        let warning = Assert.Single(LocalUnusedSupport.warnings result)
        Assert.Equal(5, warning.Range.Start.Line)
        Assert.Equal(8, warning.Range.Start.Column)
        Assert.Equal(15, warning.Range.End.Column)
        Assert.Contains(result.Graph.Nodes.Values, fun node -> node.IsReachable && (match node.Kind with SemanticKind.Set _ -> true | _ -> false))

    [<Fact>]
    member _.``A failed local initializer does not receive a secondary unused warning``() =
        let result = LocalUnusedSupport.own "module Local\n[<EntryPoint>]\nlet main _ =\n    let broken = missing\n    0\n"
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8009")
        Assert.Empty(LocalUnusedSupport.warnings result)
