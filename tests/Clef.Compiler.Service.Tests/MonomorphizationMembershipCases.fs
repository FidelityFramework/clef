namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private MonomorphizationMembership =
    let modules (result: CheckResult) =
        result.Graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.ModuleDef (_, members) -> Some (node, members)
            | _ -> None) |> Seq.toList

    let assertReferences (result: CheckResult) =
        let moduleNodes = modules result
        Assert.NotEmpty moduleNodes
        for node, members in moduleNodes do
            Assert.Empty node.Children
            let membership = kindEdges node.Id node.Kind |> List.filter (fun edge -> edge.Role = EdgeRole.Member) |> List.sortBy _.Ordinal
            Assert.Equal<NodeId list>(members, membership |> List.collect _.Sources)
            Assert.All(membership, fun edge -> Assert.Equal(EdgeClass.Reference, edge.Class))
            for memberId in members do
                Assert.True(result.Graph.Nodes.ContainsKey memberId,
                    $"Module {node.Id} still references retired declaration {memberId}")
                Assert.Equal(Some node.Id, result.Graph.Nodes[memberId].Parent)
        for node in result.Graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable) do
            for child in node.Children do
                Assert.True(result.Graph.Nodes.ContainsKey child,
                    $"Reachable node {node.Id} references missing child {child}")

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "MonomorphizationMembership")>]
type MonomorphizationMembershipTests() =
    [<Fact>]
    member _.``Specialized declarations replace their generic module member before parent linkage``() =
        let result = DimensionalCases.check """
let before = 2
let keep (value: 'a) : 'a = value
let after = 3
[<EntryPoint>]
let main _ =
    let number = keep before
    let enabled = keep true
    if enabled then number + after else 0
"""
        DimensionalCases.noErrors result
        MonomorphizationMembership.assertReferences result
        let namedBindings =
            result.Graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.Binding (name, _, _, _) -> Some (name, node.Id)
                | _ -> None)
            |> Map.ofSeq
        Assert.False(namedBindings.ContainsKey "keep")
        let clones = namedBindings |> Map.toList |> List.filter (fun (name, _) -> name.StartsWith("keep__mono"))
        Assert.Equal(2, clones.Length)
        let before = namedBindings["before"]
        let after = namedBindings["after"]
        let _, members = MonomorphizationMembership.modules result |> List.find (fun (_, members) -> List.contains before members)
        let beforeIndex = List.findIndex ((=) before) members
        let afterIndex = List.findIndex ((=) after) members
        Assert.Equal(beforeIndex + clones.Length + 1, afterIndex)
        for _, clone in clones do
            let cloneIndex = List.findIndex ((=) clone) members
            Assert.True(beforeIndex < cloneIndex && cloneIndex < afterIndex)

    [<Fact>]
    member _.``Removing an unused generic removes its module membership too``() =
        let result = DimensionalCases.check """
let unused (value: 'a) : 'a = value
[<EntryPoint>]
let main _ = 0
"""
        DimensionalCases.noErrors result
        MonomorphizationMembership.assertReferences result
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            match node.Kind with
            | SemanticKind.Binding ("unused", _, _, _) -> true
            | _ -> false)
