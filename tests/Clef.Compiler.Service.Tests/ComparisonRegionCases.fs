namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module RegionEmission = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission

module private ComparisonRegionFixture =
    let source prefix operator =
        $"module ComparisonRegions\n{prefix}let first (left: float) (right: float) = left < right\nlet second (left: float) (right: float) = left {operator} right\n[<EntryPoint>]\nlet main _ = if first 1.25 2.5 && second 1.25 2.5 then 0 else 1\n"
    let prepare authority source =
        let result = RealComparisonFixture.check authority source
        DimensionalCases.noErrors result
        RegionEmission.prepare result.Graph |> Result.defaultWith (sprintf "%A" >> failwith)
    let regions (graph: SemanticGraph) =
        graph.Codata.Value.WitnessSegmentation.Value.Regions
        |> List.map (fun region -> region.Identity, region) |> Map.ofList
    let first = "callable:ComparisonRegions:first"
    let second = "callable:ComparisonRegions:second"
    let get name graph =
        let rows = regions graph
        Assert.True(rows.ContainsKey name, sprintf "Missing independent region %s: %A" name rows.Keys)
        rows[name]

    // These controls isolate the segmentation projector from source admission.
    // A manually edited contract is not claimed to be a newly settled graph.
    let ownedContract (region: WitnessRegion) (graph: SemanticGraph) =
        graph.Codata.Value.CallableContracts.Values
        |> Seq.filter (fun contract ->
            contract.Participants |> List.exists (fun participant ->
                participant.Role = ParticipantRole.CallableImplementation &&
                participant.Group = contract.Identity && participant.Ordinal = 0 &&
                Some participant.Node = region.Root))
        |> Assert.Single
    let projectContracts (contracts: Map<NodeId, CallableContract>) (graph: SemanticGraph) =
        let held = graph.Codata.Value
        let emission = held.WitnessEmission.Value
        let emission = {emission with Callable = {emission.Callable with Contracts = contracts}}
        let changed = {graph with Codata = lazy {held with CallableContracts = contracts}}
        let scope =
            Clef.Compiler.Baker.Recipes.WitnessScopeRecipes.projectWithEmission emission changed
            |> Result.defaultWith (sprintf "%A" >> failwith)
        let segmentation = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessSegmentation.project changed emission scope
        changed, segmentation

type ComparisonRegionCases() =
    [<Theory>]
    [<InlineData("=")>]
    [<InlineData("<>")>]
    [<InlineData("<")>]
    [<InlineData("<=")>]
    [<InlineData(">")>]
    [<InlineData(">=")>]
    member _.``Settled real comparisons retain exact regions across fresh checks and renumbering`` operator =
        let before = ComparisonRegionFixture.prepare RealComparisonFixture.authority (ComparisonRegionFixture.source "" operator)
        let after = ComparisonRegionFixture.prepare RealComparisonFixture.authority (ComparisonRegionFixture.source "let extra () = false\n" operator)
        for name in [ComparisonRegionFixture.first; ComparisonRegionFixture.second] do
            let original = ComparisonRegionFixture.get name before
            let current = ComparisonRegionFixture.get name after
            Assert.NotEqual<NodeId option>(original.Root, current.Root)
            Assert.Equal(original.Fingerprint, current.Fingerprint)
            // Current proof support is deliberately conservative. Retention of
            // witness output never reuses the previous revision's proof receipt.
            Assert.True(Set.isSubset (after.Nodes.Keys |> Set.ofSeq) current.Supports)
            let contracts = after.Codata.Value.CallableContracts.Values |> Seq.filter (fun contract ->
                contract.Participants |> List.exists (fun participant ->
                    participant.Role = ParticipantRole.CallableImplementation && Some participant.Node = current.Root)) |> Seq.toList
            Assert.NotEmpty contracts
            for contract in contracts do
                Assert.False(current.Members.Contains contract.Identity)
                for participant in contract.Participants do
                    if after.Nodes.ContainsKey participant.Node then Assert.Contains(participant.Node, current.Supports)
            let operations = after.Codata.Value.WitnessEmission.Value.Numeric.Operations.Values |> Seq.filter (fun row -> current.Members.Contains row.Site)
            let operation = Assert.Single operations
            Assert.Contains(operation.Declaration.Value, current.Supports)
            Assert.True(Set.isSubset operation.Participants current.Supports)
            for operand in operation.Operands do
                Assert.True(Set.isSubset operand.Carrier.Value.Participants current.Supports)

    [<Fact>]
    member _.``Editing a comparison invalidates only its scalar witness region`` () =
        let prepare op = ComparisonRegionFixture.prepare RealComparisonFixture.authority (ComparisonRegionFixture.source "" op)
        let before, after = prepare "<", prepare ">"
        let region name graph = (ComparisonRegionFixture.get name graph).Fingerprint
        Assert.Equal(region ComparisonRegionFixture.first before, region ComparisonRegionFixture.first after)
        Assert.NotEqual<string>(region ComparisonRegionFixture.second before, region ComparisonRegionFixture.second after)

    [<Fact>]
    member _.``Numeric declaration renumbering preserves the same complete interface`` () =
        let source = ComparisonRegionFixture.source "" "<"
        let before = ComparisonRegionFixture.prepare RealComparisonFixture.authority source
        let authority = RealComparisonFixture.authority.Replace("module WriteAuthority", "module WriteAuthority\nlet unrelated () = false")
        let after = ComparisonRegionFixture.prepare authority source
        let get graph =
            let region = ComparisonRegionFixture.get ComparisonRegionFixture.first graph
            let operation = graph.Codata.Value.WitnessEmission.Value.Numeric.Operations.Values |> Seq.filter (fun row -> region.Members.Contains row.Site) |> Assert.Single
            region, operation
        let original, oldOperation = get before
        let current, newOperation = get after
        Assert.NotEqual<NodeId option>(oldOperation.Declaration, newOperation.Declaration)
        Assert.Equal(original.Fingerprint, current.Fingerprint)

    [<Fact>]
    member _.``Comparison region retains the complete offered source format declaration`` () =
        let source = ComparisonRegionFixture.source "" "<"
        let before = ComparisonRegionFixture.prepare RealComparisonFixture.authority source
        // The format boundary is an explicit source interface field even when
        // this comparison has no arithmetic result requiring an adaptation.
        let authority = RealComparisonFixture.authority.Replace("MaxMagnitude = \"1.7976931348623157e308\"; Boundary = \"wrap\"", "MaxMagnitude = \"1.7976931348623157e308\"; Boundary = \"exact\"")
        let after = ComparisonRegionFixture.prepare authority source
        Assert.NotEqual<string>((ComparisonRegionFixture.get ComparisonRegionFixture.first before).Fingerprint, (ComparisonRegionFixture.get ComparisonRegionFixture.first after).Fingerprint)
        let operation = before.Codata.Value.WitnessEmission.Value.Numeric.Operations.Values |> Seq.find (fun row -> (ComparisonRegionFixture.get ComparisonRegionFixture.first before).Members.Contains row.Site)
        let declaration = before.Nodes[operation.Declaration.Value]
        let stale = { before with Nodes = before.Nodes.Add(declaration.Id, { declaration with Children = [] }) }
        Assert.True(RegionEmission.admit stale |> Result.isError)

    [<Fact>]
    member _.``Platform target edits invalidate comparison fingerprints`` () =
        let graph = ComparisonRegionFixture.prepare RealComparisonFixture.authority (ComparisonRegionFixture.source "" "<")
        let before = ComparisonRegionFixture.get ComparisonRegionFixture.first graph
        let platform = graph.Platform.Value
        let changed = { graph with Platform = Some { platform with Dimensions = platform.Dimensions.Add("Register", 32) } }
        let emission = graph.Codata.Value.WitnessEmission.Value
        let sourceScope = Clef.Compiler.Baker.Recipes.WitnessScopeRecipes.projectWithEmission emission changed |> Result.defaultWith (sprintf "%A" >> failwith)
        let after = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessSegmentation.project changed emission sourceScope
        let current = after.Regions |> List.find (fun region -> region.Identity = before.Identity)
        Assert.NotEqual<string>(before.Fingerprint, current.Fingerprint)
        Assert.True(RegionEmission.admit changed |> Result.isError)

    [<Theory>]
    [<InlineData("live")>]
    [<InlineData("different-prefix")>]
    [<InlineData("extra-child")>]
    member _.``Only the exact retired comparison prefix may share a region actual`` defect =
        let graph = ComparisonRegionFixture.prepare RealComparisonFixture.authority (ComparisonRegionFixture.source "" "<")
        let region = ComparisonRegionFixture.get ComparisonRegionFixture.first graph
        let emission = graph.Codata.Value.WitnessEmission.Value
        let operation = emission.Numeric.Operations.Values |> Seq.filter (fun row -> region.Members.Contains row.Site) |> Assert.Single
        let first, second = operation.Operands[0].Actual, operation.Operands[1].Actual
        let parent = graph.Nodes.Values |> Seq.filter (fun node -> not (region.Members.Contains node.Id) && List.contains first node.Children) |> Assert.Single
        Assert.False(parent.IsReachable)
        Assert.True(parent.Parent.IsNone)
        Assert.Contains(parent.Id, region.Supports)
        let common = (ComparisonRegionFixture.regions graph).Item "common"
        Assert.DoesNotContain(parent.Id, common.Members)
        let changed =
            match defect, parent.Kind with
            | "live", _ -> { parent with IsReachable = true }
            | "different-prefix", SemanticKind.Application(callee, _) -> { parent with Kind = SemanticKind.Application(callee, [second]); Children = [callee; second] }
            | _ -> { parent with Children = parent.Children @ [second] }
        let stale = { graph with Nodes = graph.Nodes.Add(parent.Id, changed) }
        let sourceScope = Clef.Compiler.Baker.Recipes.WitnessScopeRecipes.projectWithEmission emission stale |> Result.defaultWith (sprintf "%A" >> failwith)
        let segmentation = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessSegmentation.project stale emission sourceScope
        Assert.DoesNotContain(segmentation.Regions, fun row -> row.Identity = region.Identity)
        Assert.True(RegionEmission.admit stale |> Result.isError)

    [<Theory>]
    [<InlineData("missing")>]
    [<InlineData("duplicate")>]
    member _.``Unsettled or ambiguous comparison formats never acquire independent regions`` defect =
        let authority =
            if defect = "missing" then IntrinsicWriteFixture.authority else
            RealComparisonFixture.authority.Replace("Representations = [|", "Representations = [| { Name = \"other64\"; Capability = \"native\"; Family = \"ieee\"; Bits = 64; MinMagnitude = \"-1.7976931348623157e308\"; MaxMagnitude = \"1.7976931348623157e308\"; Boundary = \"wrap\" }; ")
        let result = RealComparisonFixture.check authority (ComparisonRegionFixture.source "" "<")
        Assert.True(RegionEmission.prepare result.Graph |> Result.isError)

    [<Theory>]
    [<InlineData("let helper (value: float) = value\n", "helper left < right")>]
    [<InlineData("", "let mutable cell = left in cell < right")>]
    member _.``Ordinary calls and storage remain in the common region`` (prefix, body) =
        let source = $"module ComparisonRegions\n{prefix}let first (left: float) (right: float) = {body}\n[<EntryPoint>]\nlet main _ = if first 1.25 2.5 then 0 else 1\n"
        let result = RealComparisonFixture.check RealComparisonFixture.authority source
        let graph = RegionEmission.prepare result.Graph |> Result.defaultWith (sprintf "%A" >> failwith)
        Assert.False((ComparisonRegionFixture.regions graph).ContainsKey ComparisonRegionFixture.first)

    [<Fact>]
    member _.``Callable support changes retain scalar fingerprints and current support`` () =
        let graph = ComparisonRegionFixture.prepare RealComparisonFixture.authority (ComparisonRegionFixture.source "" "<")
        let before = ComparisonRegionFixture.get ComparisonRegionFixture.first graph
        let contract = ComparisonRegionFixture.ownedContract before graph
        let source, premise =
            contract.SourcePremises |> Map.toSeq |> Seq.find (fun (id, _) ->
                graph.Nodes.TryFind id |> Option.exists (fun node -> node.Children.IsEmpty))
        let support = {graph.Nodes[source] with Id = NodeId.fresh(); IsReachable = false}
        let nextOrdinal =
            contract.Participants |> List.filter (fun participant -> participant.Role = ParticipantRole.Source)
            |> List.map _.Ordinal |> List.fold max -1 |> (+) 1
        let participant : Participant =
            {Role = ParticipantRole.Source; Group = contract.Identity; Ordinal = nextOrdinal; Node = support.Id}
        let changedContract =
            {contract with
                SourcePremises = contract.SourcePremises.Add(support.Id, {premise with Reachable = false})
                Participants = contract.Participants @ [participant]}
        let contracts = graph.Codata.Value.CallableContracts.Add(contract.Identity, changedContract)
        let changed, segmentation =
            ComparisonRegionFixture.projectContracts contracts {graph with Nodes = graph.Nodes.Add(support.Id, support)}
        let current = segmentation.Regions |> Seq.filter (fun row -> row.Identity = before.Identity) |> Assert.Single
        Assert.Equal(before.Fingerprint, current.Fingerprint)
        Assert.DoesNotContain(support.Id, before.Supports)
        Assert.Contains(support.Id, current.Supports)
        Assert.NotEqual<Map<NodeId, BoundarySourcePremise>>(contract.SourcePremises, changed.Codata.Value.CallableContracts[contract.Identity].SourcePremises)
        Assert.Equal<Participant list>(changedContract.Participants, changed.Codata.Value.CallableContracts[contract.Identity].Participants)
        // Local fingerprint erasure never grants publication or proof authority.
        Assert.True(RegionEmission.admit changed |> Result.isError)

    [<Fact>]
    member _.``A callable interface only edit changes its scalar fingerprint`` () =
        let graph = ComparisonRegionFixture.prepare RealComparisonFixture.authority (ComparisonRegionFixture.source "" "<")
        let before = ComparisonRegionFixture.get ComparisonRegionFixture.first graph
        let contract = ComparisonRegionFixture.ownedContract before graph
        Assert.Equal<int option>(None, contract.EnvironmentBytes)
        let changedContract = {contract with EnvironmentBytes = Some 0}
        let contracts = graph.Codata.Value.CallableContracts.Add(contract.Identity, changedContract)
        let changed, segmentation = ComparisonRegionFixture.projectContracts contracts graph
        Assert.Same(graph.Nodes, changed.Nodes)
        Assert.Same(graph.Edges, changed.Edges)
        Assert.Equal<Map<NodeId, BoundarySourcePremise>>(contract.SourcePremises, changedContract.SourcePremises)
        Assert.Equal<Participant list>(contract.Participants, changedContract.Participants)
        match segmentation.Regions |> List.tryFind (fun row -> row.Identity = before.Identity) with
        | Some current -> Assert.NotEqual<string>(before.Fingerprint, current.Fingerprint)
        | None -> ()
        Assert.True(RegionEmission.admit changed |> Result.isError)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Native receiving contracts exclude scalar reuse with or without an ordinary contract`` keepOrdinary =
        let graph = ComparisonRegionFixture.prepare RealComparisonFixture.authority (ComparisonRegionFixture.source "" "<")
        let before = ComparisonRegionFixture.get ComparisonRegionFixture.first graph
        let contract = ComparisonRegionFixture.ownedContract before graph
        let identity = if keepOrdinary then NodeId.fresh() else contract.Identity
        let participants =
            contract.Participants |> List.map (fun participant ->
                {participant with
                    Group = identity
                    Node = if participant.Role = ParticipantRole.CallableContract then identity else participant.Node})
        // The projector's candidate policy must refuse native classification
        // before it could silently omit any unsupported native interface field.
        // Source admission separately rejects this deliberately unrenewed row.
        let native = {contract with Identity = identity; Kind = CallableKind.NativeEntry; Participants = participants}
        let contracts = graph.Codata.Value.CallableContracts.Add(identity, native)
        let changed, segmentation = ComparisonRegionFixture.projectContracts contracts graph
        Assert.DoesNotContain(segmentation.Regions, fun row -> row.Identity = before.Identity)
        let common = segmentation.Regions |> Seq.filter (fun row -> row.Identity = "common") |> Assert.Single
        Assert.True(Set.isSubset before.Members common.Members)
        Assert.True(RegionEmission.admit changed |> Result.isError)
