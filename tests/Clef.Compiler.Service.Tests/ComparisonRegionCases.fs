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

    // A declared extern with an explicit result hypothesis, in its own source
    // unit beside the comparison program. Nothing in the comparison program
    // calls it unless a case says so. This is the platform-library shape that
    // left every default-profile program without scalar regions.
    let foreignDeclarations = """module Foreign
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Pointer of int | Void
type PassBy = Value | Reference
type CallConv = | CDecl
type Transfer = Borrowed | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type ResultBound = Constant of int | Argument of int
type ResultRole = | ReturnValue
type ExternalExecutionHypothesis = { Identity:string; Version:string; Source:string }
type ResultRangeDescriptor = { Binding:string; Role:ResultRole; Hypothesis:ExternalExecutionHypothesis; Lower:ResultBound; Upper:ResultBound }
[<FidelityExtern("c", "native_read")>]
let read (count: int) : int = NativeDefault.zeroed ()
let readDescriptor: Expr<FunctionDescriptor> = <@ {
    CName="native_read"; Parameters=[| {Name="count";Type=Integer(Unsigned,32);PassBy=Value} |]
    ReturnType=Integer(Signed,64); CallingConvention=CDecl; OwnershipTransfer=Undeclared } @>
let readRange: Expr<ResultRangeDescriptor> = <@ {
    Binding="Foreign.read"; Role=ResultRole.ReturnValue
    Hypothesis={Identity="fixture.read";Version="1";Source="foreign.clef:synthetic-pilot"}
    Lower=Constant (-1); Upper=Argument 0 } @>
"""
    let prepareBeside authority (declarations: string option) source =
        let parse text path =
            match Clef.Compiler.NativeService.parseStringWithDefaults text path with
            | Clef.Compiler.NativeService.ParseSuccess input -> input
            | Clef.Compiler.NativeService.ParseError errors -> failwithf "%A" errors
        let platform =
            { IntrinsicWriteFixture.platform with
                Representations = IntrinsicWriteFixture.platform.Representations.Add(RealComparisonFixture.representation.Name, RealComparisonFixture.representation) }
        let inputs =
            [ parse authority "write-authority.clef" ]
            @ (declarations |> Option.map (fun text -> [ parse text "foreign.clef" ]) |> Option.defaultValue [])
            @ [ parse source "real-comparison.clef" ]
        let result = Clef.Compiler.NativeService.checkParsedInputsWithPlatform inputs (Some platform)
        DimensionalCases.noErrors result
        RegionEmission.prepare result.Graph |> Result.defaultWith (sprintf "%A" >> failwith)
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
    [<Fact>]
    member _.``Domain authority presence and node rows reach their consumers`` () =
        let graph = ComparisonRegionFixture.prepare RealComparisonFixture.authority (ComparisonRegionFixture.source "" "<")
        let segment graph = Clef.Compiler.PSGSaturation.SemanticGraph.Segmentation.segment graph |> Result.defaultWith (sprintf "%A" >> failwith)
        let first = "module:ComparisonRegions/binding:first"
        let second = "module:ComparisonRegions/binding:second"
        let root = (segment graph).Regions[first].Root
        let change numeric boundary =
            { graph with
                Edges =
                    graph.Edges |> List.map (fun edge ->
                        match edge.Role with
                        | EdgeRole.NumericDomain domain -> { edge with Role = EdgeRole.NumericDomain(numeric domain) }
                        | EdgeRole.BoundaryDomain domain -> { edge with Role = EdgeRole.BoundaryDomain(boundary domain) }
                        | _ -> edge) }
        let assertChanged before after =
            let schedule = Clef.Compiler.PSGSaturation.SemanticGraph.Rebuild.scheduleRebuild before after |> Result.defaultWith (sprintf "%A" >> failwith)
            Assert.NotEqual(schedule.Baseline.Regions[first].CanonicalProofSupportDigest, schedule.Candidate.Regions[first].CanonicalProofSupportDigest)
            Assert.Equal(Clef.Compiler.PSGSaturation.SemanticGraph.Rebuild.RegionDisposition.Reelaborate, schedule.Regions[first])
        let absent = change (fun d -> { d with FiniteCellRelations = None }) (fun d -> { d with StringOriginRelations = None })
        let finite = change (fun d -> { d with FiniteCellRelations = Some [] }) (fun d -> { d with StringOriginRelations = None })
        let boundary = change (fun d -> { d with FiniteCellRelations = None }) (fun d -> { d with StringOriginRelations = Some [] })
        assertChanged absent finite
        assertChanged absent boundary
        let noCaptures = change (fun d -> { d with CaptureRelations = [] }) id
        let captured = change (fun d -> { d with CaptureRelations = [EdgeClass.Obligation, true, 0, [root], root] }) id
        assertChanged noCaptures captured
        let schedule = Clef.Compiler.PSGSaturation.SemanticGraph.Rebuild.scheduleRebuild noCaptures captured |> Result.defaultWith (sprintf "%A" >> failwith)
        Assert.Equal(Clef.Compiler.PSGSaturation.SemanticGraph.Rebuild.RegionDisposition.Retained, schedule.Regions[second])
        let assertScoped before after =
            assertChanged before after
            let schedule = Clef.Compiler.PSGSaturation.SemanticGraph.Rebuild.scheduleRebuild before after |> Result.defaultWith (sprintf "%A" >> failwith)
            Assert.True(schedule.Baseline.SupportEdges <> schedule.Candidate.SupportEdges)
            Assert.Equal(Clef.Compiler.PSGSaturation.SemanticGraph.Rebuild.RegionDisposition.Retained, schedule.Regions[second])
        let cell : FiniteCellSourceRelation =
            { Class = EdgeClass.Range; Kind = FiniteCellRelationKind.Named "fixture"; Ordinal = 0; Sources = [root]; Target = root }
        let finiteRow = change (fun d -> { d with FiniteCellRelations = Some [cell] }) (fun d -> { d with StringOriginRelations = None })
        assertScoped finite finiteRow
        let origin : StringOriginRelation =
            { Recorded = true; Class = EdgeClass.Boundary; Flavor = StringOriginRelationKind.Named "fixture"; Ordinal = 0; Sources = [root]; Target = root }
        let boundaryRow = change (fun d -> { d with FiniteCellRelations = None }) (fun d -> { d with StringOriginRelations = Some [origin] })
        assertScoped boundary boundaryRow
        let sequence : SequenceRangeAuthority =
            { Participants = Set.empty; Enumerators = Set.empty; Premises = Map.empty; Relations = []; Obligations = [] }
        let noSequence = change (fun d -> { d with SequenceRangeAuthority = None }) id
        let emptySequence = change (fun d -> { d with SequenceRangeAuthority = Some sequence }) id
        let sequenceRow = change (fun d -> { d with SequenceRangeAuthority = Some { sequence with Participants = Set.singleton root } }) id
        assertChanged noSequence emptySequence
        assertScoped emptySequence sequenceRow
        let contexts : RangeContextFacts =
            { ContextDepth = 0; Invocations = []; Values = Map.empty; Reads = Map.empty; Premises = Map.empty
              SourceRelations = Ok []; CaptureRelations = []; Platform = None; Roots = [] }
        let noContexts = change (fun d -> { d with RangeContextFacts = None }) id
        let emptyContexts = change (fun d -> { d with RangeContextFacts = Some contexts }) id
        let contextRow = change (fun d -> { d with RangeContextFacts = Some { contexts with Roots = [root, DeclRoot.EntryPoint] } }) id
        assertChanged noContexts emptyContexts
        assertScoped emptyContexts contextRow
        let sourceRelation : SourceRangeRelation =
            { Class = EdgeClass.Range; Kind = SourceRangeRelationKind.Named "fixture"; Ordinal = 0; Sources = [root]; Target = root }
        let relationRow = change (fun d -> { d with RangeContextFacts = Some { contexts with SourceRelations = Ok [sourceRelation] } }) id
        assertScoped emptyContexts relationRow

    [<Fact>]
    member _.``Scalar proof support normalizes obligation identities and source coordinates`` () =
        let graph = ComparisonRegionFixture.prepare RealComparisonFixture.authority (ComparisonRegionFixture.source "" "<")
        let region = ComparisonRegionFixture.get ComparisonRegionFixture.first graph
        let originalEmission = graph.Codata.Value.WitnessEmission.Value
        let operation = originalEmission.Numeric.Operations.Values |> Seq.find (fun row -> region.Members.Contains row.Site)
        let info : ObligationInfo =
            { Id = "claim_100"; Kind = "fixture"; Logic = "QF_LIA"; Statement = "fixture"
              Source = "comparison.clef:1:2"; Refs = []; Body = ObligationBody.StorageReservation(3, 4) }
        let obligation = Clef.Compiler.Baker.Ingredients.Obligations.obligationNode graph.Nodes[operation.Site] 0 info
        let project info =
            let changed = { graph with Nodes = graph.Nodes.Add(obligation.Id, { obligation with Kind = SemanticKind.Obligation info }) }
            let operation = { operation with Obligations = [obligation.Id] }
            let numeric = { originalEmission.Numeric with Operations = originalEmission.Numeric.Operations.Add(operation.Site, operation) }
            let emission = { originalEmission with Numeric = numeric }
            let scope = Clef.Compiler.Baker.Recipes.WitnessScopeRecipes.projectWithEmission emission changed |> Result.defaultWith (sprintf "%A" >> failwith)
            let projection = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessSegmentation.project changed emission scope
            (projection.Regions |> List.find (fun row -> row.Identity = region.Identity)).CanonicalProofSupportDigest
        let baseline = project info
        let shifted = project { info with Id = "claim_999"; Source = "comparison.clef:42:7" }
        let changedBody = project { info with Body = ObligationBody.StorageReservation(3, 3) }
        Assert.Equal(baseline, shifted)
        Assert.NotEqual(baseline, changedBody)

    [<Fact>]
    member _.``Scalar proof support tracks the source numeric core census`` () =
        let source = ComparisonRegionFixture.source "" "<"
        let authority = RealComparisonFixture.authority
        let width = authority.Replace("Name = \"Pointer\"; Bits = 64", "Name = \"Pointer\"; Bits = 32")
        let offered = authority.Replace("Representations = [|", "Representations = [| { Name = \"extra16\"; Capability = \"native\"; Family = \"int\"; Bits = 16; MinMagnitude = \"-32768\"; MaxMagnitude = \"32767\"; Boundary = \"wrap\" }; ")
        Assert.NotEqual(authority, width)
        Assert.NotEqual(authority, offered)
        let original = ComparisonRegionFixture.prepare authority source
        let baseline = (ComparisonRegionFixture.get ComparisonRegionFixture.first original).CanonicalProofSupportDigest
        for changedAuthority in [width; offered] do
            let prepared = ComparisonRegionFixture.prepare changedAuthority source
            let changed = { prepared with Platform = original.Platform }
            Assert.Equal(original.Platform, changed.Platform)
            let emission = changed.Codata.Value.WitnessEmission.Value
            let scope =
                Clef.Compiler.Baker.Recipes.WitnessScopeRecipes.projectWithEmission emission changed
                |> Result.defaultWith (sprintf "%A" >> failwith)
            let projected = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessSegmentation.project changed emission scope
            let region = projected.Regions |> List.find (fun row -> row.Identity = ComparisonRegionFixture.first)
            Assert.NotEqual(baseline, region.CanonicalProofSupportDigest)

    [<Fact>]
    member _.``Platform census changes immediately alter proof support`` () =
        let graph = ComparisonRegionFixture.prepare RealComparisonFixture.authority (ComparisonRegionFixture.source "" "<")
        let original = ComparisonRegionFixture.get ComparisonRegionFixture.first graph
        let platform = graph.Platform.Value
        let representation = platform.Representations.Values |> Seq.head
        let variants =
            [ { platform with Dimensions = platform.Dimensions.Add("CensusTest", 37) }
              { platform with Representations = platform.Representations.Add(representation.Name, { representation with Bits = representation.Bits + 1 }) }
              { platform with Representations = platform.Representations.Add("additional-census-entry", { representation with Name = "additional-census-entry" }) } ]
        let emission = graph.Codata.Value.WitnessEmission.Value
        for platform in variants do
            let changed = { graph with Platform = Some platform }
            let scope = Clef.Compiler.Baker.Recipes.WitnessScopeRecipes.projectWithEmission emission changed |> Result.defaultWith (sprintf "%A" >> failwith)
            let projection = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessSegmentation.project changed emission scope
            let current = projection.Regions |> List.find (fun region -> region.Identity = original.Identity)
            Assert.NotEqual(original.CanonicalProofSupportDigest, current.CanonicalProofSupportDigest)

    [<Fact>]
    member _.``Fresh checks and source trivia preserve all region digests`` () =
        let source = (ComparisonRegionFixture.source "" "<").Replace("let first", "/// Original documentation\nlet first")
        let before = ComparisonRegionFixture.prepare RealComparisonFixture.authority source
        let variants =
            [ source
              "\n// shifted\n" + source
              source.Replace("Original documentation", "Revised documentation") ]
        let original = ComparisonRegionFixture.regions before
        let baseline = Clef.Compiler.PSGSaturation.SemanticGraph.Segmentation.segment before |> Result.defaultWith (sprintf "%A" >> failwith)
        for text in variants do
            let after = ComparisonRegionFixture.prepare RealComparisonFixture.authority text
            let current = ComparisonRegionFixture.regions after
            Assert.Equal<Set<string>>(original.Keys |> Set.ofSeq, current.Keys |> Set.ofSeq)
            for KeyValue(name, region) in original do
                Assert.Equal(region.CallableInterfaceDigest, current[name].CallableInterfaceDigest)
                Assert.True(region.SemanticRealizationDigest = current[name].SemanticRealizationDigest, sprintf "Realization differs for %s, variant %d" name (List.findIndex ((=) text) variants))
                Assert.Equal(region.CanonicalProofSupportDigest, current[name].CanonicalProofSupportDigest)
            let plan = Clef.Compiler.PSGSaturation.SemanticGraph.Segmentation.segment after |> Result.defaultWith (sprintf "%A" >> failwith)
            for KeyValue(name, region) in baseline.Regions do
                Assert.Equal(region.CallableInterfaceDigest, plan.Regions[name].CallableInterfaceDigest)
                Assert.Equal(region.SemanticRealizationDigest, plan.Regions[name].SemanticRealizationDigest)
                Assert.Equal(region.CanonicalProofSupportDigest, plan.Regions[name].CanonicalProofSupportDigest)
            let schedule = Clef.Compiler.PSGSaturation.SemanticGraph.Rebuild.scheduleRebuild before after |> Result.defaultWith (sprintf "%A" >> failwith)
            Assert.Empty schedule.Receipt.InvalidatedRegions

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
            Assert.Equal(original.CallableInterfaceDigest, current.CallableInterfaceDigest)
            Assert.Equal(original.SemanticRealizationDigest, current.SemanticRealizationDigest)
            Assert.Equal(original.CanonicalProofSupportDigest, current.CanonicalProofSupportDigest)
            match current.ProofSupportCoverage with
            | ProofSupportCoverage.Global(participants, censuses) ->
                Assert.NotEmpty participants
                Assert.Contains(censuses, fun c -> c.Kind = ProofSupportCensusKind.NumericInterface)
            | other -> failwithf "Expected Global proof-support coverage for comparison region, got %A" other
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
        let firstBefore, firstAfter = ComparisonRegionFixture.get ComparisonRegionFixture.first before, ComparisonRegionFixture.get ComparisonRegionFixture.first after
        let secondBefore, secondAfter = ComparisonRegionFixture.get ComparisonRegionFixture.second before, ComparisonRegionFixture.get ComparisonRegionFixture.second after
        Assert.Equal(firstBefore.CallableInterfaceDigest, firstAfter.CallableInterfaceDigest)
        Assert.Equal(firstBefore.SemanticRealizationDigest, firstAfter.SemanticRealizationDigest)
        Assert.Equal(firstBefore.CanonicalProofSupportDigest, firstAfter.CanonicalProofSupportDigest)
        Assert.Equal(secondBefore.CallableInterfaceDigest, secondAfter.CallableInterfaceDigest)
        Assert.NotEqual(secondBefore.SemanticRealizationDigest, secondAfter.SemanticRealizationDigest)
        Assert.NotEqual(secondBefore.CanonicalProofSupportDigest, secondAfter.CanonicalProofSupportDigest)

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
        Assert.Equal(original.CallableInterfaceDigest, current.CallableInterfaceDigest)
        Assert.Equal(original.SemanticRealizationDigest, current.SemanticRealizationDigest)
        Assert.Equal(original.CanonicalProofSupportDigest, current.CanonicalProofSupportDigest)

    [<Fact>]
    member _.``Comparison region retains the complete offered source format declaration`` () =
        let source = ComparisonRegionFixture.source "" "<"
        let before = ComparisonRegionFixture.prepare RealComparisonFixture.authority source
        // The format boundary is an explicit source interface field even when
        // this comparison has no arithmetic result requiring an adaptation.
        let authority = RealComparisonFixture.authority.Replace("MaxMagnitude = \"1.7976931348623157e308\"; Boundary = \"wrap\"", "MaxMagnitude = \"1.7976931348623157e308\"; Boundary = \"exact\"")
        let after = ComparisonRegionFixture.prepare authority source
        let firstBefore = ComparisonRegionFixture.get ComparisonRegionFixture.first before
        let firstAfter = ComparisonRegionFixture.get ComparisonRegionFixture.first after
        Assert.NotEqual(firstBefore.SemanticRealizationDigest, firstAfter.SemanticRealizationDigest)
        Assert.NotEqual(firstBefore.CanonicalProofSupportDigest, firstAfter.CanonicalProofSupportDigest)
        let operation = before.Codata.Value.WitnessEmission.Value.Numeric.Operations.Values |> Seq.find (fun row -> firstBefore.Members.Contains row.Site)
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
        Assert.NotEqual(before.CallableInterfaceDigest, current.CallableInterfaceDigest)
        Assert.NotEqual(before.SemanticRealizationDigest, current.SemanticRealizationDigest)
        Assert.NotEqual(before.CanonicalProofSupportDigest, current.CanonicalProofSupportDigest)
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
    member _.``Unrelated boundary declarations preserve scalar regions and their fingerprints`` () =
        let authority = RealComparisonFixture.authority.Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")
        let source = ComparisonRegionFixture.source "" "<"
        let alone = ComparisonRegionFixture.prepareBeside authority None source
        let beside = ComparisonRegionFixture.prepareBeside authority (Some ComparisonRegionFixture.foreignDeclarations) source
        // The declaration's hypothesis is published for the whole program.
        Assert.NotEmpty beside.Codata.Value.WitnessEmission.Value.Boundary.ResultHypotheses
        for name in [ComparisonRegionFixture.first; ComparisonRegionFixture.second] do
            let original = ComparisonRegionFixture.get name alone
            let current = ComparisonRegionFixture.get name beside
            Assert.Equal(original.CallableInterfaceDigest, current.CallableInterfaceDigest)
            Assert.Equal(original.SemanticRealizationDigest, current.SemanticRealizationDigest)
            Assert.Equal(original.CanonicalProofSupportDigest, current.CanonicalProofSupportDigest)

    [<Fact>]
    member _.``A foreign call stays in the common region without refusing a sibling scalar region`` () =
        let authority = RealComparisonFixture.authority.Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")
        let source = "module ComparisonRegions\nlet first (left: float) (right: float) = left < right\nlet probe (count: int) = Foreign.read count\n[<EntryPoint>]\nlet main _ = if first 1.25 2.5 && probe 3 >= 0 then 0 else 1\n"
        let graph = ComparisonRegionFixture.prepareBeside authority (Some ComparisonRegionFixture.foreignDeclarations) source
        let regions = ComparisonRegionFixture.regions graph
        Assert.True(regions.ContainsKey ComparisonRegionFixture.first, sprintf "Missing region beside a foreign call: %A" regions.Keys)
        Assert.False(regions.ContainsKey "callable:ComparisonRegions:probe")
        let probeCall =
            graph.Codata.Value.WitnessEmission.Value.Numeric.ForeignResultUses
            |> List.map (fun row -> row.Application.Call)
        Assert.NotEmpty probeCall
        for call in probeCall do
            Assert.Contains(call, regions["common"].Members)

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
        Assert.Equal(before.CallableInterfaceDigest, current.CallableInterfaceDigest)
        Assert.Equal(before.SemanticRealizationDigest, current.SemanticRealizationDigest)
        Assert.NotEqual(before.CanonicalProofSupportDigest, current.CanonicalProofSupportDigest)
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
        | Some current ->
            Assert.NotEqual(before.CallableInterfaceDigest, current.CallableInterfaceDigest)
            Assert.NotEqual(before.SemanticRealizationDigest, current.SemanticRealizationDigest)
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
