namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module RegionSettlement = Clef.Compiler.Nanopass.SequenceRegions
module RegionRuntime = Clef.Compiler.Nanopass.SequenceRuntime
module RegionControl = Clef.Compiler.Baker.Recipes.SequenceControlRecipes
module RegionRanges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis
module RegionPlacement = Clef.Compiler.PSGSaturation.SemanticGraph.Placement

module private RegionFixture =
    let frame (builder: NodeBuilder) wide =
        let node name ty = builder.Create(SemanticKind.PatternBinding name, ty, dummyRange)
        let sequenceType = Types.mkSeqType Types.boolType
        let owner = node "sequence-owner" sequenceType
        let generator = node "generator" (NativeType.TFun(NativeType.TSeqEnumerator Types.boolType, Types.boolType))
        let formal = node "environment" (NativeType.TSeqEnumerator Types.boolType)
        let state, current = node "state" Types.intType, node "current" Types.boolType
        let slot (source: SemanticNode) offset size alignment carrier =
            { Source = source.Id; ValueType = source.Type; Holds = CaptureSlotKind.Scalar carrier; IsCapture = false
              Field = { Name = string source.Id; Slot = carrier; Offset = Some offset; Size = Some size; Align = Some alignment } }
        let prefix = [slot state 0 1 1 (SettledSlot.Integer(8, None)); slot current 1 1 1 SettledSlot.Bool]
        let slots = if wide then prefix @ [slot (node "payload" Types.intType) 4 4 4 (SettledSlot.Integer(32, None))] else prefix
        { Owner = owner.Id; Generator = generator.Id; Formal = formal.Id; State = state.Id; Current = current.Id
          Slots = slots; Bytes = (if wide then 8 else 2); Alignment = (if wide then 4 else 1)
          ScratchSlots = []; ScratchBytes = 0; ScratchAlignment = 1; Initializers = []; ResumeStates = [0; 1]; Obligations = [] }

    let site (builder: NodeBuilder) =
        builder.Create(SemanticKind.PatternBinding "acquisition", NativeType.TSeqEnumerator Types.boolType, dummyRange).Id

    let platform: PlatformContext =
        let signed: NumericRepresentation = {
            Name = "signed8"; Capability = "native"; Family = "int"; Bits = 8
            MinMagnitude = "-128"; MaxMagnitude = "127"; Boundary = "wrap" }
        let unsigned: NumericRepresentation = {
            Name = "unsigned64"; Capability = "native"; Family = "uint"; Bits = 64
            MinMagnitude = "0"; MaxMagnitude = "18446744073709551615"; Boundary = "wrap" }
        { PlatformId = "sequence-region-test"; Dimensions = Map.ofList ["Pointer", 64; "Register", 64]
          Representations = Map.ofList [signed.Name, signed; unsigned.Name, unsigned]
          EndpointReturns = Map.empty; PlatformLibraryPath = None; PlatformDescription = None
          PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.empty
          Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
          AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None }

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceRegions")>]
type SequenceRegionCases() =
    [<Fact>]
    member _.``Distinct acquisition identities for one child owner receive disjoint complete backing regions``() =
        let builder = NodeBuilder()
        let parent, child = RegionFixture.frame builder false, RegionFixture.frame builder true
        let first, second = RegionFixture.site builder, RegionFixture.site builder
        let graph = builder.Build []
        let frames = Map.ofList [parent.Owner, parent; child.Owner, child]
        let result = RegionSettlement.settle graph frames
                        (Map.ofList [first, parent.Generator; second, parent.Generator])
                        (Map.ofList [first, child.Owner; second, child.Owner])
        Assert.Empty result.Unresolved
        let firstRegion, secondRegion = result.Regions[first], result.Regions[second]
        Assert.Equal(4, firstRegion.Offset)
        Assert.Equal(12, secondRegion.Offset)
        Assert.Equal(8, firstRegion.Bytes)
        Assert.Equal(8, secondRegion.Bytes)
        Assert.True(firstRegion.Offset + firstRegion.Bytes <= secondRegion.Offset)
        Assert.Equal(20, result.Frames[parent.Owner].Bytes)
        Assert.Equal(4, result.Frames[parent.Owner].Alignment)
        for region in [firstRegion; secondRegion] do
            Assert.Equal(parent.Owner, region.ParentOwner)
            Assert.Equal(parent.Formal, region.ParentFormal)
            Assert.Equal(child.Owner, region.ChildOwner)
        let proof = Assert.Single result.Evidence.NewNodes
        match proof.Kind with
        | SemanticKind.Obligation { Body = ObligationBody.ContinuationLayout(slots, 20, 4) } ->
            Assert.Equal<(int * int * int) list>([0, 1, 1; 1, 1, 1; 4, 8, 4; 12, 8, 4], slots)
        | kind -> failwithf "Missing complete prefix-plus-child extent obligation: %A" kind
        let relation = result.Evidence.NewEdges |> List.filter (fun edge -> edge.Target = proof.Id) |> Assert.Single
        let expected = parent.Owner :: (parent.Slots |> List.map _.Source) @ [first; second; child.Owner] |> Set.ofList
        Assert.Equal<Set<NodeId>>(expected, Set.ofList relation.Sources)
        for site in [first; second] do
            let region = result.Evidence.NewEdges |> List.filter (fun edge -> edge.Role = EdgeRole.ContinuationRegion && edge.Target = site) |> Assert.Single
            Assert.Equal<NodeId list>([parent.Owner; child.Owner; parent.Formal], region.Sources)
        Assert.Contains(proof.Id, result.Frames[parent.Owner].Obligations)
        Assert.Equal(2, frames[parent.Owner].Bytes)

    [<Fact>]
    member _.``Parent extent includes the completed nested child extent in dependency order``() =
        let builder = NodeBuilder()
        let outer, middle, inner = RegionFixture.frame builder false, RegionFixture.frame builder false, RegionFixture.frame builder true
        let middleSite, innerSite = RegionFixture.site builder, RegionFixture.site builder
        let result = RegionSettlement.settle (builder.Build [])
                        (Map.ofList [outer.Owner, outer; middle.Owner, middle; inner.Owner, inner])
                        (Map.ofList [middleSite, outer.Generator; innerSite, middle.Generator])
                        (Map.ofList [middleSite, middle.Owner; innerSite, inner.Owner])
        Assert.Empty result.Unresolved
        Assert.Equal(12, result.Frames[middle.Owner].Bytes)
        Assert.Equal(12, result.Regions[middleSite].Bytes)
        Assert.Equal(4, result.Regions[middleSite].Offset)
        Assert.Equal(16, result.Frames[outer.Owner].Bytes)
        Assert.Equal(8, result.Regions[innerSite].Bytes)
        Assert.Equal(2, result.Evidence.NewNodes.Length)

    [<Theory>]
    [<InlineData("cycle")>]
    [<InlineData("missing-origin")>]
    [<InlineData("missing-child-frame")>]
    member _.``Unsettled region dependencies remain residual without invented extents``(defect: string) =
        let builder = NodeBuilder()
        let parent, child = RegionFixture.frame builder false, RegionFixture.frame builder true
        let first, second = RegionFixture.site builder, RegionFixture.site builder
        let frames = Map.ofList [parent.Owner, parent; child.Owner, child]
        let sites, origins =
            match defect with
            | "cycle" ->
                Map.ofList [first, parent.Generator; second, child.Generator], Map.ofList [first, child.Owner; second, parent.Owner]
            | "missing-origin" -> Map.ofList [first, parent.Generator], Map.empty
            | "missing-child-frame" -> Map.ofList [first, parent.Generator], Map.ofList [first, second]
            | _ -> failwith "Unknown region defect"
        let result = RegionSettlement.settle (builder.Build []) frames sites origins
        Assert.NotEmpty result.Unresolved
        Assert.Empty result.Regions
        Assert.Empty result.Evidence.NewNodes
        for frame in frames.Values do Assert.Equal(frame.Bytes, result.Frames[frame.Owner].Bytes)

    [<Fact>]
    member _.``A mutable cell captured by a local child is promoted to parent persistent storage even without scalar liveness``() =
        let source = DimensionalCases.check """
[<EntryPoint>]
let main _ =
    let outer = seq {
        let mutable seed = true
        let child = seq { yield seed; seed <- false; yield seed }
        yield! child
    }
    for value in outer do ignore value
    0
"""
        DimensionalCases.noErrors source
        let original = source.Graph
        let seed = original.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Binding("seed", true, _, _) -> true | _ -> false) |> Assert.Single
        let child = original.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.SeqExpr(_, captures) -> captures |> List.exists (fun capture -> capture.SourceNodeId = Some seed.Id) | _ -> false) |> Assert.Single
        let parent = original.Nodes.Values |> Seq.filter (fun node ->
            node.Id <> child.Id && match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false) |> Assert.Single
        let control = match RegionControl.forOwner original parent with Ok control -> control | Error residual -> failwithf "%A" residual
        Assert.DoesNotContain(control.LiveAcross.Values, fun live -> live.Contains seed.Id)
        let platform = RegionFixture.platform
        let graph, diagnostics = RegionRanges.run (Some platform) { original with Platform = Some platform }
        Assert.Empty diagnostics
        let graph = RegionPlacement.settle (Some platform) graph
        let settled, result = RegionRuntime.normalize graph original.Codata.Value.Curry
        Assert.Empty result.Diagnostics
        let frame = result.Frames[parent.Id]
        Assert.Contains(frame.Slots, fun slot -> slot.Source = seed.Id)
        Assert.DoesNotContain(frame.ScratchSlots, fun slot -> slot.Source = seed.Id)
        Assert.Contains(settled.Edges, fun edge ->
            edge.Role = EdgeRole.ContinuationBorrow && edge.Sources = [parent.Id; frame.Generator; seed.Id] && edge.Target = child.Id)
        Assert.Contains(result.Regions.Values, fun region -> region.ParentOwner = parent.Id && region.ChildOwner = child.Id)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Nested constructor evaluates its exact capture read or borrow before the live clone`` mutableCapture =
        let declaration = if mutableCapture then "let mutable seed = true" else "let seed = true"
        let checkedSource = DimensionalCases.check (
            "[<EntryPoint>]\nlet main _ =\n    let outer = seq {\n        " + declaration +
            "\n        let child = seq { yield seed; yield seed }\n        yield! child\n    }\n    for value in outer do ignore value\n    0\n")
        DimensionalCases.noErrors checkedSource
        let original = checkedSource.Graph
        let seed = original.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding("seed", _, _, _) -> true | _ -> false) |> Assert.Single
        let child = original.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && (match node.Kind with
                                 | SemanticKind.SeqExpr(_, captures) -> captures |> List.exists (fun capture -> capture.SourceNodeId = Some seed.Id)
                                 | _ -> false)) |> Assert.Single
        let graph, diagnostics = RegionRanges.run (Some RegionFixture.platform) { original with Platform = Some RegionFixture.platform }
        Assert.Empty diagnostics
        let graph = RegionPlacement.settle (Some RegionFixture.platform) graph
        let settled, result = RegionRuntime.normalize graph original.Codata.Value.Curry
        Assert.Empty result.Diagnostics
        let clone = settled.Edges |> List.choose (fun edge ->
            if edge.Class = EdgeClass.Provenance && edge.Role = EdgeRole.ContinuationValue && edge.Sources = [child.Id] then
                match settled.Nodes[edge.Target] with
                | { Kind = SemanticKind.SeqExpr _; IsReachable = true } as node -> Some node
                | _ -> None
            else None) |> Assert.Single
        let initializer = result.Initializers[clone.Id] |> List.filter (fun (source, _) -> source = seed.Id) |> Assert.Single |> snd
        let formation = settled.Nodes[initializer]
        Assert.True formation.IsReachable
        match formation.Kind with
        | SemanticKind.FrameBorrow(_, source) when mutableCapture -> Assert.Equal(seed.Id, source)
        | SemanticKind.FrameRead(_, source) when not mutableCapture -> Assert.Equal(seed.Id, source)
        | kind -> failwithf "Capture lost its value/address distinction: %A" kind
        match clone.Kind with
        | SemanticKind.SeqExpr(_, captures) -> Assert.Contains(captures, fun capture -> capture.SourceNodeId = Some initializer && capture.IsMutable = mutableCapture)
        | _ -> failwith "Missing cloned constructor"
        let block = settled.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && (match node.Kind with
                                 | SemanticKind.Sequential actions -> List.contains initializer actions && List.contains clone.Id actions
                                 | _ -> false)) |> Assert.Single
        let actions = match block.Kind with SemanticKind.Sequential actions -> actions | _ -> []
        Assert.True(List.findIndex ((=) initializer) actions < List.findIndex ((=) clone.Id) actions)
        // Formation is ordinary structural evaluation; capture metadata alone
        // must neither schedule its read nor resurrect the old constructor.
        let operands = kindEdges block.Id block.Kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources
        Assert.Contains(initializer, operands)
        Assert.Contains(clone.Id, operands)
        Assert.False settled.Nodes[child.Id].IsReachable
        Assert.True(settled.Nodes.ContainsKey child.Id)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Storage layout ownership preserves source provenance without executing its constructor`` callerStorage =
        let builder = NodeBuilder()
        let body = builder.Create(SemanticKind.Literal NativeLiteral.Unit, Types.unitType, dummyRange)
        let formal = builder.Create(SemanticKind.PatternBinding "environment", NativeType.TSeqEnumerator Types.boolType, dummyRange)
        let generator = builder.Create(SemanticKind.Lambda(["environment", formal.Type, formal.Id], body.Id, [], None, LambdaContext.SeqGenerator),
                                       NativeType.TFun(formal.Type, Types.unitType), dummyRange)
        let owner = builder.Create(SemanticKind.SeqExpr(generator.Id, []), Types.mkSeqType Types.boolType, dummyRange)
        let clone = builder.Create(SemanticKind.SeqExpr(generator.Id, []), owner.Type, dummyRange)
        let kind = if callerStorage then SemanticKind.ContinuationAllocate owner.Id else SemanticKind.ContinuationStorage owner.Id
        let storage = builder.Create(kind, owner.Type, dummyRange)
        let graph = builder.Build [storage.Id, DeclRoot.EntryPoint; clone.Id, DeclRoot.EntryPoint]
        let ownership = kindEdges storage.Id storage.Kind |> Assert.Single
        Assert.Equal(EdgeClass.Provenance, ownership.Class)
        Assert.Equal(EdgeRole.Definition, ownership.Role)
        Assert.Equal<NodeId list>([owner.Id], ownership.Sources)
        let references = Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.getSemanticReferences storage
        Assert.DoesNotContain(owner.Id, references)
        let marked = Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable graph
        Assert.False marked.Nodes[owner.Id].IsReachable
        Assert.True marked.Nodes[clone.Id].IsReachable
        Assert.True marked.Nodes[generator.Id].IsReachable
        Assert.True marked.Nodes[storage.Id].IsReachable
        Assert.True(marked.Nodes.ContainsKey owner.Id)
