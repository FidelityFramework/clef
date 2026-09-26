namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module Families = Clef.Compiler.Nanopass.SequenceFamilies
module FamilyOrigins = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceOrigins
module FamilyControl = Clef.Compiler.Baker.Recipes.SequenceControlRecipes
module FamilyRuntime = Clef.Compiler.Nanopass.SequenceRuntime
module FamilyRanges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis

module private FamilyFixture =
    let source () =
        let result = DimensionalCases.check """
let inspect (items: seq<int<m>>) = Seq.tryHead items
[<EntryPoint>]
let main _ =
    let small = seq { yield 1<m> }
    let large = seq { yield 1000<m> }
    let empty: seq<int<m>> = seq { () }
    let unrelated = seq { yield 3<m> }
    ignore (inspect small)
    ignore (inspect large)
    ignore (inspect empty)
    ignore unrelated
    0
"""
        DimensionalCases.noErrors result
        result.Graph

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
        |> Assert.Single

    let controls (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.SeqExpr _ when node.IsReachable ->
                match FamilyControl.forOwner graph node with
                | Ok control -> Some(node.Id, control)
                | Result.Error residual -> failwithf "Invalid source control: %A" residual
            | _ -> None) |> Map.ofSeq

    let plan graph =
        Families.plan graph (FamilyOrigins.settleFlows graph graph.Codata.Value.Curry) (controls graph)

    let context : PlatformContext =
        let integer name family bits minimum maximum : NumericRepresentation =
            { Name = name; Family = family; Bits = bits; MinMagnitude = minimum; MaxMagnitude = maximum
              Capability = "native"; Boundary = "wrap" }
        let representations = [integer "signed8" "int" 8 "-128" "127"; integer "unsigned8" "uint" 8 "0" "255"
                               integer "unsigned16" "uint" 16 "0" "65535"; integer "unsigned64" "uint" 64 "0" "18446744073709551615"]
        { PlatformId = "sequence-family-test"; Dimensions = Map.ofList ["Pointer", 64; "Register", 64]
          Representations = representations |> List.map (fun value -> value.Name, value) |> Map.ofList
          EndpointReturns = Map.empty; PlatformLibraryPath = None; PlatformDescription = None; PlatformArchitecture = None
          PlatformOS = None; PlatformSourcePaths = Set.empty; Predicates = Map.empty; FreestandingStartup = None
          SubstrateKind = None; RuntimeModel = None; AvailableMemorySpaces = []; DefaultMemorySpace = None
          ClockFrequencyMhz = None; NsPerWeightUnit = None }

    let native () =
        let source = source ()
        let graph, diagnostics = FamilyRanges.run (Some context) { source with Platform = Some context }
        Assert.Empty(diagnostics |> List.filter (fun diagnostic -> diagnostic.Severity = NativeDiagnosticSeverity.Error))
        let graph, settlement = FamilyRuntime.normalize graph graph.Codata.Value.Curry
        Assert.Empty settlement.Diagnostics
        graph, settlement

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceFamilies")>]
type SequenceFamilyCases() =
    [<Fact>]
    member _.``Families connect exact formal flows without merging unrelated equal element types``() =
        let graph = FamilyFixture.source ()
        let planning = FamilyFixture.plan graph
        Assert.Empty planning.Unresolved
        let unique, _ = FamilyOrigins.settle graph graph.Codata.Value.Curry
        let owner name = unique[(FamilyFixture.binding name graph).Id]
        let shared = planning.Plans[planning.ByOwner[owner "small"]]
        Assert.Equal<Set<NodeId>>(Set.ofList [owner "small"; owner "large"; owner "empty"], shared.Owners)
        Assert.NotEqual(shared.Identity, planning.ByOwner[owner "unrelated"])
        Assert.Equal(Some(ValueRange.bounded 1I 1000I), shared.CurrentRange)
        Assert.Empty shared.Payloads[owner "empty"]
        Assert.NotEmpty shared.Payloads[owner "small"]
        Assert.Equal(ValueRange.bounded -1I 1I, shared.StateRange)

    [<Fact>]
    member _.``Actual generators retain individual fields under one placed current and extent contract``() =
        let graph, settlement = FamilyFixture.native ()
        let family = settlement.Families.Values |> Seq.filter (fun family -> family.Members.Count = 3) |> Assert.Single
        let current = family.CurrentField |> Option.get
        Assert.Equal(SettledSlot.Integer(16, Some "unsigned16"), current.Slot)
        Assert.Equal(3, family.Members.Count)
        let empty = family.Members.Values |> Seq.filter (fun memberContract -> memberContract.Current.IsNone) |> Assert.Single
        Assert.DoesNotContain(empty.Slots, fun slot -> empty.Uninitialized.Contains slot.Source)
        Assert.Equal(Some(ValueRange.bounded -1I 0I), graph.Nodes[empty.State].ValueRange)
        for owner, memberContract in family.Members |> Map.toList do
            let frame = settlement.Frames[owner]
            Assert.Equal(family.Bytes, frame.Bytes)
            Assert.Equal(family.Alignment, frame.Alignment)
            Assert.Equal(frame.Generator, memberContract.Generator)
            Assert.Equal(frame.Formal, memberContract.Formal)
            Assert.Equal<ContinuationSlot list>(frame.Slots, memberContract.Slots)
            Assert.Contains(graph.Edges, fun edge -> edge.Role = EdgeRole.SequenceFamilyLayout && edge.Target = owner && List.contains frame.Generator edge.Sources)
            match memberContract.Current with
            | Some id ->
                let field = frame.Slots |> List.find (fun slot -> slot.Source = id)
                Assert.Equal(current.Slot, field.Field.Slot)
                Assert.Equal(current.Offset, field.Field.Offset)
                Assert.Contains(id, memberContract.Uninitialized)
            | None -> Assert.DoesNotContain(frame.Slots, fun slot -> slot.Source = frame.Current)

    [<Fact>]
    member _.``Source sequence formals retain a protocol while actual generator formals name only storage``() =
        let graph, settlement = FamilyFixture.native ()
        let formal = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && node.Kind = SemanticKind.PatternBinding "items") |> Assert.Single
        let shape = Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.valueShape graph
        Assert.Equal(CallableValueShape.Sequence formal.Id, shape formal)
        for frame in settlement.Frames.Values do
            Assert.Equal(CallableValueShape.Data frame.Formal, shape graph.Nodes[frame.Formal])
            Assert.Equal(CallableValueShape.Sequence frame.Owner, shape graph.Nodes[frame.Owner])

    [<Fact>]
    member _.``Fresh-copy evidence preserves deferred captures and cannot admit current or run a body``() =
        let graph, settlement = FamilyFixture.native ()
        Assert.NotEmpty settlement.TemplateCopies
        let copies, evidence, residuals = Families.copies graph settlement.Families settlement.Flows settlement.Residences settlement.Regions settlement.Initializers settlement.Destinations
        Assert.Empty residuals
        Assert.Empty evidence.NewNodes
        Assert.Equal<Map<NodeId, SequenceTemplateCopy>>(settlement.TemplateCopies, copies)
        for acquisition, copy in copies |> Map.toList do
            let family = settlement.Families[copy.Family]
            Assert.Equal(EscapeKind.StackScoped, copy.Residence)
            Assert.Equal(family.Bytes, copy.Bytes)
            Assert.Equal(family.Alignment, copy.Alignment)
            Assert.Equal(NTUMemorySpace.Default, copy.AddressSpace)
            for allocations in copy.TemplateStorage.Values do
                Assert.NotEmpty allocations
                Assert.DoesNotContain(copy.StorageSite, allocations)
            Assert.Contains(graph.Edges, fun edge -> edge.Role = EdgeRole.SequenceTemplateCopy && edge.Target = acquisition && List.contains copy.Template edge.Sources)
            for owner, captures in copy.Captures |> Map.toList do
                Assert.Equal<Set<NodeId>>(family.Members[owner].Captures, captures)
                Assert.Equal<Set<NodeId>>(family.Members[owner].Uninitialized, copy.Uninitialized[owner])
                Assert.DoesNotContain(family.Members[owner].State, copy.Uninitialized[owner])
        Assert.All(evidence.NewEdges, fun edge -> Assert.Equal(EdgeRole.SequenceTemplateCopy, edge.Role))

    [<Theory>]
    [<InlineData("template-storage")>]
    [<InlineData("capture-authority")>]
    [<InlineData("memory-space")>]
    member _.``Opaque copy cannot manufacture missing source storage or initialization premises`` variant =
        let graph, settlement = FamilyFixture.native ()
        let acquisition, copy = settlement.TemplateCopies |> Map.toList |> List.head
        let owner, storage = copy.TemplateStorage |> Map.toList |> List.head
        let residences =
            if variant = "template-storage" then storage |> Set.fold (fun (facts: Map<NodeId, EscapeKind>) id -> facts.Remove id) settlement.Residences
            else settlement.Residences
        let initializers = if variant = "capture-authority" then settlement.Initializers.Remove owner else settlement.Initializers
        let graph = if variant = "memory-space" then { graph with Platform = None } else graph
        let copies, _, residuals = Families.copies graph settlement.Families settlement.Flows residences settlement.Regions initializers settlement.Destinations
        Assert.False(copies.ContainsKey acquisition)
        Assert.Contains(residuals, fun residual -> residual.Site = acquisition)

    [<Theory>]
    [<InlineData("wrong-template")>]
    [<InlineData("missing-residence")>]
    member _.``Fresh-copy proof cannot be reused for another template or missing storage`` variant =
        let graph, settlement = FamilyFixture.native ()
        let acquisition, copy = settlement.TemplateCopies |> Map.toList |> List.find (fun (_, copy) -> settlement.Families[copy.Family].Members.Count = 3)
        let graph, residences =
            if variant = "missing-residence" then graph, settlement.Residences.Remove copy.StorageSite
            else
                let unrelated = FamilyFixture.binding "unrelated" graph
                let node = graph.Nodes[acquisition]
                let changed =
                    match node.Kind with
                    | SemanticKind.Application(callee, [_]) -> { node with Kind = SemanticKind.Application(callee, [unrelated.Id]); Children = [callee; unrelated.Id] }
                    | kind -> failwithf "Missing acquisition: %A" kind
                { graph with Nodes = graph.Nodes.Add(acquisition, changed) }, settlement.Residences
        let copies, _, residuals = Families.copies graph settlement.Families settlement.Flows residences settlement.Regions settlement.Initializers settlement.Destinations
        Assert.False(copies.ContainsKey acquisition)
        Assert.Contains(residuals, fun residual -> residual.Site = acquisition)

    [<Theory>]
    [<InlineData("opaque")>]
    [<InlineData("wrong-element")>]
    member _.``Incomplete or contradictory alternatives cannot acquire a common protocol`` variant =
        let graph = FamilyFixture.source ()
        let flows = FamilyOrigins.settleFlows graph graph.Codata.Value.Curry
        let formal = flows.Values |> Seq.filter (fun flow -> flow.Owners.Count = 3) |> Seq.head
        let changed =
            if variant = "opaque" then { formal with Unknown = Set.singleton formal.Occurrence }
            else { formal with ElementType = Types.boolType }
        let planning = Families.plan graph (flows.Add(formal.Occurrence, changed)) (FamilyFixture.controls graph)
        Assert.NotEmpty planning.Unresolved
        for owner in formal.Owners do Assert.False(planning.ByOwner.ContainsKey owner)

    [<Fact>]
    member _.``A changed yielded range invalidates the old common current meet``() =
        let graph = FamilyFixture.source ()
        let original = FamilyFixture.plan graph
        let family = original.Plans.Values |> Seq.filter (fun plan -> plan.Owners.Count = 3) |> Assert.Single
        let payload = family.Payloads.Values |> Seq.collect id |> Seq.maxBy (fun id -> NodeId.value id)
        let changedNode = { graph.Nodes[payload] with ValueRange = Some(ValueRange.bounded 100000I 100000I) }
        let changed = { graph with Nodes = graph.Nodes.Add(payload, changedNode) }
        let current = FamilyFixture.plan changed
        Assert.NotEqual(family.CurrentRange, current.Plans[family.Identity].CurrentRange)
        Assert.True(ValueRange.contains current.Plans[family.Identity].CurrentRange.Value (ValueRange.bounded 100000I 100000I))
