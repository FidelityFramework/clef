namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
open Clef.Compiler.Nanopass.Recipe
module EvidenceControl = Clef.Compiler.Baker.Recipes.SequenceControlRecipes
module EvidenceMachine = Clef.Compiler.Baker.Recipes.SequenceMachineRecipes
module ContinuationEvidence = Clef.Compiler.Baker.Recipes.SequenceContinuationEvidence
module EvidenceFold = Clef.Compiler.Nanopass.ObligationElaboration
module EvidenceReplacements = Clef.Compiler.Nanopass.FoldIn
module EvidenceFanOut = Clef.Compiler.Nanopass.FanOut
module EvidenceProgram = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization

module private ContinuationFacts =
    type Fixture = {
        Graph: SemanticGraph
        Control: EvidenceControl.Control
        Frame: ContinuationFrame
        Machine: EvidenceMachine.Machine
    }

    let fixture source =
        let checkedSource = DimensionalCases.check (source + "\n[<EntryPoint>]\nlet main _ = ignore outer; 0\n")
        DimensionalCases.noErrors checkedSource
        let graph = checkedSource.Graph
        let owner = graph.Nodes.Values |> Seq.filter (fun node -> match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false) |> Assert.Single
        let control = match EvidenceControl.forOwner graph owner with Ok control -> control | Error failure -> failwithf "%A" failure
        let formal =
            match graph.Nodes[control.Generator].Kind with
            | SemanticKind.Lambda([_, _, formal], _, _, _, _) -> formal
            | kind -> failwithf "Missing source formal: %A" kind
        let slot name ty range =
            { owner with Id = NodeId.fresh(); Kind = SemanticKind.PatternBinding name; Type = ty
                         ValueRange = range; Children = []; Parent = None; Metadata = Map.empty; IsReachable = false }
        let states = control.ResumeEntries |> Map.keys |> Seq.toList
        let state = slot "state" Types.intType (Some(ValueRange.bounded -1I (bigint (List.max states))))
        let element = match owner.Type with NativeType.TSeq element -> element | _ -> failwith "Not a sequence"
        let current = slot "current" element None
        let graph = { graph with Nodes = graph.Nodes.Add(state.Id, state).Add(current.Id, current) }
        let required = EvidenceMachine.requiredValues graph control
        let captures =
            match owner.Kind with SemanticKind.SeqExpr(_, captures) -> captures |> List.choose _.SourceNodeId |> Set.ofList | _ -> Set.empty
        let live = control.LiveAcross.Values |> Seq.fold Set.union Set.empty |> Set.intersect required |> Set.union captures
        // This fixture exercises evidence and identity only. No platform,
        // physical placement, layout discharge or native readiness is claimed.
        let fields ids = ids |> Set.toList |> List.map (fun id ->
            { Source = id; ValueType = graph.Nodes[id].Type; Holds = CaptureSlotKind.Scalar(SettledSlot.Opaque "evidence fixture")
              IsCapture = false
              Field = { Name = string id; Slot = SettledSlot.Opaque "evidence fixture"
                        Offset = None; Size = None; Align = None } })
        let frame = {
            Owner = owner.Id; Generator = control.Generator; Formal = formal; State = state.Id; Current = current.Id
            Slots = fields (live |> Set.add state.Id |> Set.add current.Id)
            ScratchSlots = fields (Set.difference required live)
            Bytes = 0; Alignment = 1; ScratchBytes = 0; ScratchAlignment = 1
            Initializers = []; ResumeStates = states; Obligations = [] }
        { Graph = graph; Control = control; Frame = frame; Machine = EvidenceMachine.build graph control frame }

    let twoCuts () = fixture "let outer = seq {\n    let saved = 17\n    yield 1\n    yield saved\n}"
    let evidence fixture =
        match ContinuationEvidence.forMachine fixture.Graph fixture.Control fixture.Frame fixture.Machine with
        | Ok enrichment -> enrichment
        | Error residual -> failwithf "Expected resident continuation evidence: %A" residual
    let cuts fixture = fixture.Control.Steps.Values |> Seq.choose (fun step ->
        match step.Instruction with EvidenceControl.Instruction.Suspend(payload, state) -> Some(step, payload, state) | _ -> None) |> Seq.toList
    let retainedCut fixture = cuts fixture |> List.find (fun (step, _, _) -> not (Set.isEmpty fixture.Control.LiveAcross[step.Label]))
    let relation role target edges =
        edges |> List.filter (fun (edge: Hyperedge) -> edge.Role = role && edge.Target = target) |> Assert.Single
    let fields (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target

    let programCell () =
        let source = """
type MemorySpace = { Name: string; Kind: string; Capacity: int; Alignment: int; Granularity: int; Growth: string; Access: string; Base: int option }
type ProgramLifetimeSpaces = { Immutable: string; Mutable: string option }
type PlatformDescription = { Id: string; Spaces: MemorySpace array; ProgramLifetime: ProgramLifetimeSpaces option }
let image = { Name = "image"; Kind = "rodata"; Capacity = 1024; Alignment = 16; Granularity = 16; Growth = "fixed"; Access = "r"; Base = None }
let state = { Name = "state"; Kind = "data"; Capacity = 1024; Alignment = 16; Granularity = 16; Growth = "fixed"; Access = "rw"; Base = None }
let description = { Id = "evidence"; Spaces = [| image; state |]; ProgramLifetime = Some { Immutable = "image"; Mutable = Some "state" } }
let mutable shared = 1
let outer = seq { yield shared; shared <- shared + 1; yield shared }
"""
        let fixture = fixture source
        let context: PlatformContext = {
            PlatformId = "evidence"; Dimensions = Map.ofList ["Pointer", 64; "Register", 64]
            Representations = Map.empty; EndpointReturns = Map.empty; PlatformLibraryPath = None
            PlatformDescription = Some "Dimensions.description"; PlatformArchitecture = None; PlatformOS = None
            PlatformSourcePaths = Set.singleton (System.IO.Path.GetFullPath "dimensions.clef")
            Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
            AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None }
        let graph, diagnostics = Clef.Compiler.Nanopass.ProgramInitialization.settleValueAuthority true { fixture.Graph with Platform = Some context }
        Assert.Empty diagnostics
        let shared = graph.Nodes.Values |> Seq.filter (fun node -> match node.Kind with SemanticKind.Binding("shared", true, _, _) -> true | _ -> false) |> Assert.Single
        Assert.True((EvidenceProgram.tryValueAuthority graph shared.Id).IsSome)
        { fixture with Graph = graph }, shared.Id

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceContinuationEvidence")>]
type SequenceContinuationEvidenceCases() =
    [<Fact>]
    member _.``Cut liveness and resume evidence remain resident with exact source and generated participants``() =
        let fixture = ContinuationFacts.twoCuts ()
        let nodes, edges = fixture.Graph.Nodes, fixture.Graph.Edges
        let evidence = ContinuationFacts.evidence fixture
        let folded = EvidenceFold.foldIn { evidence with NewNodes = fixture.Machine.Nodes @ evidence.NewNodes } fixture.Graph
        for step, payload, state in ContinuationFacts.cuts fixture do
            let cut = ContinuationFacts.relation (EdgeRole.SuspensionCut state) step.Origin folded.Edges
            Assert.Equal<NodeId list>([fixture.Frame.Owner; fixture.Frame.Generator; payload], cut.Sources)
            let resume = ContinuationFacts.relation (EdgeRole.SuspensionResume state) fixture.Machine.ResumeBodies[state] folded.Edges
            Assert.Equal<NodeId list>([fixture.Frame.Owner; fixture.Frame.Generator; step.Origin], resume.Sources)
            let action = ContinuationFacts.relation (EdgeRole.SuspensionResumeAction state) fixture.Machine.CaseBodies[fixture.Machine.ResumeTargets[state]] folded.Edges
            Assert.Equal<NodeId list>([fixture.Frame.Owner; fixture.Frame.Generator; fixture.Machine.ResumeBodies[state]; step.Origin], action.Sources)
            let live = folded.Edges |> List.filter (fun edge ->
                edge.Role = EdgeRole.SuspensionLiveAcross && edge.Sources = [fixture.Frame.Owner; fixture.Frame.Generator; step.Origin])
            Assert.Equal<Set<NodeId>>(fixture.Control.LiveAcross[step.Label], live |> List.map _.Target |> Set.ofList)
        Assert.Contains(evidence.NewEdges, fun edge -> edge.Role = EdgeRole.SuspensionLiveAcross)
        let initial = ContinuationFacts.relation (EdgeRole.SuspensionResume 0) fixture.Machine.ResumeBodies[0] folded.Edges
        Assert.Equal<NodeId list>([fixture.Frame.Owner; fixture.Frame.Generator], initial.Sources)
        let initialAction = ContinuationFacts.relation (EdgeRole.SuspensionResumeAction 0) fixture.Machine.CaseBodies[fixture.Machine.ResumeTargets[0]] folded.Edges
        Assert.Equal<NodeId list>([fixture.Frame.Owner; fixture.Frame.Generator; fixture.Machine.ResumeBodies[0]], initialAction.Sources)
        let completed = ContinuationFacts.relation EdgeRole.SuspensionCompleted fixture.Machine.CompletedBody folded.Edges
        Assert.Equal<NodeId list>([fixture.Frame.Owner; fixture.Frame.Generator; fixture.Frame.State], completed.Sources)
        for edge in evidence.NewEdges do
            for id in edge.Target :: edge.Sources do Assert.True(folded.Nodes.ContainsKey id)
        let discriminants =
            evidence.NewNodes
            |> List.map (fun node ->
                match node.Kind with
                | SemanticKind.Obligation { Body = ObligationBody.IntegerLiteralRange(value, lower, upper) } ->
                    Assert.Equal(-1I, lower)
                    Assert.Equal(2I, upper)
                    Assert.False node.IsReachable
                    value
                | kind -> failwithf "Unexpected continuation obligation: %A" kind)
            |> Set.ofList
        Assert.Equal<Set<bigint>>(Set.ofList [-1I; 0I; 1I; 2I], discriminants)
        Assert.Same(nodes, fixture.Graph.Nodes)
        Assert.Same(edges, fixture.Graph.Edges)

    [<Fact>]
    member _.``An empty sequence has only initial and completed states with no fabricated cut``() =
        let fixture = ContinuationFacts.fixture "let outer: seq<int> = seq { () }"
        let evidence = ContinuationFacts.evidence fixture
        Assert.DoesNotContain(evidence.NewEdges, fun edge -> match edge.Role with EdgeRole.SuspensionCut _ | EdgeRole.SuspensionLiveAcross -> true | _ -> false)
        let values =
            evidence.NewNodes
            |> List.choose (fun node ->
                match node.Kind with
                | SemanticKind.Obligation { Body = ObligationBody.IntegerLiteralRange(value, lower, upper) }
                    when lower = -1I && upper = 0I -> Some value
                | _ -> None)
            |> Set.ofList
        Assert.Equal<Set<bigint>>(Set.ofList [-1I; 0I], values)

    [<Theory>]
    [<InlineData("initial-state")>]
    [<InlineData("zero-cut")>]
    [<InlineData("missing-live-slot")>]
    [<InlineData("wrong-delimiter")>]
    [<InlineData("missing-entry")>]
    [<InlineData("wrong-target")>]
    [<InlineData("wrong-completed-write")>]
    member _.``Malformed state control residence and generated entries cannot publish evidence``(defect: string) =
        let fixture = ContinuationFacts.twoCuts ()
        let cut, _, state = ContinuationFacts.retainedCut fixture
        let changed =
            match defect with
            | "initial-state" ->
                { fixture with Control = { fixture.Control with ResumeEntries = fixture.Control.ResumeEntries.Remove 0 } }
            | "zero-cut" ->
                let payload = match cut.Instruction with EvidenceControl.Instruction.Suspend(payload, _) -> payload | _ -> failwith "No cut"
                { fixture with Control = { fixture.Control with Steps = fixture.Control.Steps.Add(cut.Label, { cut with Instruction = EvidenceControl.Instruction.Suspend(payload, 0) }) } }
            | "missing-live-slot" ->
                let live = fixture.Control.LiveAcross[cut.Label] |> Set.toList |> List.head
                { fixture with Frame = { fixture.Frame with Slots = fixture.Frame.Slots |> List.filter (fun slot -> slot.Source <> live) } }
            | "wrong-delimiter" ->
                let edges =
                    fixture.Graph.Edges |> List.map (fun edge ->
                        if edge.Role = EdgeRole.Delimiter && edge.Target = cut.Origin then
                            { edge with Sources = [fixture.Frame.Generator; fixture.Frame.Owner] }
                        else edge)
                { fixture with Graph = { fixture.Graph with Edges = edges } }
            | "missing-entry" ->
                { fixture with Machine = { fixture.Machine with ResumeBodies = fixture.Machine.ResumeBodies.Remove state } }
            | "wrong-target" ->
                { fixture with Machine = { fixture.Machine with ResumeTargets = fixture.Machine.ResumeTargets.Add(state, -100) } }
            | "wrong-completed-write" ->
                let literals = fixture.Machine.Nodes |> List.choose (fun node ->
                    match node.Kind with SemanticKind.Literal(NativeLiteral.Int(-1L, _)) -> Some node.Id | _ -> None) |> Set.ofList
                Assert.NotEmpty literals
                let nodes =
                    fixture.Machine.Nodes |> List.map (fun node ->
                        if literals.Contains node.Id then
                            { node with Kind = SemanticKind.Literal(NativeLiteral.Int(0L, NTUKind.NTUint(NTUWidth.Resolved WidthDimension.Register))) }
                        else node)
                { fixture with Machine = { fixture.Machine with Nodes = nodes } }
            | _ -> failwith "Unknown evidence defect"
        match ContinuationEvidence.forMachine changed.Graph changed.Control changed.Frame changed.Machine with
        | Ok _ -> failwithf "Malformed %s acquired continuation evidence" defect
        | Error residual ->
            Assert.Equal(fixture.Frame.Owner, residual.Owner)
            Assert.False(System.String.IsNullOrWhiteSpace residual.Reason)

    [<Fact>]
    member _.``Resident suspension participants follow ordinary recipe replacement identities``() =
        let fixture = ContinuationFacts.twoCuts ()
        let evidence = ContinuationFacts.evidence fixture
        let graph = EvidenceFold.foldIn { evidence with NewNodes = fixture.Machine.Nodes @ evidence.NewNodes } fixture.Graph
        let cut, _, state = ContinuationFacts.retainedCut fixture
        let live = fixture.Control.LiveAcross[cut.Label] |> Set.toList |> List.head
        let ids = Set.ofList [cut.Origin; live; fixture.Machine.ResumeBodies[state]]
        let creator (node: SemanticNode) _ =
            let fresh = { node with Id = NodeId.fresh() }
            RecipeCreated { OriginalNodeId = node.Id; ReplacementRootId = fresh.Id; NewNodes = [fresh]
                            ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = "Continuation evidence replacement" }
        let recipes = EvidenceFanOut.fanOut "Baker" (fun node -> ids.Contains node.Id) creator graph
        let folded = EvidenceReplacements.foldIn recipes graph
        let remap id = recipes.ReplacementMap.TryFind id |> Option.defaultValue id
        for original in evidence.NewEdges do
            let expected = { original with Sources = List.map remap original.Sources; Target = remap original.Target }
            Assert.Contains(folded.Edges, fun edge -> ContinuationFacts.fields edge = ContinuationFacts.fields expected)

    [<Fact>]
    member _.``External cell writes retain the resolved declaration instead of acquiring private storage``() =
        let fixture = ContinuationFacts.fixture "let mutable shared = 0\nlet outer = seq { shared <- 1; yield shared; shared <- 2; yield shared }"
        let shared = fixture.Graph.Nodes.Values |> Seq.filter (fun node -> match node.Kind with SemanticKind.Binding("shared", true, _, _) -> true | _ -> false) |> Assert.Single
        Assert.Contains(fixture.Control.Steps.Values, fun step -> step.Defines.Contains shared.Id)
        Assert.DoesNotContain(shared.Id, EvidenceMachine.requiredValues fixture.Graph fixture.Control)
        Assert.DoesNotContain(fixture.Frame.Slots @ fixture.Frame.ScratchSlots, fun slot -> slot.Source = shared.Id)
        let nodes = fixture.Machine.Nodes |> List.fold (fun nodes node -> Map.add node.Id node nodes) fixture.Graph.Nodes
        let writes = fixture.Machine.Nodes |> List.choose (fun node ->
            match node.Kind with
            | SemanticKind.Set(reference, _) ->
                match nodes[reference].Kind with SemanticKind.VarRef("shared", Some source) -> Some source | _ -> None
            | _ -> None)
        Assert.Equal<NodeId list>([shared.Id; shared.Id], writes)
        Assert.Contains(fixture.Machine.Nodes, fun node -> match node.Kind with SemanticKind.VarRef("shared", Some source) -> source = shared.Id | _ -> false)
        Assert.DoesNotContain(fixture.Machine.Nodes, fun node ->
            match node.Kind with SemanticKind.FrameRead(_, source) | SemanticKind.FrameWrite(_, source, _) -> source = shared.Id | _ -> false)
        ContinuationFacts.evidence fixture |> ignore

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Declared and explicitly captured mutable cells retain their owned storage`` captured =
        let source =
            if captured then "let outer =\n    let mutable cell = 0\n    seq { cell <- 1; yield cell; cell <- 2; yield cell }"
            else "let outer = seq { let mutable cell = 0 in cell <- 1; yield cell; cell <- 2; yield cell }"
        let fixture = ContinuationFacts.fixture source
        let cell = fixture.Graph.Nodes.Values |> Seq.filter (fun node -> match node.Kind with SemanticKind.Binding("cell", true, _, _) -> true | _ -> false) |> Assert.Single
        Assert.Contains(cell.Id, EvidenceMachine.requiredValues fixture.Graph fixture.Control)
        Assert.Contains(fixture.Frame.Slots @ fixture.Frame.ScratchSlots, fun slot -> slot.Source = cell.Id)
        Assert.Contains(fixture.Machine.Nodes, fun node -> match node.Kind with SemanticKind.FrameWrite(_, source, _) -> source = cell.Id | _ -> false)
        Assert.DoesNotContain(fixture.Machine.Nodes, fun node -> match node.Kind with SemanticKind.VarRef("cell", Some source) -> source = cell.Id | _ -> false)
        ContinuationFacts.evidence fixture |> ignore

    [<Fact>]
    member _.``External declaration liveness does not fabricate suspension residence``() =
        let fixture = ContinuationFacts.fixture "let mutable shared = 1\nlet outer = seq { yield shared; yield shared }"
        let shared = fixture.Graph.Nodes.Values |> Seq.filter (fun node -> match node.Kind with SemanticKind.Binding("shared", true, _, _) -> true | _ -> false) |> Assert.Single
        Assert.Contains(fixture.Control.LiveAcross.Values, fun live -> live.Contains shared.Id)
        Assert.DoesNotContain(shared.Id, EvidenceMachine.requiredValues fixture.Graph fixture.Control)
        Assert.DoesNotContain(fixture.Frame.Slots @ fixture.Frame.ScratchSlots, fun slot -> slot.Source = shared.Id)
        // This change preserves source references; it does not establish the
        // separate startup/use/space authority needed for an external resident.
        match ContinuationEvidence.forMachine fixture.Graph fixture.Control fixture.Frame fixture.Machine with
        | Error _ -> ()
        | Ok _ -> failwith "External mutable declaration acquired unproven residence"

    [<Fact>]
    member _.``A resident scalar program cell survives suspension with its exact startup authority``() =
        let fixture, shared = ContinuationFacts.programCell ()
        Assert.Contains(fixture.Control.LiveAcross.Values, fun live -> live.Contains shared)
        Assert.DoesNotContain(fixture.Frame.Slots @ fixture.Frame.ScratchSlots, fun slot -> slot.Source = shared)
        let authority = EvidenceProgram.tryValueAuthority fixture.Graph shared |> Option.get
        let evidence = ContinuationFacts.evidence fixture
        let step, _, _ = ContinuationFacts.cuts fixture |> List.find (fun (step, _, _) -> fixture.Control.LiveAcross[step.Label].Contains shared)
        let relation = ContinuationFacts.relation EdgeRole.SuspensionLiveAcross shared evidence.NewEdges
        Assert.Equal<NodeId list>(List.distinct ([fixture.Frame.Owner; fixture.Frame.Generator; step.Origin] @ authority.Evidence.Sources), relation.Sources)
        Assert.All(relation.Sources, fun id -> Assert.True(fixture.Graph.Nodes.ContainsKey id))

    [<Theory>]
    [<InlineData("missing-authority")>]
    [<InlineData("wrong-authority")>]
    [<InlineData("descriptor-value")>]
    member _.``Program cell residence cannot bypass missing authority or prove descriptor backing`` defect =
        let fixture, shared = ContinuationFacts.programCell ()
        let graph =
            match defect with
            | "missing-authority" ->
                { fixture.Graph with Edges = fixture.Graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramValue || edge.Target <> shared) }
            | "wrong-authority" ->
                let edges =
                    fixture.Graph.Edges |> List.map (fun edge ->
                        if edge.Role = EdgeRole.ProgramValue && edge.Target = shared then { edge with Sources = List.rev edge.Sources } else edge)
                { fixture.Graph with Edges = edges }
            | "descriptor-value" ->
                { fixture.Graph with Nodes = fixture.Graph.Nodes.Add(shared, { fixture.Graph.Nodes[shared] with Type = NativeType.TSeq Types.intType }) }
            | _ -> failwith "Unknown program residence defect"
        Assert.True(EvidenceProgram.isSlotBinding graph shared)
        match ContinuationEvidence.forMachine graph fixture.Control fixture.Frame fixture.Machine with
        | Error residual ->
            Assert.Equal(fixture.Frame.Owner, residual.Owner)
            Assert.Equal(fixture.Frame.Owner, residual.Site)
            Assert.Equal("Continuation liveness lacks exact control incidence or persistent value residence.", residual.Reason)
        | Ok _ -> failwithf "Unproved %s acquired suspension residence" defect
