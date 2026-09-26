namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module LazyStorage = Clef.Compiler.PSGSaturation.SemanticGraph.LazyResidence
module LazySource = Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues
module LazyFactory = Clef.Compiler.Nanopass.LazyFactoryResults
module LazyRuntime = Clef.Compiler.Nanopass.LazyRuntime

module internal LazyResidenceFixture =
    let check source =
        match parseAndCheck source "lazy-residence.clef" with
        | Success result ->
            DimensionalCases.noErrors result
            Clef.Compiler.Nanopass.LazyElaboration.normalize result.Graph
        | result -> failwithf "Expected checked source: %A" result

    let factories = """
module LazyResidenceFixture
let make (value: bool) = lazy value
[<EntryPoint>]
let main _ =
    let first = make false
    let second = make true
    ignore (Lazy.force first)
    ignore (Lazy.force second)
    0
"""

    let prepare graph = LazyFactory.prepare graph graph.Codata.Value.Curry |> fst
    let rows role graph = graph.Edges |> List.filter (fun edge -> edge.Role = role)

    let platform pointerBits : PlatformContext =
        { PlatformId = "lazy-runtime-test"
          Dimensions = Map.ofList ["Pointer", pointerBits; "Register", 64]
          Representations = Map.empty; EndpointReturns = Map.empty
          PlatformLibraryPath = None; PlatformDescription = None; PlatformArchitecture = None; PlatformOS = None
          PlatformSourcePaths = Set.empty; Predicates = Map.empty; FreestandingStartup = None
          SubstrateKind = None; RuntimeModel = None; AvailableMemorySpaces = []; DefaultMemorySpace = None
          ClockFrequencyMhz = None; NsPerWeightUnit = None }

    let programWith source =
        let authority = """
module LazyAuthority
type WidthDeclaration = { Name: string; Bits: int }
type Representation = { Name: string; Capability: string; Family: string; Bits: int; MinMagnitude: string; MaxMagnitude: string; Boundary: string }
type TargetCore = { Widths: WidthDeclaration array; Representations: Representation array }
type MemorySpace = { Name: string; Kind: string; Capacity: int; Alignment: int; Granularity: int; Growth: string; Access: string; Base: int option }
type ProgramLifetimeSpaces = { Immutable: string; Mutable: string option }
type PlatformDescription = { Id: string; Core: TargetCore option; Spaces: MemorySpace array; ProgramLifetime: ProgramLifetimeSpaces option }
let image = { Name = "constant-image"; Kind = "rodata"; Capacity = 1024; Alignment = 16; Granularity = 16; Growth = "fixed"; Access = "r"; Base = None }
let state = { Name = "state-storage"; Kind = "data"; Capacity = 1024; Alignment = 16; Granularity = 16; Growth = "fixed"; Access = "rw"; Base = None }
let core = { Widths = [| { Name = "Pointer"; Bits = 64 }; { Name = "Register"; Bits = 64 } |]; Representations = [| { Name = "signed64"; Capability = "native"; Family = "int"; Bits = 64; MinMagnitude = "-9223372036854775808"; MaxMagnitude = "9223372036854775807"; Boundary = "wrap" }; { Name = "uint8"; Capability = "native"; Family = "uint"; Bits = 8; MinMagnitude = "0"; MaxMagnitude = "255"; Boundary = "wrap" } |] }
let description = { Id = "lazy-runtime-test"; Core = Some core; Spaces = [| image; state |]; ProgramLifetime = Some { Immutable = "constant-image"; Mutable = Some "state-storage" } }
"""
        let source = defaultArg source """
module ProgramLazy
let make (value: bool) = lazy value
let direct = lazy true
let first = make false
let second = make true
let alias = first
[<EntryPoint>]
let main _ =
    ignore (Lazy.force direct)
    ignore (Lazy.force alias)
    ignore (Lazy.force second)
    0
"""
        let inputs =
            [authority, "lazy-authority.clef"; source, "lazy-program.clef"]
            |> List.map (fun (text, path) ->
                match parseStringWithDefaults text path with
                | ParseSuccess input -> input
                | ParseError errors -> failwithf "Expected parsed program Lazy source: %A" errors)
        let signed: NumericRepresentation =
            { Name = "signed64"; Capability = "native"; Family = "int"; Bits = 64
              MinMagnitude = "-9223372036854775808"; MaxMagnitude = "9223372036854775807"; Boundary = "wrap" }
        let context =
            { platform 64 with
                PlatformDescription = Some "LazyAuthority.description"
                PlatformSourcePaths = Set.singleton (System.IO.Path.GetFullPath "lazy-authority.clef")
                Representations = Map.ofList [signed.Name, signed] }
        // Source-declared program storage and a byte-addressed CPU layout are
        // required together; this fixture makes no native emission claim.
        let result = checkParsedInputsWithPlatform inputs (Some context)
        DimensionalCases.noErrors result
        result.Graph

    let program () = programWith None

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values
        |> Seq.find (fun node ->
            match node.Kind with
            | SemanticKind.Binding(actual, false, _, _) -> node.IsReachable && actual = name
            | _ -> false)
        |> _.Id

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "LazyResidence")>]
type LazyResidenceCases() =
    [<Fact>]
    member _.``Program references retain direct formation and distinct actual factory allocations`` () =
        let graph = LazyResidenceFixture.program ()
        let read name = LazyRuntime.programInstance graph (LazyResidenceFixture.binding name graph) |> Option.get
        let directOwner, directAllocation = read "direct"
        let direct = LazySource.instance graph directOwner |> Option.get
        Assert.Equal(direct.Environment, directAllocation)
        let firstOwner, firstAllocation = read "first"
        let secondOwner, secondAllocation = read "second"
        Assert.Equal(firstOwner, secondOwner)
        Assert.NotEqual(firstAllocation, secondAllocation)
        Assert.Equal((firstOwner, firstAllocation), read "alias")
        let factory = LazySource.instance graph firstOwner |> Option.get
        Assert.NotEqual(factory.Environment, firstAllocation)
        Assert.NotEqual(factory.Environment, secondAllocation)
        for allocation in [directAllocation; firstAllocation; secondAllocation] do
            Assert.Equal(Some EscapeKind.StaticLifetime, graph.Codata.Value.Escapes.TryFind allocation)

    [<Theory>]
    [<InlineData("startup-authority")>]
    [<InlineData("factory-call")>]
    [<InlineData("allocation")>]
    member _.``Program instance access retracts with startup or exact destination authority`` defect =
        let original = LazyResidenceFixture.program ()
        let first = LazyResidenceFixture.binding "first" original
        let _, allocation = LazyRuntime.programInstance original first |> Option.get
        let graph =
            match defect with
            | "startup-authority" ->
                let edges =
                    original.Edges |> List.filter (fun edge ->
                        not (edge.Role = EdgeRole.ProgramValue && edge.Target = first))
                { original with Edges = edges }
            | "factory-call" ->
                let edges =
                    original.Edges |> List.filter (fun edge ->
                        not (edge.Role = EdgeRole.LazyResultCall && List.contains allocation edge.Sources))
                { original with Edges = edges }
            | _ ->
                let node = original.Nodes[allocation]
                { original with Nodes = original.Nodes.Add(allocation, { node with Kind = SemanticKind.LazyAllocate(NodeId.fresh()) }) }
        Assert.True((LazyRuntime.programInstance graph first).IsNone)

    [<Fact>]
    member _.``Complete local forces retain their original mutable cell in the covering activation`` () =
        let graph = LazyResidenceFixture.check """
module LocalLazy
[<EntryPoint>]
let main _ =
    let mutable cell = false
    let delayed = lazy (cell <- true; cell)
    let alias = delayed
    ignore (Lazy.force alias)
    cell <- false
    ignore (Lazy.force delayed)
    0
"""
        let reading = LazyStorage.analyze graph
        Assert.Empty reading.Residuals
        let _, contract = LazySource.instances graph |> Map.toList |> Assert.Single
        Assert.Equal(Some EscapeKind.StackScoped, reading.Sites.TryFind contract.Environment)
        Assert.Single reading.Evidence |> ignore

    [<Fact>]
    member _.``Each exact factory call receives distinct caller storage while preparation proves no residence`` () =
        let raw = LazyResidenceFixture.check LazyResidenceFixture.factories
        let before = LazyStorage.analyze raw
        Assert.NotEmpty before.Residuals
        let graph = LazyResidenceFixture.prepare raw
        Assert.Empty(LazyResidenceFixture.rows EdgeRole.LazyResidence graph)
        Assert.Single(LazyResidenceFixture.rows EdgeRole.LazyResultDestination graph) |> ignore
        let rows = LazyResidenceFixture.rows EdgeRole.LazyResultCall graph
        Assert.Equal(2, rows.Length)
        let allocations = rows |> List.map (fun row -> row.Sources[3])
        Assert.Equal(2, allocations |> List.distinct |> List.length)
        let reading = LazyStorage.analyze graph
        Assert.Empty reading.Residuals
        Assert.Equal(2, reading.Sites.Count)
        for allocation in allocations do Assert.Equal(Some EscapeKind.StackScoped, reading.Sites.TryFind allocation)
        Assert.Single reading.Destinations |> ignore
        let again = LazyResidenceFixture.prepare graph
        Assert.Equal(graph.Nodes.Count, again.Nodes.Count)
        Assert.Equal(2, (LazyResidenceFixture.rows EdgeRole.LazyResultCall again).Length)

    [<Fact>]
    member _.``Eager factory formation keeps its marker and separate deferred lazy body in residence evidence`` () =
        let source = LazyResidenceFixture.factories.Replace("= lazy value", "= eager (lazy value)")
        let graph = LazyResidenceFixture.check source |> LazyResidenceFixture.prepare |> Clef.Compiler.Nanopass.EagerDemand.normalize
        let marker, formation =
            graph.Nodes.Values |> Seq.choose (fun node ->
                match node.Kind with SemanticKind.EagerExpr value when node.IsReachable -> Some(node.Id, value) | _ -> None)
            |> Assert.Single
        let contract = LazySource.instance graph formation |> Option.get
        let reading = LazyStorage.analyze graph
        Assert.Empty reading.Residuals
        Assert.Single reading.Destinations |> ignore
        Assert.Equal(2, reading.Evidence.Length)
        for proof in reading.Evidence do Assert.Contains(marker, proof.Sources)
        let demand =
            graph.Edges |> List.filter (fun edge ->
                edge.Target = marker && edge.Role = EdgeRole.EagerDemand EagerFrontier.Expression) |> Assert.Single
        Assert.Equal<NodeId list>([marker; formation], demand.Sources)
        Assert.DoesNotContain(contract.ThunkBody, demand.Sources)
        let invalid = { graph with Nodes = graph.Nodes.Add(marker, { graph.Nodes[marker] with Children = [] }) }
        let retracted = LazyStorage.analyze invalid
        Assert.Empty retracted.Destinations
        Assert.NotEmpty retracted.Residuals

    [<Fact>]
    member _.``Hidden lazy result storage preserves source eager actual ordinal`` () =
        let source = LazyResidenceFixture.factories.Replace("make false", "make (eager false)").Replace("make true", "make (eager true)")
        let graph = LazyResidenceFixture.check source |> LazyResidenceFixture.prepare |> Clef.Compiler.Nanopass.EagerDemand.normalize
        let destinations = LazyResidenceFixture.rows EdgeRole.LazyResultDestination graph
        Assert.Single destinations |> ignore
        let calls = LazyResidenceFixture.rows EdgeRole.LazyResultCall graph
        Assert.Equal(2, calls.Length)
        for call in calls do
            let demand = graph.Edges |> List.filter (fun edge ->
                edge.Target = call.Target && edge.Role = EdgeRole.EagerDemand EagerFrontier.Actual) |> Assert.Single
            Assert.Equal(0, demand.Ordinal)
            match graph.Nodes[call.Target].Kind with
            | SemanticKind.Application(_, [destination; marker]) ->
                Assert.Equal(call.Sources[4], destination)
                Assert.Equal(marker, demand.Sources.Head)
            | _ -> failwith "Expected only the hidden destination before the original eager actual"
        let changed = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.LazyResultDestination) }
        let retracted = Clef.Compiler.Nanopass.EagerDemand.normalize changed
        for call in calls do
            Assert.DoesNotContain(retracted.Edges, fun edge ->
                edge.Target = call.Target && edge.Role = EdgeRole.EagerDemand EagerFrontier.Actual)
            Assert.Contains(retracted.Edges, fun edge -> edge.Target = call.Target && edge.Role = EdgeRole.EagerDemandPending)

    [<Fact>]
    member _.``Destination insertion preserves ordinary actual identities without introducing argument evaluation spines`` () =
        let raw = LazyResidenceFixture.check """
module LazyArguments
let make (unused: bool) (value: bool) = lazy value
[<EntryPoint>]
let main _ =
    let mutable seen = false
    let value = make (seen <- true; false) true
    ignore (Lazy.force value)
    0
"""
        let graph = LazyResidenceFixture.prepare raw
        let relation = LazyResidenceFixture.rows EdgeRole.LazyResultCall graph |> Assert.Single
        let sourceCall =
            raw.Nodes.Values
            |> Seq.filter (fun node ->
                match node.Kind with
                | SemanticKind.Application(_, arguments) ->
                    match graph.Nodes[relation.Target].Kind with
                    | SemanticKind.Application(_, actuals) -> List.tail actuals = arguments
                    | _ -> false
                | _ -> false)
            |> Assert.Single
        match sourceCall.Kind, graph.Nodes[sourceCall.Id].Kind, graph.Nodes[relation.Target].Kind with
        | SemanticKind.Application(_, original), SemanticKind.Sequential [storage; call], SemanticKind.Application(_, actuals) ->
            Assert.Equal(relation.Target, call)
            Assert.Equal<NodeId list>(original, List.tail actuals)
            Assert.DoesNotContain(storage, original)
            Assert.Equal([relation.Sources[3]], graph.Nodes[storage].Children)
        | kinds -> failwithf "Expected destination-only sequencing: %A" kinds

    [<Theory>]
    [<InlineData("missing-call")>]
    [<InlineData("changed-allocation")>]
    [<InlineData("independent-reference")>]
    member _.``Incomplete destination sets changed allocations and opaque uses retract residence`` defect =
        let original = LazyResidenceFixture.check LazyResidenceFixture.factories |> LazyResidenceFixture.prepare
        Assert.Empty((LazyStorage.analyze original).Residuals)
        let row = LazyResidenceFixture.rows EdgeRole.LazyResultCall original |> List.head
        let allocation = row.Sources[3]
        let graph =
            match defect with
            | "missing-call" ->
                let edges = original.Edges |> List.filter (fun edge ->
                    not (edge.Role = EdgeRole.LazyResultCall && edge.Target = row.Target))
                { original with Edges = edges }
            | "changed-allocation" ->
                let node = original.Nodes[allocation]
                { original with Nodes = original.Nodes.Add(allocation, { node with Kind = SemanticKind.LazyAllocate(NodeId.fresh()) }) }
            | _ ->
                let consumer = original.Nodes.Values |> Seq.find (fun node -> match node.Kind with SemanticKind.Literal _ -> true | _ -> false)
                let edge = { Class = EdgeClass.Reference; Role = EdgeRole.Argument; Sources = [allocation]; Target = consumer.Id; Ordinal = 0 }
                { original with Edges = edge :: original.Edges }
        let reading = LazyStorage.analyze graph
        Assert.False(reading.Sites.ContainsKey allocation)
        Assert.NotEmpty reading.Residuals

    [<Fact>]
    member _.``Caller destination does not extend a factory local mutable cell lifetime`` () =
        let raw = LazyResidenceFixture.check """
module RetainedLocalCell
let make () =
    let mutable cell = false
    lazy (cell <- true; cell)
[<EntryPoint>]
let main _ =
    let value = make ()
    ignore (Lazy.force value)
    0
"""
        let graph = LazyResidenceFixture.prepare raw
        let call = LazyResidenceFixture.rows EdgeRole.LazyResultCall graph |> Assert.Single
        let reading = LazyStorage.analyze graph
        Assert.False(reading.Sites.ContainsKey call.Sources[3])
        Assert.Contains(reading.Residuals, fun pending -> pending.Reason.Contains("original mutable capture cell"))

    [<Theory>]
    [<InlineData(32)>]
    [<InlineData(64)>]
    member _.``Typed lazy layout joins source guard mutable cell identity and complete storage uses`` pointerBits =
        let raw = LazyResidenceFixture.check """
module TypedLazyStorage
[<EntryPoint>]
let main _ =
    let mutable cell = false
    let delayed = lazy (cell <- true; cell)
    ignore (Lazy.force delayed)
    0
"""
        let graph, settled = LazyRuntime.settle { raw with Platform = Some(LazyResidenceFixture.platform pointerBits) }
        Assert.Empty settled.Diagnostics
        let owner, layout = settled.Layouts |> Map.toList |> Assert.Single
        let contract = LazySource.instance graph owner |> Option.get
        Assert.True(LazyRuntime.validate graph layout)
        Assert.Equal(3, layout.Slots.Length)
        Assert.Equal(contract.Computed, layout.Slots[0].Source)
        Assert.Equal(contract.Cached, layout.Slots[1].Source)
        Assert.Empty(graph.Nodes[contract.Cached].Children)
        let cell, _, _ = contract.Captured |> Assert.Single
        Assert.Equal(cell, layout.Slots[2].Source)
        Assert.Equal(CaptureSlotKind.CellView Types.boolType, layout.Slots[2].Holds)
        Assert.DoesNotContain(layout.Slots, fun slot -> slot.Source = contract.Thunk)
        Assert.False(LazyRuntime.validate graph { layout with Bytes = layout.Bytes + 1 })
        let withoutUses = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.LazyMemoization) }
        Assert.False(LazyRuntime.validate withoutUses layout)
        let withoutLayout = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.LazyLayout) }
        Assert.False(LazyRuntime.validate withoutLayout layout)
        let refreshed, current = LazyRuntime.settle graph
        Assert.Empty current.Diagnostics
        let replacement = current.Layouts[owner]
        Assert.True(LazyRuntime.validate refreshed replacement)
        Assert.Equal<NodeId list>(layout.Obligations, replacement.Obligations)
        Assert.All(layout.Obligations, fun id -> Assert.True(refreshed.Nodes.ContainsKey id))
        Assert.Single(LazyResidenceFixture.rows EdgeRole.LazyLayout refreshed) |> ignore
        let invalidated, retired = LazyRuntime.settle withoutUses
        Assert.Empty retired.Layouts
        Assert.Empty invalidated.Codata.Value.LazyLayouts
        Assert.Empty invalidated.Codata.Value.LazyOrigins
        Assert.All(layout.Obligations, fun id -> Assert.False(invalidated.Nodes.ContainsKey id))
        Assert.False(invalidated.Codata.Value.Escapes.ContainsKey contract.Environment)
        let access, environment =
            graph.Nodes.Values |> Seq.pick (fun node ->
                match node.Kind with
                | SemanticKind.LazyRead(environment, slot) when slot = cell -> Some(node.Id, environment)
                | _ -> None)
        let joint = LazyResidenceFixture.rows EdgeRole.LazyLayout graph |> Assert.Single
        for participant in [access; environment; contract.Formal; contract.ThunkBody; contract.Thunk] do
            Assert.Contains(participant, joint.Sources)
        let reference = graph.Nodes[environment]
        let reference = { reference with Kind = SemanticKind.VarRef("other_instance", Some contract.Environment); Children = [] }
        let changed = { graph with Nodes = graph.Nodes.Add(environment, reference) }
        Assert.Equal(Some owner, LazySource.tryOwner changed environment)
        Assert.False(LazyRuntime.validate changed layout)
        let retired, current = LazyRuntime.settle changed
        Assert.Empty current.Layouts
        Assert.Empty retired.Codata.Value.LazyLayouts
        Assert.False(retired.Codata.Value.Escapes.ContainsKey contract.Environment)
        Assert.All(layout.Obligations, fun id -> Assert.False(retired.Nodes.ContainsKey id))

    [<Fact>]
    member _.``Shared factory layout retains distinct actual allocations and no unproved cache instance`` () =
        let raw = LazyResidenceFixture.check LazyResidenceFixture.factories |> LazyResidenceFixture.prepare
        let graph, settled = LazyRuntime.settle { raw with Platform = Some(LazyResidenceFixture.platform 64) }
        Assert.Empty settled.Diagnostics
        let owner, layout = settled.Layouts |> Map.toList |> Assert.Single
        Assert.True(LazyRuntime.validate graph layout)
        Assert.Equal(2, settled.Residences.Count)
        let rows = LazyResidenceFixture.rows EdgeRole.LazyResultCall graph
        for row in rows do
            Assert.Equal(Some owner, settled.Origins.TryFind row.Sources[3])
        let remaining =
            graph.Edges |> List.filter (fun edge ->
                not (edge.Role = EdgeRole.LazyResultCall && edge.Target = rows.Head.Target))
        let withoutOneCall = { graph with Edges = remaining }
        Assert.False(LazyRuntime.validate withoutOneCall layout)

    [<Theory>]
    [<InlineData("source")>]
    [<InlineData("platform")>]
    [<InlineData("reachability")>]
    member _.``Revoked lazy admission retires its proof and dependent joints while preserving unrelated authority`` defect =
        let raw = LazyResidenceFixture.check "module RetiredLazy\n[<EntryPoint>]\nlet main _ =\n    let value = lazy true\n    if Lazy.force value then 0 else 1\n"
        let graph, settled = LazyRuntime.settle { raw with Platform = Some(LazyResidenceFixture.platform 64) }
        Assert.Empty settled.Diagnostics
        let owner, layout = settled.Layouts |> Map.toList |> Assert.Single
        let obligation = Assert.Single layout.Obligations
        let independent = NodeId.fresh()
        let original = graph.Nodes[obligation]
        let unrelated =
            match original.Kind with
            | SemanticKind.Obligation info ->
                { original with Id = independent; Kind = SemanticKind.Obligation { info with Id = "independent-layout-test" } }
            | kind -> failwithf "Expected owned layout obligation: %A" kind
        let dependent = { Class = EdgeClass.Provenance; Role = EdgeRole.LazyCapture false
                          Sources = [obligation]; Target = owner; Ordinal = 91 }
        let retained = { dependent with Sources = [independent]; Ordinal = 92 }
        let previous = graph.Codata.Value
        let graph =
            { graph with Nodes = graph.Nodes.Add(independent, unrelated)
                         Edges = dependent :: retained :: graph.Edges
                         Codata = lazy { previous with Escapes = previous.Escapes.Add(independent, EscapeKind.StaticLifetime) } }
        let revised =
            match defect with
            | "platform" -> { graph with Platform = None }
            | "reachability" -> { graph with Nodes = graph.Nodes |> Map.map (fun _ node -> { node with IsReachable = false }) }
            | _ -> graph
        let retired, reading = LazyRuntime.settleWhenSourceAdmitted (defect <> "source") revised
        Assert.Empty reading.Layouts
        Assert.Empty retired.Codata.Value.LazyLayouts
        Assert.Empty retired.Codata.Value.LazyOrigins
        Assert.Empty retired.Codata.Value.LazyDestinations
        Assert.Empty(LazyResidenceFixture.rows EdgeRole.LazyLayout retired)
        Assert.Empty(LazyResidenceFixture.rows EdgeRole.LazyResidence retired)
        Assert.False(retired.Nodes.ContainsKey obligation)
        Assert.DoesNotContain(retired.Edges, fun edge -> edge.Target = obligation || List.contains obligation edge.Sources)
        Assert.True(retired.Nodes.ContainsKey independent)
        Assert.Contains(retired.Edges, fun edge -> edge.Ordinal = 92 && edge.Sources = [independent])
        Assert.Equal(Some EscapeKind.StaticLifetime, retired.Codata.Value.Escapes.TryFind independent)
        Assert.All(settled.Residences.Keys, fun id -> Assert.False(retired.Codata.Value.Escapes.ContainsKey id))
        Assert.False(LazyRuntime.validate retired layout)

    [<Fact>]
    member _.``Cached string results and immutable captures retain exact program backing across factory aliases`` () =
        let source = """
module RetainedLazyStrings
let make () = lazy "factory result"
[<EntryPoint>]
let main _ =
    let original = "captured value"
    let delayed = lazy original
    let made = make ()
    let alias = made
    ignore (Lazy.force delayed)
    ignore (Lazy.force alias)
    0
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let layouts = graph.Codata.Value.LazyLayouts
        Assert.Equal(2, layouts.Count)
        let backing = Clef.Compiler.PSGSaturation.SemanticGraph.StaticStringLayout.literalEvidence graph
        let authority =
            Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.resolve graph
            |> Option.get
            |> Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.immutableProgramAuthority
        Assert.NotEmpty authority
        for layout in layouts.Values do
            Assert.True(LazyRuntime.validate graph layout)
            let cached = layout.Slots |> List.find (fun slot -> slot.Source = layout.Cached)
            Assert.Equal(CaptureSlotKind.ValueView Types.stringType, cached.Holds)
            Assert.Equal(SettledSlot.Pointer 5, cached.Field.Slot)
            let incidence = LazyResidenceFixture.rows EdgeRole.LazyResidence graph |> List.filter (fun edge -> edge.Target = layout.Owner)
            Assert.NotEmpty incidence
            for row in incidence do
                Assert.All(authority, fun id -> Assert.Contains(id, row.Sources))
                Assert.Contains(row.Sources, fun id -> backing.ContainsKey id)
            let contract = LazySource.instance graph layout.Owner |> Option.get
            Assert.Empty graph.Nodes[contract.Cached].Children
        let captured = layouts.Values |> Seq.find (fun layout -> layout.Slots |> List.exists _.IsCapture)
        Assert.Contains(captured.Slots, fun slot -> slot.IsCapture && slot.Holds = CaptureSlotKind.ValueView Types.stringType)
        let factory = Assert.Single(LazyResidenceFixture.rows EdgeRole.LazyResultCall graph)
        Assert.True(graph.Codata.Value.LazyOrigins.ContainsKey factory.Sources[3])

    [<Theory>]
    [<InlineData("pool-bytes")>]
    [<InlineData("pool-authority")>]
    [<InlineData("authority")>]
    [<InlineData("literal")>]
    [<InlineData("opaque-result")>]
    [<InlineData("mutable-alias")>]
    [<InlineData("environment-instance")>]
    [<InlineData("result-annotation")>]
    member _.``Cached string proof retracts when actual backing or immutable result provenance changes`` defect =
        let source = """
module RevisedLazyString
[<EntryPoint>]
let main _ =
    let original = "cached value"
    let delayed = lazy original
    ignore (Lazy.force delayed)
    0
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let _, layout = graph.Codata.Value.LazyLayouts |> Map.toList |> Assert.Single
        let contract = LazySource.instance graph layout.Owner |> Option.get
        let slot, _, _ = Assert.Single contract.Captured
        let pool = graph.StaticStringPool |> Option.get
        let literal = pool.Entries |> List.find (fun entry -> entry.Content = "cached value") |> _.NodeIds |> List.head
        let revised =
            match defect with
            | "pool-bytes" ->
                let bytes = pool.Bytes |> List.mapi (fun ordinal value -> if ordinal = 0 then value ^^^ 1uy else value)
                { graph with StaticStringPool = Some { pool with Bytes = bytes } }
            | "pool-authority" -> { graph with StaticStringPool = Some { pool with DeclarationNode = NodeId.fresh() } }
            | "authority" -> { graph with Nodes = graph.Nodes.Remove pool.DeclarationNode }
            | "literal" ->
                let node = graph.Nodes[literal]
                { graph with Nodes = graph.Nodes.Add(literal, { node with Kind = SemanticKind.Literal(NativeLiteral.String "new value") }) }
            | "opaque-result" ->
                let node = graph.Nodes[contract.ThunkBody]
                { graph with Nodes = graph.Nodes.Add(node.Id, { node with Kind = SemanticKind.Application(NodeId.fresh(), []); Children = [] }) }
            | "result-annotation" ->
                let body = graph.Nodes[contract.ThunkBody]
                let child = NodeId.fresh()
                let copied = { body with Id = child; Parent = Some body.Id }
                let annotated = { body with Kind = SemanticKind.TypeAnnotation(child, Types.boolType); Children = [child] }
                { graph with Nodes = graph.Nodes.Add(child, copied).Add(body.Id, annotated) }
            | "environment-instance" ->
                let environment =
                    graph.Nodes.Values |> Seq.pick (fun node ->
                        match node.Kind with
                        | SemanticKind.LazyRead(environment, actualSlot) when actualSlot = slot -> Some environment
                        | _ -> None)
                let node = graph.Nodes[environment]
                // The formation and formal describe the same schema. The
                // thunk must still use its actual invocation's formal.
                { graph with Nodes = graph.Nodes.Add(environment, { node with Kind = SemanticKind.VarRef("other_instance", Some contract.Environment); Children = [] }) }
            | _ ->
                let node = graph.Nodes[slot]
                match node.Kind with
                | SemanticKind.Binding(name, false, annotation, scope) ->
                    { graph with Nodes = graph.Nodes.Add(slot, { node with Kind = SemanticKind.Binding(name, true, annotation, scope) }) }
                | kind -> failwithf "Expected immutable original binding: %A" kind
        if defect = "environment-instance" then
            Assert.Equal(Some layout.Owner, LazySource.tryOwner revised contract.Environment)
            Assert.NotEmpty((LazySource.settle revised).Residuals)
        Assert.False(LazyRuntime.validate revised layout)
        let retired, reading = LazyRuntime.settle revised
        Assert.Empty reading.Layouts
        Assert.NotEmpty reading.Diagnostics
        Assert.Empty retired.Codata.Value.LazyLayouts
        Assert.All(layout.Obligations, fun id -> Assert.False(retired.Nodes.ContainsKey id))

    [<Fact>]
    member _.``Only an exact lazy instance admits its explicit environment thunk as ordinary callable code`` () =
        let graph = LazyResidenceFixture.check """
module LazyThunkCode
[<EntryPoint>]
let main _ =
    let delayed = lazy true
    ignore (Lazy.force delayed)
    0
"""
        let owner, contract = LazySource.instances graph |> Map.toList |> Assert.Single
        let inputs : Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.Inputs =
            { Layouts = Map.empty; Origins = Map.empty; Known = Map.empty }
        let carriers, residuals = Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.settle inputs graph
        Assert.DoesNotContain(residuals, fun pending -> pending.Occurrence = contract.Thunk)
        let code = carriers[contract.Thunk]
        Assert.Equal(contract.Thunk, code.Implementation)
        let _, parameterType, formal = code.Parameters |> Assert.Single
        Assert.Equal(LazySource.environmentType, parameterType)
        Assert.Equal(contract.Formal, formal)
        Assert.True(code.Environment.IsNone)
        Assert.False(carriers.ContainsKey owner)
        let withoutInstance = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.LazyInstance) }
        let stale, _ = Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.settle inputs withoutInstance
        Assert.False(stale.ContainsKey contract.Thunk)
