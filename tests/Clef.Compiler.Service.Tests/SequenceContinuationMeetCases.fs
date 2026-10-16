namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module Meets = Clef.Compiler.PSGSaturation.SemanticGraph.Meets

module private ContinuationMeetFixture =
    // Integer meets consume the source selector's declared target domain.
    // Ranges alone must not invent a platform or an operand representation.
    let context : PlatformContext =
        let integer name family bits minimum maximum : NumericRepresentation =
            { Name = name; Capability = "native"; Family = family; Bits = bits
              MinMagnitude = minimum; MaxMagnitude = maximum; Boundary = "wrap" }
        let offered =
            [ integer "signed8" "int" 8 "-128" "127"
              integer "signed16" "int" 16 "-32768" "32767"
              integer "signed64" "int" 64 "-9223372036854775808" "9223372036854775807"
              integer "unsigned8" "uint" 8 "0" "255"
              integer "unsigned16" "uint" 16 "0" "65535"
              integer "unsigned64" "uint" 64 "0" "18446744073709551615" ]
        { PlatformLoading = None; PlatformId = "continuation-meet-test"
          Dimensions = Map.ofList ["Pointer", 64; "Register", 64]
          Representations = offered |> List.map (fun representation -> representation.Name, representation) |> Map.ofList
          EndpointReturns = Map.empty; PlatformLibraryPath = None; PlatformDescription = None
          PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.empty
          Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
          AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None; ProjectMemoryPolicy = None }

    let build valueType valueRange readType readRange sourceType sourceRange holds scratchHolds =
        let builder = NodeBuilder()
        let node name ty = builder.Create(SemanticKind.PatternBinding name, ty, dummyRange)
        let sequenceType = Types.mkSeqType sourceType
        let owner = node "owner" sequenceType
        let frame = node "frame" (NativeType.TNativePtr sequenceType)
        let scratch = node "scratch" (Types.mkArrayType Types.boolType)
        let source = node "source" sourceType
        let value = node "value" valueType
        let read = builder.Create(SemanticKind.FrameRead(frame.Id, source.Id), readType, dummyRange)
        let write = builder.Create(SemanticKind.FrameWrite(frame.Id, source.Id, value.Id), Types.unitType, dummyRange)
        let scratchWrite = builder.Create(SemanticKind.FrameWrite(scratch.Id, source.Id, value.Id), Types.unitType, dummyRange)
        let currentFunction = builder.Create(SemanticKind.Intrinsic
            { Module = IntrinsicModule.SeqEnumerator; Operation = "current"; Category = IntrinsicCategory.Pure; FullName = "SeqEnumerator.current" },
            NativeType.TFun(NativeType.TSeqEnumerator sourceType, readType), dummyRange)
        let current = builder.Create(SemanticKind.Application(currentFunction.Id, [frame.Id]), readType, dummyRange)
        let slot kind : ContinuationSlot =
            let field = match kind with CaptureSlotKind.Scalar field -> field | _ -> SettledSlot.Pointer 5
            { Source = source.Id; ValueType = sourceType; Holds = kind; IsCapture = true
              Field = { Name = "source"; Slot = field; Offset = None; Size = None; Align = None } }
        // This is a scalar meet unit fixture, not frame placement or generator
        // admission. The explicit platform above supplies integer selection.
        let plan: ContinuationFrame =
            { Owner = owner.Id; Generator = owner.Id; Formal = frame.Id; State = source.Id; Current = source.Id
              Slots = [slot holds]; Bytes = 0; Alignment = 1; ScratchSlots = [slot scratchHolds]
              ScratchBytes = 0; ScratchAlignment = 1; Initializers = []; ResumeStates = []; Obligations = [] }
        let raw = builder.BuildWithPlatform([], context)
        let ranges = Map.ofList [source.Id, sourceRange; value.Id, valueRange; read.Id, readRange; current.Id, readRange]
        let graph =
            { raw with Nodes = raw.Nodes |> Map.map (fun id node -> { node with IsReachable = true; ValueRange = ranges |> Map.tryFind id |> Option.flatten })
                       Codata = lazy (failwith "Continuation meet derivation forced unfinished Codata") }
        let frames = Map.ofList [owner.Id, plan]
        // A scratch reference can also carry an origin; explicit scratch
        // identity must select ScratchSlots, not the persistent frame slots.
        let origins = Map.ofList [frame.Id, owner.Id; scratch.Id, owner.Id]
        let storage = Map.ofList [scratch.Id, owner.Id]
        graph, frames, origins, storage, read.Id, write.Id, scratchWrite.Id, current.Id, value.Id

    let one (result: Map<NodeId, Meet list>) consumer operand fromWidth toWidth adaptation =
        let actual = result |> Map.find consumer |> Assert.Single
        Assert.Equal(consumer, actual.Consumer)
        Assert.Equal(operand, actual.Operand)
        Assert.Equal(fromWidth, actual.From)
        Assert.Equal(toWidth, actual.To)
        Assert.Equal(adaptation, actual.Adapt)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceContinuationMeets")>]
type SequenceContinuationMeetCases() =
    [<Theory>]
    [<InlineData("sequence", false)>]
    [<InlineData("sequence", true)>]
    [<InlineData("closure", false)>]
    [<InlineData("closure", true)>]
    member _.``Formation meets scalar captures into placed slots without loading captured cells`` boundary cell =
        let kind = if cell then CaptureSlotKind.CellView Types.intType else CaptureSlotKind.Scalar(SettledSlot.Integer(64, None))
        let graph, frames, origins, storage, _, _, _, _, value =
            ContinuationMeetFixture.build Types.intType (Some(ValueRange.Bounded(0I, 255I)))
                Types.intType (Some(ValueRange.Bounded(0I, 255I))) Types.intType (Some(ValueRange.Bounded(0I, 255I))) kind kind
        let owner, frame = frames |> Map.toList |> Assert.Single
        let source = frame.Slots.Head.Source
        let values = [source, value]
        let original = graph.Nodes[owner]
        let changed =
            if boundary = "sequence" then { original with Kind = SemanticKind.SeqExpr(frame.Generator, []) }
            else { original with Kind = SemanticKind.EnvironmentCreate(owner, values) }
        let graph = { graph with Nodes = graph.Nodes.Add(owner, changed) }
        let actual =
            if boundary = "sequence" then
                Meets.continuations frames (origins.Add(owner, owner)) storage (Map.ofList [owner, values]) graph
            else
                let layout: EnvironmentLayout =
                    { Owner = owner; Implementation = frame.Generator; Formal = frame.Formal
                      Slots = frame.Slots; Bytes = frame.Bytes; Alignment = frame.Alignment; Obligations = [] }
                Meets.environments (Map.ofList [owner, layout]) Map.empty graph
        if cell then Assert.False(actual.ContainsKey owner)
        else ContinuationMeetFixture.one actual owner value 8 64 MeetKind.ExtendUnsigned

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Frame writes retain the operand sign and exact selected storage`` signed =
        let range = if signed then ValueRange.Bounded(-128I, 127I) else ValueRange.Bounded(0I, 255I)
        let scalar bits = CaptureSlotKind.Scalar(SettledSlot.Integer(bits, None))
        let graph, frames, origins, storage, _, write, scratchWrite, _, value =
            ContinuationMeetFixture.build Types.intType (Some range) Types.intType (Some range)
                Types.intType (Some range) (scalar 64) (scalar 16)
        let originalNodes = graph.Nodes
        let actual = Meets.continuations frames origins storage Map.empty graph
        Assert.Same(originalNodes, graph.Nodes)
        let adaptation = if signed then MeetKind.ExtendSigned else MeetKind.ExtendUnsigned
        ContinuationMeetFixture.one actual write value 8 64 adaptation
        ContinuationMeetFixture.one actual scratchWrite value 8 16 adaptation

    [<Fact>]
    member _.``Frame and current reads widen from the slot to the consumer representation`` () =
        let scalar = CaptureSlotKind.Scalar(SettledSlot.Integer(8, None))
        let graph, frames, origins, storage, read, _, _, current, _ =
            ContinuationMeetFixture.build Types.intType (Some(ValueRange.Bounded(0I, 255I)))
                Types.intType (Some(ValueRange.Bounded(0I, (1I <<< 64) - 1I)))
                Types.intType (Some(ValueRange.Bounded(0I, 255I))) scalar scalar
        let actual = Meets.continuations frames origins storage Map.empty graph
        ContinuationMeetFixture.one actual read read 8 64 MeetKind.ExtendUnsigned
        ContinuationMeetFixture.one actual current current 8 64 MeetKind.ExtendUnsigned

    [<Fact>]
    member _.``Captured cell payload uses original held width and refined read range`` () =
        let cell = CaptureSlotKind.CellView Types.intType
        let graph, frames, origins, storage, read, write, _, _, value =
            ContinuationMeetFixture.build Types.intType (Some(ValueRange.Bounded(0I, 255I)))
                Types.intType (Some(ValueRange.Bounded(0I, 255I)))
                Types.intType (Some(ValueRange.Bounded(0I, 65535I))) cell cell
        let actual = Meets.continuations frames origins storage Map.empty graph
        ContinuationMeetFixture.one actual write value 8 16 MeetKind.ExtendUnsigned
        ContinuationMeetFixture.one actual read read 16 8 MeetKind.Truncate

    [<Fact>]
    member _.``Real storage meets preserve declared floating representation boundaries`` () =
        let graph, frames, origins, storage, read, write, _, current, value =
            ContinuationMeetFixture.build Types.floatType None Types.floatType None Types.floatType None
                (CaptureSlotKind.Scalar(SettledSlot.Real 32)) (CaptureSlotKind.Scalar(SettledSlot.Real 64))
        let actual = Meets.continuations frames origins storage Map.empty graph
        ContinuationMeetFixture.one actual write value 64 32 MeetKind.TruncateFloat
        ContinuationMeetFixture.one actual read read 32 64 MeetKind.ExtendFloat
        ContinuationMeetFixture.one actual current current 32 64 MeetKind.ExtendFloat

    [<Fact>]
    member _.``Buffer descriptor fields never receive integer payload adaptations`` () =
        let native = Types.mkArrayType Types.intType
        let view = CaptureSlotKind.ValueView native
        let graph, frames, origins, storage, _, _, _, _, _ =
            ContinuationMeetFixture.build native None native None native None view view
        Assert.Empty(Meets.continuations frames origins storage Map.empty graph)

    [<Fact>]
    member _.``Continuation integer meets refuse a missing platform instead of inventing widths`` () =
        let scalar = CaptureSlotKind.Scalar(SettledSlot.Integer(64, None))
        let graph, frames, origins, storage, _, write, _, _, value =
            ContinuationMeetFixture.build Types.intType (Some(ValueRange.Bounded(0I, 255I)))
                Types.intType (Some(ValueRange.Bounded(0I, 255I)))
                Types.intType (Some(ValueRange.Bounded(0I, 255I))) scalar scalar
        ContinuationMeetFixture.one (Meets.continuations frames origins storage Map.empty graph)
            write value 8 64 MeetKind.ExtendUnsigned
        let missing = { graph with Platform = None }
        Assert.Empty(Meets.continuations frames origins storage Map.empty missing)

    [<Fact>]
    member _.``Continuation writes require an observable operand range`` () =
        let scalar = CaptureSlotKind.Scalar(SettledSlot.Integer(64, None))
        let graph, frames, origins, storage, _, write, scratchWrite, _, value =
            ContinuationMeetFixture.build Types.intType (Some(ValueRange.Bounded(0I, 255I)))
                Types.intType (Some(ValueRange.Bounded(0I, 255I)))
                Types.intType (Some(ValueRange.Bounded(0I, 255I))) scalar scalar
        ContinuationMeetFixture.one (Meets.continuations frames origins storage Map.empty graph)
            write value 8 64 MeetKind.ExtendUnsigned
        let missing = { graph with Nodes = graph.Nodes.Add(value, { graph.Nodes[value] with ValueRange = None }) }
        let actual = Meets.continuations frames origins storage Map.empty missing
        Assert.False(actual.ContainsKey write)
        Assert.False(actual.ContainsKey scratchWrite)

    [<Fact>]
    member _.``Continuation operands select from the actual offered representations`` () =
        let scalar = CaptureSlotKind.Scalar(SettledSlot.Integer(64, None))
        let graph, frames, origins, storage, _, write, _, _, value =
            ContinuationMeetFixture.build Types.intType (Some(ValueRange.Bounded(0I, 255I)))
                Types.intType (Some(ValueRange.Bounded(0I, 255I)))
                Types.intType (Some(ValueRange.Bounded(0I, 255I))) scalar scalar
        ContinuationMeetFixture.one (Meets.continuations frames origins storage Map.empty graph)
            write value 8 64 MeetKind.ExtendUnsigned
        let context =
            { ContinuationMeetFixture.context with
                Representations = ContinuationMeetFixture.context.Representations.Remove("unsigned8").Remove("signed8") }
        let changed = { graph with Platform = Some context }
        ContinuationMeetFixture.one (Meets.continuations frames origins storage Map.empty changed)
            write value 16 64 MeetKind.ExtendUnsigned
