namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module FramePlacement = Clef.Compiler.PSGSaturation.SemanticGraph.Placement
module FrameRanges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis

module private ContinuationFields =
    // The declared-representation fixture used by DimensionalCases' generic
    // record placement gate, exercised through the actual range-selection pass.
    let context pointerBits : PlatformContext =
        let representation bits maximum : NumericRepresentation =
            { Name = "unsigned" + string bits; Capability = "native"; Family = "uint"; Bits = bits
              MinMagnitude = "0"; MaxMagnitude = maximum; Boundary = "wrap" }
        let offered = [representation 8 "255"; representation 16 "65535"; representation 64 "18446744073709551615"]
        { PlatformId = "continuation-placement-test"
          Dimensions = Map.ofList ["Pointer", pointerBits; "Register", 64]
          Representations = offered |> List.map (fun item -> item.Name, item) |> Map.ofList
          EndpointReturns = Map.empty; PlatformLibraryPath = None; PlatformDescription = None
          PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.empty
          Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
          AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None }

    let graph pointerBits =
        let result = DimensionalCases.check """
type Packet = { Ready: bool }
[<EntryPoint>]
let main _ =
    let state = 2
    let current = true
    let distance = 1000<m>
    let mutable cell = 17
    let packet = { Ready = true }
    let pair = (true, false)
    let values = seq { yield true }
    let delegated = seq { yield! values }
    cell <- 19
    ignore state
    ignore current
    ignore distance
    ignore cell
    ignore packet
    ignore pair
    ignore values
    ignore delegated
    0
"""
        DimensionalCases.noErrors result
        let platform = context pointerBits
        let graph = { result.Graph with Platform = Some platform }
        FrameRanges.run (Some platform) graph |> fst

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
        |> Assert.Single

    let capture mutableCell (node: SemanticNode) : CaptureInfo =
        { Name = "same-spelling"; Type = node.Type; IsMutable = mutableCell; SourceNodeId = Some node.Id }

    let placed = function
        | Ok (SettledLayout.Record(fields, Some bytes, Some alignment), descriptors) -> fields, bytes, alignment, descriptors
        | other -> failwithf "Expected settled continuation fields: %A" other

    let frame graph captures live =
        FramePlacement.placeContinuation graph (binding "state" graph).Id (binding "current" graph).Id captures live

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ContinuationPlacement")>]
type ContinuationPlacementCases() =
    [<Fact>]
    member _.``Scalar frame tiles bool and measured integer by selected representation without a code pointer``() =
        let graph = ContinuationFields.graph 64
        let state, current, distance = ContinuationFields.binding "state" graph, ContinuationFields.binding "current" graph, ContinuationFields.binding "distance" graph
        let fields, bytes, alignment, descriptors =
            ContinuationFields.frame graph [ContinuationFields.capture false distance] [] |> ContinuationFields.placed
        Assert.Equal(4, bytes)
        Assert.Equal(2, alignment)
        Assert.Equal<int option list>([Some 0; Some 1; Some 2], fields |> List.map _.Offset)
        Assert.Equal<int option list>([Some 1; Some 1; Some 2], fields |> List.map _.Size)
        Assert.Equal<NodeId list>([state.Id; current.Id; distance.Id], descriptors |> List.map _.Source)
        Assert.Equal<FramePlacement.ContinuationRole list>([FramePlacement.ContinuationRole.State; FramePlacement.ContinuationRole.Current; FramePlacement.ContinuationRole.Capture], descriptors |> List.map _.Role)
        Assert.Equal(SettledSlot.Integer(16, Some "unsigned16"), fields[2].Slot)
        Assert.DoesNotContain(fields, fun field -> match field.Slot with SettledSlot.Pointer _ -> true | _ -> false)
        Assert.Equal("int<m>", formatType (applySubst distance.Type))

    [<Theory>]
    [<InlineData(32)>]
    [<InlineData(64)>]
    member _.``Mutable capture preserves its exact source cell as a complete typed view``(pointerBits: int) =
        let graph = ContinuationFields.graph pointerBits
        let cell = ContinuationFields.binding "cell" graph
        let _, bytes, alignment, descriptors =
            ContinuationFields.frame graph [ContinuationFields.capture true cell] [] |> ContinuationFields.placed
        let saved = descriptors[2]
        let pointerBytes = pointerBits / 8
        Assert.Equal(cell.Id, saved.Source)
        Assert.Equal(CaptureSlotKind.CellView (applySubst cell.Type), saved.Holds)
        Assert.Equal(SettledSlot.Pointer 5, saved.Field.Slot)
        Assert.Equal(Some pointerBytes, saved.Field.Offset)
        Assert.Equal(Some (5 * pointerBytes), saved.Field.Size)
        Assert.Equal(pointerBytes, alignment)
        Assert.Equal(6 * pointerBytes, bytes)

    [<Theory>]
    [<InlineData("packet")>]
    [<InlineData("values")>]
    member _.``Immutable buffer capture retains the value view rather than reconstructing an address``(name: string) =
        let graph = ContinuationFields.graph 64
        let source = ContinuationFields.binding name graph
        let _, _, _, descriptors = ContinuationFields.frame graph [ContinuationFields.capture false source] [] |> ContinuationFields.placed
        Assert.Equal(source.Id, descriptors[2].Source)
        Assert.Equal(CaptureSlotKind.ValueView (applySubst source.Type), descriptors[2].Holds)
        Assert.Equal(Some 40, descriptors[2].Field.Size)

    [<Fact>]
    member _.``Missing and mismatched capture identities are residual rather than matched by spelling``() =
        let graph = ContinuationFields.graph 64
        let distance, current = ContinuationFields.binding "distance" graph, ContinuationFields.binding "current" graph
        let capture = ContinuationFields.capture false distance
        let missing = { graph with Nodes = graph.Nodes.Remove distance.Id }
        Assert.Equal(Error (FramePlacement.ContinuationPlacementError.MissingSource distance.Id), ContinuationFields.frame missing [capture] [])
        match ContinuationFields.frame graph [{ capture with SourceNodeId = Some current.Id }] [] with
        | Error (FramePlacement.ContinuationPlacementError.InvalidCapture _) -> ()
        | result -> failwithf "Mismatched origin was admitted: %A" result

    [<Fact>]
    member _.``Unresolved type and aggregate scalar fields stay explicit residuals``() =
        let graph = ContinuationFields.graph 64
        let current, pair = ContinuationFields.binding "current" graph, ContinuationFields.binding "pair" graph
        let generic = { current with Type = freshTypeVar current.Range }
        let unresolved = { graph with Nodes = graph.Nodes.Add(current.Id, generic) }
        for candidate, id in [unresolved, current.Id; graph, pair.Id] do
            match FramePlacement.placeContinuationLocals candidate [id] with
            | Error (FramePlacement.ContinuationPlacementError.UnsupportedField(actual, _)) -> Assert.Equal(id, actual)
            | result -> failwithf "Unsettled scalar field was assigned a carrier: %A" result

    [<Fact>]
    member _.``Transient activation placement has no persistent state or current prefixes``() =
        let graph = ContinuationFields.graph 64
        let flag, distance = ContinuationFields.binding "current" graph, ContinuationFields.binding "distance" graph
        let fields, bytes, alignment, descriptors = FramePlacement.placeContinuationLocals graph [flag.Id; distance.Id] |> ContinuationFields.placed
        Assert.Equal(4, bytes)
        Assert.Equal(2, alignment)
        Assert.Equal<int option list>([Some 0; Some 2], fields |> List.map _.Offset)
        Assert.Equal<NodeId list>([flag.Id; distance.Id], descriptors |> List.map _.Source)
        Assert.All(descriptors, fun descriptor -> Assert.Equal(FramePlacement.ContinuationRole.Local, descriptor.Role))
        let empty, size, align, descriptors = FramePlacement.placeContinuationLocals graph [] |> ContinuationFields.placed
        Assert.Empty empty
        Assert.Empty descriptors
        Assert.Equal(0, size)
        Assert.Equal(1, align)

    [<Fact>]
    member _.``Absent platform and unobservable integer ranges cannot invent frame storage``() =
        let graph = ContinuationFields.graph 64
        Assert.Equal(Error FramePlacement.ContinuationPlacementError.MissingPlatform, ContinuationFields.frame { graph with Platform = None } [] [])
        let state = ContinuationFields.binding "state" graph
        let damaged = { graph with Nodes = graph.Nodes.Add(state.Id, { state with ValueRange = Some ValueRange.Unbounded }) }
        match ContinuationFields.frame damaged [] [] with
        | Error (FramePlacement.ContinuationPlacementError.UnsettledField(actual, _)) -> Assert.Equal(state.Id, actual)
        | result -> failwithf "An unobservable state range selected storage: %A" result

    [<Fact>]
    member _.``Delegated iterator and sequence values retain typed views in current persistent and transient slots``() =
        let graph = ContinuationFields.graph 64
        let values, state = ContinuationFields.binding "values" graph, ContinuationFields.binding "state" graph
        let iterator =
            graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && match node.Kind, applySubst node.Type with
                                    | SemanticKind.Binding _, NativeType.TSeqEnumerator _ -> true
                                    | _ -> false)
            |> Assert.Single
        let _, _, _, current = FramePlacement.placeContinuation graph state.Id values.Id [] [] |> ContinuationFields.placed
        let _, _, _, persistent = ContinuationFields.frame graph [] [iterator.Id] |> ContinuationFields.placed
        let _, _, _, transient = FramePlacement.placeContinuationLocals graph [iterator.Id] |> ContinuationFields.placed
        for source, role, descriptor in [
            values, FramePlacement.ContinuationRole.Current, current[1]
            iterator, FramePlacement.ContinuationRole.LiveAcross, persistent[2]
            iterator, FramePlacement.ContinuationRole.Local, Assert.Single transient
        ] do
            Assert.Equal(source.Id, descriptor.Source)
            Assert.Equal(role, descriptor.Role)
            Assert.Equal(CaptureSlotKind.ValueView (applySubst source.Type), descriptor.Holds)
            Assert.Equal(SettledSlot.Pointer 5, descriptor.Field.Slot)
            Assert.Equal(Some 40, descriptor.Field.Size)
            Assert.Equal(Some 8, descriptor.Field.Align)
