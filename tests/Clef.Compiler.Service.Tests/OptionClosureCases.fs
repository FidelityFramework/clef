namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

module private OptionClosures =
    let option payload = NativeType.TApp(Types.optionTyCon, [payload])

    let context pointerBits : PlatformContext = {
        PlatformId = "option-closure-test"
        Dimensions = Map.ofList ["Pointer", pointerBits; "Register", 64]
        Representations = Map.empty; EndpointReturns = Map.empty; PlatformLibraryPath = None
        PlatformDescription = None; PlatformArchitecture = None; PlatformOS = None
        PlatformSourcePaths = Set.empty; Predicates = Map.empty; FreestandingStartup = None
        SubstrateKind = None; RuntimeModel = None; AvailableMemorySpaces = []
        DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None }

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable && match node.Kind with
                                | SemanticKind.Binding (actual, _, _, _) -> actual = name || actual.EndsWith("." + name)
                                | _ -> false)

    let descendants (graph: SemanticGraph) root =
        let rec visit seen id =
            if Set.contains id seen then seen
            else
                let node = graph.Nodes[id]
                List.fold visit (Set.add id seen) node.Children
        visit Set.empty root |> Set.toList |> List.map (fun id -> graph.Nodes[id])

    let concrete expected actual =
        let actual = applySubst actual
        Assert.False(hasUnboundVars actual, $"Unresolved closure type: {formatType actual}")
        Assert.Empty(freeMeasureVars actual)
        Assert.Equal(formatType expected, formatType actual)

/// C-01's capture frontier and the existing placement contract are checked after
/// source checking and Baker fold-in. This does not assert that the later complete
/// pair-representation migration or closure VC dispatch has already landed.
/// NativeCallbacks/OptionCallbacks separately checks evaluation and invocation.
[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "OptionClosures")>]
type OptionClosureTests() =
    [<Theory>]
    [<InlineData("map", 32)>]
    [<InlineData("map", 64)>]
    [<InlineData("bind", 32)>]
    [<InlineData("bind", 64)>]
    [<InlineData("filter", 32)>]
    [<InlineData("filter", 64)>]
    [<InlineData("exists", 32)>]
    [<InlineData("exists", 64)>]
    [<InlineData("forall", 32)>]
    [<InlineData("forall", 64)>]
    member _.``Stored Option operations carry a typed snapshot into a placed closure``(operation: string, pointerBits: int) =
        let distance = DimensionalCases.measuredInt DimensionalCases.metre
        let speed = DimensionalCases.measuredInt (Dimension.mul DimensionalCases.metre (Dimension.pow -1 DimensionalCases.second))
        let callbackResult, residualResult, callbackAnnotation, original, replacement, accepts =
            match operation with
            | "map" -> speed, OptionClosures.option speed, "int<m/s>", "distance / 2<s>", "distance / 3<s>", "match result with Some value -> value = 6<m/s> | None -> false"
            | "bind" -> OptionClosures.option speed, OptionClosures.option speed, "int<m/s> option", "Some (distance / 2<s>)", "None", "match result with Some value -> value = 6<m/s> | None -> false"
            | "filter" -> Types.boolType, OptionClosures.option distance, "bool", "distance > 0<m>", "distance < 0<m>", "match result with Some value -> value = 12<m> | None -> false"
            | _ -> Types.boolType, Types.boolType, "bool", "distance > 0<m>", "distance < 0<m>", "result"
        let source = $"""
let mutable callback: int<m> -> {callbackAnnotation} = fun distance -> {original}
[<EntryPoint>]
let main _ =
    let stored = Option.{operation} callback
    callback <- fun distance -> {replacement}
    let result = stored (Some 12<m>)
    if ({accepts}) then 0 else 1
"""
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        let graph = result.Graph
        let stored = OptionClosures.binding "stored" graph
        let closure =
            OptionClosures.descendants graph stored.Id
            |> List.filter (fun node ->
                node.IsReachable && match node.Kind with
                                    | SemanticKind.Lambda (_, _, captures, _, _) -> not captures.IsEmpty
                                    | _ -> false)
            |> Assert.Single
        let callbackType = NativeType.TFun(distance, callbackResult)
        let residualType = NativeType.TFun(OptionClosures.option distance, residualResult)
        OptionClosures.concrete residualType stored.Type
        OptionClosures.concrete residualType closure.Type
        Assert.False(graph.Codata.Value.Curry.AbsorbedLambdas.Contains closure.Id)
        Assert.Equal(Some (MetadataValue.Bool true), closure.Metadata.TryFind ClosureMetadata.RequiresClosurePair)
        Assert.Equal(Some (MetadataValue.String "Baker"), closure.Metadata.TryFind ElaborationMetadata.Kind)

        match closure.Kind with
        | SemanticKind.Lambda (parameters, body, captures, _, _) ->
            let _, parameterType, parameterId = Assert.Single parameters
            OptionClosures.concrete (OptionClosures.option distance) parameterType
            Assert.True(graph.Nodes.ContainsKey parameterId)
            OptionClosures.concrete parameterType graph.Nodes[parameterId].Type
            OptionClosures.concrete residualResult graph.Nodes[body].Type
            let capture = Assert.Single captures
            Assert.False capture.IsMutable
            OptionClosures.concrete callbackType capture.Type
            let sourceId = capture.SourceNodeId |> Option.defaultWith (fun () -> failwith "A closure capture has no source node")
            let snapshot = graph.Nodes[sourceId]
            Assert.True snapshot.IsReachable
            OptionClosures.concrete callbackType snapshot.Type
            match snapshot.Kind with
            | SemanticKind.Binding (_, false, _, _) -> ()
            | kind -> failwithf "The supplied callback was not evaluated into an immutable snapshot: %A" kind
            Assert.NotEqual((OptionClosures.binding "callback" graph).Id, sourceId)
            Assert.Contains(OptionClosures.descendants graph body, fun node ->
                match node.Kind with
                | SemanticKind.VarRef (_, Some definition) -> definition = sourceId
                | _ -> false)

            // As in ClosureValueCases, a source-only check leaves physical layout
            // unsettled; supply the target dimensions to the owning placement stage.
            let placements = Clef.Compiler.PSGSaturation.SemanticGraph.Placement.closures (Some (OptionClosures.context pointerBits)) graph
            let placement = placements[closure.Id]
            let slot = Assert.Single placement.Captures
            Assert.Equal(capture.SourceNodeId, slot.SourceNode)
            Assert.False slot.Mutable
            Assert.Equal(CaptureSlotKind.Address, slot.Holds)
            Assert.Equal(0, slot.ByteOffset)
            Assert.Equal(pointerBits / 8, slot.Bytes)
            Assert.Equal(slot.Bytes, placement.CapturesBytes)
            Assert.Equal(placement.PrefixBytes + slot.Bytes, placement.WithPrefixBytes)
        | kind -> failwithf "A stored Option operation has no closure: %A" kind

        let reachable = graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable) |> Seq.toList
        Assert.Contains(reachable, fun node -> match node.Kind with SemanticKind.DUGetTag _ -> true | _ -> false)
        Assert.Contains(reachable, fun node -> match node.Kind with SemanticKind.DUEliminate _ -> true | _ -> false)
        Assert.DoesNotContain(reachable, fun node ->
            match node.Kind with
            | SemanticKind.Intrinsic info -> info.Module = IntrinsicModule.Option
            | _ -> false)

    [<Fact>]
    member _.``A stored Option callable rejects a different input dimension``() =
        let result = DimensionalCases.check """
let stored = Option.map (fun (distance: int<m>) -> distance / 2<s>)
let wrong = stored (Some 1<s>)
"""
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8040")
