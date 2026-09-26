namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module UnionPlacement = Clef.Compiler.PSGSaturation.SemanticGraph.Placement

module private UnionPlacementFixture =
    let context bits : PlatformContext =
        { PlatformId = "union-placement-test"; Dimensions = Map.ofList ["Pointer", bits; "Register", bits]
          Representations = Map.empty; EndpointReturns = Map.empty; PlatformLibraryPath = None
          PlatformDescription = None; PlatformArchitecture = None; PlatformOS = None
          PlatformSourcePaths = Set.empty; Predicates = Map.empty; FreestandingStartup = None
          SubstrateKind = None; RuntimeModel = None; AvailableMemorySpaces = []; DefaultMemorySpace = None
          ClockFrequencyMhz = None; NsPerWeightUnit = None }

    let union fields =
        NativeType.TUnion(mkTypeConRef "AlignedChoice" 0 TypeLayout.Union,
                         fields |> List.mapi (fun index fields -> { Name = "Case" + string index; Index = index; Fields = fields }))

    let place context ty =
        let builder = NodeBuilder()
        builder.Create(SemanticKind.PatternBinding "value", ty, dummyRange) |> ignore
        let raw = builder.Build []
        let placed = UnionPlacement.settle context { raw with Platform = context }
        placed.Layouts.Value.Values |> Seq.filter (function SettledLayout.Union _ -> true | _ -> false) |> Assert.Single

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "UnionPlacement")>]
type UnionPlacementCases() =
    [<Theory>]
    [<InlineData(32, "option")>]
    [<InlineData(64, "option")>]
    [<InlineData(32, "result")>]
    [<InlineData(64, "result")>]
    [<InlineData(32, "union")>]
    [<InlineData(64, "union")>]
    member _.``Every union family aligns its retained descriptor payload and allocation`` bits family =
        let descriptor = Types.mkArrayType Types.uint8Type
        let ty =
            match family with
            | "option" -> NativeType.TApp(Types.optionTyCon, [descriptor])
            | "result" -> NativeType.TApp(mkTypeConRef "Result" 2 TypeLayout.Union, [Types.boolType; descriptor])
            | _ -> UnionPlacementFixture.union [[]; [None, Types.boolType]; [None, descriptor]]
        match UnionPlacementFixture.place (Some(UnionPlacementFixture.context bits)) ty with
        | SettledLayout.Union(cases, Some offset, Some bytes, Some alignment) ->
            let word = bits / 8
            Assert.Equal(word, offset)
            Assert.Equal(word, alignment)
            Assert.Equal(6 * word, bytes)
            Assert.Contains(cases, fun (_, slot) -> slot = Some(SettledSlot.Pointer 5))
            Assert.Equal(0, offset % alignment)
            Assert.Equal(0, bytes % alignment)
        | other -> failwithf "Descriptor union did not settle: %A" other

    [<Theory>]
    [<InlineData(32, 32)>]
    [<InlineData(64, 48)>]
    member _.``Maximum alignment is independent from maximum payload size and requires tail padding`` bits expectedBytes =
        let ty = UnionPlacementFixture.union [[]; [None, Types.mkArrayType Types.uint8Type]; [None, Types.floatType]]
        match UnionPlacementFixture.place (Some(UnionPlacementFixture.context bits)) ty with
        | SettledLayout.Union(_, Some offset, Some bytes, Some alignment) ->
            Assert.Equal(8, offset)
            Assert.Equal(8, alignment)
            Assert.Equal(expectedBytes, bytes)
        | other -> failwithf "Mixed descriptor/real union did not settle: %A" other

    [<Fact>]
    member _.``Payload-free cases retain only their discriminant storage`` () =
        let ty = UnionPlacementFixture.union [[]; []]
        match UnionPlacementFixture.place (Some(UnionPlacementFixture.context 64)) ty with
        | SettledLayout.Union(cases, Some 1, Some 1, Some 1) -> Assert.All(cases, fun (_, payload) -> Assert.True payload.IsNone)
        | other -> failwithf "Empty cases acquired payload storage: %A" other

    [<Theory>]
    [<InlineData("no-platform")>]
    [<InlineData("fabric")>]
    [<InlineData("opaque")>]
    member _.``Missing extent authority leaves union placement unsettled`` missing =
        let platform = UnionPlacementFixture.context 64
        let context =
            match missing with
            | "no-platform" -> None
            | "fabric" -> Some { platform with SubstrateKind = Some SubstrateKind.FPGA }
            | _ -> Some platform
        let payload = if missing = "opaque" then NativeType.TError "unsettled member" else Types.mkArrayType Types.uint8Type
        let ty = UnionPlacementFixture.union [[]; [None, payload]]
        match UnionPlacementFixture.place context ty with
        | SettledLayout.Union(_, None, None, None) -> ()
        | other -> failwithf "Union invented an offset, extent or alignment: %A" other
