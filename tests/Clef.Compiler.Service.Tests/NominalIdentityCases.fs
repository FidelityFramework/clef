namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module NominalRecords = Clef.Compiler.PSGSaturation.SemanticGraph.RecordInstances
module NominalPlacement = Clef.Compiler.PSGSaturation.SemanticGraph.Placement
module IdentityKeys = Clef.Compiler.NativeTypedTree.TypeIdentities
module IdentityDescriptors = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

module private NominalFixture =
    let check files =
        files |> List.map (fun (name, source) ->
            match parseStringWithDefaults source name with
            | ParseSuccess input -> input
            | other -> failwithf "Parse failed: %A" other)
        |> checkParsedInputs

    let accepted files =
        let result = check files
        DimensionalCases.noErrors result
        result.Graph

    let definitions graph =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind, node.Type with
            | SemanticKind.TypeDef(_, TypeDefKind.RecordDef _, _), NativeType.TApp(tc, _) ->
                Some(NominalTypeIdentity.ofConstructor tc, node.Type)
            | _ -> None) |> Map.ofSeq

    let ty moduleName name graph = (definitions graph)[{Module = [moduleName]; Name = name}]

    let context bits : PlatformContext =
        { PlatformId = "nominal-identity-test"; Dimensions = Map.ofList ["Pointer", bits; "Register", bits]
          Representations = Map.empty; EndpointReturns = Map.empty; PlatformLibraryPath = None
          PlatformDescription = None; PlatformArchitecture = None; PlatformOS = None
          PlatformSourcePaths = Set.empty; Predicates = Map.empty; FreestandingStartup = None
          SubstrateKind = None; RuntimeModel = None; AvailableMemorySpaces = []; DefaultMemorySpace = None
          ClockFrequencyMhz = None; NsPerWeightUnit = None }

    let split (main: string) =
        [ "left.clef", "module Left\ntype Cell = { Value: bool }\nlet cell = { Value = true }\nlet read () = cell.Value\n"
          "right.clef", "module Right\ntype Cell = { Value: float }\nlet cell = { Value = 2.0 }\nlet read () = cell.Value\n"
          "main.clef", "module Main\n[<EntryPoint>]\nlet main _ =\n    " + main.Replace("\n", "\n    ") + "\n" ]

    let fields graph ty = NominalRecords.tryFields ty graph |> Option.get

    let singleSlot expected bytes graph ty =
        match graph.Layouts.Value[IdentityKeys.ofType ty] with
        | SettledLayout.Record([field], Some actualBytes, Some alignment) ->
            Assert.Equal("Value", field.Name)
            Assert.Equal(expected, field.Slot)
            Assert.Equal(Some 0, field.Offset)
            Assert.Equal(Some bytes, field.Size)
            Assert.Equal(bytes, actualBytes)
            Assert.Equal(bytes, alignment)
        | other -> failwithf "Unexpected layout: %A" other

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "NominalIdentity")>]
type NominalIdentityCases() =
    [<Theory>]
    [<InlineData(32)>]
    [<InlineData(64)>]
    member _.``Accepted independent files retain different actual field layouts even without final projection`` bits =
        let graph = NominalFixture.split "if Left.read () && Right.read () = 2.0 then 0 else 1" |> NominalFixture.accepted
        let graph = NominalPlacement.settle (Some(NominalFixture.context bits)) graph
        let left = NominalFixture.ty "Left" "Cell" graph
        let right = NominalFixture.ty "Right" "Cell" graph
        Assert.NotEqual(IdentityKeys.ofType left, IdentityKeys.ofType right)
        NominalFixture.singleSlot SettledSlot.Bool 1 graph left
        NominalFixture.singleSlot (SettledSlot.Real 64) 8 graph right

    [<Fact>]
    member _.``Later files can project either same-spelling nominal declaration``() =
        let graph = NominalFixture.split "if Left.cell.Value && Right.cell.Value = 2.0 then 0 else 1" |> NominalFixture.accepted
        Assert.Equal<NativeType>(Types.boolType, (NominalFixture.fields graph (NominalFixture.ty "Left" "Cell" graph)).Head |> snd)
        Assert.Equal<NativeType>(Types.floatType, (NominalFixture.fields graph (NominalFixture.ty "Right" "Cell" graph)).Head |> snd)

    [<Fact>]
    member _.``Nominal owner identity survives expected record construction and aliases``() =
        let files = NominalFixture.split "let local: Left.Cell = {Value = false}\nlet alias = local\nif alias.Value || Right.cell.Value <> 2.0 then 1 else 0"
        NominalFixture.accepted files |> ignore

    [<Fact>]
    member _.``Field ranges do not join distinct nominal owners with the same spelling``() =
        let graph = NominalFixture.accepted [
            "left.clef", "module Left\ntype Cell = { Value: int }\nlet cell = {Value = 1}\n"
            "right.clef", "module Right\ntype Cell = { Value: int }\nlet cell = {Value = 4096}\n"
            "main.clef", "module Main\n[<EntryPoint>]\nlet main _ = if Left.cell.Value = 1 && Right.cell.Value = 4096 then 0 else 1\n" ]
        Assert.Equal(ValueRange.point 1I, graph.FieldRanges.Value[{Module = ["Left"]; Name = "Cell"}]["Value"])
        Assert.Equal(ValueRange.point 4096I, graph.FieldRanges.Value[{Module = ["Right"]; Name = "Cell"}]["Value"])

    [<Fact>]
    member _.``Generic instance identity preserves nominal owner and independent dimensions``() =
        let graph = NominalFixture.accepted [
            "units.clef", "module Units\n[<Measure>] type m\n[<Measure>] type s\n"
            "left.clef", "module Left\nopen Units\ntype Cell<[<Measure>] 'u> = { Value: float<'u> }\nlet cell = {Value = 2.0<m>}\n"
            "right.clef", "module Right\nopen Units\ntype Cell<[<Measure>] 'u> = { Value: float<'u> }\nlet cell = {Value = 3.0<s>}\n"
            "main.clef", "module Main\nopen Units\n[<EntryPoint>]\nlet main _ = if Left.cell.Value = 2.0<m> && Right.cell.Value = 3.0<s> then 0 else 1\n" ]
        let instances =
            graph.Nodes.Values |> Seq.choose (fun node ->
                match node.Kind, applySubst node.Type with
                | SemanticKind.RecordExpr _, (NativeType.TApp(tc, _) as ty) when tc.Name = "Cell" -> Some ty
                | _ -> None)
            |> Seq.toList
        Assert.Equal(2, instances.Length)
        let keys = instances |> List.map IdentityKeys.ofType |> Set.ofList
        Assert.Equal(2, keys.Count)
        for instance in instances do
            match instance, NominalFixture.fields graph instance with
            | NativeType.TApp(tc, [NativeType.TMeasure dimension]), ["Value", NativeType.TNum(_, fieldDimension)] ->
                Assert.Equal<Dimension>(dimension, fieldDimension)
                let unitName = if tc.Module = ["Left"] then "m" else "s"
                Assert.Equal<Dimension>(Dimension.ofBase {Module = ["Units"]; Name = unitName}, dimension)
            | other -> failwithf "Lost generic field identity: %A" other

    [<Fact>]
    member _.``A saved unresolved key is immutable and a new source substitution gets a new key``() =
        let parameter = freshTypeParam "value" TypeParamKind.Type dummyRange
        let alias = freshTypeParam "alias" TypeParamKind.Type dummyRange
        union alias parameter
        let before = IdentityKeys.ofType (NativeType.TVar alias)
        let saved = Map.ofList [before, "old snapshot"]
        Assert.Equal(IdentityKeys.ofType (NativeType.TVar parameter), before)
        bind parameter Types.boolType
        let after = IdentityKeys.ofType (NativeType.TVar alias)
        Assert.NotEqual(before, after)
        Assert.Equal("old snapshot", saved[before])
        Assert.False(saved.ContainsKey after)

    [<Fact>]
    member _.``Keys retain native kind sorts and qualified dimension identity without display encoding``() =
        let sameNameDifferentKind = { Types.intTyCon with NTUKind = Some(NTUKind.NTUint(NTUWidth.Fixed 32)) }
        Assert.NotEqual(IdentityKeys.ofType Types.intType, IdentityKeys.ofType (NativeType.TNum(CarrierRef.Carrier sameNameDifferentKind, Dimension.one)))
        let named parts name = {Types.boolTyCon with Module = parts; Name = name}
        Assert.NotEqual(IdentityKeys.ofType(NativeType.TApp(named ["A.B"] "C", [])), IdentityKeys.ofType(NativeType.TApp(named ["A"; "B"] "C", [])))
        let measured owner = NativeType.TNum(CarrierRef.Carrier Types.floatTyCon, Dimension.ofBase {Module = [owner]; Name = "m"})
        Assert.NotEqual(IdentityKeys.ofType(measured "Left"), IdentityKeys.ofType(measured "Right"))

    [<Fact>]
    member _.``Dimensioned array element ranges retain each exact measure instance``() =
        let source = """module Elements
[<Measure>] type m
[<Measure>] type s
let distances = [|1<m>; 2<m>|]
let durations = [|4096<s>; 8192<s>|]
[<EntryPoint>]
let main _ = if distances.[0] = 1<m> && durations.[0] = 4096<s> then 0 else 1
"""
        let graph = NominalFixture.accepted ["elements.clef", source]
        let element name =
            graph.Nodes.Values |> Seq.pick (fun node ->
                match node.Kind, applySubst node.Type with
                | SemanticKind.Binding(actual, _, _, _), NativeType.TApp(tc, [element]) when actual = name && tc.Name = "array" -> Some element
                | _ -> None)
        Assert.Equal(ValueRange.Bounded(1I, 2I), graph.ElementRanges.Value[IdentityKeys.ofType(element "distances")])
        Assert.Equal(ValueRange.Bounded(4096I, 8192I), graph.ElementRanges.Value[IdentityKeys.ofType(element "durations")])

    [<Theory>]
    [<InlineData("Left.Cell", false)>]
    [<InlineData("Cell", true)>]
    member _.``A descriptor seeds only its exact nominal declaration and ambiguous names retain no authority``(declared: string, ambiguous: bool) =
        let descriptor = """module Descriptors
type FieldDescriptor = { Name: string; Repr: string }
type PeripheralLayout = { Fields: FieldDescriptor array; Size: int; Alignment: int }
type StructDescriptor = { Name: string; Layout: PeripheralLayout }
let descriptor: Expr<StructDescriptor> = <@ {Name="DECLARED"; Layout={Fields=[|{Name="Value"; Repr="u8"}|]; Size=1; Alignment=1}} @>
"""
        let result = NominalFixture.check [
            "left.clef", "module Left\ntype Cell = {Value:int}\nlet cell = {Value=1}\n"
            "right.clef", "module Right\ntype Cell = {Value:int}\nlet cell = {Value=4096}\n"
            "descriptor.clef", descriptor.Replace("DECLARED", declared)
            "main.clef", "module Main\n[<EntryPoint>]\nlet main _ = if Left.cell.Value=1 && Right.cell.Value=4096 then 0 else 1\n" ]
        let read = IdentityDescriptors.readDescriptors result.Graph
        let layout = Assert.Single read.Layouts
        if ambiguous then
            Assert.True(layout.RecordType.IsNone)
            Assert.Contains(read.Findings, fun finding -> finding.Defect = IdentityDescriptors.DeclarationDefect.Ambiguous)
        else
            DimensionalCases.noErrors result
            let expected: NominalTypeIdentity = {Module=["Left"]; Name="Cell"}
            Assert.Equal<NominalTypeIdentity option>(Some expected, layout.RecordType)
            Assert.Empty read.Findings
            Assert.Equal(ValueRange.unsignedOf 8, result.Graph.FieldRanges.Value[{Module=["Left"]; Name="Cell"}]["Value"])
            Assert.Equal(ValueRange.point 4096I, result.Graph.FieldRanges.Value[{Module=["Right"]; Name="Cell"}]["Value"])

    [<Fact>]
    member _.``Abbreviations cannot replace nominal definition authority in a new graph snapshot``() =
        let source = """module Aliases
type Cell = {Value:bool}
type Alias = Cell
let value: Alias = {Value=true}
[<EntryPoint>]
let main _ = if value.Value then 0 else 1
"""
        let graph = NominalFixture.accepted ["aliases.clef", source]
        let ty = NominalFixture.ty "Aliases" "Cell" graph
        Assert.Equal<(string * NativeType) list>(["Value", Types.boolType], NominalFixture.fields graph ty)
        let definition = NominalRecords.tryDefinition {Module=["Aliases"]; Name="Cell"} graph |> Option.get
        let without = {graph with Nodes = graph.Nodes.Remove definition.Id}
        Assert.True(NominalRecords.tryDefinition {Module=["Aliases"]; Name="Cell"} without |> Option.isNone)
        Assert.True(NominalRecords.tryFields ty without |> Option.isNone)
        Assert.True(NominalRecords.tryFields ty graph |> Option.isSome)
