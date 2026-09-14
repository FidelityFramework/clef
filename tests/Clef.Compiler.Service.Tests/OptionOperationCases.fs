namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

/// Source-level schemes and Baker's graph contract. NativeCallbacks/OptionCallbacks
/// separately checks callback counts, branch behavior and captured values in a binary.
[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "OptionOperations")>]
type OptionOperationTests() =
    [<Fact>]
    member _.``Option annotations and constructors share the NTU identity used by recipes``() =
        let result = DimensionalCases.check "let present: int<m> option = Some 1<m>\nlet absent: int<m> option = None\n"
        DimensionalCases.noErrors result
        for name in ["present"; "absent"] do
            match DimensionalCases.bindingType name result with
            | NativeType.TApp (constructor, [payload]) ->
                Assert.Equal<TypeConRef>(Types.optionTyCon, constructor)
                DimensionalCases.same (DimensionalCases.measuredInt DimensionalCases.metre) payload
            | other -> failwithf "Expected canonical option, got %A" other

    [<Fact>]
    member _.``A declared Option member keeps lexical precedence over a library scheme``() =
        let result = DimensionalCases.check """
module Option =
    let map (x: int<m>) = x + 1<m>
let value = Option.map 2<m>
"""
        DimensionalCases.noErrors result
        DimensionalCases.same (DimensionalCases.measuredInt DimensionalCases.metre)
            (DimensionalCases.bindingType "value" result)

    [<Fact>]
    member _.``A value named Option keeps function field resolution``() =
        let result = DimensionalCases.check """
type Surface = { map: int<m> -> int<m> }
let Option = { map = fun x -> x + 1<m> }
let value = Option.map 2<m>
"""
        DimensionalCases.noErrors result
        DimensionalCases.same (DimensionalCases.measuredInt DimensionalCases.metre)
            (DimensionalCases.bindingType "value" result)

    [<Fact>]
    member _.``Option schemes instantiate independently and retain measured result types``() =
        let result = DimensionalCases.check """
let speed = Option.map (fun distance -> distance / 2<s>) (Some 12<m>)
let enabled = Option.map (fun value -> value > 0) (Some 3)
let elapsed = Option.bind (fun value -> if value then Some 4<s> else None) (Some true)
let filtered = Option.filter (fun distance -> distance > 0<m>) (Some 12<m>)
let exists = Option.exists (fun distance -> distance > 0<m>) (Some 12<m>)
let forall = Option.forall (fun elapsed -> elapsed > 0<s>) None
"""
        DimensionalCases.noErrors result
        let option ty = NativeType.TApp(Types.optionTyCon, [ty])
        let same name ty = DimensionalCases.same ty (DimensionalCases.bindingType name result)
        same "speed" (option (DimensionalCases.measuredInt (Dimension.mul DimensionalCases.metre (Dimension.pow -1 DimensionalCases.second))))
        same "enabled" (option Types.boolType)
        same "elapsed" (option (DimensionalCases.measuredInt DimensionalCases.second))
        same "filtered" (option (DimensionalCases.measuredInt DimensionalCases.metre))
        same "exists" Types.boolType
        same "forall" Types.boolType

    [<Fact>]
    member _.``Option HOFs settle to existing DU and conditional nodes before witnessing``() =
        let result = DimensionalCases.check """
let mapped = Option.map (fun x -> x + 1) (Some 2)
let bound = Option.bind (fun x -> Some (x > 0)) (Some 2)
let kept = Option.filter (fun x -> x > 0) (Some 2)
let found = Option.exists (fun x -> x > 0) (Some 2)
let every = Option.forall (fun x -> x > 0) (None: int option)
[<EntryPoint>]
let main _ =
    if Option.get mapped = 3 && Option.get bound && Option.get kept = 2 && found && every then 0 else 1
"""
        DimensionalCases.noErrors result
        let nodes = result.Graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable) |> Seq.toList
        Assert.Contains(nodes, fun node -> match node.Kind with SemanticKind.DUGetTag _ -> true | _ -> false)
        Assert.Contains(nodes, fun node -> match node.Kind with SemanticKind.DUEliminate _ -> true | _ -> false)
        Assert.Contains(nodes, fun node -> match node.Kind with SemanticKind.DUConstruct _ -> true | _ -> false)
        Assert.Contains(nodes, fun node -> match node.Kind with SemanticKind.IfThenElse _ -> true | _ -> false)
        Assert.DoesNotContain(nodes, fun node ->
            match node.Kind with
            | SemanticKind.Intrinsic info when info.Module = IntrinsicModule.Option -> true
            | _ -> false)

    [<Theory>]
    [<InlineData("map")>]
    [<InlineData("bind")>]
    [<InlineData("filter")>]
    [<InlineData("exists")>]
    [<InlineData("forall")>]
    member _.``Option input dimensions are checked before decomposition``(operation: string) =
        let callback =
            match operation with
            | "map" -> "(fun (x: int<s>) -> x)"
            | "bind" -> "(fun (x: int<s>) -> Some x)"
            | _ -> "(fun (x: int<s>) -> x > 0<s>)"
        let result = DimensionalCases.check $"let bad = Option.{operation} {callback} (Some 1<m>)"
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8040")

    [<Theory>]
    [<InlineData("filter")>]
    [<InlineData("exists")>]
    [<InlineData("forall")>]
    member _.``Option predicates must return bool``(operation: string) =
        let result = DimensionalCases.check $"let bad = Option.{operation} (fun x -> x + 1) (Some 2)"
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Severity = NativeDiagnosticSeverity.Error)
