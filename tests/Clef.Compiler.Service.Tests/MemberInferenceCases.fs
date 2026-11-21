namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private MemberOracle =
    let check source = DimensionalCases.check source
    let accepted source =
        let result = check source
        DimensionalCases.noErrors result
        result
    let ty name (result: CheckResult) =
        result.Graph.Nodes.Values
        |> Seq.filter (fun node -> match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
        |> Assert.Single |> fun node -> applySubst node.Type
    let equal expected actual = Assert.Equal<NativeType>(expected, applySubst actual)
    let rejected code source =
        let result = check source
        Assert.Contains(result.Diagnostics, fun diagnostic ->
            diagnostic.Code = code && diagnostic.Severity = NativeDiagnosticSeverity.Error
            && diagnostic.Range.File = "dimensions.clef")
        result

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "MemberInference")>]
type MemberInferenceCases() =
    [<Fact>]
    member _.``An unknown ordinary field relation cannot escape as an unconstrained scheme``() =
        let result = MemberOracle.rejected "CCS8711" "let project x = x.Value\n"
        match MemberOracle.ty "project" result with
        | NativeType.TForall _ -> failwith "Unresolved receiver and field became independently quantified"
        | _ -> ()

    [<Fact>]
    member _.``Unresolved member diagnostics preserve distinct inferred and explicitly quoted receivers across checks``() =
        let source = """let read (named: '``?0``) first second =
    let a: int = first.Left
    let b: int = first.Again
    let c: int = second.Other
    let d: int = named.Explicit
    (a, b, c, d)
"""
        let check () =
            let checkedSource = MemberOracle.rejected "CCS8711" source
            checkedSource.Diagnostics |> List.filter (fun d -> d.Code = "CCS8711")
        let first = check ()
        let headers =
            [ "'``?0``.Explicit"; "'?0.Other"; "'?1.Again"; "'?1.Left" ]
            |> List.map (fun memberName ->
                $"Member constraint '{memberName}: int' remains unresolved; supply receiver context or retain it in an inline member scheme.")
        Assert.Equal<string list>(headers, first |> List.map _.Message)
        MemberOracle.accepted "let keep value = value\nlet useValue f x = f x\n" |> ignore
        let shape (d: Diagnostic) = d.Code, d.Severity, d.Range, d.Reachability, d.Message
        Assert.Equal<_ list>(first |> List.map shape, check () |> List.map shape)

    [<Fact>]
    member _.``Unresolved member constraints share inferred labels across union-find aliases and keep observed quoted names``() =
        let check parameter expectedLeft =
            let source = $"let read {parameter} q =\n    let r = if true then p else q\n    let a: int = p.Left\n    let b: int = q.Again\n    (a,b,r)\n"
            let result = MemberOracle.rejected "CCS8711" source
            let messages = result.Diagnostics |> List.filter (fun row -> row.Code = "CCS8711") |> List.map _.Message
            let fields = ["'?0.Again"; expectedLeft + ".Left"]
            Assert.Equal<string list>(fields |> List.map (fun field -> $"Member constraint '{field}: int' remains unresolved; supply receiver context or retain it in an inline member scheme."), messages)
        check "p" "'?0"
        check "(p: '``space here``)" "'``space here``"

    [<Fact>]
    member _.``Undefined member on a concrete function preserves unresolved variable identity across checks``() =
        let check () =
            let result = MemberOracle.rejected "CCS8702" "let project x = x.Value\nlet bad = project (fun y -> y)\n"
            result.Diagnostics |> List.filter (fun d -> d.Code = "CCS8702") |> List.map _.Message
        let expected = ["Type ''?0 -> '?0' does not define member 'Value'."]
        Assert.Equal<string list>(expected, check ())
        MemberOracle.accepted "let keep x = x\nlet apply f x = f x\n" |> ignore
        Assert.Equal<string list>(expected, check ())

    [<Fact>]
    member _.``A concrete actual without the required field is rejected at source checking``() =
        MemberOracle.rejected "CCS8702" "let project x = x.Value\nlet bad = project 1\n" |> ignore

    [<Fact>]
    member _.``Later nominal context solves both ordinary receiver and measured result``() =
        let result = MemberOracle.accepted """
let project x = x.Value
type Quantity<[<Measure>] 'u> = { Value: float<'u> }
let actual = { Value = 2.0<m> }
let value = project actual
"""
        MemberOracle.equal (DimensionalCases.measured DimensionalCases.metre) (MemberOracle.ty "value" result)

    [<Fact>]
    member _.``Ordinary pending member relation stays shared through immutable aliases``() =
        let result = MemberOracle.accepted "let length x = x.Length\nlet alias = length\nlet value = alias \"abc\"\n"
        MemberOracle.equal Types.intType (MemberOracle.ty "value" result)
        MemberOracle.rejected "CCS8003" "let length x = x.Length\nlet alias = length\nlet first = alias \"abc\"\nlet second = alias [|1|]\n" |> ignore

    [<Fact>]
    member _.``Resolving array membership before generalization retains element polymorphism``() =
        let result = MemberOracle.accepted """
let length values =
    let count = values.Length
    let also = Array.length values
    count + also
let first = length [|1; 2|]
let second = length [|true|]
"""
        for name in ["first"; "second"] do MemberOracle.equal Types.intType (MemberOracle.ty name result)
        match MemberOracle.ty "length" result with
        | NativeType.TForall(parameters, NativeType.TFun(NativeType.TApp(_, [NativeType.TVar element]), _)) ->
            Assert.Contains(parameters, fun parameter -> parameter.Id = element.Id)
        | other -> failwithf "Lost array element generalization: %s" (formatType other)

    [<Fact>]
    member _.``Chained pending fields solve to a fixed point using actual nominal context``() =
        let result = MemberOracle.accepted """
let project x = x.Inner.Value
type Quantity<[<Measure>] 'u> = { Value: float<'u> }
type Envelope<[<Measure>] 'u> = { Inner: Quantity<'u> }
let actual = { Inner = { Value = 3.0<s> } }
let value = project actual
"""
        MemberOracle.equal (DimensionalCases.measured DimensionalCases.second) (MemberOracle.ty "value" result)

    [<Fact>]
    member _.``Inline member schemes independently instantiate distinct measured nominal owners``() =
        let result = MemberOracle.accepted """
let inline project x = x.Value
type Distance = { Value: float<m> }
type Duration = { Value: float<s> }
let length = project { Distance.Value = 2.0<m> }
let time = project { Duration.Value = 3.0<s> }
"""
        MemberOracle.equal (DimensionalCases.measured DimensionalCases.metre) (MemberOracle.ty "length" result)
        MemberOracle.equal (DimensionalCases.measured DimensionalCases.second) (MemberOracle.ty "time" result)

    [<Fact>]
    member _.``Explicit inline member schemes preserve receiver and result relation``() =
        let result = MemberOracle.accepted """
let inline project (x: ^a) : ^b = ((^a) : (member Value: ^b) x)
type Distance = { Value: float<m> }
type Duration = { Value: float<s> }
let length = project { Distance.Value = 2.0<m> }
let time = project { Duration.Value = 3.0<s> }
"""
        MemberOracle.equal (DimensionalCases.measured DimensionalCases.metre) (MemberOracle.ty "length" result)
        MemberOracle.equal (DimensionalCases.measured DimensionalCases.second) (MemberOracle.ty "time" result)

    [<Fact>]
    member _.``Inline membership rejects an invalid actual and a conflicting result dimension``() =
        MemberOracle.rejected "CCS8702" "let inline project x = x.Value\nlet bad = project 1\n" |> ignore
        MemberOracle.rejected "CCS8040" "let inline project x = x.Value\ntype Distance = { Value: float<m> }\nlet bad: float<s> = project { Value = 2.0<m> }\n" |> ignore

    [<Fact>]
    member _.``Inline member instances do not mutate the declaration or another instance``() =
        let result = MemberOracle.accepted "let inline length x = x.Length\nlet first = length \"abc\"\nlet second = length [|true; false|]\nlet third = length [|2.0<m>|]\n"
        for name in ["first"; "second"; "third"] do MemberOracle.equal Types.intType (MemberOracle.ty name result)

    [<Fact>]
    member _.``Concrete record receivers cannot supply nonexistent fields``() =
        MemberOracle.rejected "CCS8702" "type Actual = { Known: int }\nlet actual = { Known = 1 }\nlet bad = actual.Missing\n" |> ignore

    [<Fact>]
    member _.``Known nominal generic projection remains independently measure polymorphic``() =
        let result = MemberOracle.accepted """
type Quantity<[<Measure>] 'u> = { Value: float<'u> }
let project x = x.Value
let length = project { Value = 2.0<m> }
let time = project { Value = 3.0<s> }
"""
        MemberOracle.equal (DimensionalCases.measured DimensionalCases.metre) (MemberOracle.ty "length" result)
        MemberOracle.equal (DimensionalCases.measured DimensionalCases.second) (MemberOracle.ty "time" result)

    [<Fact>]
    member _.``Distinct partial inline uses retain independent measured member premises``() =
        let result = MemberOracle.accepted """
let inline project ignored x = x.Value
let first = project ()
let second = project ()
type Distance = { Value: float<m> }
type Duration = { Value: float<s> }
let length = first { Distance.Value = 2.0<m> }
let time = second { Duration.Value = 3.0<s> }
"""
        MemberOracle.equal (DimensionalCases.measured DimensionalCases.metre) (MemberOracle.ty "length" result)
        MemberOracle.equal (DimensionalCases.measured DimensionalCases.second) (MemberOracle.ty "time" result)

    [<Fact>]
    member _.``Inline result measures follow the actual field across independently fresh schemes``() =
        let result = MemberOracle.accepted """
let inline square x = x.Value * x.Value
type Distance = { Value: float<m> }
type Duration = { Value: float<s> }
let area = square { Distance.Value = 2.0<m> }
let durationSquared = square { Duration.Value = 3.0<s> }
"""
        MemberOracle.equal (DimensionalCases.measured (Dimension.pow 2 DimensionalCases.metre)) (MemberOracle.ty "area" result)
        MemberOracle.equal (DimensionalCases.measured (Dimension.pow 2 DimensionalCases.second)) (MemberOracle.ty "durationSquared" result)

    [<Fact>]
    member _.``Repeated member support requires one result dimension before any application``() =
        let source = """
let inline impossible x =
    let length: float<m> = x.Value
    let duration: float<s> = x.Value
    (length, duration)
"""
        MemberOracle.rejected "CCS8040" source |> ignore

    [<Fact>]
    member _.``Concrete anonymous field results retain their exact measured type``() =
        let result = MemberOracle.accepted "let value = {| Value = 3.0<m> |}\nlet actual = value.Value\n"
        MemberOracle.equal (DimensionalCases.measured DimensionalCases.metre) (MemberOracle.ty "actual" result)

    [<Fact>]
    member _.``Explicit type application retains its concrete member obligation``() =
        let result = MemberOracle.accepted """
let inline project<'a, 'b> (value: 'a) : 'b = value.Value
type Distance = { Value: float<m> }
let length = project<Distance, float<m>> { Value = 2.0<m> }
"""
        MemberOracle.equal (DimensionalCases.measured DimensionalCases.metre) (MemberOracle.ty "length" result)
        MemberOracle.rejected "CCS8702" "let inline project<'a,'b> (value:'a):'b = value.Value\nlet bad = project<int,bool> 3\n" |> ignore

    [<Fact>]
    member _.``The equality solver retains lexical member premises as deferred``() =
        let receiver = freshTypeVar dummyRange
        let result = freshTypeVar dummyRange
        let premise = Constraint.HasMember(receiver, "Value", result, dummyRange)
        match Clef.Compiler.NativeTypedTree.Unify.solveConstraint premise with
        | Clef.Compiler.NativeTypedTree.Unify.Deferred [actual] -> Assert.True(obj.ReferenceEquals(premise, actual))
        | other -> failwithf "The single-constraint API lost its lexical member premise: %A" other
        match Clef.Compiler.NativeTypedTree.Unify.solveConstraints [premise] with
        | Clef.Compiler.NativeTypedTree.Unify.Deferred [actual] -> Assert.True(obj.ReferenceEquals(premise, actual))
        | other -> failwithf "A lexical member relation was lost: %A" other

    [<Theory>]
    [<InlineData("let inline broken () = (1).Missing")>]
    [<InlineData("type Actual = { Known:int }\nlet inline broken (value:Actual) = value.Missing")>]
    member _.``Generalizing an inline result cannot hide a missing concrete member``(source: string) =
        MemberOracle.rejected "CCS8702" source |> ignore
