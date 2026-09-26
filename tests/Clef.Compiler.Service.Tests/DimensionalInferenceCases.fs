namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module InferenceRecords = Clef.Compiler.PSGSaturation.SemanticGraph.RecordInstances

module private InferenceOracle =
    let binding name (result: CheckResult) =
        result.Graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false) |> Assert.Single
    let ty name result = (binding name result).Type |> applySubst
    let check source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        result
    // Comparison never unifies the expected answer into an inference cell.
    let equalType expected actual = Assert.Equal<NativeType>(applySubst expected, applySubst actual)
    let quantity expectedKind expectedDimension ty =
        match applySubst ty with
        | NativeType.TNum(carrier, dimension) ->
            match CarrierRef.resolve carrier with
            | CarrierRef.Carrier actual -> Assert.Equal(expectedKind, actual.Name)
            | _ -> failwith "Numeric kind remained unresolved"
            let dimension = resolveDim dimension
            Assert.Empty dimension.Vars
            Assert.Equal<Dimension>(expectedDimension, dimension)
        | other -> failwithf "Expected a resolved numeric type, got %s" (formatType other)
    // Type checking is the oracle here, before executable reachability can
    // downgrade a diagnostic in an otherwise unused library declaration.
    let errors result = result.Diagnostics |> List.filter (fun diagnostic -> diagnostic.Severity = NativeDiagnosticSeverity.Error)
    let reject code source =
        let result = DimensionalCases.check source
        Assert.Contains(errors result, fun diagnostic -> diagnostic.Code = code && diagnostic.Range.File = "dimensions.clef")
    let m = DimensionalCases.metre
    let s = DimensionalCases.second
    let mul = Dimension.mul
    let pow = Dimension.pow

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "DimensionalInference")>]
type DimensionalInferenceCases() =
    [<Fact>]
    member _.``Unannotated residual composition instantiates complete measure schemes independently``() =
        let result = InferenceOracle.check """
let compose f g x = f (g x)
let square x = x * x
let inverse x = 1.0 / x
let inverseSquare = compose inverse square
let distance = inverseSquare 2.0<m>
let duration = inverseSquare 3.0<s>
"""
        InferenceOracle.quantity "float" (InferenceOracle.pow -2 InferenceOracle.m) (InferenceOracle.ty "distance" result)
        InferenceOracle.quantity "float" (InferenceOracle.pow -2 InferenceOracle.s) (InferenceOracle.ty "duration" result)

    [<Fact>]
    member _.``Unannotated nested helpers retain captured dimensions while generalizing their own operand``() =
        let result = InferenceOracle.check """
let scaled x =
    let multiply y = x * y
    (multiply 2.0<m>, multiply 3.0<s>)
let result = scaled 4.0<m>
"""
        let measured = DimensionalCases.measured
        InferenceOracle.equalType (NativeType.TTuple([measured (InferenceOracle.pow 2 InferenceOracle.m); measured (InferenceOracle.mul InferenceOracle.m InferenceOracle.s)], false)) (InferenceOracle.ty "result" result)

    [<Fact>]
    member _.``A quantified inferred measure is recorded as a scheme and each use retains a concrete substitution``() =
        let result = InferenceOracle.check "let inverse x = 1.0 / x\nlet distance = inverse 2.0<m>\nlet duration = inverse 3.0<s>\n"
        let occurrences = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.VarRef("inverse", _) -> true | _ -> false) |> Seq.toList
        Assert.Equal(2, occurrences.Length)
        for occurrence in occurrences do
            match occurrence.Metadata.TryFind SchemeMetadata.Declaration with
            | Some(MetadataValue.Type(NativeType.TForall(parameters, body))) ->
                let quantified = parameters |> List.filter (fun parameter -> parameter.Kind = TypeParamKind.Measure) |> List.map _.Id |> Set.ofList
                Assert.NotEmpty quantified
                let measures = freeMeasureVars body |> List.map _.Id |> Set.ofList
                Assert.True(Set.isSubset measures quantified)
                Assert.NotEmpty measures
                Assert.Empty(freeMeasureVars occurrence.Type)
                Assert.False(hasUnboundVars occurrence.Type)
            | other -> failwithf "Lost the declaration's inferred quantified scheme: %A" other
        InferenceOracle.quantity "float" (Dimension.inv InferenceOracle.m) (InferenceOracle.ty "distance" result)
        InferenceOracle.quantity "float" (Dimension.inv InferenceOracle.s) (InferenceOracle.ty "duration" result)

    [<Fact>]
    member _.``An unresolved shared mutable measure is diagnosed rather than counted as a generic scheme``() =
        let result = DimensionalCases.check "let mutable state = 0.0<_>\n"
        Assert.Contains(InferenceOracle.errors result, fun diagnostic -> diagnostic.Code = "CCS8047")
        let state = InferenceOracle.ty "state" result
        match state with NativeType.TForall _ -> failwith "Shared mutable storage was generalized" | _ -> ()
        Assert.NotEmpty(freeMeasureVars state)

    [<Fact>]
    member _.``Additional source constraints narrow shared anonymous measures and aliases consistently``() =
        let prefix = "let mutable state = 0.0<_>\nlet observed = state\n"
        // These are separate complete checks of progressively constrained source.
        // They do not assert reuse or incremental compilation of graph revisions.
        let pending = DimensionalCases.check prefix
        Assert.Contains(InferenceOracle.errors pending, fun diagnostic -> diagnostic.Code = "CCS8047")
        for spelling, expected in ["m", InferenceOracle.m; "s", InferenceOracle.s] do
            let result = InferenceOracle.check (prefix + $"state <- 2.0<{spelling}>\nlet finalValue = state\n")
            for name in ["state"; "observed"; "finalValue"] do InferenceOracle.quantity "float" expected (InferenceOracle.ty name result)
        InferenceOracle.reject "CCS8040" (prefix + "state <- 2.0<m>\nstate <- 3.0<s>\n")

    [<Fact>]
    member _.``Unannotated nominal projection helpers preserve generic measure instances through aliases``() =
        let result = InferenceOracle.check """
type Quantity<[<Measure>] 'u> = { Value: float<'u> }
let unwrap quantity = quantity.Value
let alias = unwrap
let distance = { Value = 3.0<m> }
let duration = { Value = 4.0<s> }
let length = alias distance
let time = alias duration
"""
        InferenceOracle.quantity "float" InferenceOracle.m (InferenceOracle.ty "length" result)
        InferenceOracle.quantity "float" InferenceOracle.s (InferenceOracle.ty "time" result)
        for name, expected in ["distance", InferenceOracle.m; "duration", InferenceOracle.s] do
            let fields = InferenceRecords.tryFields (InferenceOracle.ty name result) result.Graph |> Option.get
            InferenceOracle.quantity "float" expected (fields |> List.exactlyOne |> snd)

    [<Fact>]
    member _.``Measured tuple projection and immutable aliases retain correlated native kinds``() =
        let result = InferenceOracle.check """
let project (left, right) = (left * right, left / right)
let original = (6<m>, 2<s>)
let alias = original
let product, quotient = project alias
"""
        InferenceOracle.quantity "int" (InferenceOracle.mul InferenceOracle.m InferenceOracle.s) (InferenceOracle.ty "product" result)
        InferenceOracle.quantity "int" (InferenceOracle.mul InferenceOracle.m (Dimension.inv InferenceOracle.s)) (InferenceOracle.ty "quotient" result)

    [<Fact>]
    member _.``Coupled exponent constraints solve both anonymous actual dimensions together``() =
        let result = InferenceOracle.check """
let paired x y = (x * y, x / y)
let result: float<m^3*s> * float<m/s> = paired 2.0<_> 3.0<_>
"""
        for literal, expected in [2.0, InferenceOracle.pow 2 InferenceOracle.m; 3.0, InferenceOracle.mul InferenceOracle.m InferenceOracle.s] do
            let actuals = result.Graph.Nodes.Values |> Seq.filter (fun node ->
                match node.Kind with SemanticKind.Literal(NativeLiteral.Float(value, _)) -> value = literal | _ -> false) |> Seq.toList
            Assert.NotEmpty actuals
            for actual in actuals do InferenceOracle.quantity "float" expected actual.Type

    [<Fact>]
    member _.``Individually solvable exponent equations reject a jointly nonintegral solution``() =
        InferenceOracle.reject "CCS8041" "let paired x y = (x * y, x / y)\nlet bad: float<m^2*s> * float<m/s> = paired 2.0<_> 3.0<_>\n"

    [<Fact>]
    member _.``Coupled scheme uses do not leak one actual solution into another``() =
        let result = InferenceOracle.check """
let paired x y = (x * y, x / y)
let first = paired 2.0<m^2> 3.0<m*s>
let second = paired 4.0<s^2> 5.0<m/s>
"""
        let measured = DimensionalCases.measured
        InferenceOracle.equalType (NativeType.TTuple([measured (InferenceOracle.mul (InferenceOracle.pow 3 InferenceOracle.m) InferenceOracle.s); measured (InferenceOracle.mul InferenceOracle.m (Dimension.inv InferenceOracle.s))], false)) (InferenceOracle.ty "first" result)
        InferenceOracle.equalType (NativeType.TTuple([measured (InferenceOracle.mul InferenceOracle.m InferenceOracle.s); measured (InferenceOracle.mul (InferenceOracle.pow 3 InferenceOracle.s) (Dimension.inv InferenceOracle.m))], false)) (InferenceOracle.ty "second" result)

    [<Fact>]
    member _.``Independent mutable factory instances infer dimensions while aliases retain one cell``() =
        let header = "type Cell<'a> = { mutable Value: 'a option }\nlet make () = { Value = None }\n"
        let result = InferenceOracle.check (header + "let distance = make ()\nlet duration = make ()\ndistance.Value <- Some 1.0<m>\nduration.Value <- Some 2.0<s>\n")
        for name, expected in ["distance", InferenceOracle.m; "duration", InferenceOracle.s] do
            match InferenceRecords.tryFields (InferenceOracle.ty name result) result.Graph |> Option.get |> List.exactlyOne |> snd |> applySubst with
            | NativeType.TApp(_, [value]) -> InferenceOracle.quantity "float" expected value
            | other -> failwithf "Lost inferred mutable payload: %A" other
        InferenceOracle.reject "CCS8040" (header + "let distance = make ()\nlet alias = distance\ndistance.Value <- Some 1.0<m>\nalias.Value <- Some 2.0<s>\n")

    [<Fact>]
    member _.``A fully applied factory returning a callable does not borrow residual generalization``() =
        InferenceOracle.reject "CCS8040" "let make () =\n    let mutable state = None\n    fun value -> state <- Some value\nlet shared = make ()\nshared 1.0<m>\nshared 2.0<s>\n"
        InferenceOracle.reject "CCS8040" "let inline make () =\n    let mutable state = None\n    fun value -> state <- Some value\nlet shared = make ()\nshared 1.0<m>\nshared 2.0<s>\n"

    [<Fact>]
    member _.``Residual generalization retains captured shared storage constraints``() =
        InferenceOracle.reject "CCS8040" "let mutable state = None\nlet store ignored value = state <- Some value\nlet residual = store ()\nresidual 1.0<m>\nresidual 2.0<s>\n"

    [<Fact>]
    member _.``An underapplied body may contain deferred effects without changing measure quantification``() =
        let result = InferenceOracle.check """
let mutable calls = 0
let multiply factor value =
    calls <- calls + 1
    factor * value
let twice = multiply 2.0
let length = twice 3.0<m>
let time = twice 4.0<s>
"""
        InferenceOracle.quantity "float" InferenceOracle.m (InferenceOracle.ty "length" result)
        InferenceOracle.quantity "float" InferenceOracle.s (InferenceOracle.ty "time" result)
        Assert.Contains(result.Graph.Nodes.Values, fun node -> match node.Kind with SemanticKind.Set _ -> true | _ -> false)

    [<Fact>]
    member _.``Tuple arguments retain one logical boundary after a curried prefix``() =
        let result = InferenceOracle.check """
let product factor (left, right) = factor * left * right
let twice = product 2.0
let area = twice (3.0<m>, 4.0<m>)
let mixed = twice (5.0<m>, 6.0<s>)
"""
        InferenceOracle.quantity "float" (InferenceOracle.pow 2 InferenceOracle.m) (InferenceOracle.ty "area" result)
        InferenceOracle.quantity "float" (InferenceOracle.mul InferenceOracle.m InferenceOracle.s) (InferenceOracle.ty "mixed" result)
        let declaration = InferenceOracle.binding "product" result
        let rec implementation id =
            let node = result.Graph.Nodes[id]
            match node.Kind with
            | SemanticKind.Lambda(parameters, _, _, _, _) -> parameters
            | SemanticKind.Binding _ | SemanticKind.TypeAnnotation _ -> implementation (List.exactlyOne node.Children)
            | _ -> failwithf "Expected original callable declaration, got %A" node.Kind
        let parameters = implementation declaration.Id
        Assert.Equal(2, parameters.Length)
        match parameters[1] |> fun (_, ty, _) -> applySubst ty with
        | NativeType.TTuple([_; _], false) -> ()
        | other -> failwithf "Tuple formal was flattened: %A" other

    [<Fact>]
    member _.``Inline nested tuple projections preserve measured element annotations``() =
        let result = InferenceOracle.check """
let inline project ((left: float<'u>), (right, divisor)) = left * right / divisor
let value = project (6.0<m>, (8.0<s>, 2.0<m>))
"""
        InferenceOracle.quantity "float" InferenceOracle.s (InferenceOracle.ty "value" result)
        InferenceOracle.reject "CCS8040" "let project ((left, right): float<m> * float<s>) = left / right\nlet invalid = project (2.0<s>, 3.0<m>)\n"

    [<Fact>]
    member _.``Nominal projection inference respects visible record identities and field kind``() =
        let result = InferenceOracle.check """
module Hidden =
    type Other<[<Measure>] 'u> = { Value: int<'u> }
type Quantity<[<Measure>] 'u> = { Value: float<'u> }
let unwrap quantity = quantity.Value
let value = unwrap { Value = 2.0<m> }
"""
        InferenceOracle.quantity "float" InferenceOracle.m (InferenceOracle.ty "value" result)
        InferenceOracle.reject "CCS8003" "type Quantity<[<Measure>] 'u> = { Value: float<'u> }\nlet unwrap quantity = quantity.Value\nlet invalid = unwrap 2.0<m>\n"

    [<Fact>]
    member _.``Ambiguous field labels do not manufacture an unconstrained projection scheme``() =
        InferenceOracle.reject "CCS8704" "type Distance = { Value: float<m> }\ntype Duration = { Value: float<s> }\nlet unwrap quantity = quantity.Value\n"
        let result = InferenceOracle.check """
type Distance = { Value: float<m> }
type Duration = { Value: float<s> }
let unwrap (quantity: Distance) = quantity.Value
let value = unwrap { Distance.Value = 2.0<m> }
"""
        InferenceOracle.quantity "float" InferenceOracle.m (InferenceOracle.ty "value" result)

    [<Theory>]
    [<InlineData("CCS8701", "let empty = { }")>]
    [<InlineData("CCS8702", "type A = { Known: int }\nlet bad = { Missing = 1 }")>]
    [<InlineData("CCS8703", "type A = { First: int }\ntype B = { Second: int }\nlet bad = { First = 1; Second = 2 }")>]
    member _.``Field resolution diagnostics distinguish empty unknown and conflicting labels``(code: string, source: string) =
        InferenceOracle.reject code source

    [<Fact>]
    member _.``Record construction requires one admissible owner independently of declaration order``() =
        let first = "type First = { Value: float<m> }\n"
        let second = "type Second = { Value: float<m> }\n"
        for declarations in [first + second; second + first] do
            InferenceOracle.reject "CCS8704" (declarations + "let ambiguous = { Value = 2.0<m> }\n")
            let annotated = InferenceOracle.check (declarations + "let selected: First = { Value = 2.0<m> }\nlet value = selected.Value\n")
            InferenceOracle.quantity "float" InferenceOracle.m (InferenceOracle.ty "value" annotated)
            let qualified = InferenceOracle.check (declarations + "let selected = { First.Value = 2.0<m> }\nlet value = selected.Value\n")
            InferenceOracle.quantity "float" InferenceOracle.m (InferenceOracle.ty "value" qualified)
        let complete = InferenceOracle.check "type Complete = { Value: float<m> }\ntype Extra = { Value: float<m>; Other: int }\nlet selected = { Value = 2.0<m> }\nlet value = selected.Value\n"
        InferenceOracle.quantity "float" InferenceOracle.m (InferenceOracle.ty "value" complete)

    [<Fact>]
    member _.``An actual declared argument type disambiguates a record literal at each scheme use``() =
        for inlineModifier in [""; "inline "] do
            for declarations, invoke in ["", "unwrap ()"; "let alias = unwrap\n", "alias ()"; "let partial = unwrap ()\n", "partial"] do
                let source =
                    "type Quantity<[<Measure>] 'u> = { Value: float<'u> }\n"
                    + "type Other<[<Measure>] 'u> = { Value: float<'u> }\n"
                    + "let " + inlineModifier + "unwrap ignored (quantity: Quantity<'u>) = quantity.Value\n"
                    + declarations
                    + "let length = " + invoke + " { Value = 3.0<m> }\n"
                    + "let time = " + invoke + " { Value = 4.0<s> }\n"
                let result = InferenceOracle.check source
                InferenceOracle.quantity "float" InferenceOracle.m (InferenceOracle.ty "length" result)
                InferenceOracle.quantity "float" InferenceOracle.s (InferenceOracle.ty "time" result)
        let concrete =
            "type Quantity<[<Measure>] 'u> = { Value: float<'u> }\n"
            + "type Other<[<Measure>] 'u> = { Value: float<'u> }\n"
            + "let unwrap (quantity: Quantity<m>) = quantity.Value\n"
        InferenceOracle.reject "CCS8040" (concrete + "let wrongDimension = unwrap { Value = 1.0<s> }\n")
        InferenceOracle.reject "CCS8003" (concrete + "let wrongOwner = unwrap { Other.Value = 1.0<m> }\n")
