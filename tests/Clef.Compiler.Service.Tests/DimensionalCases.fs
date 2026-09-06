// Normative: clef-lang-spec/spec/{units-of-measure,ntu-types,conformance}.md
// Shared by the discoverable xUnit suite and the narrow FSI runner.
module Clef.Compiler.Service.Tests.DimensionalCases

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.Unify
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.NativeTypedTree.Expressions.Intrinsics
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

let check body =
    let source = "module Dimensions\n[<Measure>] type m\n[<Measure>] type s\n" + body
    match parseAndCheck source "dimensions.clef" with
    | Success result | CheckFailure result -> result
    | ParseFailure errors -> failwithf "Parse failed: %A" errors

let noErrors result =
    let errors = result.Diagnostics |> List.filter (fun d -> d.Severity = NativeDiagnosticSeverity.Error)
    if not errors.IsEmpty then failwithf "Unexpected errors: %A" errors

let bindingType name result =
    let ty = result.Graph.Nodes |> Map.values |> Seq.pick (fun node ->
        match node.Kind with
        | SemanticKind.Binding(name = bindingName) when bindingName = name -> Some (applySubst node.Type)
        | _ -> None)
    if hasUnboundVars ty then failwithf "Binding '%s' has unresolved type %s" name (formatType ty)
    ty

let metre = MCon("m", ["Dimensions"])
let second = MCon("s", ["Dimensions"])
let measured measure = NativeType.TApp(Types.floatTyCon, [NativeType.TMeasure measure])

let same expected actual =
    match tryUnify expected actual dummyRange with
    | Result.Ok () -> ()
    | Result.Error error -> failwith (formatError error)

let different expected actual =
    match tryUnify expected actual dummyRange with
    | Result.Error (TypeMismatch _) -> ()
    | other -> failwithf "Expected dimensional mismatch, got %A" other

let tests = [
    "power survives elaboration", fun () ->
        let result = check "let keep (x: float<m^2>) = x\n"
        noErrors result
        match bindingType "keep" result with
        | NativeType.TFun(NativeType.TApp(_, [NativeType.TMeasure measure]), _) ->
            same (measured (MProd(metre, metre))) (measured measure)
            different (measured metre) (measured measure)
        | ty -> failwithf "Measure lost during elaboration: %s" (formatType ty)

    "measures participate in identity", fun () ->
        different (measured metre) (measured second)
        different (measured metre) (measured (MCon("m", ["Other"])))
        different (measured metre) Types.floatType

    "Abelian group equality", fun () ->
        let equivalent = [
            MProd(metre, second), MProd(second, metre)
            MProd(MProd(metre, second), metre), MProd(metre, MProd(second, metre))
            MProd(MOne, metre), metre
            MProd(metre, MInv metre), MOne
            MInv(MProd(metre, second)), MProd(MInv metre, MInv second)
        ]
        for left, right in equivalent do same (measured left) (measured right)
        same Types.floatType (measured MOne)

    "literal and abbreviation survive elaboration", fun () ->
        let result = check "[<Measure>] type acceleration = m/s^2\nlet value: float<acceleration> = 1.0<m/s^2>\n"
        noErrors result
        same (measured (MProd(metre, MInv(MProd(second, second))))) (bindingType "value" result)

    "integer measures survive elaboration", fun () ->
        let result = check "let value: int<m^2> = 1<m*m>\n"
        noErrors result
        same (withMeasure Types.intType (MProd(metre, metre))) (bindingType "value" result)

    "incompatible annotation is diagnosed", fun () ->
        let result = check "let value: float<m> = 1.0<s>\n"
        if not (result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8040" && d.Severity = NativeDiagnosticSeverity.Error && d.Range.File = "dimensions.clef")) then
            failwith "Expected a located diagnostic for incompatible measures"

    "unknown measure is diagnosed", fun () ->
        let result = check "let value = 1.0<missing>\n"
        if not (result.Diagnostics |> List.exists (fun d -> d.Severity = NativeDiagnosticSeverity.Error && d.Message.Contains "missing")) then
            failwith "Unknown measure silently accepted"

    "measure syntax equivalences", fun () ->
        for annotation, literal in [
            "m * s", "s m"
            "m s", "s*m"
            "m/s/s", "m/s^2"
            "/s", "s^-1"
            "m^0", "1"
            "m/m", "1"
        ] do
            let result = check $"let value: float<{annotation}> = 1.0<{literal}>\n"
            noErrors result

    "measure variable bindings survive substitution", fun () ->
        let variable = freshMeasureVar dummyRange
        let ty = measured (MVar variable)
        same ty (measured metre)
        same (applySubst ty) (measured metre)
        different ty (measured second)
        let root = freshMeasureVar dummyRange
        same (measured (MProd(MVar root, MVar root))) (measured (MProd(metre, metre)))
        same (measured (MVar root)) (measured metre)

    "measure generalization and instantiation", fun () ->
        let variable = freshMeasureVar dummyRange
        let body = NativeType.TFun(measured (MVar variable), measured (MVar variable))
        match generalizeType body with
        | NativeType.TForall([parameter], generalized) ->
            same (instantiate [parameter] [NativeType.TMeasure metre] generalized)
                (NativeType.TFun(measured metre, measured metre))
            same (instantiate [parameter] [NativeType.TMeasure second] generalized)
                (NativeType.TFun(measured second, measured second))
        | _ -> failwith "Measure parameter was not generalized"

    "arena intrinsic lifetime instantiates independently", fun () ->
        match resolveModuleIntrinsic IntrinsicModule.Arena "fromPointer" dummyRange with
        | Resolved(_, NativeType.TForall([lifetime], body)) ->
            let arena measure = NativeType.TApp(Types.arenaTyCon, [NativeType.TMeasure measure])
            let result measure = NativeType.TFun(Types.nintType, NativeType.TFun(Types.intType, arena measure))
            same (instantiate [lifetime] [NativeType.TMeasure metre] body) (result metre)
            same (instantiate [lifetime] [NativeType.TMeasure second] body) (result second)
            different (arena metre) (arena second)
        | _ -> failwith "Arena lifetime is not a quantified measure"

    "invalid dimensional syntax is diagnosed", fun () ->
        for body in [
            "let value: float<missing> = 1.0\n"
            "let value: float<int> = 1.0\n"
            "let value: float<m^(1/2)> = 1.0\n"
            "[<Measure>] type recursiveMeasure = recursiveMeasure^2\n"
        ] do
            let result = check body
            if not (result.Diagnostics |> List.exists (fun d -> d.Severity = NativeDiagnosticSeverity.Error)) then
                failwithf "Invalid dimensional syntax silently accepted: %s" body

    "core literals and functions", fun () ->
        let result = check "let answer = 42\nlet greeting = \"hello\"\nlet keep (x: int) = x\nlet number = keep answer\n"
        noErrors result
        same Types.intType (bindingType "number" result)
        same Types.stringType (bindingType "greeting" result)

    "core record and tuple annotations", fun () ->
        let result = check "type Point = { x: int; y: int }\nlet point: Point = { x = 1; y = 2 }\nlet pair: int * string = (1, \"hello\")\n"
        noErrors result
        same (NativeType.TTuple([Types.intType; Types.stringType], false)) (bindingType "pair" result)

    "scoped measure parameters generalize at each use", fun () ->
        let result = check "let keep (x: float<'u>) : float<'u> = x\nlet distance = keep 1.0<m>\nlet duration = keep 1.0<s>\n"
        noErrors result
        same (measured metre) (bindingType "distance" result)
        same (measured second) (bindingType "duration" result)

    "repeated measure parameters share identity", fun () ->
        let result = check "let first (x: float<'u>) (y: float<'u>) = x\nlet bad = first 1.0<m> 1.0<s>\n"
        if not (result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8040")) then
            failwith "Repeated named measure parameter admitted different dimensions"

    "product and quotient infer their dimensions", fun () ->
        let result = check "let area = 2.0<m> * 3.0<m>\nlet speed = 6.0<m> / 2.0<s>\nlet scalar = 6.0<m> / 2.0<m>\n"
        noErrors result
        same (measured (MProd(metre, metre))) (bindingType "area" result)
        same (measured (MProd(metre, MInv second))) (bindingType "speed" result)
        same Types.floatType (bindingType "scalar" result)

    "inferred dimensional functions instantiate independently", fun () ->
        let result = check "let square x = x * x\nlet area = square 2.0<m>\nlet timeSquared = square 3.0<s>\nlet integerArea = square 4<m>\n"
        noErrors result
        same (measured (MProd(metre, metre))) (bindingType "area" result)
        same (measured (MProd(second, second))) (bindingType "timeSquared" result)
        same (withMeasure Types.intType (MProd(metre, metre))) (bindingType "integerArea" result)

    "dimensional square root and atan2", fun () ->
        let result = check "let length = Math.sqrt 4.0<m^2>\nlet angle = Math.atan2 1.0<m> 2.0<m>\n"
        noErrors result
        same (measured metre) (bindingType "length" result)
        same Types.floatType (bindingType "angle" result)

    "measure equation uses integer group solving", fun () ->
        let u, v = freshMeasureVar dummyRange, freshMeasureVar dummyRange
        let left = MProd(measurePower (MVar u) 2I, measurePower (MVar v) 3I)
        same (measured left) (measured metre)
        if normalizeMeasure (MProd(left, MInv metre)) <> MOne then
            failwith "Solver did not establish the measure equation"

    "integer group equations admit exactly integral solutions", fun () ->
        for a in [-5I .. 5I] do
            for b in [-5I .. 5I] do
                for c in [-3I .. 3I] do
                    let u, v = freshMeasureVar dummyRange, freshMeasureVar dummyRange
                    let left = MProd(measurePower (MVar u) a, measurePower (MVar v) b)
                    let right = measurePower metre c
                    let divisor = System.Numerics.BigInteger.GreatestCommonDivisor(a, b)
                    let solvable = if divisor = 0I then c = 0I else c % divisor = 0I
                    match tryUnify (measured left) (measured right) dummyRange with
                    | Result.Ok () when solvable ->
                        if normalizeMeasure (MProd(left, MInv right)) <> MOne then
                            failwithf "Solution does not establish %A*u + %A*v = %A*m" a b c
                    | Result.Error(TypeMismatch _) when not solvable -> ()
                    | result -> failwithf "Wrong feasibility for %A*u + %A*v = %A*m: %A" a b c result

    "incompatible dimensional arithmetic is diagnosed", fun () ->
        for expression in ["1.0<m> + 2.0<s>"; "Math.sqrt 2.0<m>"; "Math.atan2 1.0<m> 2.0<s>"; "Math.sin 1.0<m>"] do
            let result = check $"let bad = {expression}\n"
            if not (result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8040")) then
                failwithf "Incompatible arithmetic silently accepted: %s" expression
        for expression in ["1<m> * 2.0<s>"; "\"length\" * 2.0<m>"] do
            let result = check $"let bad = {expression}\n"
            if not (result.Diagnostics |> List.exists (fun d -> d.Severity = NativeDiagnosticSeverity.Error)) then
                failwithf "Invalid numeric kind silently accepted: %s" expression

    "nested generalization retains captured dimensions", fun () ->
        let result = check "let scaled (x: float<'u>) =\n    let multiply y = x * y\n    (multiply 2.0<m>, multiply 3.0<s>)\nlet pair = scaled 4.0<m>\n"
        noErrors result
        same (NativeType.TTuple([measured (MProd(metre, metre)); measured (MProd(metre, second))], false)) (bindingType "pair" result)
        let invalid = check "let outer (x: float<'u>) =\n    let same (y: float<'u>) = x + y\n    same 1.0<s>\nlet bad = outer 1.0<m>\n"
        if not (invalid.Diagnostics |> List.exists (fun d -> d.Code = "CCS8040")) then
            failwith "Captured measure was generalized independently"

    "mutable measured values remain monomorphic", fun () ->
        let result = check "let mutable value = 0.0<_>\nvalue <- 1.0<m>\nlet bad: float<s> = value\n"
        if not (result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8040")) then
            failwith "Mutable value was generalized"

    "explicit measure applications use declared parameter order", fun () ->
        let result = check "let pair<[<Measure>] 'v, [<Measure>] 'u> (x: float<'u>) (y: float<'v>) = (x, y)\nlet value = pair<s, m> 1.0<m> 2.0<s>\n"
        noErrors result
        same (NativeType.TTuple([measured metre; measured second], false)) (bindingType "value" result)
        let invalid = check "let pair<[<Measure>] 'v, [<Measure>] 'u> (x: float<'u>) (y: float<'v>) = (x, y)\nlet bad = pair<s, m> 1.0<s> 2.0<m>\n"
        if not (invalid.Diagnostics |> List.exists (fun d -> d.Code = "CCS8040")) then
            failwith "Explicit measure arguments were ignored"

    "generic measured aliases expand by kind", fun () ->
        let result = check "type Scalar<[<Measure>] 'u> = float<'u>\ntype Ratio<[<Measure>] 'v, [<Measure>] 'u> = float<'u/'v>\nlet distance: Scalar<m> = 1.0<m>\nlet duration: Scalar<s> = 2.0<s>\nlet speed: Ratio<s, m> = 3.0<m/s>\n"
        noErrors result
        same (measured metre) (bindingType "distance" result)
        same (measured second) (bindingType "duration" result)
        same (measured (MProd(metre, MInv second))) (bindingType "speed" result)

    "generic record fields instantiate dimensions", fun () ->
        let result = check "type Quantity<[<Measure>] 'u> = { Value: float<'u> }\nlet distance: Quantity<m> = { Value = 1.0<m> }\nlet duration: Quantity<s> = { Value = 2.0<s> }\nlet value = distance.Value\n"
        noErrors result
        same (measured metre) (bindingType "value" result)

    "record updates preserve dimensions", fun () ->
        let valid = check "type Quantity<[<Measure>] 'u> = { mutable Value: float<'u> }\nlet distance: Quantity<m> = { Value = 1.0<m> }\ndistance.Value <- 2.0<m>\nlet copy = { distance with Value = 3.0<m> }\nlet value = copy.Value\n"
        noErrors valid
        same (measured metre) (bindingType "value" valid)
        for update in ["{ distance with Value = 2.0<s> }"; "distance.Value <- 2.0<s>"] do
            let result = check $"type Quantity<[<Measure>] 'u> = {{ mutable Value: float<'u> }}\nlet distance: Quantity<m> = {{ Value = 1.0<m> }}\nlet bad = {update}\n"
            if not (result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8040")) then
                failwith "Record update discarded the field dimension"

    "dimensional compatibility probes preserve inference state", fun () ->
        if not (canUnify (measured (MProd(metre, second))) (measured (MProd(second, metre)))) then
            failwith "Compatibility probe ignored measure equality"
        if not (canUnify Types.floatType (measured MOne)) then failwith "Dimensionless aliases differ"
        let parameter = freshMeasureVar dummyRange
        let quantity = measured (MVar parameter)
        if not (canUnify quantity (measured metre)) then failwith "Compatible variable rejected"
        if parameter.Parent <> TypeParamState.Unbound then failwith "Compatibility probe bound the original parameter"
        let repeated = NativeType.TFun(quantity, quantity)
        if canUnify repeated (NativeType.TFun(measured metre, measured second)) then
            failwith "Compatibility probe ignored repeated variable identity"
        if parameter.Parent <> TypeParamState.Unbound then failwith "Failed probe changed the original parameter"

    "recursive functions generalize dimensions after their group", fun () ->
        for definition in [
            "let rec keep n x = if n = 0 then x else keep (n - 1) x\n"
            "let rec keep n x = if n = 0 then x else again (n - 1) x\nand again n x = keep n x\n"
        ] do
            let result = check (definition + "let distance = keep 1 1.0<m>\nlet duration = keep 2 2.0<s>\n")
            noErrors result
            same (measured metre) (bindingType "distance" result)
            same (measured second) (bindingType "duration" result)
        let local = check "let outer () =\n    let rec keep n x = if n = 0 then x else keep (n - 1) x\n    (keep 1 1.0<m>, keep 2 2.0<s>)\nlet pair = outer ()\n"
        noErrors local
        same (NativeType.TTuple([measured metre; measured second], false)) (bindingType "pair" local)

    "union case patterns instantiate dimensions", fun () ->
        let result = check "type Quantity<[<Measure>] 'u> = Quantity of float<'u>\nlet distance = Quantity 1.0<m>\nlet duration = Quantity 2.0<s>\nlet unwrap quantity = match quantity with Quantity value -> value\nlet length = unwrap distance\nlet time = unwrap duration\n"
        noErrors result
        same (measured metre) (bindingType "length" result)
        same (measured second) (bindingType "time" result)
]
