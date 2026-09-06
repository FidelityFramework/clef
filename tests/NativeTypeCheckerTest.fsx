// Build CCS with -p:CopyLocalLockFileAssemblies=true, then:
// dotnet fsi tests/NativeTypeCheckerTest.fsx [test-name substring]
// Normative: clef-lang-spec/spec/{units-of-measure,ntu-types,conformance}.md
#r "../artifacts/bin/Clef.Compiler.Service/Debug/net10.0/FSharp.Json.dll"
#r "../artifacts/bin/Clef.Compiler.Service/Debug/net10.0/XParsec.dll"
#r "../artifacts/bin/Clef.Compiler.Service/Debug/net10.0/Clef.Compiler.Service.dll"

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
    result.Graph.Nodes |> Map.values |> Seq.pick (fun node ->
        match node.Kind with
        | SemanticKind.Binding(name = bindingName) when bindingName = name -> Some (applySubst node.Type)
        | _ -> None)

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
            "let same (x: float<'u>) (y: float<'u>) = x\n"
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
]

let filter = fsi.CommandLineArgs |> Array.tryItem 1 |> Option.defaultValue ""
let selected = tests |> List.filter (fun (name, _) -> name.Contains filter)
if selected.IsEmpty then failwithf "No test matches '%s'" filter
let mutable failures = 0
for name, test in selected do
    try test (); printfn "PASS %s" name
    with error -> failures <- failures + 1; eprintfn "FAIL %s: %s" name error.Message
if failures > 0 then failwithf "%d native type check(s) failed" failures
printfn "%d native type checks passed" selected.Length
