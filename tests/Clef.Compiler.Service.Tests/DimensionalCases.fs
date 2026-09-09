// Normative: clef-lang-spec/spec/{units-of-measure,ntu-types,conformance}.md
// Shared by the discoverable xUnit suite and the narrow FSI runner.
module Clef.Compiler.Service.Tests.DimensionalCases

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
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
    if hasUnboundVars ty || not (List.isEmpty (freeMeasureVars ty)) then
        failwithf "Binding '%s' has unresolved type %s" name (formatType ty)
    ty

let metre = Dimension.ofBase { Name = "m"; Module = ["Dimensions"] }
let second = Dimension.ofBase { Name = "s"; Module = ["Dimensions"] }
let measured measure = NativeType.TNum(CarrierRef.Carrier Types.floatTyCon, measure)
let measuredInt measure = NativeType.TNum(CarrierRef.Carrier Types.intTyCon, measure)
let product (left, right) = Dimension.mul left right
// These algebra cases enumerate only small integral exponents.
let power dimension (exponent: bigint) = Dimension.pow (int exponent) dimension
let recordFamily fields = layoutOf (NativeType.TAnon(fields, true))

let same expected actual =
    match tryUnify expected actual dummyRange with
    | Result.Ok () -> ()
    | Result.Error error -> failwith (formatError error)

let different expected actual =
    match tryUnify expected actual dummyRange with
    | Result.Error (MeasureMismatch _ | NoIntegerSolution _) -> ()
    | other -> failwithf "Expected dimensional mismatch, got %A" other

let tests = [
    "unused executable helper warning targets its source name and clears on reference", fun () ->
        let units = "module App.Units\n[<Measure>] type m\n[<Measure>] type s\nlet speed (distance: float<m>) (elapsed: float<s>) = distance / elapsed\nlet speedIntegers (distance: int<m>) (elapsed: int<s>) = distance / elapsed\n"
        let main call = "module App.Main\nopen App.Units\n[<EntryPoint>]\nlet main _ = if " + call + " then 0 else 1\n"
        let checkedFiles call =
            ["Units.clef", units; "Main.clef", main call] |> List.map (fun (file, source) ->
                match parseStringWithDefaults source file with
                | ParseSuccess input -> input
                | ParseError errors -> failwithf "Parse failed: %A" errors)
            |> fun inputs -> checkParsedInputsWithPlatformAndSources inputs None (Set.ofList ["Units.clef"; "Main.clef"])
        let result = checkedFiles "speed 12.0<m> 3.0<s> > 0.0<m/s>"
        noErrors result
        match result.Diagnostics |> List.filter Diagnostic.isUnnecessary with
        | [warning] ->
            if warning.Code <> "CCS8500" || Diagnostic.effectiveSeverity warning <> NativeDiagnosticSeverity.Warning
               || warning.Range.File <> "Units.clef" || warning.Range.Start.Line <> 5
               || warning.Range.Start.Column <> 4 || warning.Range.End.Column <> 17 then
                failwithf "Unused helper did not receive a warning at its exact name: %A" warning
        | warnings -> failwithf "Expected one own-source helper warning: %A" warnings
        let used = checkedFiles "speed 12.0<m> 3.0<s> > 0.0<m/s> && speedIntegers 12<m> 3<s> > 0<m/s>"
        noErrors used
        if used.Diagnostics |> List.exists Diagnostic.isUnnecessary then failwith "Adding a resolved reference did not clear the unused warning"

    "unused warnings require executable source ownership and preserve dependency APIs", fun () ->
        let files = [
            "Dependency.clef", "module Dependency\nlet publicApi (x: int) = x\n"
            "Application.clef", "module Application\nlet inline identity x = x\n[<EntryPoint>]\nlet main _ = identity 0\n"
        ]
        let inputs = files |> List.map (fun (file, source) ->
            match parseStringWithDefaults source file with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Parse failed: %A" errors)
        for result in [
            checkParsedInputsWithPlatformAndSources inputs None (Set.singleton "Application.clef")
            checkParsedInputsWithPlatformAndSources inputs None Set.empty
            checkParsedInputsWithPlatform inputs None
        ] do
            noErrors result
            if result.Diagnostics |> List.exists Diagnostic.isUnnecessary then
                failwith "Dependency/library surface or a substituted inline use was incorrectly reported as unused"

    "unused warnings do not obscure a failed declaration or intentional underscore binding", fun () ->
        let source = "module Application\nlet broken (x: int) = missing\nlet _reserved (x: int) = x\n[<EntryPoint>]\nlet main _ = 0\n"
        let input =
            match parseStringWithDefaults source "Application.clef" with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Parse failed: %A" errors
        let result = checkParsedInputsWithPlatformAndSources [input] None (Set.singleton "Application.clef")
        if not (result.Diagnostics |> List.exists (fun diagnostic -> diagnostic.Code = "CCS8009")) then
            failwith "Expected the original unresolved-value diagnostic"
        if result.Diagnostics |> List.exists Diagnostic.isUnnecessary then
            failwith "An unused warning obscured a source error or ignored an underscore declaration"

    "library output preserves public APIs even with a CPU target and main-named binding", fun () ->
        let directory = System.IO.Path.Combine(System.IO.Path.GetTempPath(), "clef-unused-library-" + System.Guid.NewGuid().ToString("N"))
        System.IO.Directory.CreateDirectory directory |> ignore
        try
            let project = System.IO.Path.Combine(directory, "Library.fidproj")
            System.IO.File.WriteAllText(System.IO.Path.Combine(directory, "Library.clef"),
                "module Library\nlet publicApi (x: int) = x\nlet main _ = 0\n")
            for target, output, expectedWarning in ["cpu", "console", true; "cpu", "library", false; "library", "library", false] do
                System.IO.File.WriteAllText(project,
                    $"[package]\nname = \"Library\"\nversion = \"0.1.0\"\n[compilation]\ntarget = \"{target}\"\n[build]\nsources = [\"Library.clef\"]\noutput_kind = \"{output}\"\n")
                match Clef.Compiler.Project.ProjectChecker.checkProject project with
                | Result.Error error -> failwith error
                | Result.Ok result ->
                    noErrors result.CheckResult
                    let warning = result.CheckResult.Diagnostics |> List.exists Diagnostic.isUnnecessary
                    if warning <> expectedWarning then
                        failwithf "Unused warning ignored project output %s/%s: %A" target output result.CheckResult.Diagnostics
        finally
            System.IO.Directory.Delete(directory, true)

    "measured real literals retain exact source points beside their numeric carrier", fun () ->
        let result = check "let distance = 12.0<m>\nlet elapsed = 3.0<s>\n"
        noErrors result
        for source, expected, dimension in ["12.0", bigint 12, metre; "3.0", bigint 3, second] do
            let node, value = result.Graph.Nodes.Values |> Seq.pick (fun node ->
                match node.Metadata |> Map.tryFind "Numeric.RealLiteral" with
                | Some (MetadataValue.RealLiteral(text, value)) when text = source -> Some (node, value)
                | _ -> None)
            if value.Numerator <> expected || value.Denominator <> bigint.One then
                failwithf "Measured literal %s lost its exact value: %A" source value
            if node.ValueRange.IsSome then failwith "A real source point was fabricated as an integer ValueRange"
            same (measured dimension) node.Type
        same (measured metre) (bindingType "distance" result)
        same (measured second) (bindingType "elapsed" result)

    "real literal metadata preserves decimal fractions signs separators and exponents", fun () ->
        for source, numerator, denominator in [
            "0.1", bigint.One, bigint 10
            "-1.25e+2", bigint -125, bigint.One
            "1_2.5e-1", bigint 5, bigint 4
            "-0.000", bigint.Zero, bigint.One
        ] do
            let result = check $"let value = {source}<m>\n"
            noErrors result
            let node, text, value = result.Graph.Nodes.Values |> Seq.pick (fun node ->
                match node.Metadata |> Map.tryFind "Numeric.RealLiteral" with
                | Some (MetadataValue.RealLiteral(text, value)) -> Some (node, text, value)
                | _ -> None)
            if text <> source || value.Numerator <> numerator || value.Denominator <> denominator then
                failwithf "Real literal %s lost its source identity or exact decimal value: %s, %A" source text value
            if node.ValueRange.IsSome then failwith "A fractional source point was coerced into an integer range"
            match node.Kind with
            | SemanticKind.Literal (NativeLiteral.Float _) -> ()
            | other -> failwithf "Real metadata replaced the existing runtime literal carrier: %A" other

    "real literal underflow cannot erase a nonzero exact source point", fun () ->
        let result = check "let tiny = 1e-400<m>\n"
        noErrors result
        let node, value = result.Graph.Nodes.Values |> Seq.pick (fun node ->
            match node.Metadata |> Map.tryFind "Numeric.RealLiteral" with
            | Some (MetadataValue.RealLiteral("1e-400", value)) -> Some (node, value)
            | _ -> None)
        if value.Numerator <> bigint.One || value.Denominator <> System.Numerics.BigInteger.Pow(bigint 10, 400) then
            failwithf "Hosted underflow replaced the source value: %A" value
        match node.Kind with
        | SemanticKind.Literal (NativeLiteral.Float (approximation, _)) when approximation = 0.0 -> ()
        | other -> failwithf "Expected the underflowing approximation beside exact source evidence: %A" other
        if node.ValueRange.IsSome then failwith "Real underflow manufactured an integer singleton zero"

    "real literals beyond exact-source limits have an explicit diagnostic", fun () ->
        for source in ["1e4097"; "1e-4097"; "0." + String.replicate 4096 "1"] do
            let result = check $"let value = {source}<m>\n"
            if not (result.Diagnostics |> List.exists (fun diagnostic ->
                diagnostic.Code = "CCS8401"
                && diagnostic.Severity = NativeDiagnosticSeverity.Error
                && diagnostic.Range.File = "dimensions.clef")) then
                failwithf "Unsupported exact real literal was not diagnosed: %A" result.Diagnostics
            if result.Graph.Nodes.Values |> Seq.exists (fun node -> Map.containsKey "Numeric.RealLiteral" node.Metadata) then
                failwith "A rejected exact real literal still acquired source evidence"

    "dimensional obligations retain actual operands, results and graph premises", fun () ->
        let result = check """let speed (distance: float<m>) (elapsed: float<s>) = distance / elapsed
[<EntryPoint>]
let main _ = if speed 12.0<m> 3.0<s> > 0.0<m/s> then 0 else 1
"""
        noErrors result
        let obligations = Clef.Compiler.Nanopass.ObligationDischarge.ofGraph result.Graph
        let division = obligations |> List.tryFind (fun ob -> ob.Kind = "dimension-quotient")
        match division with
        | Some { Body = ObligationBody.DimensionalRelation(DimensionalRule.Quotient, left, right, Some actual) } ->
            if left <> metre || right <> second || actual <> product(metre, Dimension.inv second) then
                failwithf "Incorrect dimensional evidence: %A" division
        | _ -> failwithf "Missing structured division obligation: %A" obligations
        if not (obligations |> List.exists (fun ob -> ob.Kind = "dimension-comparison")) then
            failwith "Measured comparison lost its compatibility obligation"

    "dimensional recipes check a corrupt graph result instead of recomputing it", fun () ->
        let result = check """let speed (distance: float<m>) (elapsed: float<s>) = distance / elapsed
[<EntryPoint>]
let main _ = if speed 12.0<m> 3.0<s> > 0.0<m/s> then 0 else 1
"""
        noErrors result
        let nodes = result.Graph.Nodes |> Map.map (fun _ node ->
            match node.Kind, node.Type with
            | SemanticKind.Application _, NativeType.TNum(_, dimension)
                when dimension = product(metre, Dimension.inv second) -> { node with Type = measured metre }
            | _ -> node)
        let corrupted = { result.Graph with Nodes = nodes }
        let enrichment = Clef.Compiler.Nanopass.ObligationElaboration.elaborate corrupted
        let evidence = enrichment.NewNodes |> List.choose (fun node ->
            match node.Kind with SemanticKind.Obligation ob -> Some ob | _ -> None)
        if not (evidence |> List.exists (fun ob ->
            match ob.Body with
            | ObligationBody.DimensionalRelation(DimensionalRule.Quotient, _, _, Some actual) -> actual = metre
            | _ -> false)) then
            failwith "Recipe replaced the graph's incorrect result with a manufactured correct dimension"

    "dimensional re-elaboration retains snapshot facts after another inference session", fun () ->
        let result = check """let divide (left: float<'u>) (right: float<'v>) = left / right
[<EntryPoint>]
let main _ = if divide 12.0<m> 3.0<s> > 0.0<m/s> then 0 else 1
"""
        noErrors result
        let bodies () =
            (Clef.Compiler.Nanopass.ObligationElaboration.elaborate result.Graph).NewNodes
            |> List.choose (fun node ->
                match node.Kind with
                | SemanticKind.Obligation { Body = ObligationBody.DimensionalRelation _ as body } -> Some body
                | _ -> None)
        let before = bodies ()
        let variables =
            before
            |> List.collect (function
                | ObligationBody.DimensionalRelation (_, left, right, output) ->
                    left :: right :: Option.toList output
                    |> List.collect (fun dim -> dim.Vars |> Map.toList |> List.map fst)
                | _ -> [])
            |> List.distinct
        if variables.IsEmpty then failwith "Expected formal dimension variables in the retained generic operation"
        try
            resetTypeParamCounter ()
            check "let ratio = 1.0<m> / 2.0<s>\n" |> noErrors
            // A later session may reuse the retained graph's variable IDs.
            // Bind any IDs not already reused, making store contamination
            // observable even if fresh-variable allocation order changes.
            for variable in variables do
                if lookupMeasure variable |> Option.isNone then
                    bindMeasures [ variable, Dimension.one ]
            if bodies () <> before then
                failwith "Dimensional obligations read another inference session instead of retained graph facts"
        finally
            resetTypeParamCounter ()

    "record layout remains a deferred family with unresolved fields in any position", fun () ->
        let unknowns = [
            TypeLayout.Opaque
            TypeLayout.Inline(-1, -1)
            TypeLayout.Inline(4, -1)
        ]
        for layout in unknowns do
            let unknown = NativeType.TApp({ Types.boolTyCon with Layout = layout }, [])
            for fields in [ [unknown; Types.boolType]; [Types.boolType; unknown]; [Types.boolType; unknown; Types.charType] ] do
                let actual = recordFamily (fields |> List.mapi (fun i ty -> string i, ty))
                if actual <> TypeLayout.Record then
                    failwithf "A later field fabricated a layout after %A: %A" layout actual

    "record layout remains a deferred family with target-dependent fields", fun () ->
        let fields = [
            Types.intType
            Types.stringType
            NativeType.TApp(Types.arrayTyCon, [Types.boolType])
            NativeType.TNativePtr Types.boolType
            NativeType.TApp(Types.fnPtrTyCon, [])
            NativeType.TByref(Types.boolType, ByrefKind.InOut)
            NativeType.TTuple([Types.boolType], false)
            NativeType.TFun(Types.boolType, Types.boolType)
            NativeType.TApp({ Types.boolTyCon with Layout = TypeLayout.NTUCompound 3 }, [])
        ]
        for field in fields do
            let actual = recordFamily ["value", field; "marker", Types.boolType]
            if actual <> TypeLayout.Record then
                failwithf "Target-independent checking selected a machine layout for %s: %A" (formatType field) actual

    "layout defers target-dependent option and result payloads", fun () ->
        let resultTyCon = mkTypeConRef "result" 2 TypeLayout.Union
        for payload in [Types.intType; Types.stringType; NativeType.TNativePtr Types.boolType] do
            let types = [
                NativeType.TApp(Types.optionTyCon, [payload])
                NativeType.TApp(resultTyCon, [payload; Types.boolType])
                NativeType.TApp(resultTyCon, [Types.boolType; payload])
                NativeType.TApp(resultTyCon, [payload; freshTypeVar dummyRange])
            ]
            for ty in types do
                match layoutOf ty with
                | TypeLayout.Inline(size, align) when size >= 0 && align > 0 ->
                    failwithf "A payload with unresolved layout acquired concrete storage: %s -> %d/%d" (formatType ty) size align
                | _ -> ()

    "layout defers union carrier policy even for known payloads", fun () ->
        // option-operations-representation.md §2: tag width is platform policy;
        // §2.1: JSIR may erase a carrier after proving its payload excludes undefined.
        let resultTyCon = mkTypeConRef "result" 2 TypeLayout.Union
        for payload in [Types.boolType; Types.charType; measured metre] do
            for ty in [ NativeType.TApp(Types.optionTyCon, [payload]); NativeType.TApp(resultTyCon, [payload; Types.boolType]) ] do
                match layoutOf ty with
                | TypeLayout.Inline(size, align) when size >= 0 && align > 0 ->
                    failwithf "Source type selected a union carrier before its target policy: %s -> %d/%d" (formatType ty) size align
                | _ -> ()

    "known record fields still defer byte layout until saturation", fun () ->
        let cases = [
            [], TypeLayout.Record
            ["flag", Types.boolType], TypeLayout.Record
            ["first", Types.boolType; "character", Types.charType; "last", Types.boolType], TypeLayout.Record
            ["dimension", NativeType.TMeasure metre; "flag", Types.boolType], TypeLayout.Record
        ]
        for fields, expected in cases do
            let actual = recordFamily fields
            if actual <> expected then failwithf "Expected %A, got %A" expected actual

    "record family does not sum large field extents during type checking", fun () ->
        let large = NativeType.TApp({ Types.boolTyCon with Layout = TypeLayout.Inline(System.Int32.MaxValue, 1) }, [])
        let actual = recordFamily ["first", large; "second", large; "third", large]
        if actual <> TypeLayout.Record then failwithf "Aggregate layout overflow produced fabricated storage: %A" actual

    "layout deferral keeps generic measured code usable", fun () ->
        let result = check "type Reading<[<Measure>] 'u, 'a> = { Context: 'a; Quantity: float<'u>; Valid: bool }\nlet reading = { Context = true; Quantity = 1.0<m>; Valid = true }\nlet length = reading.Quantity\n"
        noErrors result
        same (measured metre) (bindingType "length" result)
        let declarationLayout = result.Graph.Nodes.Values |> Seq.pick (fun node ->
            match node.Kind, node.Type with
            | SemanticKind.TypeDef(name = "Reading"), NativeType.TApp(tc, _) -> Some tc.Layout
            | _ -> None)
        if declarationLayout <> TypeLayout.Record then
            failwithf "Generic declaration fixed storage before its context type was known: %A" declarationLayout

    "power survives elaboration", fun () ->
        let result = check "let keep (x: float<m^2>) = x\n"
        noErrors result
        match bindingType "keep" result with
        | NativeType.TFun(NativeType.TNum(_, measure), _) ->
            same (measured (product(metre, metre))) (measured measure)
            different (measured metre) (measured measure)
        | ty -> failwithf "Measure lost during elaboration: %s" (formatType ty)

    "measures participate in identity", fun () ->
        different (measured metre) (measured second)
        different (measured metre) (measured (Dimension.ofBase { Name = "m"; Module = ["Other"] }))
        different (measured metre) Types.floatType

    "Abelian group equality", fun () ->
        let equivalent = [
            product(metre, second), product(second, metre)
            product(product(metre, second), metre), product(metre, product(second, metre))
            product(Dimension.one, metre), metre
            product(metre, Dimension.inv metre), Dimension.one
            Dimension.inv(product(metre, second)), product(Dimension.inv metre, Dimension.inv second)
        ]
        for left, right in equivalent do same (measured left) (measured right)
        same Types.floatType (measured Dimension.one)

    "literal and abbreviation survive elaboration", fun () ->
        let result = check "[<Measure>] type acceleration = m/s^2\nlet value: float<acceleration> = 1.0<m/s^2>\n"
        noErrors result
        same (measured (product(metre, Dimension.inv(product(second, second))))) (bindingType "value" result)

    "integer measures survive elaboration", fun () ->
        let result = check "let value: int<m^2> = 1<m*m>\n"
        noErrors result
        same (measuredInt (product(metre, metre))) (bindingType "value" result)

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
        let variable = freshMeasureVar None
        let ty = measured (Dimension.ofVar variable)
        same ty (measured metre)
        same (applySubst ty) (measured metre)
        different ty (measured second)
        let root = freshMeasureVar None
        same (measured (product(Dimension.ofVar root, Dimension.ofVar root))) (measured (product(metre, metre)))
        same (measured (Dimension.ofVar root)) (measured metre)

    "measure generalization and instantiation", fun () ->
        let variable = freshMeasureVar None
        let body = NativeType.TFun(measured (Dimension.ofVar variable), measured (Dimension.ofVar variable))
        match generalizeType Set.empty body with
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
        same (measured (product(metre, metre))) (bindingType "area" result)
        same (measured (product(metre, Dimension.inv second))) (bindingType "speed" result)
        same Types.floatType (bindingType "scalar" result)

    "inferred dimensional functions instantiate independently", fun () ->
        let result = check "let square x = x * x\nlet area = square 2.0<m>\nlet timeSquared = square 3.0<s>\nlet integerArea = square 4<m>\n"
        noErrors result
        same (measured (product(metre, metre))) (bindingType "area" result)
        same (measured (product(second, second))) (bindingType "timeSquared" result)
        same (measuredInt (product(metre, metre))) (bindingType "integerArea" result)

    "dimensional square root and atan2", fun () ->
        let result = check "let length = Math.sqrt 4.0<m^2>\nlet angle = Math.atan2 1.0<m> 2.0<m>\n"
        noErrors result
        same (measured metre) (bindingType "length" result)
        same Types.floatType (bindingType "angle" result)

    "measure equation uses integer group solving", fun () ->
        let u, v = freshMeasureVar None, freshMeasureVar None
        let left = product(power (Dimension.ofVar u) 2I, power (Dimension.ofVar v) 3I)
        same (measured left) (measured metre)
        if resolveDim (product(left, Dimension.inv metre)) <> Dimension.one then
            failwith "Solver did not establish the measure equation"

    "integer group equations admit exactly integral solutions", fun () ->
        for a in [-5I .. 5I] do
            for b in [-5I .. 5I] do
                for c in [-3I .. 3I] do
                    let u, v = freshMeasureVar None, freshMeasureVar None
                    let left = product(power (Dimension.ofVar u) a, power (Dimension.ofVar v) b)
                    let right = power metre c
                    let divisor = System.Numerics.BigInteger.GreatestCommonDivisor(a, b)
                    let solvable = if divisor = 0I then c = 0I else c % divisor = 0I
                    match tryUnify (measured left) (measured right) dummyRange with
                    | Result.Ok () when solvable ->
                        if resolveDim (product(left, Dimension.inv right)) <> Dimension.one then
                            failwithf "Solution does not establish %A*u + %A*v = %A*m" a b c
                    | Result.Error(MeasureMismatch _ | NoIntegerSolution _) when not solvable -> ()
                    | result -> failwithf "Wrong feasibility for %A*u + %A*v = %A*m: %A" a b c result

    "incompatible dimensional arithmetic is diagnosed", fun () ->
        for expression, expectedCode in [
            "1.0<m> + 2.0<s>", "CCS8040"
            "Math.sqrt 2.0<m>", "CCS8041"
            "Math.atan2 1.0<m> 2.0<s>", "CCS8040"
            "Math.sin 1.0<m>", "CCS8040"
        ] do
            let result = check $"let bad = {expression}\n"
            if not (result.Diagnostics |> List.exists (fun d -> d.Code = expectedCode && d.Severity = NativeDiagnosticSeverity.Error)) then
                failwithf "Expected %s for incompatible arithmetic: %s; got %A" expectedCode expression result.Diagnostics
        for expression in ["1<m> * 2.0<s>"; "\"length\" * 2.0<m>"] do
            let result = check $"let bad = {expression}\n"
            if not (result.Diagnostics |> List.exists (fun d -> d.Severity = NativeDiagnosticSeverity.Error)) then
                failwithf "Invalid numeric kind silently accepted: %s" expression

    "nested generalization retains captured dimensions", fun () ->
        let result = check "let scaled (x: float<'u>) =\n    let multiply y = x * y\n    (multiply 2.0<m>, multiply 3.0<s>)\nlet pair = scaled 4.0<m>\n"
        noErrors result
        same (NativeType.TTuple([measured (product(metre, metre)); measured (product(metre, second))], false)) (bindingType "pair" result)
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
        same (measured (product(metre, Dimension.inv second))) (bindingType "speed" result)

    "generic record fields instantiate dimensions", fun () ->
        let result = check "type Quantity<[<Measure>] 'u> = { Value: float<'u> }\nlet distance: Quantity<m> = { Value = 1.0<m> }\nlet duration: Quantity<s> = { Value = 2.0<s> }\nlet value = distance.Value\n"
        noErrors result
        same (measured metre) (bindingType "value" result)

    "shared record labels preserve measure parameter kinds", fun () ->
        let result = check "type Earlier<[<Measure>] 'u> = { Value: float<'u> }\ntype Later<[<Measure>] 'u> = { Value: float<'u> }\nlet distance = { Value = 1.0<m> }\nlet duration = { Value = 2.0<s> }\nlet length = distance.Value\nlet time = duration.Value\n"
        noErrors result
        same (measured metre) (bindingType "length" result)
        same (measured second) (bindingType "time" result)

    "record updates preserve dimensions", fun () ->
        let valid = check "type Quantity<[<Measure>] 'u> = { mutable Value: float<'u> }\nlet distance: Quantity<m> = { Value = 1.0<m> }\ndistance.Value <- 2.0<m>\nlet copy = { distance with Value = 3.0<m> }\nlet value = copy.Value\n"
        noErrors valid
        same (measured metre) (bindingType "value" valid)
        for update in ["{ distance with Value = 2.0<s> }"; "distance.Value <- 2.0<s>"] do
            let result = check $"type Quantity<[<Measure>] 'u> = {{ mutable Value: float<'u> }}\nlet distance: Quantity<m> = {{ Value = 1.0<m> }}\nlet bad = {update}\n"
            if not (result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8040")) then
                failwith "Record update discarded the field dimension"

    "dimensional compatibility probes preserve inference state", fun () ->
        if not (canUnify (measured (product(metre, second))) (measured (product(second, metre)))) then
            failwith "Compatibility probe ignored measure equality"
        if not (canUnify Types.floatType (measured Dimension.one)) then failwith "Dimensionless aliases differ"
        let parameter = freshMeasureVar None
        let quantity = measured (Dimension.ofVar parameter)
        if not (canUnify quantity (measured metre)) then failwith "Compatible variable rejected"
        if lookupMeasure parameter <> None then failwith "Compatibility probe bound the original parameter"
        let repeated = NativeType.TFun(quantity, quantity)
        if canUnify repeated (NativeType.TFun(measured metre, measured second)) then
            failwith "Compatibility probe ignored repeated variable identity"
        if lookupMeasure parameter <> None then failwith "Failed probe changed the original parameter"

    // Parser compatibility exercises an explicit recursive group; canonical Clef
    // discovers dependency groups from ordinary declarations (tracked separately).
    "legacy recursive-group AST generalizes dimensions after its group", fun () ->
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

    "mutable option assignments retain payload types", fun () ->
        // BAREWire's layout validator clears an optional endpoint on failure.
        // None still needs the cell's payload type before union layout settles.
        for value, expected in [ "1", Types.intType; "1.0<m>", measured metre ] do
            let result = check (sprintf "let mutable endpoint = Some %s\nendpoint <- None\n" value)
            noErrors result
            let mutable options = 0
            for node in result.Graph.Nodes.Values do
                match node.Type with
                | NativeType.TApp(tycon, [payload]) when tycon.Name = "option" ->
                    options <- options + 1
                    if hasUnboundVars payload || not (List.isEmpty (freeMeasureVars payload)) then
                        failwithf "Unresolved option payload reached the graph: %A" node.Kind
                    same expected payload
                | _ -> ()
            if options = 0 then failwith "The option assignment was not checked"

    "lambda metadata carries resolved dimensions", fun () ->
        let result = check "let advance x = x + 1.0<m>\n"
        noErrors result
        let parameterType = result.Graph.Nodes.Values |> Seq.pick (fun node ->
            match node.Kind with
            | SemanticKind.Lambda([("x", ty, _)], _, _, _, _) -> Some ty
            | _ -> None)
        match parameterType with
        | NativeType.TNum(_, measure) ->
            if measure <> metre then failwith "Lambda metadata retained an unresolved or incorrect dimension"
        | ty -> failwithf "Unresolved lambda metadata crossed the checker boundary: %s" (formatType ty)

    "match metadata carries resolved dimensions", fun () ->
        let result = check "type Quantity<[<Measure>] 'u> = Quantity of float<'u>\nlet length = match Quantity 1.0<m> with Quantity value -> value\n"
        noErrors result
        let payloadType = result.Graph.Nodes.Values |> Seq.pick (fun node ->
            match node.Kind with
            | SemanticKind.Match(_, [{ Pattern = Pattern.Union(_, _, Some(Pattern.Tuple [Pattern.Var(_, ty)]), _) }]) -> Some ty
            | SemanticKind.CaseElimination(_, [{ Pattern = Pattern.Union(_, _, Some(Pattern.Tuple [Pattern.Var(_, ty)]), _) }]) -> Some ty
            | _ -> None)
        match payloadType with
        | NativeType.TNum(_, measure) ->
            if measure <> metre then failwith "Pattern metadata retained an unresolved measure variable"
        | _ -> failwith "Pattern payload type lost its dimension"

    "invalid generic dimensions produce diagnostics without crashing", fun () ->
        for body in [
            "type Scalar<[<Measure>] 'u> = float<'u>\nlet keep (x: Scalar<missing>) = x\n"
            "type Quantity<[<Measure>] 'u> = { Value: float<'u> }\nlet keep (x: Quantity<m, s>) = x.Value\n"
            "let keep (x: float<m, s>) = x\n"
            "let keep (x: missing<m>) = x\n"
            "let keep (x: m) = x\n"
        ] do
            let result = check body
            if not (result.Diagnostics |> List.exists (fun d -> d.Severity = NativeDiagnosticSeverity.Error && d.Range.File = "dimensions.clef")) then
                failwithf "Invalid type accepted without a located diagnostic: %s" body

    "numeric type equality constraints enforce dimensions", fun () ->
        match solveConstraint (Constraint.Equals(measured metre, measured second, dummyRange)) with
        | Result.Error(MeasureMismatch _) -> ()
        | _ -> failwith "Measure constraint silently ignored"
        match solveConstraint (Constraint.Equals(Types.stringType, measured metre, dummyRange)) with
        | Result.Error(TypeMismatch _) -> ()
        | _ -> failwith "Measure constraint accepted a nonnumeric type"

    "source numeric names do not select representations", fun () ->
        for name in ["int8"; "int16"; "int32"; "int64"; "uint8"; "uint16"; "uint32"; "uint64"; "byte"; "sbyte"; "uint"; "nativeint"; "unativeint"; "float32"; "single"; "double"; "float64"; "Posit8"; "Posit16"; "Posit32"; "Posit64"] do
            let result = check $"let keep (x: {name}) = x\n"
            if not (result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8706" && d.Severity = NativeDiagnosticSeverity.Error && d.Range.File = "dimensions.clef")) then
                failwithf "Width-named source type was not diagnosed: %s" name
            let measured = check $"let keep (x: {name}<m>) = x\n"
            if not (measured.Diagnostics |> List.exists (fun d -> d.Code = "CCS8706" && d.Severity = NativeDiagnosticSeverity.Error)) then
                failwithf "Measured width-named source type was not diagnosed: %s" name

    "width-bearing literal suffixes are diagnosed", fun () ->
        for literal in ["1L"; "1u"; "1uy"; "1s"; "1n"; "1.0f"; "1L<m>"; "1.0f<m>"] do
            let result = check $"let value = {literal}\n"
            if not (result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8018" && d.Severity = NativeDiagnosticSeverity.Error && d.Range.File = "dimensions.clef")) then
                failwithf "Width-bearing suffix was not diagnosed: %s" literal

    "numeric kind mismatch has its specified diagnostic", fun () ->
        let result = check "let value: float<m> = 1<m>\n"
        if not (result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8003")) then
            failwith "Numeric kind mismatch did not produce CCS8003"

    "rounding and integer to real arithmetic preserve dimensions", fun () ->
        for operation in ["floor"; "ceiling"; "round"; "truncate"] do
            let result = check $"let value = Math.{operation} 2.5<m>\n"
            noErrors result
            same (measuredInt metre) (bindingType "value" result)
        let result = check "let value = float 2<m>\nlet minimum = Math.min 1.0<m> 2.0<m>\n"
        noErrors result
        same (measured metre) (bindingType "value" result)
        same (measured metre) (bindingType "minimum" result)

    "conversion names cannot discard dimensional identity", fun () ->
        for expression in ["int 1.5<m>"; "int64 1<m>"; "float32 1.0<m>"; "byte 1<m>"; "float true"] do
            let result = check $"let value = {expression}\n"
            if not (result.Diagnostics |> List.exists (fun d -> d.Severity = NativeDiagnosticSeverity.Error)) then
                failwithf "Conversion discarded dimensions: %s" expression

    "explicit type application requires established parameters", fun () ->
        let result = check "let apply f = f<float<m>> 1.0<m>\n"
        if not (result.Diagnostics |> List.exists (fun d -> d.Severity = NativeDiagnosticSeverity.Error)) then
            failwith "Explicit application silently fabricated a generic signature"

    "constant patterns enforce dimensions", fun () ->
        let result = check "let bad = match 1.0<m> with 2.0<s> -> true | _ -> false\n"
        if not (result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8040")) then
            failwith "Constant pattern ignored its measure"

    "qualified measured types retain their argument kinds", fun () ->
        let result = check "module Quantities =\n    type Scalar<[<Measure>] 'u> = float<'u>\n    type Quantity<[<Measure>] 'u> = { Value: float<'u> }\nlet distance: Quantities.Scalar<m> = 1.0<m>\nlet duration: Quantities.Quantity<s> = { Value = 2.0<s> }\nlet time = duration.Value\n"
        noErrors result
        same (measured metre) (bindingType "distance" result)
        same (measured second) (bindingType "time" result)

    "sharing immutable records permits independent dimensions", fun () ->
        let result = check "type Holder<'a> = { Value: 'a option }\nlet empty = { Value = None }\nlet distance: Holder<float<m>> = empty\nlet duration: Holder<float<s>> = empty\nlet length = distance.Value\nlet time = duration.Value\n"
        noErrors result
        same (NativeType.TApp(Types.optionTyCon, [measured metre])) (bindingType "length" result)
        same (NativeType.TApp(Types.optionTyCon, [measured second])) (bindingType "time" result)

    "sharing phantom record measures permits independent dimensions", fun () ->
        let result = check "type Phantom<[<Measure>] 'u> = { Value: int }\nlet phantom = { Value = 1 }\nlet distance: Phantom<m> = phantom\nlet duration: Phantom<s> = phantom\n"
        noErrors result
        for name, expected in ["distance", metre; "duration", second] do
            match bindingType name result with
            | NativeType.TApp(_, [NativeType.TMeasure measure]) -> same (measured expected) (measured measure)
            | ty -> failwithf "Phantom measure lost from %s: %s" name (formatType ty)

    "sharing lazy immutable results permits independent dimensions", fun () ->
        let result = check "let delayed = lazy None\nlet distance: float<m> option = Lazy.force delayed\nlet duration: float<s> option = Lazy.force delayed\n"
        noErrors result
        same (NativeType.TApp(Types.optionTyCon, [measured metre])) (bindingType "distance" result)
        same (NativeType.TApp(Types.optionTyCon, [measured second])) (bindingType "duration" result)

    "sharing lazy immutable functions permits independent dimensions", fun () ->
        let result = check "let delayed = lazy (fun x -> x)\nlet distance = (Lazy.force delayed) 1.0<m>\nlet duration = (Lazy.force delayed) 2.0<s>\n"
        noErrors result
        same (measured metre) (bindingType "distance" result)
        same (measured second) (bindingType "duration" result)

    "sharing immutable union and list constructions permits independent dimensions", fun () ->
        for expression, annotation in ["Some None", "option option"; "[None]", "option list"; "lazy (Some None)", "option option Lazy"] do
            let result = check $"let empty = {expression}\nlet distance: float<m> {annotation} = empty\nlet duration: float<s> {annotation} = empty\n"
            noErrors result

    "sharing mutable record contents retains one dimensional identity", fun () ->
        let sources = [
            "type Cell<'a> = { mutable Value: 'a option }\nlet shared = { Value = None }\nshared.Value <- Some 1.0<m>\nshared.Value <- Some 2.0<s>\n"
            "type Cell<'a> = { mutable Value: 'a option }\ntype Holder<'a> = { Inner: Cell<'a> }\nlet shared = { Inner = { Value = None } }\nshared.Inner.Value <- Some 1.0<m>\nshared.Inner.Value <- Some 2.0<s>\n"
            "type Cell<'a> = { mutable Value: 'a option }\nlet shared = { Value = None }\nlet alias = shared\nalias.Value <- Some 1.0<m>\nshared.Value <- Some 2.0<s>\n"
            "type Cell<'a> = { mutable Value: 'a option }\nlet shared = { Value = None }\nlet set x = shared.Value <- Some x\nset 1.0<m>\nset 2.0<s>\n"
            "let mutable shared = None\nlet alias = shared\nlet distance: float<m> option = alias\nlet duration: float<s> option = shared\n"
            "type Cell<'a> = { mutable Value: 'a option }\ntype Holder<'a> = { Inner: Cell<'a>; Flag: bool }\nlet original = { Inner = { Value = None }; Flag = false }\nlet copied = { original with Flag = true }\ncopied.Inner.Value <- Some 1.0<m>\noriginal.Inner.Value <- Some 2.0<s>\n"
            "type Cell<'a> = { mutable Value: 'a option }\nlet wrapped = Some { Value = None }\nlet distance: Cell<float<m>> option = wrapped\nlet duration: Cell<float<s>> option = wrapped\n"
        ]
        for source in sources do
            let result = check source
            if not (result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8040" && d.Range.File = "dimensions.clef")) then
                failwithf "Shared mutable storage acquired independent dimensions: %A" result.Diagnostics

    "sharing memoized mutable results retains one dimensional identity", fun () ->
        let sources = [
            "type Cell<'a> = { mutable Value: 'a option }\nlet delayed = lazy { Value = None }\nlet shared = Lazy.force delayed\nshared.Value <- Some 1.0<m>\nshared.Value <- Some 2.0<s>\n"
            "let delayed = lazy (let mutable state = None in fun x -> state <- Some x)\nlet set = Lazy.force delayed\nset 1.0<m>\nset 2.0<s>\n"
            "let mutable state = None\nlet delayed = lazy (fun x -> state <- Some x)\nlet set = Lazy.force delayed\nset 1.0<m>\nset 2.0<s>\n"
            "let make () =\n    let mutable state = None\n    fun x -> state <- Some x\nlet set = make ()\nset 1.0<m>\nset 2.0<s>\n"
        ]
        for source in sources do
            let result = check source
            if not (result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8040" && d.Range.File = "dimensions.clef")) then
                failwithf "Memoization or closure construction changed shared storage identity: %A" result.Diagnostics

    "sharing inline results retains allocated mutable identity", fun () ->
        let sources = [
            "type Cell<'a> = { mutable Value: 'a option }\nlet inline identity x = x\nlet shared = identity { Value = None }\nlet distance: Cell<float<m>> = shared\nlet duration: Cell<float<s>> = shared\n"
            "type Cell<'a> = { mutable Value: 'a option }\ntype Holder<'a> = { Inner: Cell<'a> }\nlet inline identity x = x\nlet shared = { Inner = identity { Value = None } }\nlet distance: Holder<float<m>> = shared\nlet duration: Holder<float<s>> = shared\n"
            "let inline make () =\n    let mutable state = None\n    fun x -> state <- Some x\nlet shared = make ()\nlet distance: float<m> -> unit = shared\nlet duration: float<s> -> unit = shared\n"
        ]
        for source in sources do
            let result = check source
            if not (result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8040" && d.Range.File = "dimensions.clef")) then
                failwithf "Inline expansion hid fresh shared storage: %A" result.Diagnostics

    "sharing intrinsic aliases permits independent dimensions", fun () ->
        let result = check "let convert = float\nlet distance = convert 1<m>\nlet duration = convert 2<s>\n"
        noErrors result
        same (measured metre) (bindingType "distance" result)
        same (measured second) (bindingType "duration" result)

    "collection literals retain element dimensions and collection kind", fun () ->
        for expression, expected, isArray, count in [
            "[1.0<m>; 2.0<m>]", NativeType.TList(measured metre), false, 2
            "[|1.0<m>; 2.0<m>|]", NativeType.TApp(Types.arrayTyCon, [measured metre]), true, 2
            "[(1.0<m>; 2.0<m>)]", NativeType.TList(measured metre), false, 1
        ] do
            let result = check $"let values = {expression}\n"
            noErrors result
            same expected (bindingType "values" result)
            let children = result.Graph.Nodes.Values |> Seq.pick (fun node ->
                match node.Kind with
                | SemanticKind.ListExpr items when not isArray -> Some items
                | SemanticKind.ArrayExpr items when isArray -> Some items
                | _ -> None)
            if children.Length <> count then failwithf "Collection element boundaries changed: %A" children

    "collection literals diagnose mixed dimensions", fun () ->
        for expression in ["[1.0<m>; 2.0<s>]"; "[|1.0<m>; 2.0<s>|]"] do
            let result = check $"let invalid = {expression}\n"
            if not (result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8040" && d.Range.File = "dimensions.clef")) then
                failwithf "Collection silently discarded its element dimensions: %A" result.Diagnostics

    "computed collections diagnose unsupported elaboration", fun () ->
        for expression in ["[for n in [1; 2] -> 1.0<m>]"; "[|for n in [1; 2] -> 1.0<m>|]"; "[if true then yield 1.0<m>]"] do
            let result = check $"let values = {expression}\n"
            if not (result.Diagnostics |> List.exists (fun d -> d.Code = "CCS8401" && d.Severity = NativeDiagnosticSeverity.Error && d.Range.File = "dimensions.clef")) then
                failwithf "Unsupported comprehension fabricated an element type: %A" result.Diagnostics

    "wide unsuffixed integer literals preserve exact values in the general integer kind", fun () ->
        for source, expected in ["2147483648", 2147483648L; "-2147483649", -2147483649L;
                                 "0x80000000", 2147483648L; "140737488351232", 140737488351232L;
                                 "-9223372036854775808", System.Int64.MinValue] do
            let result = check $"let value = {source}\n"
            noErrors result
            same Types.intType (bindingType "value" result)
            let literals = result.Graph.Nodes.Values |> Seq.choose (fun node ->
                match node.Kind with SemanticKind.Literal(NativeLiteral.Int(value, _)) -> Some value | _ -> None) |> Seq.toList
            if literals <> [expected] then failwithf "Integer %s lost its exact value: %A" source literals

    "integers beyond hosted literal storage are explicitly rejected", fun () ->
        for source in ["9223372036854775808"; "-9223372036854775809"] do
            let result = check $"let value = {source}\n"
            if not (result.Diagnostics |> List.exists (fun diagnostic ->
                diagnostic.Code = "CCS8401" && diagnostic.Severity = NativeDiagnosticSeverity.Error)) then
                failwithf "Oversized hosted literal %s was not rejected: %A" source result.Diagnostics

    "large unsuffixed range endpoints parse without integer overflow", fun () ->
        match parseStringWithDefaults "module Ranges\nlet values = [140737488351232..140737488351234]\n" "ranges.clef" with
        | ParseSuccess _ -> ()
        | ParseError errors -> failwithf "Large range endpoints failed parsing: %A" errors
]
