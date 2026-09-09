// Normative: clef-lang-spec/spec/{namespaces-and-modules,inference-name-resolution,units-of-measure}.md
module Clef.Compiler.Service.Tests.ModuleScopeCases

open System
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

let private check (files: (string * string) list) =
    files
    |> List.map (fun (file, source) ->
        match parseStringWithDefaults source file with
        | ParseSuccess input -> input
        | ParseError errors -> failwithf "Parse failed for %s: %A" file errors)
    |> checkParsedInputs

let private noErrors (result: CheckResult) =
    let errors = result.Diagnostics |> List.filter (fun d -> d.Severity = NativeDiagnosticSeverity.Error)
    if not errors.IsEmpty then failwithf "Unexpected errors: %A" errors

// Parser coordinates are one-based lines and zero-based UTF-16 columns.
let private site file (source: string) line (needle: string) =
    let text = source.Split('\n').[line - 1]
    let column = text.IndexOf(needle, StringComparison.Ordinal)
    if column < 0 then failwithf "No '%s' at %s:%d" needle file line
    (file, line, column)

let private contains (file, line, column) (range: SourceRange) =
    range.File = file
    && (range.Start.Line, range.Start.Column) <= (line, column)
    && (line, column) < (range.End.Line, range.End.Column)

let private errorAt position (result: CheckResult) =
    match result.Diagnostics |> List.tryFind (fun d ->
        d.Severity = NativeDiagnosticSeverity.Error && contains position d.Range) with
    | Some diagnostic -> diagnostic
    | None -> failwithf "Expected an error at %A; diagnostics: %A" position result.Diagnostics

let private bindingAt file line (result: CheckResult) =
    result.Graph.Nodes.Values
    |> Seq.filter (fun node ->
        node.Range.File = file && node.Range.Start.Line = line
        && match node.Kind with SemanticKind.Binding _ -> true | _ -> false)
    |> Seq.exactlyOne

let private referencesAt position (result: CheckResult) =
    result.Graph.Nodes.Values
    |> Seq.choose (fun node ->
        match node.Kind with
        | SemanticKind.VarRef(_, Some definition) when contains position node.Range -> Some definition
        | _ -> None)
    |> Seq.toList

let private referenceTo position definitionFile definitionLine result =
    let expected = (bindingAt definitionFile definitionLine result).Id
    let actual = referencesAt position result
    if actual <> [expected] then
        failwithf "Expected reference at %A to %s:%d (%A), got %A"
            position definitionFile definitionLine expected actual

let private unresolved position result =
    let diagnostic = errorAt position result
    let references = referencesAt position result
    if not references.IsEmpty then
        failwithf "Unavailable name at %A retained definition edges %A" position references
    diagnostic

let private units =
    "module Demo.Units\n[<Measure>] type m\n[<Measure>] type s\nlet speed (distance: float<m>) (elapsed: float<s>) = distance / elapsed\n"

let private simpleUnits =
    "module Demo.Units\nlet speed distance elapsed = distance / elapsed\n"

let tests = [
    "removing and restoring an import removes and restores the definition edge", fun () ->
        let main =
            "module Demo.Main\nopen Demo.Units\n[<EntryPoint>]\nlet main argv =\n    let velocity = speed 12.0<m> 3.0<s>\n    if velocity > 0.0<m/s> then 0 else 1\n"
        let run source = check ["Units.clef", units; "Main.clef", source]
        let position = site "Main.clef" main 5 "speed"
        let good = run main
        noErrors good
        referenceTo position "Units.clef" 4 good
        let withoutOpen = run (main.Replace("open Demo.Units", "// open Demo.Units"))
        let diagnostic = unresolved position withoutOpen
        if not (diagnostic.Message.Contains("speed", StringComparison.Ordinal)) then
            failwithf "Missing import diagnostic did not identify speed: %A" diagnostic
        if Diagnostic.effectiveSeverity diagnostic <> NativeDiagnosticSeverity.Error then
            failwithf "Reachable missing-name diagnostic was demoted: %A" diagnostic
        let restored = run main
        noErrors restored
        referenceTo position "Units.clef" 4 restored

    "removing an imported definition cannot retain a reference from an earlier check", fun () ->
        let main = "module Demo.Main\nopen Demo.Units\nlet value = speed 12.0 3.0\n"
        let position = site "Main.clef" main 3 "speed"
        let run provider = check ["Units.clef", provider; "Main.clef", main]
        let good = run simpleUnits
        noErrors good
        referenceTo position "Units.clef" 2 good
        run (simpleUnits.Replace("let speed", "// let speed")) |> unresolved position |> ignore
        let restored = run simpleUnits
        noErrors restored
        referenceTo position "Units.clef" 2 restored

    "fully qualified values and measures require no open", fun () ->
        let main =
            "module Demo.Main\nlet value = Demo.Units.speed 12.0<Demo.Units.m> 3.0<Demo.Units.s>\n"
        let result = check ["Units.clef", units; "Main.clef", main]
        noErrors result
        referenceTo (site "Main.clef" main 2 "Demo.Units.speed") "Units.clef" 4 result

    "same-namespace sibling modules remain accessible by module name", fun () ->
        let first = "namespace Demo\nmodule Units =\n    let speed distance elapsed = distance / elapsed\n"
        let second = "namespace Demo\nmodule Main =\n    let value = Units.speed 12.0 3.0\n"
        let result = check ["Units.clef", first; "Main.clef", second]
        noErrors result
        referenceTo (site "Main.clef" second 3 "Units.speed") "Units.clef" 3 result

    "opening a parent exposes child modules but not their contents", fun () ->
        let qualified = "module Client\nopen Demo\nlet value = Units.speed 12.0 3.0\n"
        let good = check ["Units.clef", simpleUnits; "Main.clef", qualified]
        noErrors good
        referenceTo (site "Main.clef" qualified 3 "Units.speed") "Units.clef" 2 good
        let flattened = qualified.Replace("Units.speed", "speed")
        check ["Units.clef", simpleUnits; "Main.clef", flattened]
        |> unresolved (site "Main.clef" flattened 3 "speed") |> ignore

    "an open in one file does not leak into another module", fun () ->
        let first = "module First\nopen Demo.Units\nlet value = speed 12.0 3.0\n"
        let second = "module Second\nlet value = speed 12.0 3.0\n"
        let result = check ["Units.clef", simpleUnits; "First.clef", first; "Second.clef", second]
        referenceTo (site "First.clef" first 3 "speed") "Units.clef" 2 result
        unresolved (site "Second.clef" second 2 "speed") result |> ignore

    "an open in one nested module does not leak into its sibling", fun () ->
        let main =
            "module Client\nmodule First =\n    open Demo.Units\n    let value = speed 12.0 3.0\nmodule Second =\n    let value = speed 12.0 3.0\n"
        let result = check ["Units.clef", simpleUnits; "Main.clef", main]
        referenceTo (site "Main.clef" main 4 "speed") "Units.clef" 2 result
        unresolved (site "Main.clef" main 6 "speed") result |> ignore

    "measure names are available only through their lexical import or qualified path", fun () ->
        let measures = "module Demo.Measures\n[<Measure>] type distance\n"
        let main = "module Demo.Main\nopen Demo.Measures\nlet value = 1.0<distance>\n"
        let run source = check ["Measures.clef", measures; "Main.clef", source]
        run main |> noErrors
        run (main.Replace("open Demo.Measures", "// open Demo.Measures"))
        |> errorAt (site "Main.clef" main 3 "distance") |> ignore
        run (main.Replace("open Demo.Measures", "// open Demo.Measures").Replace("1.0<distance>", "1.0<Demo.Measures.distance>"))
        |> noErrors

    "a local declaration shadows an imported value with its own definition edge", fun () ->
        let main =
            "module Demo.Main\nopen Demo.Units\nlet speed distance elapsed = distance + elapsed\nlet value = speed 12.0 3.0\n"
        let result = check ["Units.clef", simpleUnits; "Main.clef", main]
        noErrors result
        referenceTo (site "Main.clef" main 4 "speed") "Main.clef" 3 result

    "record annotations preserve canonical ownership through open and qualification", fun () ->
        let provider = "module Demo.Types\ntype Token = { Value: int }\n"
        let main = "module Client\nopen Demo.Types\nlet keep (value: Token) = value\n"
        let run source = check ["Types.clef", provider; "Main.clef", source]
        let imported = run main
        noErrors imported
        let withoutOpen = main.Replace("open Demo.Types", "// open Demo.Types")
        run withoutOpen |> errorAt (site "Main.clef" main 3 "Token") |> ignore
        let qualified = run (withoutOpen.Replace("value: Token", "value: Demo.Types.Token"))
        noErrors qualified
        let owner result =
            match (bindingAt "Main.clef" 3 result).Type with
            | NativeType.TFun(NativeType.TApp(owner, []), _) -> owner.Name, owner.Module
            | ty -> failwithf "Record annotation lost its owner: %A" ty
        if owner imported <> owner qualified then
            failwith "Import and qualification selected different nominal record owners"

    "type aliases follow lexical imports without flattening child modules", fun () ->
        let provider = "module Demo.Types\ntype Count = int\n"
        let imported = "module Client\nopen Demo.Types\nlet count: Count = 1\n"
        let run source = check ["Types.clef", provider; "Main.clef", source]
        run imported |> noErrors
        let parentOnly = imported.Replace("open Demo.Types", "open Demo")
        run parentOnly |> errorAt (site "Main.clef" parentOnly 3 "Count") |> ignore
        run (parentOnly.Replace("count: Count", "count: Types.Count")) |> noErrors
        let sibling = "module Sibling\nlet count: Count = 1\n"
        check ["Types.clef", provider; "Main.clef", imported; "Sibling.clef", sibling]
        |> errorAt (site "Sibling.clef" sibling 2 "Count") |> ignore

    "global qualification bypasses a lexical module shadow for values and aliases", fun () ->
        let provider = "module Demo.Types\ntype Count = int\nlet marker = 41\n"
        let main =
            "module Client\nmodule Demo =\n    module Types =\n        type Count = bool\n        let marker = true\nlet local: Demo.Types.Count = Demo.Types.marker\nlet absolute: global.Demo.Types.Count = global.Demo.Types.marker\n"
        let result = check ["Types.clef", provider; "Main.clef", main]
        noErrors result
        referenceTo (site "Main.clef" main 6 "Demo.Types.marker") "Main.clef" 5 result
        referenceTo (site "Main.clef" main 7 "global.Demo.Types.marker") "Types.clef" 3 result

    "qualified record context resolves a literal without importing its labels", fun () ->
        let provider = "module Demo.Types\ntype Token = { Value: int }\ntype Other = { Value: int }\n"
        let main = "module Client\nlet token: Demo.Types.Token = ({ Value = 1 })\n"
        let run source = check ["Types.clef", provider; "Main.clef", source]
        run main |> noErrors
        let unannotated = "module Client\nlet token = { Value = 1 }\n"
        run unannotated |> errorAt (site "Main.clef" unannotated 2 "Value") |> ignore
        let following = main + "let stray = { Value = 2 }\n"
        run following |> errorAt (site "Main.clef" following 3 "Value") |> ignore
        let conflicting = main.Replace("{ Value = 1 }", "{ Demo.Types.Other.Value = 1 }")
        let diagnostic = run conflicting |> errorAt (site "Main.clef" conflicting 2 "Demo.Types.Other.Value")
        if diagnostic.Code <> "CCS8003" then failwithf "Conflicting field owner was not rejected: %A" diagnostic

    "qualified record context retains concrete measure arguments", fun () ->
        let provider = "module Demo.Types\ntype Quantity<[<Measure>] 'u> = { Value: float<'u> }\n"
        let main = "module Client\n[<Measure>] type m\n[<Measure>] type s\nlet value: Demo.Types.Quantity<m> = { Value = 1.0<m> }\n"
        let run source = check ["Types.clef", provider; "Main.clef", source]
        run main |> noErrors
        let invalid = main.Replace("1.0<m>", "1.0<s>")
        let diagnostic = run invalid |> errorAt (site "Main.clef" invalid 4 "1.0<s>")
        if diagnostic.Code <> "CCS8040" then failwithf "Annotated measure argument was lost: %A" diagnostic

    "type lookup chooses the nearest declaration across aliases and nominal types", fun () ->
        let provider = "module Lib\ntype Token = int\n"
        let main = "module Client\nopen Lib\ntype Token = { Value: bool }\nlet keep (x: Token) = x\n"
        let result = check ["Lib.clef", provider; "Main.clef", main]
        noErrors result
        match (bindingAt "Main.clef" 4 result).Type with
        | NativeType.TFun(NativeType.TApp(owner, []), _) when owner.Module = ["Client"] -> ()
        | ty -> failwithf "Imported alias displaced the local nominal declaration: %A" ty
        let result = check ["Lib.clef", "module Lib\ntype Token = { Value: int }\n";
                            "Main.clef", "module Client\nopen Lib\ntype Token = bool\nlet keep (x: Token) = x\n"]
        noErrors result
        match (bindingAt "Main.clef" 4 result).Type with
        | NativeType.TFun(domain, _) when formatType domain = "bool" -> ()
        | ty -> failwithf "Imported nominal declaration displaced the local alias: %A" ty

    "module abbreviations cannot replace bare value parameters", fun () ->
        let provider = "module Lib\nlet item = 1\n"
        let main = "module Client\nmodule short = Lib\nlet keep (short: int) = short\nlet imported = short.item\n"
        let result = check ["Lib.clef", provider; "Main.clef", main]
        noErrors result
        match (bindingAt "Main.clef" 3 result).Type with
        | NativeType.TFun(domain, result) when formatType domain = "int" && formatType result = "int" -> ()
        | ty -> failwithf "Module alias displaced the parameter: %A" ty
        referenceTo (site "Main.clef" main 4 "short.item") "Lib.clef" 2 result
]
