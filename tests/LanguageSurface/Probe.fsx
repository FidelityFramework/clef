// Source-checking inventory, not native execution or proof conformance.
// Build Composer first, then: dotnet fsi tests/LanguageSurface/Probe.fsx
#I "../../../Composer/src/bin/Debug/net10.0"
#r "Fidelity.Data.dll"
#r "Clef.Compiler.Service.dll"

open System
open System.IO
open System.Security.Cryptography
open Clef.Compiler.NativeService
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

type Expectation = Accept | Reject of expectedCode: string option
type Probe = { Name: string; Expected: Expectation; Body: string }

let probes = [
    { Name = "generalized-function"; Expected = Accept
      Body = "let identity x = x\nlet main () = (identity true, identity ())" }
    { Name = "captured-function"; Expected = Accept
      Body = "let capture x = fun () -> x\nlet main () = (capture true) ()" }
    { Name = "generic-record-field"; Expected = Accept
      Body = "type Box<'a> = { Value: 'a }\nlet read (box: Box<'a>) = box.Value\nlet main () = (read { Value = true }, read { Value = () })" }
    { Name = "option-map"; Expected = Accept
      Body = "let main () = Option.map (fun x -> not x) (Some true)" }
    { Name = "option-bind"; Expected = Accept
      Body = "let main () = Option.bind (fun x -> Some (not x)) (Some true)" }
    { Name = "option-filter"; Expected = Accept
      Body = "let main () = Option.filter (fun x -> x) (Some true)" }
    { Name = "option-map-dimensions"; Expected = Accept
      Body = "[<Measure>] type m\n[<Measure>] type s\nlet main (value: float<m> option) (elapsed: float<s>) = Option.map (fun distance -> distance / elapsed) value" }
    { Name = "incompatible-dimensions-rejected"; Expected = Reject (Some "CCS8040")
      Body = "[<Measure>] type m\n[<Measure>] type s\nlet main (distance: float<m>) (elapsed: float<s>) = distance + elapsed" }
    { Name = "option-fold"; Expected = Accept
      Body = "let main () = Option.fold (fun state value -> state && value) true (Some false)" }
    { Name = "result-map"; Expected = Accept
      Body = "let main (value: Result<bool, bool>) = Result.map (fun x -> not x) value" }
    { Name = "result-bind"; Expected = Accept
      Body = "let main (value: Result<bool, bool>) = Result.bind (fun x -> Ok (not x)) value" }
    { Name = "list-map"; Expected = Accept
      Body = "let main () = List.map (fun x -> not x) [true; false]" }
    { Name = "list-fold"; Expected = Accept
      Body = "let main () = List.fold (fun state value -> state && value) true [true; false]" }
    { Name = "null-rejected"; Expected = Reject (Some "CCS8010")
      Body = "let main () = null" }
    { Name = "obj-rejected"; Expected = Reject (Some "CCS8706")
      Body = "let main (value: obj) = value" }
    { Name = "boxing-rejected"; Expected = Reject (Some "CCS8009")
      Body = "let main () = box true" }
    // A plain function has no admitted builder operations. These must not be
    // accepted by dropping return/do!/return! or treating the body as eager code.
    { Name = "non-builder-return-rejected"; Expected = Reject None
      Body = "let builder x = x\nlet main () =\n    builder {\n        return true\n    }" }
    { Name = "non-builder-return-from-rejected"; Expected = Reject None
      Body = "let builder x = x\nlet main () =\n    builder {\n        return! true\n    }" }
    { Name = "non-builder-do-bang-rejected"; Expected = Reject None
      Body = "let builder x = x\nlet main () =\n    builder {\n        do! true\n        return ()\n    }" }
    { Name = "non-builder-let-bang-rejected"; Expected = Reject None
      Body = "let builder x = x\nlet main () =\n    builder {\n        let! value = true\n        return value\n    }" }
]

let compiler = typeof<CheckResult>.Assembly.Location
printfn "CCS assembly: %s" compiler
printfn "CCS SHA256: %s" (SHA256.HashData(File.ReadAllBytes compiler) |> Convert.ToHexString)
printfn "Scope: source checking only; no platform, native execution, or solver claim."
let mutable gaps = 0
for probe in probes do
    let source = "module LanguageSurface\n" + probe.Body + "\n"
    let outcome, diagnostics =
        match parseAndCheck source (probe.Name + ".clef") with
        | ParseFailure errors -> "parse-failure", errors
        | Success result ->
            let graphErrors = result.Graph.Nodes |> Map.toList |> List.choose (fun (_, node) ->
                match node.Kind with SemanticKind.Error message -> Some message | _ -> None)
            let hasErrorDiagnostic = result.Diagnostics |> List.exists (fun d ->
                Diagnostic.effectiveSeverity d = NativeDiagnosticSeverity.Error)
            (if hasErrorDiagnostic then "success-with-error-diagnostics"
             elif not graphErrors.IsEmpty then "accepted-with-error-nodes"
             else "accepted"),
            (result.Diagnostics |> List.map (fun d -> $"{d.Code}: {d.Message}")) @ graphErrors
        | CheckFailure result ->
            let located = result.Diagnostics |> List.filter (fun d ->
                Diagnostic.effectiveSeverity d = NativeDiagnosticSeverity.Error &&
                d.Range.File = probe.Name + ".clef" && d.Range.Start.Line > 0)
            let intended = match probe.Expected with
                           | Reject (Some code) -> located |> List.exists (fun d -> d.Code = code)
                           | _ -> true
            (if located.IsEmpty then "unlocated-failure"
             elif not intended then "wrong-rejection-reason"
             else "rejected"),
            result.Diagnostics |> List.map (fun d -> $"{d.Code}: {d.Message}")
    // A parser failure or a crash is never counted as a successful rejection.
    let met = match probe.Expected, outcome with Accept, "accepted" | Reject _, "rejected" -> true | _ -> false
    if not met then gaps <- gaps + 1
    printfn "%s %s: expected=%A observed=%s" (if met then "MET" else "GAP") probe.Name probe.Expected outcome
    if not met || (match probe.Expected with Reject _ -> true | Accept -> false) then
        for diagnostic in diagnostics do printfn "  %s" diagnostic
printfn "%d/%d source expectations met; %d gaps." (probes.Length - gaps) probes.Length gaps
exit (if gaps = 0 then 0 else 1)
