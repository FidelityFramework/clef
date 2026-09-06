// Build CCS with -p:CopyLocalLockFileAssemblies=true, then:
// dotnet fsi tests/NativeTypeCheckerTest.fsx [test-name substring]
// Normative: clef-lang-spec/spec/{units-of-measure,ntu-types,conformance}.md
#r "../artifacts/bin/Clef.Compiler.Service/Debug/net10.0/FSharp.Json.dll"
#r "../artifacts/bin/Clef.Compiler.Service/Debug/net10.0/XParsec.dll"
#r "../artifacts/bin/Clef.Compiler.Service/Debug/net10.0/Clef.Compiler.Service.dll"

#load "Clef.Compiler.Service.Tests/DimensionalCases.fs"

open Clef.Compiler.Service.Tests.DimensionalCases

let filter = fsi.CommandLineArgs |> Array.tryItem 1 |> Option.defaultValue ""
let selected = tests |> List.filter (fun (name, _) -> name.Contains filter)
if selected.IsEmpty then failwithf "No test matches '%s'" filter
let mutable failures = 0
for name, test in selected do
    try test (); printfn "PASS %s" name
    with error -> failures <- failures + 1; eprintfn "FAIL %s: %s" name error.Message
if failures > 0 then failwithf "%d native type check(s) failed" failures
printfn "%d native type checks passed" selected.Length
