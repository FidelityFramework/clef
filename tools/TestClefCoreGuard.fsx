// Automated controls for tools/ClefCoreGuard.fsx (clef #165 Increment A).
// Positive, exact-reason negative, directive/lexer-boundary negative,
// per-token nesting depth, split-directive identifier chain, extended-string,
// escape-decoding, stale-table, and ratchet controls. Every case runs the
// production guard as a subprocess, so the rules under test are the exact rules
// MSBuild executes before CoreCompile.
//
//   dotnet fsi --nologo --quiet tools/TestClefCoreGuard.fsx [<compiled-inputs-manifest>]
open System
open System.IO
open System.Diagnostics
open System.Globalization

let scriptPath = fsi.CommandLineArgs[0]
let repoRoot = Path.GetFullPath(Path.Combine(Path.GetDirectoryName scriptPath, ".."))
let guard = Path.Combine(repoRoot, "tools/ClefCoreGuard.fsx")
let allowances = Path.Combine(repoRoot, "build/ClefCore.allowances.tsv")

let dotnet =
    let d = Environment.GetEnvironmentVariable "DOTNET_HOST_PATH"
    if String.IsNullOrEmpty d then "dotnet" else d

// Parse SDK version strings numerically so e.g. 10.0.401 sorts after 9.0.300,
// and stable releases sort after pre-release builds of the same core version.
let parseSdkVersion (ver: string) =
    let dash = ver.IndexOf('-')
    let core = if dash >= 0 then ver.Substring(0, dash) else ver
    let preRank = if dash >= 0 then 0 else 1
    let nums =
        core.Split('.')
        |> Array.map (fun part ->
            match Int32.TryParse(part, NumberStyles.Integer, CultureInfo.InvariantCulture) with
            | true, n -> n
            | false, _ -> -1)
    let part i = if i < nums.Length then nums[i] else 0
    (part 0, part 1, part 2, preRank, ver)

let discoverSdkFcsRefs () =
    let candidates = ResizeArray<string * string>()
    let addFromRoot (root: string) =
        if not (String.IsNullOrEmpty root) && Directory.Exists root then
            let sdkDir = Path.Combine(root, "sdk")
            if Directory.Exists sdkDir then
                for verDir in Directory.GetDirectories sdkDir do
                    let ver = Path.GetFileName verDir
                    let dll = Path.Combine(verDir, "FSharp/FSharp.Compiler.Service.dll")
                    if File.Exists dll then candidates.Add(ver, dll)
    addFromRoot (Environment.GetEnvironmentVariable "DOTNET_ROOT")
    let dotnetDir =
        if Path.IsPathRooted dotnet then Path.GetDirectoryName dotnet else ""
    addFromRoot dotnetDir
    if candidates.Count = 0 then
        try
            let psi = ProcessStartInfo(dotnet)
            psi.RedirectStandardOutput <- true
            psi.RedirectStandardError <- true
            psi.ArgumentList.Add "--list-sdks"
            use p = Process.Start(psi)
            let outTask = p.StandardOutput.ReadToEndAsync()
            let errTask = p.StandardError.ReadToEndAsync()
            if p.WaitForExit(15_000) then
                let out = outTask.Result
                let _ = errTask.Result
                if p.ExitCode = 0 then
                    for line in out.Split('\n') do
                        let trimmed = line.Trim()
                        let lb = trimmed.IndexOf('[')
                        let rb = trimmed.LastIndexOf(']')
                        if lb > 0 && rb > lb then
                            let ver = trimmed.Substring(0, lb).Trim()
                            let baseDir = trimmed.Substring(lb + 1, rb - lb - 1).Trim()
                            let dll = Path.Combine(baseDir, ver, "FSharp/FSharp.Compiler.Service.dll")
                            if File.Exists dll then candidates.Add(ver, dll)
            else
                try p.Kill(true) with _ -> ()
        with _ -> ()
    candidates
    |> Seq.distinctBy snd
    |> Seq.sortBy (fun (ver, _) -> parseSdkVersion ver)
    |> Seq.toList

let fcsRef =
    let env = Environment.GetEnvironmentVariable "ClefGuardFcsRef"
    if not (String.IsNullOrEmpty env) then env
    else
        let found = discoverSdkFcsRefs ()
        if found.IsEmpty then "" else found |> List.last |> snd

let workDir = Path.Combine(Path.GetTempPath(), "clef165a-guard-controls-" + Guid.NewGuid().ToString("N"))
Directory.CreateDirectory workDir |> ignore

let src ls = String.concat "\n" ls + "\n"

let writeFixtureFile (relPath: string) (source: string) =
    let full = Path.Combine(workDir, relPath)
    Directory.CreateDirectory(Path.GetDirectoryName full) |> ignore
    File.WriteAllText(full, source)
    full

let fixture (name: string) (source: string) =
    let full = writeFixtureFile name source
    let manifestPath = full + ".manifest.tsv"
    File.WriteAllText(manifestPath, "P\t" + workDir + "\nF\t" + full + "\t" + name + "\n")
    manifestPath

let batchManifest (manifestName: string) (entries: (string * string) list) =
    let rows =
        [ yield "P\t" + workDir
          for (relPath, source) in entries do
              let full = writeFixtureFile relPath source
              yield "F\t" + full + "\t" + relPath ]
    let manifestPath = Path.Combine(workDir, manifestName)
    File.WriteAllText(manifestPath, src rows)
    manifestPath

let rowsFile (path: string) (rows: string list) =
    File.WriteAllText(path, if rows.IsEmpty then "" else src rows)

let subprocessTimeoutMs = 60_000

let run args =
    let psi = ProcessStartInfo(dotnet)
    psi.WorkingDirectory <- repoRoot
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    psi.ArgumentList.Add "fsi"
    psi.ArgumentList.Add "--nologo"
    psi.ArgumentList.Add "--quiet"
    if fcsRef <> "" then psi.ArgumentList.Add ("--reference:" + fcsRef)
    psi.ArgumentList.Add guard
    for a in args do psi.ArgumentList.Add a
    use p = Process.Start(psi)
    let outTask = p.StandardOutput.ReadToEndAsync()
    let errTask = p.StandardError.ReadToEndAsync()
    if p.WaitForExit(subprocessTimeoutMs) then
        p.WaitForExit()
        (p.ExitCode, outTask.Result, errTask.Result)
    else
        try p.Kill(true) with _ -> ()
        (-1, "", sprintf "TIMEOUT after %d ms waiting for ClefCoreGuard.fsx" subprocessTimeoutMs)

let mutable failures = 0
let mutable passes = 0

let assertCond (label: string) (ok: bool) (detail: string) =
    if ok then
        passes <- passes + 1
        printfn "PASS  %s" label
    else
        failures <- failures + 1
        printfn "FAIL  %s: %s" label detail

let expectAll (label: string) (wantExit: int) (wantTexts: string list) ((exitCode, out, err): int * string * string) =
    let combined = out + "\n" + err
    let missing = wantTexts |> List.filter (fun t -> t <> "" && not (combined.Contains(t, StringComparison.Ordinal)))
    if exitCode = wantExit && missing.IsEmpty then
        passes <- passes + 1
        printfn "PASS  %s (exit %d)" label exitCode
    else
        failures <- failures + 1
        printfn "FAIL  %s: expected exit %d, missing=[%s], got exit %d: %s"
            label wantExit (String.concat "; " missing) exitCode (err.Trim())

let expectExactStderrLines (label: string) (wantExit: int) (wantLines: string list) ((exitCode, _, err): int * string * string) =
    let actualLines =
        err.Split('\n')
        |> Array.map (fun l -> l.Trim())
        |> Array.filter (fun l -> l.Length > 0)
        |> Array.toList
    if exitCode = wantExit && actualLines = wantLines then
        passes <- passes + 1
        printfn "PASS  %s (exit %d, %d stderr line(s))" label exitCode actualLines.Length
    else
        failures <- failures + 1
        printfn "FAIL  %s: expected exit %d / lines [%s], got exit %d / lines [%s]"
            label wantExit (String.concat "; " wantLines) exitCode (String.concat "; " actualLines)

let expect (label: string) (wantExit: int) (wantText: string) result =
    expectAll label wantExit (if wantText = "" then [] else [wantText]) result

// Locate fsc.dll, FSharp.Core.dll, and the .NET 10 reference assembly pack from fcsRef
// so fixture compilation checks exercise the real F# 10 compiler with the project's flags.
let fscToolchain =
    let fsharpDir =
        if not (String.IsNullOrEmpty fcsRef) then Path.GetDirectoryName fcsRef else ""
    let fscDll = Path.Combine(fsharpDir, "fsc.dll")
    let fsharpCoreDll = Path.Combine(fsharpDir, "FSharp.Core.dll")
    let dotnetRoot =
        if String.IsNullOrEmpty fsharpDir then ""
        else Path.GetFullPath(Path.Combine(fsharpDir, "../../.."))
    let refPackDir =
        let packsRoot = Path.Combine(dotnetRoot, "packs/Microsoft.NETCore.App.Ref")
        if Directory.Exists packsRoot then
            Directory.GetDirectories packsRoot
            |> Array.sortBy (fun d -> parseSdkVersion (Path.GetFileName d))
            |> Array.tryLast
            |> Option.map (fun d -> Path.Combine(d, "ref/net10.0"))
            |> Option.defaultValue ""
        else ""
    (fscDll, fsharpCoreDll, refPackDir)

let compileCheckFixtures (label: string) (fsPaths: string list) (defines: string list) =
    let fscDll, fsharpCoreDll, refDir = fscToolchain
    if not (File.Exists fscDll) || not (File.Exists fsharpCoreDll) || not (Directory.Exists refDir) then
        failures <- failures + 1
        printfn "FAIL  %s: could not locate fsc toolchain (fsc=%s fsharpCore=%s refDir=%s)" label fscDll fsharpCoreDll refDir
    else
        let outDll = Path.Combine(workDir, "compile-probe-" + Guid.NewGuid().ToString("N") + ".dll")
        let psi = ProcessStartInfo(dotnet)
        psi.WorkingDirectory <- repoRoot
        psi.RedirectStandardOutput <- true
        psi.RedirectStandardError <- true
        for a in [
            fscDll; "--nologo"; "--target:library"; "--out:" + outDll
            "--langversion:preview"; "--warnaserror+"; "--warnon:3218"; "--warnon:3390"; "--checknulls+"
            "--noframework"; "-r:" + fsharpCoreDll
        ] do
            psi.ArgumentList.Add a
        for d in defines do psi.ArgumentList.Add ("--define:" + d)
        for r in Directory.GetFiles(refDir, "*.dll") do psi.ArgumentList.Add ("-r:" + r)
        for fsPath in fsPaths do psi.ArgumentList.Add fsPath
        use p = Process.Start(psi)
        let outTask = p.StandardOutput.ReadToEndAsync()
        let errTask = p.StandardError.ReadToEndAsync()
        let exitCode, out, err =
            if p.WaitForExit(subprocessTimeoutMs) then
                p.WaitForExit()
                (p.ExitCode, outTask.Result, errTask.Result)
            else
                try p.Kill(true) with _ -> ()
                (-1, "", sprintf "TIMEOUT after %d ms compiling %d fixture(s)" subprocessTimeoutMs fsPaths.Length)
        assertCond label (exitCode = 0 && out.Trim() = "" && err.Trim() = "")
            (sprintf "exit=%d out=%s err=%s" exitCode (out.Trim()) (err.Trim()))

let runControls () =
    let emptyAllowance = Path.Combine(workDir, "empty.allowances.tsv")
    rowsFile emptyAllowance []

    // ---- SDK version ordering control ---------------------------------------
    assertCond "positive: numeric SDK sort orders 10.0.401 after 9.0.300 and after 10.0.401-preview.1"
        (parseSdkVersion "10.0.401" > parseSdkVersion "9.0.300" &&
         parseSdkVersion "10.0.401" > parseSdkVersion "10.0.401-preview.1")
        "numeric SDK version ordering failed"

    // ---- positive controls --------------------------------------------------
    let cleanFixtureRel = "Baker/Recipes/CleanFixture.fs"
    let cleanManifest =
        fixture cleanFixtureRel (src [
            "#nowarn \"40\""
            "module CleanFixture"
            "open System"
            "type ReflectionKind = Structural | Nominal"
            "type ConcurrentCount = { ConcurrentCount: int }"
            "type EnvironmentCreate = { EnvironmentCreate: int }"
            "type Holder = { Environment: {| Exit: int |} }"
            "let useField (h: Holder) = h.Environment.Exit"
            "let getHolder () : Holder = { Environment = {| Exit = 0 |} }"
            "let useExpr () = (getHolder ()).Environment.Exit"
            "let bareEnvironmentWord = \"Environment\""
            "let progress () = printf \"done %d%%A and %%%%A and %%+A more\" 1"
            "let interpEscaped = $\"literal %%A and %%%%A and %%+A\""
            "let extLiteral2 xs = $$\"\"\"%A{{xs}}\"\"\""
            "let extLiteral3a xs = $$$\"\"\"%A{{{xs}}}\"\"\""
            "let extLiteral3b xs = $$$\"\"\"%%A{{{xs}}}\"\"\""
            "let extLiteral7 xs = $$$$$$$\"\"\"%%%%%%A{{{{{{{xs}}}}}}}\"\"\""
            "let twoNestedInterp x ="
            "    $\"\"\"outer {"
            "                $\"inner {x}\""
            "              }\"\"\""
            "let escapedBackslash = \"\\\\u0025A\""
            "let escapedBackslashTrigraph = \"\\\\293A\""
            "let escapedDoublePct = \"\\u0025\\u0025A\""
            "let verbatimEscape = @\"\\u0025A\""
            "let verbatimUnicodeTrigraph = @\"\\\u07c07\u0beb\""
            "let tripleEscape = \"\"\"\\u0025A\"\"\""
            "let tripleHighTrigraph = \"\"\"\\293A\"\"\""
            "let verbatimInterpEscape x = $@\"\\u0025A{x}\""
            "let tripleInterpEscape x = $\"\"\"\\u0025A{x}\"\"\""
            "let asciiZeroTrigraph = \"\\000\""
            "let byteLit = \"%A\"B"
            "let charLit = '%'"
            "let hashCharLit = '#'"
            "let hashInString = \"#light # 1\""
            "let splitLine = \"%"
            "A\""
            "let pad s = sprintf \"%s text\" s"
            "let useDisposable (x: #IDisposable) = x"
            "type line_suffix = interface end"
            "let useLineSuffix (x:"
            "#line_suffix"
            ") = x"
            "(* ConditionalWeakTable and System.Reflection appear only in this comment"
            "#if CLEF_NEVER"
            "#line 1 \"comment.fs\""
            "#light"
            "*)"
            "let tripleWithDirective = \"\"\"hello"
            "#if CLEF_NEVER"
            "#line 1 \"string.fs\""
            "#light \"on\""
            "world\"\"\""
            "let note = \"ConditionalWeakTable and %s are mentioned in a string\""
            "#if NULLABLE"
            "#if INNER"
            "let optional = Some 1"
            "#else"
            "let optional = Some 2"
            "#endif"
            "#else"
            "let optional = None"
            "#endif"])
    expect "positive: ban-free file with #nowarn, nested #if, flexible types, 2-deep interp, 7-$ literal %A, escapes, and non-matching identifiers" 0 ""
        (run ["check"; cleanManifest; emptyAllowance])
    let cleanFixtureFull = Path.Combine(workDir, cleanFixtureRel)
    compileCheckFixtures "positive: CleanFixture.fs compiles cleanly with fsc project flags (default defines)" [cleanFixtureFull] []
    compileCheckFixtures "positive: CleanFixture.fs compiles cleanly with fsc project flags (--define:NULLABLE)" [cleanFixtureFull] ["NULLABLE"]
    compileCheckFixtures "positive: CleanFixture.fs compiles cleanly with fsc project flags (--define:NULLABLE --define:INNER)" [cleanFixtureFull] ["NULLABLE"; "INNER"]

    // Verify active code AFTER #if inside block comments and triple-quoted
    // strings is still scanned and catches banned identifiers.
    let activeAfterNonDirectiveIf =
        fixture "Baker/Recipes/ActiveAfterLiteralIf.fs" (src [
            "module ActiveAfterLiteralIf"
            "(* comment containing a directive"
            "#if CLEF_NEVER"
            "*)"
            "let doc = \"\"\"hello"
            "#if CLEF_NEVER"
            "world\"\"\""
            "let cache = ConditionalWeakTable<int, int>()"])
    expect "negative: active code after #if inside block comment and triple-quoted string is still scanned" 1
        "ActiveAfterLiteralIf.fs(8,13): error CLEF001: ConditionalWeakTable allowance=0 actual=1"
        (run ["check"; activeAfterNonDirectiveIf; emptyAllowance])

    let baseRows = Path.Combine(workDir, "base.allowances.tsv")
    let sameRows = Path.Combine(workDir, "same.allowances.tsv")
    let shrunkRows = Path.Combine(workDir, "shrunk.allowances.tsv")
    rowsFile baseRows ["Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t3"]
    rowsFile sameRows ["Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t3"]
    rowsFile shrunkRows ["Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t1"]
    expect "positive: ratchet accepts an unchanged count" 0 "" (run ["ratchet"; baseRows; sameRows])
    expect "positive: ratchet accepts a shrunken count" 0 "" (run ["ratchet"; baseRows; shrunkRows])

    let admitProposed = Path.Combine(workDir, "admit-proposed.allowances.tsv")
    let admitCensus = Path.Combine(workDir, "admit-census.allowances.tsv")
    rowsFile admitProposed [
        "Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t2"
        "NativeTypedTree/NewRule.fs\t%A\t4"
    ]
    rowsFile admitCensus [
        "Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t3"
        "NativeTypedTree/NewRule.fs\t%A\t4"
    ]
    expect "positive: ratchet --admit-new-rules accepts shrunk existing rule and measured new rule" 0 ""
        (run ["ratchet"; baseRows; admitProposed; "--admit-new-rules"; admitCensus])

    // ---- table-driven exact-reason negatives for EVERY single banned rule ---
    // Each rule sits in its own isolated Zone A file so removing any single rule
    // from ClefCoreGuard.fsx causes its dedicated assertion to fail.
    let singleRuleCases : (string * string * string * string list) list = [
        // 29 bare names
        "FSharpValue", "Baker/Recipes/Rule_FSharpValue.fs", "FSharpValue", ["module R"; "let x = FSharpValue.GetUnionFields"]
        "FSharpType", "Baker/Recipes/Rule_FSharpType.fs", "FSharpType", ["module R"; "let x = FSharpType.IsUnion"]
        "ConditionalWeakTable", "Baker/Recipes/Rule_ConditionalWeakTable.fs", "ConditionalWeakTable", ["module R"; "let x = ConditionalWeakTable<int, int>()"]
        "ProcessStartInfo", "Baker/Recipes/Rule_ProcessStartInfo.fs", "ProcessStartInfo", ["module R"; "let x = ProcessStartInfo(\"ls\")"]
        "ConcurrentDictionary", "Baker/Recipes/Rule_ConcurrentDictionary.fs", "ConcurrentDictionary", ["module R"; "let x = ConcurrentDictionary<int, int>()"]
        "ConcurrentQueue", "Baker/Recipes/Rule_ConcurrentQueue.fs", "ConcurrentQueue", ["module R"; "let x = ConcurrentQueue<int>()"]
        "ConcurrentBag", "Baker/Recipes/Rule_ConcurrentBag.fs", "ConcurrentBag", ["module R"; "let x = ConcurrentBag<int>()"]
        "ConcurrentStack", "Baker/Recipes/Rule_ConcurrentStack.fs", "ConcurrentStack", ["module R"; "let x = ConcurrentStack<int>()"]
        "ConcurrentExclusiveSchedulerPair", "Baker/Recipes/Rule_ConcurrentExclSched.fs", "ConcurrentExclusiveSchedulerPair", ["module R"; "open System.Threading.Tasks"; "let x = ConcurrentExclusiveSchedulerPair()"]
        "BlockingCollection", "Baker/Recipes/Rule_BlockingCollection.fs", "BlockingCollection", ["module R"; "let x = BlockingCollection<int>()"]
        "ThreadLocal", "Baker/Recipes/Rule_ThreadLocal.fs", "ThreadLocal", ["module R"; "let x = ThreadLocal<int>()"]
        "ThreadStatic", "Baker/Recipes/Rule_ThreadStatic.fs", "ThreadStatic", ["module R"; "open System"; "[<ThreadStatic>]"; "let mutable x = 0"]
        "ThreadStaticAttribute", "Baker/Recipes/Rule_ThreadStaticAttr.fs", "ThreadStaticAttribute", ["module R"; "open System"; "type T() ="; "    [<ThreadStaticAttribute; DefaultValue>]"; "    static val mutable x: int"]
        "IsValueCreated", "Baker/Recipes/Rule_IsValueCreated.fs", "IsValueCreated", ["module R"; "let x (v: Lazy<int>) = v.IsValueCreated"]
        "get_IsValueCreated", "Baker/Recipes/Rule_GetIsValueCreated.fs", "get_IsValueCreated", ["module R"; "let x (v: Lazy<int>) = v.get_IsValueCreated()"]
        "Reflection", "Baker/Recipes/Rule_Reflection.fs", "Reflection", ["module R"; "open System"; "let x = Reflection.Assembly.GetExecutingAssembly()"]
        "Concurrent", "Baker/Recipes/Rule_Concurrent.fs", "Concurrent", ["module R"; "open System.Collections"; "let x = Concurrent.OrderablePartitioner"]
        "failwith", "Nanopass/Rule_failwith.fs", "failwith", ["module R"; "let x () = failwith \"error\""]
        "failwithf", "Nanopass/Rule_failwithf.fs", "failwithf", ["module R"; "let x () = failwithf \"%s\" \"error\""]
        "invalidOp", "Nanopass/Rule_invalidOp.fs", "invalidOp", ["module R"; "let x () = invalidOp \"error\""]
        "invalidArg", "Nanopass/Rule_invalidArg.fs", "invalidArg", ["module R"; "let x () = invalidArg \"a\" \"error\""]
        "nullArg", "Nanopass/Rule_nullArg.fs", "nullArg", ["module R"; "let x () = nullArg \"a\""]
        "raise", "Nanopass/Rule_raise.fs", "raise", ["module R"; "let x e = raise e"]
        "reraise", "Nanopass/Rule_reraise.fs", "reraise", ["module R"; "let x () = reraise ()"]
        "Stopwatch", "NativeTypedTree/Rule_Stopwatch.fs", "Stopwatch", ["module R"; "let x = Stopwatch.StartNew()"]
        "Console", "NativeTypedTree/Rule_Console.fs", "Console", ["module R"; "let x = Console.Error"]
        "GetEnvironmentVariable", "NativeTypedTree/Rule_GetEnvVar.fs", "GetEnvironmentVariable", ["module R"; "let x = GetEnvironmentVariable \"X\""]
        "GetEnvironmentVariables", "NativeTypedTree/Rule_GetEnvVars.fs", "GetEnvironmentVariables", ["module R"; "let x = GetEnvironmentVariables ()"]
        "GetFolderPath", "NativeTypedTree/Rule_GetFolderPath.fs", "GetFolderPath", ["module R"; "let x = GetFolderPath 0"]
        // 7 dotted namespace prefixes
        "System.Reflection", "PSGSaturation/Rule_SysReflection.fs", "System.Reflection", ["module R"; "open System.Reflection"]
        "Microsoft.FSharp.Reflection", "PSGSaturation/Rule_MsFSharpReflection.fs", "Microsoft.FSharp.Reflection", ["module R"; "open Microsoft.FSharp.Reflection"]
        "System.Collections.Concurrent", "PSGSaturation/Rule_SysConcurrent.fs", "System.Collections.Concurrent", ["module R"; "open System.Collections.Concurrent"]
        "System.Diagnostics.Stopwatch", "PSGSaturation/Rule_SysStopwatch.fs", "System.Diagnostics.Stopwatch", ["module R"; "let x = System.Diagnostics.Stopwatch.StartNew()"]
        "System.Environment", "PSGSaturation/Rule_SysEnvironment.fs", "System.Environment", ["module R"; "let x = System.Environment.Exit 1"]
        "System.Console", "PSGSaturation/Rule_SysConsole.fs", "System.Console", ["module R"; "let x = System.Console.Error"]
        "System.Threading.ThreadLocal", "PSGSaturation/Rule_SysThreadLocal.fs", "System.Threading.ThreadLocal", ["module R"; "let x = System.Threading.ThreadLocal<int>()"]
        // Chain-head Environment. and open type Environment forms (after open System)
        "Environment.Exit", "NativeTypedTree/Rule_EnvExit.fs", "Environment", ["module R"; "open System"; "let x () = Environment.Exit 1"]
        "Environment.ProcessorCount", "NativeTypedTree/Rule_EnvProc.fs", "Environment", ["module R"; "open System"; "let x = Environment.ProcessorCount"]
        "Environment.TickCount", "NativeTypedTree/Rule_EnvTick.fs", "Environment", ["module R"; "open System"; "let x = Environment.TickCount"]
        "Environment.SetEnvironmentVariable", "NativeTypedTree/Rule_EnvSet.fs", "Environment", ["module R"; "open System"; "let x () = Environment.SetEnvironmentVariable(\"A\",\"B\")"]
        "Environment.GetCommandLineArgs", "NativeTypedTree/Rule_EnvArgs.fs", "Environment", ["module R"; "open System"; "let x = Environment.GetCommandLineArgs()"]
        "backtick Environment.Exit", "NativeTypedTree/Rule_EnvBacktick.fs", "Environment", ["module R"; "open System"; "let x () = ``Environment``.Exit 1"]
        "open type Environment", "NativeTypedTree/Rule_OpenTypeEnv.fs", "Environment", ["module R"; "open System"; "open type Environment"; "let x = ProcessorCount"]
        "open type backtick Environment", "NativeTypedTree/Rule_OpenTypeEnvBacktick.fs", "Environment", ["module R"; "open System"; "open type ``Environment``"; "let x = TickCount"]
    ]

    let ruleBatch =
        batchManifest "single-rules.manifest.tsv"
            (singleRuleCases |> List.map (fun (_, rel, _, lines) -> rel, src lines))
    let ruleExit, _, ruleErr = run ["check"; ruleBatch; emptyAllowance]
    assertCond (sprintf "negative-batch: all %d isolated rule fixtures fail check (exit 1)" singleRuleCases.Length) (ruleExit = 1)
        (sprintf "expected exit 1, got %d" ruleExit)
    for (label, rel, ruleName, _) in singleRuleCases do
        let needle = sprintf "%s(" rel
        let ruleFragment = sprintf ": error CLEF001: %s allowance=0 actual=1" ruleName
        let matched =
            ruleErr.Split('\n')
            |> Array.exists (fun line -> line.Contains(needle, StringComparison.Ordinal) && line.Contains(ruleFragment, StringComparison.Ordinal))
        assertCond (sprintf "negative: isolated rule %s triggers %s" label ruleName) matched
            (sprintf "missing %s ... %s in stderr:\n%s" needle ruleFragment (ruleErr.Trim()))

    // ---- non-conditional directive same-line trailing code & flexible-type negatives
    let directiveTrailingCases : (string * string * string list * string list) list = [
        "#light \"on\" trailing ConditionalWeakTable", "Baker/Recipes/Dir_LightOn.fs",
            [ ": error CLEF001: directive #light is forbidden in Zone A"
              ": error CLEF001: ConditionalWeakTable allowance=0 actual=1" ],
            ["module D"; "let cache ="; "#light \"on\" System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()"]
        "#light\"on\" (no space) trailing ConditionalWeakTable", "Baker/Recipes/Dir_LightOnNoSpace.fs",
            [ ": error CLEF001: directive #light is forbidden in Zone A"
              ": error CLEF001: ConditionalWeakTable allowance=0 actual=1" ],
            ["module D"; "let cache ="; "#light\"on\" System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()"]
        "bare #light trailing failwith", "Baker/Recipes/Dir_LightBare.fs",
            [ ": error CLEF001: directive #light is forbidden in Zone A"
              ": error CLEF001: failwith allowance=0 actual=1" ],
            ["module D"; "#light let failSite () = failwith \"error\""]
        "#light with non-on/off string trailing failwith", "Baker/Recipes/Dir_LightNonOnOff.fs",
            [ ": error CLEF001: directive #light is forbidden in Zone A"
              ": error CLEF001: failwith allowance=0 actual=1" ],
            ["module D"; "#light \"foo\" let failSite () = failwith \"error\""]
        "#indent \"on\" trailing %A", "Baker/Recipes/Dir_IndentOn.fs",
            [ ": error CLEF001: directive #indent is forbidden in Zone A"
              ": error CLEF001: %A allowance=0 actual=1" ],
            ["module D"; "#indent \"on\" let show x = sprintf \"%A\" x"]
        "#define flexible type ThreadLocal", "Baker/Recipes/Dir_DefineFlexThreadLocal.fs",
            [ ": error CLEF001: directive #define is forbidden in Zone A"
              ": error CLEF001: ThreadLocal allowance=0 actual=1" ],
            ["module D"; "open System.Threading"; "type define = interface end"; "let f (x:"; "#define ThreadLocal"; ") = ()"]
        "#undef flexible type ThreadLocal", "Baker/Recipes/Dir_UndefFlexThreadLocal.fs",
            [ ": error CLEF001: directive #undef is forbidden in Zone A"
              ": error CLEF001: ThreadLocal allowance=0 actual=1" ],
            ["module D"; "open System.Threading"; "type undef = interface end"; "let f (x:"; "#undef ThreadLocal"; ") = ()"]
        "#define trailing ConditionalWeakTable", "Baker/Recipes/Dir_Define.fs",
            [ ": error CLEF001: directive #define is forbidden in Zone A"
              ": error CLEF001: ConditionalWeakTable allowance=0 actual=1" ],
            ["module D"; "#define X let cache = System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()"]
        "#undef trailing failwith", "Baker/Recipes/Dir_Undef.fs",
            [ ": error CLEF001: directive #undef is forbidden in Zone A"
              ": error CLEF001: failwith allowance=0 actual=1" ],
            ["module D"; "#undef X let failSite () = failwith \"error\""]
        "interactive #r directive refused", "Baker/Recipes/Dir_HashR.fs",
            [ "(2,1): error CLEF001: directive #r is forbidden in Zone A" ],
            ["module D"; "#r \"System.dll\""]
        "interactive #load directive refused", "Baker/Recipes/Dir_HashLoad.fs",
            [ "(2,1): error CLEF001: directive #load is forbidden in Zone A" ],
            ["module D"; "#load \"other.fsx\""]
        "interactive #I directive refused", "Baker/Recipes/Dir_HashI.fs",
            [ "(2,1): error CLEF001: directive #I is forbidden in Zone A" ],
            ["module D"; "#I \".\""]
        "interactive #time directive refused", "Baker/Recipes/Dir_HashTime.fs",
            [ "(2,1): error CLEF001: directive #time is forbidden in Zone A" ],
            ["module D"; "#time \"on\""]
        "mid-line #nowarn directive refused", "Baker/Recipes/Dir_MidNowarn.fs",
            [ ": error CLEF001: mid-line #nowarn / #warnon directive is forbidden in Zone A" ],
            ["module D"; "let exitSite () ="; "    System #nowarn \"40\""; "        .Environment.Exit 1"]
    ]
    let dirBatch =
        batchManifest "directive-trailing.manifest.tsv"
            (directiveTrailingCases |> List.map (fun (_, rel, _, lines) -> rel, src lines))
    let dirExit, _, dirErr = run ["check"; dirBatch; emptyAllowance]
    assertCond (sprintf "negative-batch: all %d non-conditional directive and flexible-type fixtures fail check (exit 1)" directiveTrailingCases.Length) (dirExit = 1)
        (sprintf "expected exit 1, got %d" dirExit)
    for (label, rel, expectedFrags, _) in directiveTrailingCases do
        let needle = sprintf "%s(" rel
        let missing =
            expectedFrags
            |> List.filter (fun frag ->
                not (dirErr.Split('\n')
                     |> Array.exists (fun line -> line.Contains(needle, StringComparison.Ordinal) && line.Contains(frag, StringComparison.Ordinal))))
        assertCond (sprintf "negative: %s caught" label) missing.IsEmpty
            (sprintf "missing %s ... [%s] in stderr:\n%s" needle (String.concat "; " missing) (dirErr.Trim()))

    // ---- line-directive refusal & backslash-quote leak negatives (line-start & mid-line)
    let lineDirectiveCases : (string * string * string list * string list * bool) list = [
        "# 1 \"x\\\" line directive refused and does not leak string state into subsequent banned sites",
        "Baker/Recipes/LineDir_HashNumBackslash.fs",
        [ "module LineDirHashNumBackslash"
          "open System"
          "# 1 \"x\\\""
          "let cache = System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()"
          "let failSite () = failwith \"hidden\""
          "let exitSite () = Environment.Exit 1"
          "let show x = sprintf \"%A\" x" ],
        [ "LineDir_HashNumBackslash.fs(3,1): error CLEF001: #line / # <int> line directives are forbidden in Zone A"
          "LineDir_HashNumBackslash.fs(4,45): error CLEF001: ConditionalWeakTable allowance=0 actual=1"
          "LineDir_HashNumBackslash.fs(5,19): error CLEF001: failwith allowance=0 actual=1"
          "LineDir_HashNumBackslash.fs(6,19): error CLEF001: Environment allowance=0 actual=1"
          "LineDir_HashNumBackslash.fs(7,23): error CLEF001: %A allowance=0 actual=1" ],
        false

        "#line 1 \"x\\\" line directive refused and does not leak string state into subsequent banned sites",
        "Baker/Recipes/LineDir_HashLineBackslash.fs",
        [ "module LineDirHashLineBackslash"
          "open System"
          "#line 1 \"x\\\""
          "let cache = System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()"
          "let failSite () = failwith \"hidden\""
          "let exitSite () = Environment.Exit 1"
          "let show x = sprintf \"%A\" x" ],
        [ "LineDir_HashLineBackslash.fs(3,1): error CLEF001: #line / # <int> line directives are forbidden in Zone A"
          "LineDir_HashLineBackslash.fs(4,45): error CLEF001: ConditionalWeakTable allowance=0 actual=1"
          "LineDir_HashLineBackslash.fs(5,19): error CLEF001: failwith allowance=0 actual=1"
          "LineDir_HashLineBackslash.fs(6,19): error CLEF001: Environment allowance=0 actual=1"
          "LineDir_HashLineBackslash.fs(7,23): error CLEF001: %A allowance=0 actual=1" ],
        false

        "#1 \"x\\\" (no space after #) line directive refused and scans subsequent code",
        "Baker/Recipes/LineDir_CompactHashNum.fs",
        [ "module LineDirCompactHashNum"
          "#1 \"x\\\""
          "let cache = System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()" ],
        [ "LineDir_CompactHashNum.fs(2,1): error CLEF001: #line / # <int> line directives are forbidden in Zone A"
          "LineDir_CompactHashNum.fs(3,45): error CLEF001: ConditionalWeakTable allowance=0 actual=1" ],
        false

        "#line 1 \"x\\\" inside an interpolated string hole refused without leaking string state",
        "Baker/Recipes/LineDir_InInterpHole.fs",
        [ "module LineDirInInterpHole"
          "let s = $\"\"\"{"
          "#line 1 \"x\\\""
          "    (System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()).GetHashCode()"
          "}\"\"\"" ],
        [ "LineDir_InInterpHole.fs(3,1): error CLEF001: #line / # <int> line directives are forbidden in Zone A"
          "LineDir_InInterpHole.fs(4,38): error CLEF001: ConditionalWeakTable allowance=0 actual=1" ],
        false

        "mid-line # 1 \"x\\\" refused and does not hide subsequent banned constructs",
        "Baker/Recipes/MidLine_HashNumAll.fs",
        [ "module MidLineHashNumAll"
          "open System"
          "let anchor = 0 # 1 \"x\\\""
          "let cache = System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()"
          "let failSite () : int = failwith String.Empty"
          "let exitSite () = Environment.Exit 1"
          "let refl () = System.Reflection.Assembly.GetExecutingAssembly().FullName"
          "let lz (v: Lazy<int>) = v.IsValueCreated"
          "let tl = new System.Threading.ThreadLocal<int>()"
          "let show x = sprintf \"%A\" x"
          "// \" resync"
          "let tail = 1" ],
        [ "MidLine_HashNumAll.fs(3,16): error CLEF001: #line / # <int> line directives are forbidden in Zone A"
          "MidLine_HashNumAll.fs(4,45): error CLEF001: ConditionalWeakTable allowance=0 actual=1"
          "MidLine_HashNumAll.fs(5,25): error CLEF001: failwith allowance=0 actual=1"
          "MidLine_HashNumAll.fs(6,19): error CLEF001: Environment allowance=0 actual=1"
          "MidLine_HashNumAll.fs(7,22): error CLEF001: System.Reflection allowance=0 actual=1"
          "MidLine_HashNumAll.fs(8,27): error CLEF001: IsValueCreated allowance=0 actual=1"
          "MidLine_HashNumAll.fs(9,31): error CLEF001: System.Threading.ThreadLocal allowance=0 actual=1"
          "MidLine_HashNumAll.fs(10,23): error CLEF001: %A allowance=0 actual=1" ],
        true

        "mid-line #line 1 \"x\\\" refused and does not hide subsequent failwith or %A",
        "Baker/Recipes/MidLine_HashLine.fs",
        [ "module MidLineHashLine"
          "open System"
          "let anchor = 1 #line 1 \"x\\\""
          "let failSite () : int = failwith String.Empty"
          "let show x = sprintf \"%A\" x" ],
        [ "MidLine_HashLine.fs(3,16): error CLEF001: #line / # <int> line directives are forbidden in Zone A"
          "MidLine_HashLine.fs(4,25): error CLEF001: failwith allowance=0 actual=1"
          "MidLine_HashLine.fs(5,23): error CLEF001: %A allowance=0 actual=1" ],
        true

        "block-comment followed by # 1 \"x\\\" refused and scans subsequent code",
        "Baker/Recipes/MidLine_CommentHashNum.fs",
        [ "module MidLineCommentHashNum"
          "open System"
          "(* note *) # 1 \"x\\\""
          "let cache = System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()"
          "let failSite () : int = failwith String.Empty" ],
        [ "MidLine_CommentHashNum.fs(3,12): error CLEF001: #line / # <int> line directives are forbidden in Zone A"
          "MidLine_CommentHashNum.fs(4,45): error CLEF001: ConditionalWeakTable allowance=0 actual=1"
          "MidLine_CommentHashNum.fs(5,25): error CLEF001: failwith allowance=0 actual=1" ],
        true

        "mid-line System # 1 \"y.fs\" refused and preserves .Environment.Exit chain",
        "NativeTypedTree/MidLine_SysHashNum.fs",
        [ "module MidLineSysHashNum"
          "let exitSite () ="
          "    System # 1 \"y.fs\""
          "        .Environment.Exit 1" ],
        [ "MidLine_SysHashNum.fs(3,12): error CLEF001: #line / # <int> line directives are forbidden in Zone A"
          "MidLine_SysHashNum.fs(4,10): error CLEF001: System.Environment allowance=0 actual=1" ],
        true

        "mid-line System #light refused and preserves .Environment.Exit chain",
        "NativeTypedTree/MidLight_SysChain.fs",
        [ "module MidLightSysChain"
          "let exitSite () ="
          "    System #light"
          "        .Environment.Exit 1" ],
        [ "MidLight_SysChain.fs(3,12): error CLEF001: directive #light is forbidden in Zone A"
          "MidLight_SysChain.fs(4,10): error CLEF001: System.Environment allowance=0 actual=1" ],
        true

        "mid-line Environment #light refused and preserves .Exit chain",
        "NativeTypedTree/MidLight_EnvChain.fs",
        [ "module MidLightEnvChain"
          "open System"
          "let exitSite () ="
          "    Environment #light"
          "        .Exit 1" ],
        [ "MidLight_EnvChain.fs(4,17): error CLEF001: directive #light is forbidden in Zone A"
          "MidLight_EnvChain.fs(4,5): error CLEF001: Environment allowance=0 actual=1" ],
        true

        "mid-line open type #light refused and preserves Environment import",
        "NativeTypedTree/MidLight_OpenType.fs",
        [ "module MidLightOpenType"
          "open System"
          "open type #light"
          "    Environment"
          "let n = ProcessorCount" ],
        [ "MidLight_OpenType.fs(3,11): error CLEF001: directive #light is forbidden in Zone A"
          "MidLight_OpenType.fs(4,5): error CLEF001: Environment allowance=0 actual=1" ],
        true

        "mid-line System #light \"on\" refused and preserves .Environment.Exit chain",
        "NativeTypedTree/MidLight_SysLightOn.fs",
        [ "module MidLightSysLightOn"
          "let exitSite () ="
          "    System #light \"on\""
          "        .Environment.Exit 1" ],
        [ "MidLight_SysLightOn.fs(3,12): error CLEF001: directive #light is forbidden in Zone A"
          "MidLight_SysLightOn.fs(4,10): error CLEF001: System.Environment allowance=0 actual=1" ],
        true

        "mid-line System #indent \"on\" refused and preserves .Environment.Exit chain",
        "NativeTypedTree/MidLight_SysIndentOn.fs",
        [ "module MidLightSysIndentOn"
          "let exitSite () ="
          "    System #indent \"on\""
          "        .Environment.Exit 1" ],
        [ "MidLight_SysIndentOn.fs(3,12): error CLEF001: directive #indent is forbidden in Zone A"
          "MidLight_SysIndentOn.fs(4,10): error CLEF001: System.Environment allowance=0 actual=1" ],
        true
    ]
    let lineDirBatch =
        batchManifest "line-directives.manifest.tsv"
            (lineDirectiveCases |> List.map (fun (_, rel, lines, _, _) -> rel, src lines))
    let lineDirExit, _, lineDirErr = run ["check"; lineDirBatch; emptyAllowance]
    assertCond (sprintf "negative-batch: all %d line-directive and mid-line #light/#indent fixtures fail check (exit 1)" lineDirectiveCases.Length) (lineDirExit = 1)
        (sprintf "expected exit 1, got %d" lineDirExit)
    for (label, _, _, wantTexts, _) in lineDirectiveCases do
        let missing = wantTexts |> List.filter (fun t -> not (lineDirErr.Contains(t, StringComparison.Ordinal)))
        assertCond (sprintf "negative: %s" label) missing.IsEmpty
            (sprintf "missing [%s] in stderr:\n%s" (String.concat "; " missing) (lineDirErr.Trim()))

    // Compile-validate all compiled mid-line #line / # <int> / #light / #indent probes with real fsc flags
    let compiledMidLineFiles =
        lineDirectiveCases
        |> List.choose (fun (_, rel, _, _, shouldCompile) -> if shouldCompile then Some (Path.Combine(workDir, rel)) else None)
    compileCheckFixtures
        (sprintf "positive: all %d mid-line directive negative fixtures compile cleanly with fsc project flags" compiledMidLineFiles.Length)
        compiledMidLineFiles []

    // ---- split-directive identifier chain & `open type` negatives -----------
    let splitChainCases : (string * string * string list * string list) list = [
        "Environment split across #endif before .Exit",
        "NativeTypedTree/Split_EnvEndif.fs",
        [ "(5,5): error CLEF001: Environment allowance=0 actual=1" ],
        [ "module S"; "open System"; "let f () ="; "#if COMPILED"; "    Environment"; "#endif"; "        .Exit 1" ]

        "Environment before #if (no #else) followed by .Exit after #endif",
        "NativeTypedTree/Split_EnvAroundIfNoElse.fs",
        [ "(4,5): error CLEF001: Environment allowance=0 actual=1" ],
        [ "module S"; "open System"; "let f () ="; "    Environment"; "#if CLEF_NEVER"; "    let _ = 0"; "#endif"; "        .Exit 1" ]

        "System split across #endif before .Environment.Exit",
        "NativeTypedTree/Split_SysEndif.fs",
        [ "(6,10): error CLEF001: System.Environment allowance=0 actual=1" ],
        [ "module S"; "let f () ="; "#if COMPILED"; "    System"; "#endif"; "        .Environment.Exit 1" ]

        "Environment in both #if and #else before #endif .Exit",
        "NativeTypedTree/Split_EnvBothBranches.fs",
        [ "(5,5): error CLEF001: Environment allowance=0 actual=1" ],
        [ "module S"; "open System"; "let f () ="; "#if CLEF_NEVER"; "    Environment"; "#else"; "    Environment"; "#endif"; "        .Exit 1" ]

        "Environment in #if branch and unrelated #else before #endif .Exit",
        "NativeTypedTree/Split_EnvFirstBranchOnly.fs",
        [ "(5,5): error CLEF001: Environment allowance=0 actual=1" ],
        [ "module S"; "open System"; "let f () ="; "#if COMPILED"; "    Environment"; "#else"; "    let _ = 0"; "#endif"; "        .Exit 1" ]

        "Environment before #if/#else followed by .Exit inside #else",
        "NativeTypedTree/Split_EnvIntoElse.fs",
        [ "(4,5): error CLEF001: Environment allowance=0 actual=1" ],
        [ "module S"; "open System"; "let f () ="; "    Environment"; "#if CLEF_NEVER"; "    let _ = 0"; "#else"; "        .Exit 1"; "#endif" ]

        "Environment split across # 1 \"x.fs\" refuses line directive and preserves .Exit chain",
        "NativeTypedTree/Split_EnvHashNum.fs",
        [ "(5,1): error CLEF001: #line / # <int> line directives are forbidden in Zone A"
          "(4,5): error CLEF001: Environment allowance=0 actual=1" ],
        [ "module S"; "open System"; "let f () ="; "    Environment"; "# 1 \"x.fs\""; "        .Exit 1" ]

        "Environment split across #line 1 \"x.fs\" refuses line directive and preserves .Exit chain",
        "NativeTypedTree/Split_EnvHashLine.fs",
        [ "(5,1): error CLEF001: #line / # <int> line directives are forbidden in Zone A"
          "(4,5): error CLEF001: Environment allowance=0 actual=1" ],
        [ "module S"; "open System"; "let f () ="; "    Environment"; "#line 1 \"x.fs\""; "        .Exit 1" ]

        "System split across # 1 \"x.fs\" refuses line directive and preserves .Environment.Exit chain",
        "NativeTypedTree/Split_SysHashNum.fs",
        [ "(4,1): error CLEF001: #line / # <int> line directives are forbidden in Zone A"
          "(5,10): error CLEF001: System.Environment allowance=0 actual=1" ],
        [ "module S"; "let f () ="; "    System"; "# 1 \"x.fs\""; "        .Environment.Exit 1" ]

        "open type split across # 1 \"x.fs\" refuses line directive and preserves Environment import",
        "NativeTypedTree/Split_OpenTypeHashNum.fs",
        [ "(4,1): error CLEF001: #line / # <int> line directives are forbidden in Zone A"
          "(5,5): error CLEF001: Environment allowance=0 actual=1" ],
        [ "module S"; "open System"; "open type"; "# 1 \"x.fs\""; "    Environment"; "let x = ProcessorCount" ]

        "open type inside #if COMPILED before #endif Environment",
        "NativeTypedTree/Split_OpenTypeEndif.fs",
        [ "(6,5): error CLEF001: Environment allowance=0 actual=1" ],
        [ "module S"; "open System"; "#if COMPILED"; "open type"; "#endif"; "    Environment"; "let x = ProcessorCount" ]

        "Environment split across #nowarn \"40\" before .Exit",
        "NativeTypedTree/Split_EnvNowarn.fs",
        [ "(4,5): error CLEF001: Environment allowance=0 actual=1" ],
        [ "module S"; "open System"; "let f () ="; "    Environment"; "#nowarn \"40\""; "        .Exit 1" ]

        "Environment split across #light \"on\" refuses directive and preserves .Exit chain",
        "NativeTypedTree/Split_EnvLightOn.fs",
        [ "(5,1): error CLEF001: directive #light is forbidden in Zone A"
          "(4,5): error CLEF001: Environment allowance=0 actual=1" ],
        [ "module S"; "open System"; "let f () ="; "    Environment"; "#light \"on\""; "        .Exit 1" ]
    ]
    let splitBatch =
        batchManifest "split-chains.manifest.tsv"
            (splitChainCases |> List.map (fun (_, rel, _, lines) -> rel, src lines))
    let splitExit, _, splitErr = run ["check"; splitBatch; emptyAllowance]
    assertCond (sprintf "negative-batch: all %d split-directive chain fixtures fail check (exit 1)" splitChainCases.Length) (splitExit = 1)
        (sprintf "expected exit 1, got %d" splitExit)
    for (label, rel, expectedFrags, _) in splitChainCases do
        let missing =
            expectedFrags
            |> List.filter (fun frag ->
                not (splitErr.Split('\n')
                     |> Array.exists (fun line -> line.Contains(rel, StringComparison.Ordinal) && line.Contains(frag, StringComparison.Ordinal))))
        assertCond (sprintf "negative: %s caught" label) missing.IsEmpty
            (sprintf "missing %s ... [%s] in stderr:\n%s" rel (String.concat "; " missing) (splitErr.Trim()))

    let splitDedup =
        fixture "NativeTypedTree/Split_EnvSameSiteDedup.fs" (src [
            "module S"
            "open System"
            "let f () ="
            "    Environment"
            "#if CLEF_NEVER"
            "#else"
            "#endif"
            "        .Exit 1" ])
    expectExactStderrLines "negative: Environment joined across empty #if/#else reports actual=1 (same site deduplicated)" 1
        [ "NativeTypedTree/Split_EnvSameSiteDedup.fs(4,5): error CLEF001: Environment allowance=0 actual=1" ]
        (run ["check"; splitDedup; emptyAllowance])

    let splitGlobalDedupRel = "NativeTypedTree/Split_SysGlobalDedup.fs"
    let splitGlobalDedup =
        fixture splitGlobalDedupRel (src [
            "module SplitSysGlobalDedup"
            "let exitSite () ="
            "#if CLEF_NEVER"
            "    global.System"
            "#else"
            "    System"
            "#endif"
            "        .Environment.Exit 1" ])
    expectExactStderrLines "negative: global.System vs System joined across #if/#else reports System.Environment actual=1 (seenSites deduplication)" 1
        [ "NativeTypedTree/Split_SysGlobalDedup.fs(8,10): error CLEF001: System.Environment allowance=0 actual=1" ]
        (run ["check"; splitGlobalDedup; emptyAllowance])
    compileCheckFixtures "positive: Split_SysGlobalDedup.fs compiles cleanly with fsc project flags"
        [Path.Combine(workDir, splitGlobalDedupRel)] []

    // ---- exhaustive %A, extended $$ strings, and escape-encoded negatives ---
    let fmtCases : (string * string * string * string list) list = [
        "bare %A", "NativeTypedTree/Fmt_Bare.fs", "(2,23): error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"%A\" x"]
        "flag %+A", "NativeTypedTree/Fmt_Plus.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"%+A\" x"]
        "width %-20A", "NativeTypedTree/Fmt_Width.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"%-20A\" x"]
        "zero-pad %0A", "NativeTypedTree/Fmt_Zero.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"%0A\" x"]
        "precision %.3A", "NativeTypedTree/Fmt_Prec.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"%.3A\" x"]
        "dynamic width %*A", "NativeTypedTree/Fmt_Star.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show w x = sprintf \"%*A\" w x"]
        "escaped+live %%%A", "NativeTypedTree/Fmt_TriplePct.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"%%%A\" x"]
        "escaped+live flag %%%+A", "NativeTypedTree/Fmt_TriplePctPlus.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"%%%+A\" x"]
        "interpolated $\"%A{x}\"", "NativeTypedTree/Fmt_Interp.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = $\"%A{x}\""]
        "interpolated verbatim $@\"%A{x}\"", "NativeTypedTree/Fmt_InterpVerb1.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = $@\"%A{x}\""]
        "interpolated verbatim @$\"%A{x}\"", "NativeTypedTree/Fmt_InterpVerb2.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = @$\"%A{x}\""]
        "interpolated triple $\"\"\"%A{x}\"\"\"", "NativeTypedTree/Fmt_InterpTriple.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = $\"\"\"%A{x}\"\"\""]
        "interpolated flags $\"%+A{x}\"", "NativeTypedTree/Fmt_InterpFlag.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = $\"%+A{x}\""]
        "INTERP_STRING_BEGIN_END + sprintf \"%A\"", "NativeTypedTree/Fmt_InterpThenSprintf.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = $\"value: \" + sprintf \"%A\" x"]
        "nested sprintf inside $\"\"\"{...}\"\"\"", "NativeTypedTree/Fmt_NestedInTripleInterp.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show v = $\"\"\"{sprintf \"%A\" v}\"\"\""]
        "nested interpolated inside triple interpolated", "NativeTypedTree/Fmt_NestedInterp.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show v = $\"\"\"outer {$\"inner %A{v}\"} tail\"\"\""]
        "multiline regular string %A", "NativeTypedTree/Fmt_MultilineRegular.fs", "(3,1): error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let s = \"line1"; "%A"; "line3\""]
        "multiline verbatim string %A", "NativeTypedTree/Fmt_MultilineVerbatim.fs", "(3,1): error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let s = @\"line1"; "%A"; "line3\""]
        "multiline triple string %A", "NativeTypedTree/Fmt_MultilineTriple.fs", "(3,1): error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let s = \"\"\"line1"; "%A"; "line3\"\"\""]
        "multiline interpolated string %A{x}", "NativeTypedTree/Fmt_MultilineInterp.fs", "(3,1): error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let s x = $\"line1"; "%A{x}"; "line3\""]
        "backslash line-continuation %\\n A", "NativeTypedTree/Fmt_LineCont.fs", "(2,20): error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let s x = sprintf \"%\\"; "  A\" x"]
        "backslash line-continuation with tab %\\n\\tA", "NativeTypedTree/Fmt_LineContTab.fs", "(2,13): error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let s x = $\"%\\"; "\tA{x}\""]
        // Extended $$, $$$, and 7-$ interpolated strings
        "extended $$ \"\"\"%%A{{x}}\"\"\"", "NativeTypedTree/Fmt_Ext2_Basic.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = $$\"\"\"%%A{{x}}\"\"\""]
        "extended $$ \"\"\"%%+A{{x}}\"\"\"", "NativeTypedTree/Fmt_Ext2_Plus.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = $$\"\"\"%%+A{{x}}\"\"\""]
        "extended $$ \"\"\"%%%A{{x}}\"\"\"", "NativeTypedTree/Fmt_Ext2_ThreePct.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = $$\"\"\"%%%A{{x}}\"\"\""]
        "extended $$$ \"\"\"%%%A{{{x}}}\"\"\"", "NativeTypedTree/Fmt_Ext3_Basic.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = $$$\"\"\"%%%A{{{x}}}\"\"\""]
        "extended $$$ \"\"\"%%%+A{{{x}}}\"\"\"", "NativeTypedTree/Fmt_Ext3_Plus.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = $$$\"\"\"%%%+A{{{x}}}\"\"\""]
        "extended $$$ \"\"\"%%%%A{{{x}}}\"\"\"", "NativeTypedTree/Fmt_Ext3_FourPct.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = $$$\"\"\"%%%%A{{{x}}}\"\"\""]
        "extended 7-$ multiline %%%%%%%A", "NativeTypedTree/Fmt_Ext7_Multi.fs", "(3,1): error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = $$$$$$$\"\"\"line1"; "%%%%%%%A{{{{{{{x}}}}}}}\"\"\""]
        "nested $ inside $$ preserves both $ counts", "NativeTypedTree/Fmt_Ext2_Nested1.fs", ": error CLEF001: %A allowance=0 actual=2",
            ["module F"; "let show v x = $$\"\"\"outer {{ $\"inner %A{v}\" }} %%A{{x}}\"\"\""]
        "nested $$ inside triple $ preserves both $ counts", "NativeTypedTree/Fmt_Ext1_Nested2.fs", ": error CLEF001: %A allowance=0 actual=2",
            ["module F"; "let show v x = $\"\"\"outer { $$\"\"\"inner %%A{{v}}\"\"\" } %A{x}\"\"\""]
        // Escape-encoded % and A in regular and regular-$ strings
        "escape \\u0025A", "NativeTypedTree/Fmt_Esc_u25.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"\\u0025A\" x"]
        "escape %\\u0041", "NativeTypedTree/Fmt_Esc_u41.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"%\\u0041\" x"]
        "escape \\x25A", "NativeTypedTree/Fmt_Esc_x25.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"\\x25A\" x"]
        "escape %\\x41", "NativeTypedTree/Fmt_Esc_x41.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"%\\x41\" x"]
        "escape \\037A (decimal trigraph)", "NativeTypedTree/Fmt_Esc_037.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"\\037A\" x"]
        "escape %\\065 (decimal trigraph)", "NativeTypedTree/Fmt_Esc_065.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"%\\065\" x"]
        "escape \\U00000025A", "NativeTypedTree/Fmt_Esc_U25.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"\\U00000025A\" x"]
        "escape %\\U00000041", "NativeTypedTree/Fmt_Esc_U41.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"%\\U00000041\" x"]
        "escape \\u0025\\u002b\\u0041 (%+A)", "NativeTypedTree/Fmt_Esc_u25plusA.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = sprintf \"\\u0025\\u002b\\u0041\" x"]
        "interp escape $\"\\u0025A{x}\"", "NativeTypedTree/Fmt_Esc_Interp25.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = $\"\\u0025A{x}\""]
        "interp escape $\"%\\u0041{x}\"", "NativeTypedTree/Fmt_Esc_Interp41.fs", ": error CLEF001: %A allowance=0 actual=1",
            ["module F"; "let show x = $\"%\\u0041{x}\""]
    ]

    let fmtBatch =
        batchManifest "format-a.manifest.tsv"
            (fmtCases |> List.map (fun (_, rel, _, lines) -> rel, src lines))
    let fmtExit, _, fmtErr = run ["check"; fmtBatch; emptyAllowance]
    assertCond (sprintf "negative-batch: all %d %%A / extended-$$ / escape fixtures fail check (exit 1)" fmtCases.Length) (fmtExit = 1)
        (sprintf "expected exit 1, got %d" fmtExit)
    for (label, rel, expectedFrag, _) in fmtCases do
        let matched =
            fmtErr.Split('\n')
            |> Array.exists (fun line -> line.Contains(rel, StringComparison.Ordinal) && line.Contains(expectedFrag, StringComparison.Ordinal))
        assertCond (sprintf "negative: %s caught" label) matched
            (sprintf "missing %s ... %s in stderr:\n%s" rel expectedFrag (fmtErr.Trim()))

    // ---- non-ASCII & out-of-range (>255) decimal trigraph negatives ---------
    let trigraphCases : (string * string * string list * string list) list = [
        "non-ASCII trigraph %\\u07c07\\u0beb refused and counted as %A",
        "NativeTypedTree/Fmt_Tri_UniA.fs",
        [ "module FmtTriUniA"
          "let show x = sprintf \"%\\\u07c07\u0beb\" x" ],
        [ "Fmt_Tri_UniA.fs(2,24): error CLEF001: non-ASCII or out-of-range decimal trigraph escape in string literal is forbidden in Zone A"
          "Fmt_Tri_UniA.fs(2,23): error CLEF001: %A allowance=0 actual=1" ]

        "non-ASCII trigraph \\u07c04\\u0bedA refused and counted as %A",
        "NativeTypedTree/Fmt_Tri_UniPct.fs",
        [ "module FmtTriUniPct"
          "let show x = sprintf \"\\\u07c04\u0bedA\" x" ],
        [ "Fmt_Tri_UniPct.fs(2,23): error CLEF001: non-ASCII or out-of-range decimal trigraph escape in string literal is forbidden in Zone A"
          "Fmt_Tri_UniPct.fs(2,23): error CLEF001: %A allowance=0 actual=1" ]

        "out-of-range trigraph \\293A (under #nowarn 1252) refused and counted as %A",
        "NativeTypedTree/Fmt_Tri_Gt255Pct.fs",
        [ "module FmtTriGt255Pct"
          "#nowarn \"1252\""
          "let show x = sprintf \"\\293A\" x" ],
        [ "Fmt_Tri_Gt255Pct.fs(3,23): error CLEF001: non-ASCII or out-of-range decimal trigraph escape in string literal is forbidden in Zone A"
          "Fmt_Tri_Gt255Pct.fs(3,23): error CLEF001: %A allowance=0 actual=1" ]

        "out-of-range trigraph %\\321 (under #nowarn 1252) refused and counted as %A",
        "NativeTypedTree/Fmt_Tri_Gt255A.fs",
        [ "module FmtTriGt255A"
          "#nowarn \"1252\""
          "let show x = sprintf \"%\\321\" x" ],
        [ "Fmt_Tri_Gt255A.fs(3,24): error CLEF001: non-ASCII or out-of-range decimal trigraph escape in string literal is forbidden in Zone A"
          "Fmt_Tri_Gt255A.fs(3,23): error CLEF001: %A allowance=0 actual=1" ]

        "interpolated non-ASCII trigraph $\"%\\u07c07\\u0beb{x}\" refused and counted as %A",
        "NativeTypedTree/Fmt_Tri_InterpUniA.fs",
        [ "module FmtTriInterpUniA"
          "let show x = $\"%\\\u07c07\u0beb{x}\"" ],
        [ "Fmt_Tri_InterpUniA.fs(2,17): error CLEF001: non-ASCII or out-of-range decimal trigraph escape in string literal is forbidden in Zone A"
          "Fmt_Tri_InterpUniA.fs(2,16): error CLEF001: %A allowance=0 actual=1" ]

        "interpolated out-of-range trigraph $\"\\293A{x}\" (under #nowarn 1252) refused and counted as %A",
        "NativeTypedTree/Fmt_Tri_InterpGt255.fs",
        [ "module FmtTriInterpGt255"
          "#nowarn \"1252\""
          "let show x = $\"\\293A{x}\"" ],
        [ "Fmt_Tri_InterpGt255.fs(3,16): error CLEF001: non-ASCII or out-of-range decimal trigraph escape in string literal is forbidden in Zone A"
          "Fmt_Tri_InterpGt255.fs(3,16): error CLEF001: %A allowance=0 actual=1" ]
    ]
    let trigraphBatch =
        batchManifest "trigraphs.manifest.tsv"
            (trigraphCases |> List.map (fun (_, rel, lines, _) -> rel, src lines))
    let triExit, _, triErr = run ["check"; trigraphBatch; emptyAllowance]
    assertCond (sprintf "negative-batch: all %d non-ASCII / >255 decimal trigraph fixtures fail check (exit 1)" trigraphCases.Length) (triExit = 1)
        (sprintf "expected exit 1, got %d" triExit)
    for (label, _, _, wantTexts) in trigraphCases do
        let missing = wantTexts |> List.filter (fun t -> not (triErr.Contains(t, StringComparison.Ordinal)))
        assertCond (sprintf "negative: %s" label) missing.IsEmpty
            (sprintf "missing [%s] in stderr:\n%s" (String.concat "; " missing) (triErr.Trim()))
    compileCheckFixtures
        (sprintf "positive: all %d non-ASCII / >255 trigraph fixtures compile cleanly with fsc project flags" trigraphCases.Length)
        (trigraphCases |> List.map (fun (_, rel, _, _) -> Path.Combine(workDir, rel))) []

    // ---- exact-boundary nesting controls (zero spurious depth errors) -------
    let depthComment15 =
        fixture "PSGSaturation/Depth_Comment15.fs" (src [
            "module DepthComment15"
            String.replicate 15 "(*"
            String.replicate 15 "*)" + " let cache = ConditionalWeakTable<int, int>()" ])
    expectExactStderrLines "negative: 15-deep block comment catches ConditionalWeakTable with zero spurious depth errors" 1
        [ "PSGSaturation/Depth_Comment15.fs(3,44): error CLEF001: ConditionalWeakTable allowance=0 actual=1" ]
        (run ["check"; depthComment15; emptyAllowance])

    let depthBrace7Multi =
        fixture "PSGSaturation/Depth_Brace7.fs" (src [
            "module DepthBrace7"
            "let s = $\"\"\"v{ Seq.length (seq { " + String.replicate 6 "yield! seq { " + "yield 1"
            "  }; yield (ConditionalWeakTable<obj, obj>()).GetHashCode() " + String.replicate 6 "} " + ") }\"\"\"" ])
    expectExactStderrLines "negative: 7-brace multiline hole catches ConditionalWeakTable with zero spurious depth errors" 1
        [ "PSGSaturation/Depth_Brace7.fs(3,13): error CLEF001: ConditionalWeakTable allowance=0 actual=1" ]
        (run ["check"; depthBrace7Multi; emptyAllowance])

    let depthBrace7Single =
        fixture "PSGSaturation/Depth_Brace7Single.fs" (src [
            "module DepthBrace7Single"
            "let s = $\"\"\"v{ Seq.length (seq { " + String.replicate 6 "yield! seq { " + "yield 1 }; yield (ConditionalWeakTable<obj, obj>()).GetHashCode() " + String.replicate 6 "} " + ") }\"\"\"" ])
    expectExactStderrLines "negative: 7-brace single-line hole catches ConditionalWeakTable with zero spurious depth errors" 1
        [ "PSGSaturation/Depth_Brace7Single.fs(2,130): error CLEF001: ConditionalWeakTable allowance=0 actual=1" ]
        (run ["check"; depthBrace7Single; emptyAllowance])

    let depthDollar7Multi =
        fixture "PSGSaturation/Depth_Dollar7Multi.fs" (src [
            "module DepthDollar7Multi"
            "let s = $$$$$$$\"\"\"line1"
            "{{{{{{ \"\"\""
            "let cache = System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()" ])
    expectExactStderrLines "negative: 7-$ multiline extended interpolated string stays in sync and catches ConditionalWeakTable with zero spurious delimiter errors" 1
        [ "PSGSaturation/Depth_Dollar7Multi.fs(4,45): error CLEF001: ConditionalWeakTable allowance=0 actual=1" ]
        (run ["check"; depthDollar7Multi; emptyAllowance])

    // ---- preprocessor branch, #if-in-hole, nesting limit, and EOF negatives -
    let hiddenManifest =
        fixture "PSGSaturation/SemanticGraph/HiddenFixture.fs" (src [
            "module HiddenFixture"
            "#if NULLABLE"
            "let cache = ConditionalWeakTable<int, int>()"
            "#endif"])
    expect "negative: ConditionalWeakTable hidden behind #if NULLABLE is caught at (3,13)" 1
        "HiddenFixture.fs(3,13): error CLEF001: ConditionalWeakTable allowance=0 actual=1"
        (run ["check"; hiddenManifest; emptyAllowance])

    let leakCases : (string * string * string list * string list) list = [
        // Preprocessor directives inside interpolation holes
        "#if COMPILED inside $\"\"\"{ ... }\"\"\" hole hiding in-hole ConditionalWeakTable",
        "PSGSaturation/HoleIf_InHole.fs",
        [ "module HoleIfInHole"
          "let cacheHash () ="
          "    $\"\"\"cache {"
          "#if COMPILED"
          "                (ConditionalWeakTable<obj, obj>()).GetHashCode()"
          "#else"
          "                0"
          "#endif"
          "              }\"\"\"" ],
        [ "HoleIf_InHole.fs(4,1): error CLEF001: preprocessor directive #if is forbidden inside an interpolated string hole"
          "HoleIf_InHole.fs(5,18): error CLEF001: ConditionalWeakTable allowance=0 actual=1" ]

        "#if COMPILED inside $\"\"\"{ ... }\"\"\" hole hiding top-level ConditionalWeakTable, %A, and failwith",
        "PSGSaturation/HoleIf_TopLevel.fs",
        [ "module HoleIfTopLevel"
          "let opener = $\"\"\"{"
          "#if COMPILED"
          "                    \"x\"}\"\"\""
          "let cache = System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()"
          "let shown = sprintf \"%A\" [1; 2]"
          "let failSite () = failwith \"error\""
          "let closer = $\"\"\"{"
          "#else"
          "                    \"y\"}\"\"\""
          "let closer2 = $\"\"\"{"
          "#endif"
          "                    \"z\"}\"\"\"" ],
        [ "HoleIf_TopLevel.fs(3,1): error CLEF001: preprocessor directive #if is forbidden inside an interpolated string hole"
          "HoleIf_TopLevel.fs(5,45): error CLEF001: ConditionalWeakTable allowance=0 actual=1"
          "HoleIf_TopLevel.fs(6,22): error CLEF001: %A allowance=0 actual=1"
          "HoleIf_TopLevel.fs(7,19): error CLEF001: failwith allowance=0 actual=1" ]

        "#if COMPILED inside $@\"{ ... }\" verbatim interpolated hole",
        "PSGSaturation/HoleIf_Verbatim.fs",
        [ "module HoleIfVerbatim"
          "let s = $@\"{"
          "#if COMPILED"
          "            failwith \"hidden\""
          "#else"
          "            \"ok\""
          "#endif"
          "          }\"" ],
        [ "HoleIf_Verbatim.fs(3,1): error CLEF001: preprocessor directive #if is forbidden inside an interpolated string hole"
          "HoleIf_Verbatim.fs(4,13): error CLEF001: failwith allowance=0 actual=1" ]

        "#if !COMPILED ... #else <banned> #endif inside $\"\"\"{ ... }\"\"\" hole",
        "PSGSaturation/HoleIf_NegatedElse.fs",
        [ "module HoleIfNegatedElse"
          "let s = $\"\"\"{"
          "#if !COMPILED"
          "            \"ok\""
          "#else"
          "            sprintf \"%A\" 1"
          "#endif"
          "          }\"\"\"" ],
        [ "HoleIf_NegatedElse.fs(3,1): error CLEF001: preprocessor directive #if is forbidden inside an interpolated string hole"
          "HoleIf_NegatedElse.fs(6,22): error CLEF001: %A allowance=0 actual=1" ]

        // Per-token & cross-line tokenizer nesting limits
        "16-deep block comment across lines refused",
        "PSGSaturation/Depth_Comment16.fs",
        [ "module DepthComment16"
          String.replicate 16 "(*"
          "*) // " + String.replicate 15 "*)" + " let cache = ConditionalWeakTable<int, int>()" ],
        [ "Depth_Comment16.fs(2,1): error CLEF001: block comment nesting depth 16 exceeds tokenizer limit (15)" ]

        "16-deep block comment on a single line refused",
        "PSGSaturation/Depth_Comment16Single.fs",
        [ "module DepthComment16Single"
          String.replicate 16 "(*" + "*) // " + String.replicate 15 "*)" + " let cache = ConditionalWeakTable<int, int>()" ],
        [ "Depth_Comment16Single.fs(2,1): error CLEF001: block comment nesting depth 16 exceeds tokenizer limit (15)" ]

        "8-brace multiline interpolation hole refused",
        "PSGSaturation/Depth_Brace8.fs",
        [ "module DepthBrace8"
          "let s = $\"\"\"v{ Seq.length (seq { " + String.replicate 7 "yield! seq { " + "yield 1"
          "  }; yield (ConditionalWeakTable<obj, obj>()).GetHashCode() " + String.replicate 7 "} " + ") }\"\"\"" ],
        [ "Depth_Brace8.fs(2,1): error CLEF001: interpolation hole brace nesting depth 8 exceeds tokenizer limit (7)" ]

        "8-brace single-line interpolation hole refused before tokenizer wraps mid-line",
        "PSGSaturation/Depth_Brace8Single.fs",
        [ "module DepthBrace8Single"
          "let s = $\"\"\"v{ Seq.length (seq { " + String.replicate 7 "yield! seq { " + "yield 1 }; yield (ConditionalWeakTable<obj, obj>()).GetHashCode() " + String.replicate 7 "} " + ") }\"\"\"" ],
        [ "Depth_Brace8Single.fs(2,1): error CLEF001: interpolation hole brace nesting depth 8 exceeds tokenizer limit (7)" ]

        "3-deep multiline nested interpolated string refused",
        "PSGSaturation/Depth_NestedInterp3.fs",
        [ "module DepthNestedInterp3"
          "let s = $\"\"\"{ $\"\"\"{ $\"{"
          "  1"
          "}\" }\"\"\" }\"\"\"" ],
        [ "Depth_NestedInterp3.fs(2,1): error CLEF001: nested interpolated string depth 3 exceeds tokenizer limit (2)" ]

        "3-deep single-line nested interpolated string refused",
        "PSGSaturation/Depth_NestedInterp3Single.fs",
        [ "module DepthNestedInterp3Single"
          "let s = $\"\"\"{ $\"\"\"{ $\"{ 1 }\" }\"\"\" }\"\"\"" ],
        [ "Depth_NestedInterp3Single.fs(2,1): error CLEF001: nested interpolated string depth 3 exceeds tokenizer limit (2)" ]

        "8-$ multiline extended interpolated string refused before tokenizer loses delimiter length",
        "PSGSaturation/Depth_Dollar8Multi.fs",
        [ "module DepthDollar8Multi"
          "let s = $$$$$$$$\"\"\"line1"
          "{{{{{{{ \"\"\""
          "let cache = System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()" ],
        [ "Depth_Dollar8Multi.fs(2,1): error CLEF001: extended interpolated string delimiter length 8 exceeds tokenizer limit (7)" ]

        "8-$ single-line extended interpolated string refused",
        "PSGSaturation/Depth_Dollar8Single.fs",
        [ "module DepthDollar8Single"
          "let s = $$$$$$$$\"\"\"hello\"\"\"" ],
        [ "Depth_Dollar8Single.fs(2,1): error CLEF001: extended interpolated string delimiter length 8 exceeds tokenizer limit (7)" ]

        "8-$ single-line extended interpolated string with hole refused and catches %A",
        "PSGSaturation/Depth_Dollar8SingleHole.fs",
        [ "module DepthDollar8SingleHole"
          "let s x = $$$$$$$$\"\"\"%%%%%%%%A{{{{{{{{x}}}}}}}}\"\"\"" ],
        [ "Depth_Dollar8SingleHole.fs(2,1): error CLEF001: extended interpolated string delimiter length 8 exceeds tokenizer limit (7)"
          "Depth_Dollar8SingleHole.fs(2,22): error CLEF001: %A allowance=0 actual=1" ]

        // Live #elif directive coverage
        "banned ConditionalWeakTable inside live #elif branch caught",
        "PSGSaturation/Elif_LiveBranch.fs",
        [ "module ElifLiveBranch"
          "#if CLEF_NEVER"
          "let a = 1"
          "#elif COMPILED"
          "let cache = System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()"
          "#else"
          "let a = 2"
          "#endif" ],
        [ "Elif_LiveBranch.fs(5,45): error CLEF001: ConditionalWeakTable allowance=0 actual=1" ]

        "unclosed comment (* before #elif hiding active #elif branch",
        "PSGSaturation/Leak_Elif.fs",
        [ "module LeakElif"
          "#if CLEF_NEVER"
          "(*"
          "#elif COMPILED"
          "let cache = System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()"
          "#endif" ],
        [ "Leak_Elif.fs(4,1): error CLEF001: conditional branch ends in unclosed Comment state before #elif"
          "Leak_Elif.fs(5,45): error CLEF001: ConditionalWeakTable allowance=0 actual=1" ]

        "unmatched #elif directive",
        "PSGSaturation/Leak_UnmatchedElif.fs",
        [ "module LeakUnmatchedElif"
          "#elif COMPILED" ],
        [ "Leak_UnmatchedElif.fs(2,1): error CLEF001: unmatched #elif directive" ]

        // Unconditional EOF lexical state refusals (no #if open)
        "EOF inside unclosed block comment refused",
        "PSGSaturation/Eof_Comment.fs",
        [ "module EofComment"
          "(* unclosed comment" ],
        [ "Eof_Comment.fs(2,1): error CLEF001: file ends in unclosed Comment state" ]

        "EOF inside unclosed string literal refused",
        "PSGSaturation/Eof_String.fs",
        [ "module EofString"
          "let s = \"unclosed" ],
        [ "Eof_String.fs(2,1): error CLEF001: file ends in unclosed String state" ]

        "EOF inside unclosed interpolation hole refused",
        "PSGSaturation/Eof_InterpHole.fs",
        [ "module EofInterpHole"
          "let s = $\"abc {1" ],
        [ "Eof_InterpHole.fs(2,1): error CLEF001: file ends in unclosed InterpolatedString state" ]

        // Lexer-state leak negatives across #if/#else/#endif
        "unclosed block comment (* inside #if CLEF_NEVER",
        "PSGSaturation/Leak_Comment.fs",
        [ "module LeakComment"
          "#if CLEF_NEVER"
          "(*"
          "#endif"
          "let cache = System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()"
          "#if CLEF_NEVER"
          "*)"
          "#endif" ],
        [ "Leak_Comment.fs(4,1): error CLEF001: conditional branch ends in unclosed Comment state before #endif"
          "Leak_Comment.fs(5,45): error CLEF001: ConditionalWeakTable allowance=0 actual=1" ]

        "unclosed regular quote \" inside #if CLEF_NEVER",
        "PSGSaturation/Leak_Quote.fs",
        [ "module LeakQuote"
          "#if CLEF_NEVER"
          "let s = \""
          "#endif"
          "let cache = System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()"
          "#if CLEF_NEVER"
          "\""
          "#endif" ],
        [ "Leak_Quote.fs(4,1): error CLEF001: conditional branch ends in unclosed String state before #endif"
          "Leak_Quote.fs(5,45): error CLEF001: ConditionalWeakTable allowance=0 actual=1" ]

        "unclosed triple quote \"\"\" inside #if CLEF_NEVER",
        "PSGSaturation/Leak_Triple.fs",
        [ "module LeakTriple"
          "#if CLEF_NEVER"
          "let s = \"\"\""
          "#endif"
          "let cache = System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()"
          "#if CLEF_NEVER"
          "\"\"\""
          "#endif" ],
        [ "Leak_Triple.fs(4,1): error CLEF001: conditional branch ends in unclosed TripleQuoteString state before #endif"
          "Leak_Triple.fs(5,45): error CLEF001: ConditionalWeakTable allowance=0 actual=1" ]

        "unclosed interpolated hole $\"abc {1 inside #if CLEF_NEVER",
        "PSGSaturation/Leak_InterpHole.fs",
        [ "module LeakInterpHole"
          "#if CLEF_NEVER"
          "let s = $\"abc {1"
          "#endif"
          "type R = { A: int }"
          "let r = { A = 1 }"
          "let cache = System.Runtime.CompilerServices.ConditionalWeakTable<obj, obj>()" ],
        [ "Leak_InterpHole.fs(4,1): error CLEF001: conditional branch ends in unclosed InterpolatedString state before #endif"
          "Leak_InterpHole.fs(7,45): error CLEF001: ConditionalWeakTable allowance=0 actual=1" ]

        "unclosed comment (* before #else hiding active #else branch",
        "PSGSaturation/Leak_Else.fs",
        [ "module LeakElse"
          "#if CLEF_NEVER"
          "(*"
          "#else"
          "let cache = ConditionalWeakTable<int, int>()"
          "#endif" ],
        [ "Leak_Else.fs(4,1): error CLEF001: conditional branch ends in unclosed Comment state before #else"
          "Leak_Else.fs(5,13): error CLEF001: ConditionalWeakTable allowance=0 actual=1" ]

        "unclosed #if at end of file",
        "PSGSaturation/Leak_UnclosedIf.fs",
        [ "module LeakUnclosedIf"
          "#if CLEF_NEVER"
          "let x = 1" ],
        [ "Leak_UnclosedIf.fs(3,1): error CLEF001: unclosed #if directive at end of file" ]

        "unmatched #else directive",
        "PSGSaturation/Leak_UnmatchedElse.fs",
        [ "module LeakUnmatchedElse"
          "#else" ],
        [ "Leak_UnmatchedElse.fs(2,1): error CLEF001: unmatched #else directive" ]

        "unmatched #endif directive",
        "PSGSaturation/Leak_UnmatchedEndif.fs",
        [ "module LeakUnmatchedEndif"
          "#endif" ],
        [ "Leak_UnmatchedEndif.fs(2,1): error CLEF001: unmatched #endif directive" ]
    ]

    for (label, rel, lines, wantTexts) in leakCases do
        let m = fixture rel (src lines)
        expectAll (sprintf "negative: %s" label) 1 wantTexts (run ["check"; m; emptyAllowance])

    let censusStructuralErr =
        fixture "PSGSaturation/Census_EofComment.fs" (src [
            "module CensusEofComment"
            "(* unclosed comment" ])
    expect "negative: census mode fails (exit 1) when structural errors are present" 1
        "Census_EofComment.fs(2,1): error CLEF001: file ends in unclosed Comment state"
        (run ["census"; censusStructuralErr])

    // ---- stale-table, nonzero-limit overflow, dead-row, malformed TSV, and ratchet negatives
    let staleManifest =
        fixture "Baker/Recipes/StaleFixture.fs" (src [
            "module StaleFixture"
            "let cache = ConditionalWeakTable<int, int>()"])
    let staleAllowance = Path.Combine(workDir, "stale.allowances.tsv")
    rowsFile staleAllowance ["Baker/Recipes/StaleFixture.fs\tConditionalWeakTable\t3"]
    expect "negative: stale slack (actual 1 < allowance 3) fails with 'lower to 1'" 1 "lower to 1"
        (run ["check"; staleManifest; staleAllowance])

    let overflowManifest =
        fixture "Baker/Recipes/OverflowFixture.fs" (src [
            "module OverflowFixture"
            "let a = ConditionalWeakTable<int, int>()"
            "let b = ConditionalWeakTable<int, int>()"
            "let c = ConditionalWeakTable<int, int>()"])
    let nonzeroAllowance = Path.Combine(workDir, "nonzero.allowances.tsv")
    rowsFile nonzeroAllowance ["Baker/Recipes/OverflowFixture.fs\tConditionalWeakTable\t2"]
    expect "negative: actual > limit > 0 reports the first excess site at (4,9)" 1
        "OverflowFixture.fs(4,9): error CLEF001: ConditionalWeakTable allowance=2 actual=3"
        (run ["check"; overflowManifest; nonzeroAllowance])

    let deadAllowance = Path.Combine(workDir, "dead.allowances.tsv")
    rowsFile deadAllowance ["Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t2"]
    expect "negative: a row for a file with 0 actual sites fails with 'remove row'" 1 "remove row"
        (run ["check"; cleanManifest; deadAllowance])

    let malformedAllowance = Path.Combine(workDir, "malformed.allowances.tsv")
    rowsFile malformedAllowance ["Baker/Recipes/CleanFixture.fs\tUnknownRule\t1"]
    expect "negative: unknown rule allowance row exits 2" 2 "Malformed allowance"
        (run ["check"; cleanManifest; malformedAllowance])

    let nonZoneAllowance = Path.Combine(workDir, "nonzone.allowances.tsv")
    rowsFile nonZoneAllowance ["Host/Outside.fs\tConditionalWeakTable\t1"]
    expect "negative: non-Zone-A path in allowances TSV exits 2" 2 "Malformed allowance"
        (run ["check"; cleanManifest; nonZoneAllowance])

    let blankLineAllowance = Path.Combine(workDir, "blankline.allowances.tsv")
    File.WriteAllText(blankLineAllowance, "Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t1\n\n")
    expect "negative: blank line in allowances TSV is refused as malformed (exit 2)" 2 "Malformed allowance"
        (run ["check"; cleanManifest; blankLineAllowance])

    let leadingZeroAllowance = Path.Combine(workDir, "leadingzero.allowances.tsv")
    rowsFile leadingZeroAllowance ["Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t01"]
    expect "negative: leading-zero '01' count in allowances TSV exits 2" 2 "Malformed allowance"
        (run ["check"; cleanManifest; leadingZeroAllowance])

    let plusCountAllowance = Path.Combine(workDir, "pluscount.allowances.tsv")
    rowsFile plusCountAllowance ["Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t+1"]
    expect "negative: signed '+1' count in allowances TSV exits 2" 2 "was not in a correct format"
        (run ["check"; cleanManifest; plusCountAllowance])

    let spaceCountAllowance = Path.Combine(workDir, "spacecount.allowances.tsv")
    rowsFile spaceCountAllowance ["Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t 1 "]
    expect "negative: whitespace-padded count in allowances TSV exits 2" 2 "was not in a correct format"
        (run ["check"; cleanManifest; spaceCountAllowance])

    let zeroCountAllowance = Path.Combine(workDir, "zerocount.allowances.tsv")
    rowsFile zeroCountAllowance ["Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t0"]
    expect "negative: zero count in allowances TSV exits 2" 2 "Invalid or duplicate allowance"
        (run ["check"; cleanManifest; zeroCountAllowance])

    let dupRowAllowance = Path.Combine(workDir, "duprow.allowances.tsv")
    rowsFile dupRowAllowance [
        "Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t1"
        "Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t1"
    ]
    expect "negative: duplicate row in allowances TSV exits 2" 2 "Invalid or duplicate allowance"
        (run ["check"; cleanManifest; dupRowAllowance])

    let raisedBase = Path.Combine(workDir, "raised-base.allowances.tsv")
    let raisedProp = Path.Combine(workDir, "raised-proposed.allowances.tsv")
    rowsFile raisedBase ["Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t1"]
    rowsFile raisedProp ["Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t2"]
    expect "negative: ratchet refuses a raised count" 1
        "allowance expansion for ConditionalWeakTable (accepted 1, proposed 2)"
        (run ["ratchet"; raisedBase; raisedProp])

    let newKeyProp = Path.Combine(workDir, "newkey-proposed.allowances.tsv")
    rowsFile newKeyProp ["Baker/Recipes/NewFile.fs\tConditionalWeakTable\t1"]
    expect "negative: ratchet refuses a new file key with exact reason" 1
        "Baker/Recipes/NewFile.fs: error CLEF001: allowance expansion for ConditionalWeakTable (accepted 0, proposed 1)."
        (run ["ratchet"; raisedBase; newKeyProp])

    let multiBase = Path.Combine(workDir, "multi-base.allowances.tsv")
    let multiProp = Path.Combine(workDir, "multi-prop.allowances.tsv")
    rowsFile multiBase [
        "Baker/Recipes/A.fs\tConditionalWeakTable\t1"
        "Baker/Recipes/B.fs\tFSharpValue\t2"
    ]
    rowsFile multiProp [
        "Baker/Recipes/A.fs\tConditionalWeakTable\t3"
        "Baker/Recipes/B.fs\tFSharpValue\t5"
        "Baker/Recipes/C.fs\t%A\t1"
    ]
    expectAll "negative: ratchet reports ALL mismatches without short-circuiting" 1
        [ "Baker/Recipes/A.fs: error CLEF001: allowance expansion for ConditionalWeakTable (accepted 1, proposed 3)."
          "Baker/Recipes/B.fs: error CLEF001: allowance expansion for FSharpValue (accepted 2, proposed 5)."
          "Baker/Recipes/C.fs: error CLEF001: allowance expansion for %A (accepted 0, proposed 1)." ]
        (run ["ratchet"; multiBase; multiProp])

    let admitBadProp = Path.Combine(workDir, "admit-bad-proposed.allowances.tsv")
    rowsFile admitBadProp [
        "Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t4"
        "NativeTypedTree/NewRule.fs\t%A\t5"
    ]
    expectAll "negative: ratchet --admit-new-rules refuses BOTH existing-rule raise and new-rule census expansion" 1
        [ "Baker/Recipes/CleanFixture.fs: error CLEF001: allowance expansion for ConditionalWeakTable (accepted 3, proposed 4)."
          "NativeTypedTree/NewRule.fs: error CLEF001: allowance expansion for new rule %A (base-census 4, proposed 5)." ]
        (run ["ratchet"; baseRows; admitBadProp; "--admit-new-rules"; admitCensus])

    let admitTrackedNewFileProp = Path.Combine(workDir, "admit-tracked-newfile-proposed.allowances.tsv")
    let admitTrackedNewFileCensus = Path.Combine(workDir, "admit-tracked-newfile-census.allowances.tsv")
    rowsFile admitTrackedNewFileProp [
        "Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t3"
        "Baker/Recipes/NewTrackedFile.fs\tConditionalWeakTable\t1"
    ]
    rowsFile admitTrackedNewFileCensus [
        "Baker/Recipes/CleanFixture.fs\tConditionalWeakTable\t3"
        "Baker/Recipes/NewTrackedFile.fs\tConditionalWeakTable\t1"
    ]
    expect "negative: ratchet --admit-new-rules refuses an already-tracked rule added in a new file" 1
        "Baker/Recipes/NewTrackedFile.fs: error CLEF001: allowance expansion for ConditionalWeakTable (accepted 0, proposed 1)."
        (run ["ratchet"; baseRows; admitTrackedNewFileProp; "--admit-new-rules"; admitTrackedNewFileCensus])

    // ---- real tree (missing manifest MUST fail, never silently SKIP) --------
    let candidateManifests =
        if fsi.CommandLineArgs.Length > 1 then
            [fsi.CommandLineArgs[1]]
        else
            [ "artifacts/obj/Clef.Compiler.Service/Debug/net10.0/ClefCore.compile.tsv"
              "src/Compiler/obj/Debug/net10.0/ClefCore.compile.tsv" ]
            |> List.map (fun p -> Path.Combine(repoRoot, p))
    let realManifest = candidateManifests |> List.tryFind File.Exists
    match realManifest with
    | Some m ->
        expect "positive: the checked-in Zone A tree matches build/ClefCore.allowances.tsv exactly" 0 ""
            (run ["check"; m; allowances])
        let censusExit, censusOut, censusErr = run ["census"; m]
        let rows = censusOut.Split('\n') |> Array.filter (fun l -> l.Trim().Length > 0)
        assertCond "positive: real-tree census succeeds and captures all 4 NativeTypes.fs %A sites"
            (censusExit = 0 && rows |> Array.contains "NativeTypedTree/NativeTypes.fs\t%A\t4")
            (sprintf "census exit=%d, err=%s" censusExit (censusErr.Trim()))
        printfn "INFO  real-tree census rows: %d (manifest %s)" rows.Length m
    | None ->
        failures <- failures + 1
        printfn "FAIL  real-tree check: no evaluated compiled-inputs manifest was found (pass path or build Clef.Compiler.Service.fsproj first)"

try
    runControls ()
finally
    if Directory.Exists workDir then
        try Directory.Delete(workDir, true) with _ -> ()

printfn "controls: %d passed, %d failure(s)" passes failures
exit (if failures = 0 then 0 else 1)
