#!/usr/bin/env fsi
// clef #165 Increment B - closure and ratchet verification for the Clef-owned
// analyzer run (Farscape ADL ANALYZER-POLICY, AUDITED-CLOSURE).
open System
open System.Collections.Generic
open System.IO
open System.Security.Cryptography
open System.Text
open System.Text.Json

let zoneRoots = [ "NativeTypedTree/"; "PSGSaturation/"; "Baker/"; "Nanopass/" ]

let boundaryCodes =
  [ "AXC001"; "AXC002"; "AXC003"; "AXC004"; "AXC005"; "AXC006"; "AXC007"; "AXC008";
    "AXC009"; "AXC010"; "AXC011"; "CLF001"; "CLF002"; "CLF003"; "CLF004" ]

let boundaryCodeSet = Set.ofList boundaryCodes

let fail (reason: string) =
  printfn "RECEIPT FAIL: %s" reason
  exit 1

let ok (what: string) = printfn "RECEIPT OK: %s" what

let sha256OfText (text: string) =
  use sha = SHA256.Create()
  let bytes = Encoding.UTF8.GetBytes text
  Convert.ToHexString(sha.ComputeHash bytes).ToLowerInvariant()

let fileHashCache = Dictionary<string, string>(StringComparer.Ordinal)

let sha256OfFile (path: string) =
  match fileHashCache.TryGetValue(path) with
  | true, cached -> cached
  | false, _ ->
    use stream = File.OpenRead path
    use sha = SHA256.Create()
    let digest = Convert.ToHexString(sha.ComputeHash stream).ToLowerInvariant()
    fileHashCache.[path] <- digest
    digest

let normalizePath (path: string) = path.Replace("\\", "/")

let canonicalPath (path: string) =
  if String.IsNullOrWhiteSpace path then ""
  else
    let cleaned =
      if path.StartsWith("file://", StringComparison.OrdinalIgnoreCase) then
        try Uri(path).LocalPath with _ -> path.Substring(7)
      else path
    try normalizePath (Path.GetFullPath cleaned)
    with _ -> normalizePath cleaned

let resolveSarifUri (baseDir: string) (uri: string) =
  if String.IsNullOrWhiteSpace uri then ""
  elif uri.StartsWith("file://", StringComparison.OrdinalIgnoreCase) then
    canonicalPath uri
  elif Path.IsPathRooted uri then
    canonicalPath uri
  else
    try normalizePath (Path.GetFullPath(uri, baseDir))
    with _ -> normalizePath uri

let fileKey (path: string) =
  let p = normalizePath path
  match p.IndexOf("src/Compiler/", StringComparison.Ordinal) with
  | -1 ->
    match p.IndexOf("tests/fixtures/", StringComparison.Ordinal) with
    | -1 -> p
    | index -> p.Substring(index + "tests/fixtures/".Length)
  | index -> p.Substring(index + "src/Compiler/".Length)

let parseText (text: string) = (JsonDocument.Parse text).RootElement
let parseFile (path: string) = parseText (File.ReadAllText path)

let objectElements (value: JsonElement) =
  if value.ValueKind = JsonValueKind.Array then
    [ for item in value.EnumerateArray() -> item ]
  else []

let tryGet (value: JsonElement) (name: string) =
  if value.ValueKind = JsonValueKind.Object then
    let mutable prop = Unchecked.defaultof<JsonElement>
    if value.TryGetProperty(name, &prop) then Some prop else None
  else None

let textOf (value: JsonElement) (name: string) =
  match tryGet value name with
  | Some property when property.ValueKind = JsonValueKind.String ->
    property.GetString() |> Option.ofObj |> Option.defaultValue ""
  | _ -> ""

let itemGroup (path: string) (group: string) =
  match tryGet (parseFile path) "Items" with
  | Some items ->
    match tryGet items group with
    | Some value -> objectElements value
    | None -> []
  | None -> []

let compileItems (path: string) =
  [ for item in itemGroup path "Compile" do
      match tryGet item "FullPath" with
      | Some value when value.ValueKind = JsonValueKind.String -> yield canonicalPath (value.GetString())
      | _ -> () ]

let referenceFiles (path: string) =
  [ for item in itemGroup path "ReferencePathWithRefAssemblies" do
      let full = textOf item "FullPath"
      if full <> "" then yield canonicalPath full
      else
        let ident = textOf item "Identity"
        if ident <> "" then yield canonicalPath ident ]

let projectReferenceFiles (path: string) =
  [ for item in itemGroup path "ProjectReference" do
      let full = textOf item "FullPath"
      if full <> "" then yield canonicalPath full
      else
        let ident = textOf item "Identity"
        if ident <> "" then yield canonicalPath ident ]

let locationOf (result: JsonElement) =
  match tryGet result "locations" with
  | Some entries ->
    let items = objectElements entries
    if items.IsEmpty then "", 0
    else
      match tryGet (List.head items) "physicalLocation" with
      | Some physical ->
        let uri =
          match tryGet physical "artifactLocation" with
          | Some artifact -> textOf artifact "uri"
          | None -> textOf physical "uri"
        let startLine =
          match tryGet physical "region" |> Option.bind (fun r -> tryGet r "startLine") with
          | Some n when n.ValueKind = JsonValueKind.Number -> n.GetInt32()
          | _ -> 0
        uri, startLine
      | None -> "", 0
  | None -> "", 0

let readResults (sarifPath: string) =
  let root = parseFile sarifPath
  [ for run in root.GetProperty("runs").EnumerateArray() do
      let results = match tryGet run "results" with Some value -> objectElements value | None -> []
      for result in results do
        let message =
          match tryGet result "message" with
          | Some body -> textOf body "text"
          | None -> ""
        let uri, startLine = locationOf result
        yield (textOf result "ruleId", uri, startLine, message) ]

let usageTable (sarifPath: string) =
  readResults sarifPath
  |> List.filter (fun (code, _, _, _) -> code.StartsWith("AXC", StringComparison.Ordinal) || code.StartsWith("CLF", StringComparison.Ordinal))
  |> List.fold (fun table (code, uri, _, _) ->
        let key = (fileKey uri, code)
        Map.add key ((Map.tryFind key table |> Option.defaultValue 0) + 1) table) Map.empty

/// Strict baseline parser: rejects malformed non-comment rows, empty file or
/// unknown rule fields, negative counts, and duplicate (file, code) keys;
/// permits a clean zero-row baseline once all legacy sites are retired.
let readBaselineStrict (path: string) : Map<string * string, int> =
  let lines = File.ReadAllLines path
  let mutable table = Map.empty
  for idx = 0 to lines.Length - 1 do
    let raw = lines.[idx].Trim()
    if raw <> "" && not (raw.StartsWith("#", StringComparison.Ordinal)) then
      let parts = raw.Split('\t')
      if parts.Length <> 3 then
        fail (sprintf "malformed baseline row at line %d: expected 3 tab-separated columns, got %d" (idx + 1) parts.Length)
      let file = normalizePath (parts.[0].Trim())
      let code = parts.[1].Trim()
      if file = "" then
        fail (sprintf "empty file path in baseline at line %d" (idx + 1))
      if code = "" || not (boundaryCodeSet.Contains code) then
        fail (sprintf "unrecognized or empty rule code in baseline at line %d: '%s'" (idx + 1) code)
      match Int32.TryParse parts.[2] with
      | true, count when count >= 0 ->
        let key = (file, code)
        if Map.containsKey key table then
          fail (sprintf "duplicate baseline key (%s, %s) at line %d" file code (idx + 1))
        table <- Map.add key count table
      | _ ->
        fail (sprintf "invalid non-negative integer count in baseline at line %d: '%s'" (idx + 1) parts.[2])
  table

let isZoneA (path: string) =
  let normalized = normalizePath path
  zoneRoots |> List.exists (fun root -> normalized.Contains("/" + root, StringComparison.Ordinal))

let takeFirst (count: int) (items: seq<'a>) =
  items |> Seq.fold (fun (acc: list<'a>) (item: 'a) -> if acc.Length < count then acc @ [item] else acc) []

let showFirst (items: list<string>) (count: int) = items |> takeFirst count |> String.concat ", "
let showFirstOf (count: int) (items: list<string>) = showFirst items count

let defaultBaseDir = __SOURCE_DIRECTORY__

/// Exact-equality ratchet enforcement against the checked-in baseline: refuses
/// new sites, increased counts, AND stale slack (`actual < limit`, preventing
/// `1 -> 0 -> 1` regrowth without lowering `ratchet.tsv`).
let verifyRatchetExact (baseline: Map<string * string, int>) (usage: Map<string * string, int>) =
  let newViolations =
    usage |> Map.toSeq |> Seq.filter (fun (key, _) -> not (Map.containsKey key baseline)) |> List.ofSeq
  if not newViolations.IsEmpty then
    fail (sprintf "ratchet refused %d new site(s): %A" newViolations.Length
            (newViolations |> takeFirst 10 |> List.map (fun ((file, code), count) -> sprintf "%s %s %d" file code count)))
  let increased =
    baseline |> Map.toSeq |> Seq.filter (fun (key, limit) -> (Map.tryFind key usage |> Option.defaultValue 0) > limit) |> List.ofSeq
  if not increased.IsEmpty then
    fail (sprintf "ratchet refused %d increased site(s): %A" increased.Length
            (increased |> takeFirst 10 |> List.map (fun ((file, code), limit) ->
              let actual = Map.tryFind (file, code) usage |> Option.defaultValue 0
              sprintf "%s %s %d > %d" file code actual limit)))
  let shrunk =
    baseline |> Map.toSeq |> Seq.filter (fun (key, limit) -> (Map.tryFind key usage |> Option.defaultValue 0) < limit) |> List.ofSeq
  if not shrunk.IsEmpty then
    fail (sprintf "ratchet refused %d shrunk site(s) (stale slack; lower baseline row): %A" shrunk.Length
            (shrunk |> takeFirst 10 |> List.map (fun ((file, code), limit) ->
              let actual = Map.tryFind (file, code) usage |> Option.defaultValue 0
              sprintf "lower baseline row (%s, %s) from %d to %d" file code limit actual)))

/// Monotonic base-vs-candidate baseline comparison: refuses any new key or
/// increased allowance in the candidate baseline relative to the accepted base
/// revision baseline; lowering or retiring rows is permitted.
let verifyRatchetBaseMonotonic (baseBaseline: Map<string * string, int>) (candidateBaseline: Map<string * string, int>) =
  let added =
    candidateBaseline |> Map.toSeq |> Seq.filter (fun (key, _) -> not (Map.containsKey key baseBaseline)) |> List.ofSeq
  if not added.IsEmpty then
    fail (sprintf "ratchet-base refused %d new baseline row(s) not present at base revision: %A" added.Length
            (added |> takeFirst 10 |> List.map (fun ((file, code), count) -> sprintf "%s %s %d" file code count)))
  let raised =
    candidateBaseline |> Map.toSeq
    |> Seq.choose (fun (key, candLimit) ->
         match Map.tryFind key baseBaseline with
         | Some baseLimit when candLimit > baseLimit -> Some (key, baseLimit, candLimit)
         | _ -> None)
    |> List.ofSeq
  if not raised.IsEmpty then
    fail (sprintf "ratchet-base refused %d raised baseline row(s): %A" raised.Length
            (raised |> takeFirst 10 |> List.map (fun ((file, code), baseLimit, candLimit) ->
              sprintf "%s %s raised %d -> %d" file code baseLimit candLimit)))
  let lowered =
    baseBaseline |> Map.toSeq
    |> Seq.filter (fun (key, baseLimit) -> (Map.tryFind key candidateBaseline |> Option.defaultValue 0) < baseLimit)
    |> Seq.length
  ok (sprintf "ratchet-base monotonic: %d base rows -> %d candidate rows (%d lowered/retired, 0 added, 0 raised)"
        baseBaseline.Count candidateBaseline.Count lowered)

let provenanceFailures
    (results: list<string * string * int * string>)
    (evaluatedRefs: Set<string>)
    (evaluatedProjRefs: Set<string> option)
    (expectedCanonicalByKey: Map<string, string> option)
    (baseDir: string)
    : list<string> =
  let receipts = results |> List.filter (fun (code, _, _, _) -> code = "AXD000")
  if receipts.IsEmpty then
    [ "the sarif report contains zero AXD000 dependency-context receipts" ]
  else
    let actualBoundaryCounts =
      results
      |> List.filter (fun (code, _, _, _) -> code.StartsWith("AXC", StringComparison.Ordinal) || code.StartsWith("CLF", StringComparison.Ordinal))
      |> List.fold (fun acc (_, uri, _, _) ->
            let canon = resolveSarifUri baseDir uri
            Map.add canon ((Map.tryFind canon acc |> Option.defaultValue 0) + 1) acc) Map.empty

    let seenKeys = HashSet<string>(StringComparer.Ordinal)
    [ for (_, uri, _, message) in receipts do
        let key = fileKey uri
        let canonUri = resolveSarifUri baseDir uri
        if not (seenKeys.Add key) then
          yield sprintf "AXD000 duplicate dependency-context receipt for %s" key
        let payload = parseText message

        // Verify boundary analyzer completion & diagnostic-count witness.
        let completedOk =
          match tryGet payload "boundaryAnalyzerCompleted" with
          | Some v when v.ValueKind = JsonValueKind.True -> true
          | _ -> false
        if not completedOk then
          yield sprintf "AXD000 receipt for %s lacks boundaryAnalyzerCompleted=true witness" key

        match tryGet payload "context" with
        | None ->
          yield sprintf "AXD000 receipt for %s has no dependency context object" key
        | Some context ->
          let rawSourcePath = textOf payload "sourcePath"
          let sourcePath = canonicalPath rawSourcePath
          let claimedSourceHash = textOf payload "sourceSha256"

          let expectedCanon =
            match expectedCanonicalByKey with
            | Some expected -> Map.tryFind key expected
            | None -> None

          if expectedCanonicalByKey.IsSome && expectedCanon.IsNone then
            yield sprintf "AXD000 receipt for %s is outside evaluated Zone A checkout scope" key

          if sourcePath = "" || not (File.Exists sourcePath) then
            yield sprintf "AXD000 receipt for %s names a source file that is not on disk: %s" key rawSourcePath
          elif canonUri <> sourcePath then
            yield sprintf "AXD000 canonical path mismatch for %s: SARIF URI resolves to %s but payload sourcePath is %s" key canonUri sourcePath
          elif expectedCanon.IsSome && expectedCanon.Value <> sourcePath then
            yield sprintf "AXD000 canonical path mismatch for %s: payload sourcePath %s does not match evaluated Compile.FullPath %s" key sourcePath expectedCanon.Value
          elif claimedSourceHash.Length <> 64 then
            yield sprintf "AXD000 source hash for %s is not a SHA-256 digest: %s" key claimedSourceHash
          else
            let hashTarget = defaultArg expectedCanon sourcePath
            let actualHash = sha256OfFile hashTarget
            if claimedSourceHash <> actualHash then
              yield sprintf "AXD000 source hash for %s is stale or invented: claimed %s, evaluated file %s"
                key claimedSourceHash actualHash

          // Verify boundary diagnostic count matches SARIF results for this file.
          match tryGet payload "boundaryDiagnosticCount" with
          | Some v when v.ValueKind = JsonValueKind.Number ->
            let declaredDiagCount = v.GetInt32()
            let actualDiagCount = Map.tryFind canonUri actualBoundaryCounts |> Option.defaultValue 0
            if declaredDiagCount <> actualDiagCount then
              yield sprintf "AXD000 boundary diagnostic count mismatch for %s: receipt declares %d but SARIF contains %d"
                key declaredDiagCount actualDiagCount
          | _ ->
            yield sprintf "AXD000 receipt for %s lacks boundaryDiagnosticCount witness" key

          // Symmetric exact set equality for @(ProjectReference) when supplied.
          match evaluatedProjRefs with
          | Some expectedProjs ->
            let citedProjsList =
              match tryGet context "referencedProjects" with
              | Some arr ->
                [ for el in objectElements arr do
                    if el.ValueKind = JsonValueKind.String then
                      yield canonicalPath (el.GetString()) ]
              | None -> []
            let citedProjs = Set.ofList citedProjsList
            if citedProjs.Count <> citedProjsList.Length then
              yield sprintf "AXD000 receipt for %s contains duplicate referencedProjects entries" key
            let uncitedProjs = expectedProjs |> Set.filter (fun p -> not (citedProjs.Contains p)) |> Set.toList
            if not uncitedProjs.IsEmpty then
              yield sprintf "AXD000 receipt for %s omits %d evaluated project reference(s), first %s" key uncitedProjs.Length (showFirst uncitedProjs 3)
            let extraProjs = citedProjs |> Set.filter (fun p -> not (expectedProjs.Contains p)) |> Set.toList
            if not extraProjs.IsEmpty then
              yield sprintf "AXD000 receipt for %s cites %d unexpected project reference(s) outside evaluated MSBuild closure, first %s" key extraProjs.Length (showFirst extraProjs 3)
          | None -> ()

          let assemblies =
            match tryGet context "assemblies" with
            | Some value -> objectElements value
            | None -> []

          let declaredCount =
            match tryGet payload "assemblyCount" with
            | Some value when value.ValueKind = JsonValueKind.Number -> value.GetInt32()
            | _ -> -1
          if declaredCount <> assemblies.Length then
            yield sprintf "AXD000 receipt for %s declares %d assemblies but records %d" key declaredCount assemblies.Length

          if assemblies.IsEmpty && not evaluatedRefs.IsEmpty then
            yield sprintf "AXD000 receipt for %s records no assemblies while MSBuild evaluated %d reference path(s)" key evaluatedRefs.Count

          let records = ResizeArray<string * string * string * string>()
          for item in assemblies do
            let file = canonicalPath (textOf item "file")
            let simpleName = textOf item "simpleName"
            let qualifiedName = textOf item "qualifiedName"
            let claimedHash = textOf item "sha256"
            if file = "" then
              yield sprintf "AXD000 assembly record for %s has no file path" key
            elif not (File.Exists file) then
              yield sprintf "AXD000 assembly record for %s names a file that is not on disk: %s" key file
            elif claimedHash = "" then
              yield sprintf "AXD000 assembly record for %s has no SHA-256 digest" key
            elif claimedHash <> sha256OfFile file then
              yield sprintf "AXD000 assembly hash for %s is stale or invented: claimed %s, evaluated file %s" file claimedHash (sha256OfFile file)
            if simpleName = "" || qualifiedName = "" then
              yield sprintf "AXD000 assembly record for %s has an empty identity" key
            records.Add (simpleName, qualifiedName, file, claimedHash)

          let citedFiles = records |> Seq.map (fun (_, _, file, _) -> file) |> Set.ofSeq
          if citedFiles.Count <> records.Count then
            yield sprintf "AXD000 assembly record for %s contains duplicate assemblies" key

          // Symmetric exact set equality between evaluated MSBuild references and cited assemblies.
          let uncited = evaluatedRefs |> Set.filter (fun file -> not (citedFiles.Contains file)) |> Set.toList
          if not uncited.IsEmpty then
            yield sprintf "AXD000 receipt for %s omits %d evaluated reference path(s), first %s" key uncited.Length (showFirst uncited 3)

          let unexpected = citedFiles |> Set.filter (fun file -> not (evaluatedRefs.Contains file)) |> Set.toList
          if not unexpected.IsEmpty then
            yield sprintf "AXD000 receipt for %s cites %d unexpected reference path(s) outside evaluated MSBuild closure, first %s" key unexpected.Length (showFirst unexpected 3)

          let claimedManifest = textOf payload "referenceManifestSha256"
          if claimedManifest = "" then
            yield sprintf "AXD000 receipt for %s has no reference manifest digest" key
          else
            let recomputedManifest =
              records |> Seq.map (fun (_, qualifiedName, file, _) -> sprintf "%s|%s" qualifiedName file)
              |> Set.ofSeq |> List.ofSeq |> List.sort |> String.concat "\n" |> sha256OfText
            if claimedManifest <> recomputedManifest then
              yield sprintf "AXD000 reference manifest digest for %s does not match its assembly records: claimed %s, recomputed %s" key claimedManifest recomputedManifest ]

let verifyProvenance
    (results: list<string * string * int * string>)
    (evaluatedRefs: Set<string>)
    (evaluatedProjRefs: Set<string> option)
    (expectedCanonicalByKey: Map<string, string> option)
    (baseDir: string) =
  let failures = provenanceFailures results evaluatedRefs evaluatedProjRefs expectedCanonicalByKey baseDir
  if not failures.IsEmpty then fail (String.concat " | " failures)
  let projMsg =
    match evaluatedProjRefs with
    | Some p -> sprintf ", exact symmetric equality on %d project reference(s)" p.Count
    | None -> ""
  ok (sprintf "AXD000 provenance & boundary-completion verified: every digest recomputed, exact symmetric equality on %d evaluated reference path(s)%s" evaluatedRefs.Count projMsg)

let scriptArgs =
  let all = Environment.GetCommandLineArgs()
  match all |> Array.tryFindIndex (fun arg -> arg.EndsWith("VerifyReceipt.fsx", StringComparison.OrdinalIgnoreCase)) with
  | Some index -> all |> Array.skip (index + 1) |> Array.toList
  | None -> all |> Array.skip 1 |> Array.toList

match scriptArgs with
  | "--zone-a" :: itemsPath :: _ ->
    let items = compileItems itemsPath
    let zoneA = items |> List.filter isZoneA
    let roots =
      zoneA |> List.map (fun path ->
        let norm = normalizePath path
        match norm.IndexOf("/Compiler/", StringComparison.Ordinal) with
        | -1 -> ""
        | index -> norm.Substring(index + 10).Split('/').[0]) |> Set.ofList
    eprintfn "Evaluated compile items %d, Zone A %d, roots %A." items.Length zoneA.Length (Set.toList roots)
    // Reserve stdout strictly for canonical Zone A file paths (safe for mapfile).
    List.iter (printfn "%s") zoneA

  | "--strict-typed-tree" :: sarifPath :: _ ->
    let incomplete =
      readResults sarifPath |> List.filter (fun (ruleId, _, _, _) -> ruleId = "AXD001")
    if not incomplete.IsEmpty then
      fail (sprintf "%d Zone A item(s) were not typed-tree analysed: %s"
        incomplete.Length
        (incomplete |> List.map (fun (_, uri, _, message) -> sprintf "%s: %s" (fileKey uri) message) |> showFirstOf 10))
    printfn "RECEIPT OK: zero AXD001 incomplete typed-tree diagnostics."

  | "--emit-baseline" :: sarifPath :: baselinePath :: _ ->
    let table = usageTable sarifPath
    let rows =
      table |> Map.toSeq |> Seq.sortBy (fun ((file, code), _) -> (file, code))
      |> Seq.map (fun ((file, code), count) -> sprintf "%s\t%s\t%d" file code count)
      |> List.ofSeq
    let header =
      [ "# clef #165 Increment B shrinking ratchet baseline";
        "# file<TAB>code<TAB>count for pre-existing Zone A boundary sites.";
        "# Emitted only by an explicit --emit-baseline act; verification only reads it." ]
    File.WriteAllLines(baselinePath, header @ rows)
    printfn "Baseline rows %d." rows.Length

  | "--ratchet" :: baselinePath :: sarifPath :: _ ->
    let baseline = readBaselineStrict baselinePath
    let usage = usageTable sarifPath
    verifyRatchetExact baseline usage
    printfn "Ratchet accepted: exact match on %d baseline rows (0 new, 0 increased, 0 shrunk)." baseline.Count

  | "--ratchet-base" :: basePath :: candidatePath :: _ ->
    let baseBaseline = readBaselineStrict basePath
    let candidateBaseline = readBaselineStrict candidatePath
    verifyRatchetBaseMonotonic baseBaseline candidateBaseline

  | "--expect" :: sarifPath :: fragment :: code :: reason :: rest ->
    let exactLine, minLine =
      match rest with
      | "--line" :: lineStr :: _ ->
        match Int32.TryParse lineStr with
        | true, n -> Some n, None
        | _ -> fail (sprintf "invalid --line value: %s" lineStr)
      | "--min-line" :: lineStr :: _ ->
        match Int32.TryParse lineStr with
        | true, n -> None, Some n
        | _ -> fail (sprintf "invalid --min-line value: %s" lineStr)
      | _ -> None, None
    let hits =
      readResults sarifPath
      |> List.filter (fun (ruleId, uri, startLine, message) ->
            ruleId = code
            && (fileKey uri).Contains(fragment, StringComparison.OrdinalIgnoreCase)
            && message.Contains(reason, StringComparison.OrdinalIgnoreCase)
            && (match exactLine with Some l -> startLine = l | None -> true)
            && (match minLine with Some m -> startLine >= m | None -> true))
    if hits.IsEmpty then
      let locNote =
        match exactLine, minLine with
        | Some l, _ -> sprintf " at exact line %d" l
        | _, Some m -> sprintf " at line >= %d" m
        | _ -> ""
      fail (sprintf "control failed: no %s diagnostic with reason '%s' in %s%s" code reason fragment locNote)
    printfn "CONTROL PASS: %d %s diagnostic(s) matching '%s' with reason '%s'" hits.Length code fragment reason

  | "--expect-none" :: sarifPath :: fragment :: _ ->
    let hits =
      readResults sarifPath
      |> List.filter (fun (ruleId, uri, _, _) ->
            (ruleId.StartsWith("AXC", StringComparison.Ordinal) || ruleId.StartsWith("CLF", StringComparison.Ordinal))
            && (fileKey uri).Contains(fragment, StringComparison.OrdinalIgnoreCase))
    if not hits.IsEmpty then
      fail (sprintf "control failed: %d boundary diagnostic(s) on the clean fixture %s: %A" hits.Length fragment (hits |> takeFirst 5))
    printfn "CONTROL PASS: clean fixture %s produced no boundary diagnostic." fragment

  | "--provenance" :: sarifPath :: refsPath :: rest ->
    let refs = referenceFiles refsPath
    if refs.IsEmpty then fail "evaluated @(ReferencePathWithRefAssemblies) is empty"
    let projRefs =
      match rest with
      | "--project-refs" :: projPath :: _ -> Some (Set.ofList (projectReferenceFiles projPath))
      | _ -> None
    verifyProvenance (readResults sarifPath) (Set.ofList refs) projRefs None defaultBaseDir

  | "--verify" :: itemsPath :: refsPath :: projRefsPath :: sarifPath :: baselinePath :: _ ->
    let items = compileItems itemsPath
    let zoneA = items |> List.filter isZoneA
    let zoneCanonicalSet = Set.ofList zoneA
    let zoneExpectedByKey =
      zoneA |> List.map (fun full -> (fileKey full, full)) |> Map.ofList
    let zoneKeys = zoneExpectedByKey |> Map.keys |> Set.ofSeq
    let roots =
      zoneA |> List.map (fun path ->
        let norm = normalizePath path
        match norm.IndexOf("/Compiler/", StringComparison.Ordinal) with
        | -1 -> ""
        | index -> norm.Substring(index + 10).Split('/').[0]) |> Set.ofList
    let expectedRoots = zoneRoots |> List.map (fun root -> root.TrimEnd('/')) |> Set.ofList
    if roots <> expectedRoots then fail (sprintf "Zone A roots present %A, expected %A" (Set.toList roots) (Set.toList expectedRoots))
    ok (sprintf "evaluated @(Compile) %d items, Zone A %d canonical files across %d roots" items.Length zoneA.Length roots.Count)

    let refs = referenceFiles refsPath
    if refs.IsEmpty then fail "evaluated @(ReferencePathWithRefAssemblies) is empty"
    let missing = refs |> List.filter (fun file -> not (File.Exists file))
    if not missing.IsEmpty then
      fail (sprintf "evaluated @(ReferencePathWithRefAssemblies) names %d assemblies that do not exist: %s" missing.Length (showFirst missing 5))
    ok (sprintf "evaluated @(ReferencePathWithRefAssemblies) %d assemblies, all present on disk" refs.Length)

    let projRefs = projectReferenceFiles projRefsPath
    let missingProjs = projRefs |> List.filter (fun file -> not (File.Exists file))
    if not missingProjs.IsEmpty then
      fail (sprintf "evaluated @(ProjectReference) names %d projects that do not exist: %s" missingProjs.Length (showFirst missingProjs 5))
    ok (sprintf "evaluated @(ProjectReference) %d project references, all present on disk" projRefs.Length)

    let results = readResults sarifPath
    let axd001 = results |> List.filter (fun (code, _, _, _) -> code = "AXD001")
    if not axd001.IsEmpty then
      fail (sprintf "AXD001 incomplete typed-tree analysis for %d Zone A item(s): %s" axd001.Length (axd001 |> List.map (fun (_, uri, _, message) -> sprintf "%s: %s" (fileKey uri) message) |> showFirstOf 5))

    let receipts = results |> List.filter (fun (code, _, _, _) -> code = "AXD000")
    if receipts.IsEmpty then fail "the sarif report contains no AXD000 dependency-context receipt"
    let receiptKeys = receipts |> List.map (fun (_, uri, _, _) -> fileKey uri) |> Set.ofList
    if receipts.Length <> receiptKeys.Count then
      fail (sprintf "AXD000 duplicate receipts detected: %d receipts for %d unique keys" receipts.Length receiptKeys.Count)
    let uncovered = zoneKeys |> Set.filter (fun key -> not (receiptKeys.Contains key)) |> Set.toList
    if not uncovered.IsEmpty then
      fail (sprintf "AXD000 receipt missing for %d Zone A files, first %s" uncovered.Length (showFirst uncovered 5))
    ok (sprintf "AXD000 boundary-completion & dependency-context receipt for all %d Zone A files" zoneKeys.Count)

    let foreign = receiptKeys |> Set.filter (fun key -> not (zoneKeys.Contains key))
    if not foreign.IsEmpty then
      fail (sprintf "AXD000 receipts for %d files outside the evaluated Zone A scope: %s" foreign.Count (showFirst (Set.toList foreign) 5))

    verifyProvenance results (Set.ofList refs) (Some (Set.ofList projRefs)) (Some zoneExpectedByKey) defaultBaseDir

    // Verify canonical full-path loader closure in every receipt (rejects same-suffix checkout substitution).
    for (_, uri, _, message) in receipts do
      let key = fileKey uri
      let payload = parseText message
      let context =
        match tryGet payload "context" with
        | Some ctx -> ctx
        | None -> fail (sprintf "AXD000 receipt for %s is missing 'context' object" key)
      let sourceFilesElem =
        match tryGet context "sourceFiles" with
        | Some sf -> sf
        | None -> fail (sprintf "AXD000 receipt for %s is missing 'context.sourceFiles'" key)
      let sourceCanonical =
        [ for file in objectElements sourceFilesElem do
            if file.ValueKind = JsonValueKind.String then
              yield canonicalPath (file.GetString()) ]
      let sourceSet = Set.ofList sourceCanonical
      let absent = zoneCanonicalSet |> Set.filter (fun p -> not (sourceSet.Contains p)) |> Set.toList
      if not absent.IsEmpty then
        fail (sprintf "AXD000 canonical loader closure for %s is short or from another checkout: %d of %d canonical Zone A paths missing (receipt closure has %d entries), first %s"
                key absent.Length zoneCanonicalSet.Count sourceCanonical.Length (showFirst absent 5))
    ok (sprintf "AXD000 canonical loader closure covers all %d evaluated Zone A paths in every receipt" zoneCanonicalSet.Count)

    let canonBaseline = canonicalPath baselinePath
    let baselineSha = sha256OfFile canonBaseline
    ok (sprintf "baseline %s sha256 %s" canonBaseline baselineSha)

    let baseline = readBaselineStrict canonBaseline
    let usage = usageTable sarifPath
    verifyRatchetExact baseline usage
    printfn "Ratchet accepted: exact match on %d baseline rows (0 new sites, 0 increases, 0 shrunk)." baseline.Count

    let counts =
      boundaryCodes |> List.map (fun code ->
        (code, usage |> Map.toSeq |> Seq.sumBy (fun ((_, ruleId), count) -> if ruleId = code then count else 0)))
    printfn "Boundary diagnostics by rule:"
    List.iter (fun (code, count) -> printfn "  %s %d" code count) counts
    printfn "RECEIPT VERIFIED."

  | _ -> fail "expected --zone-a <compile-items.json>, --strict-typed-tree <report.sarif>, --provenance <report.sarif> <references.json> [--project-refs <project-refs.json>], --emit-baseline <report.sarif> <baseline.tsv>, --ratchet <baseline.tsv> <report.sarif>, --ratchet-base <base.tsv> <candidate.tsv>, --verify <compile-items.json> <references.json> <project-refs.json> <report.sarif> <baseline.tsv>, --expect <sarif> <file> <code> <reason> [--line N | --min-line N] or --expect-none <sarif> <file>"
