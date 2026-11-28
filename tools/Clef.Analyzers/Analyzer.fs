// clef #165 Increment B - the Clef-owned typed (FCS) analyzer for the Zone A
// compiler core.
//
// Governing authority:
//   https://forge.spkez.dev/FidelityFramework/clef/issues/165 (comments #11768, #12618, #12645)
//   https://forge.spkez.dev/FidelityFramework/clef/wiki/Compiler-Core-Boundary-and-Saturation-Recovery
//     sections 1, 2, 3.2, 3.3
//   Farscape ADL ad188177: ZONE-A-ANALYZER-BOUNDARY, ANALYZER-POLICY (Option A),
//                          AUDITED-CLOSURE, COLLOQUIUM-CONVERGENCE-AND-TRIAGE,
//                          PLAIN-ENGINEERING-TERMS
//
// Syntactic checks (inline IL, null literals/patterns, extended $$ interpolated
// strings, and string-literal %A/%T/%O including dynamic * widths) walk the
// compiler's own FCS ParseTree via FSharp.Analyzers.SDK.ASTCollecting (zero
// hand-written lexer drift).  Typed expression walks use explicit iterative
// worklists with zero silent depth truncation.
//
// Enforced codes:
//   AXC001 untyped obj / box / unbox escape hatch
//   AXC002 .NET BCL or unadmitted FSharp.Core dependency outside the Option A allowlist
//   AXC003 direct BCL string or array member use (no blanket array exemption)
//   AXC004 null, isNull, Unchecked.defaultof, or reference-identity escape (incl. HashIdentity.Reference)
//   AXC005 declared obj-typed value
//   AXC006 host, process and timing primitives
//   AXC007 inline MSIL escape hatch (SynExpr.LibraryOnlyILAssembly, incl. spaced/inline-IL CLR throw)
//   AXC008 CLR throw, including implicit throws (failwith/failwithf/nullArgCheck/Option.get/List.head)
//   AXC009 reflection (incl. typeof/typedefof/GetType), constant-folded/runtime PrintfFormat, %A/%T/%O/$$
//   AXC010 ambient/process-wide mutable state (incl. lock, Lazy.IsValueCreated, module-level ref closures)
//   AXC011 mutable cells, ref-cell operators/abbreviations, and legacy mutable BCL collections (ratchet)
//   CLF001 re-invoked publication or PlatformResolution.read* inside a recipe or pass
//   CLF002 host I/O, wall-clock, stdout/stderr, HostTools, Clef.Compiler.IO/Activity, or Driver APIs
//   CLF003 normalize* invocation ratchet in NativeService.fs
//   CLF004 per-region segmentation node-keys-union / unfiltered-edges ratchet
//   AXD000 dependency-context and boundary-completion receipt emitted ONLY after
//          clefZoneABoundary completes all parse-tree and typed-tree checks for a file
//   AXD001 analysis incomplete (no typed tree)
module Clef.Analyzers

open System
open System.Collections.Concurrent
open System.Collections.Generic
open System.IO
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open ClefAnalyzerAllowlist

// ---------------------------------------------------------------------------
// Zone A membership
// ---------------------------------------------------------------------------
let private normalizePath (path: string) = path.Replace('\\', '/')

let private canonicalPath (path: string) =
  if String.IsNullOrWhiteSpace path then ""
  else
    try normalizePath (Path.GetFullPath path)
    with _ -> normalizePath path

let private zoneRelativePath (path: string) =
  let path = normalizePath path
  match path.IndexOf("src/Compiler/", StringComparison.Ordinal) with
  | -1 -> None
  | index -> Some (path.Substring(index + "src/Compiler/".Length))

let private isZoneAFile (path: string) =
  match zoneRelativePath path with
  | Some relative -> List.exists (fun root -> relative.StartsWith(root, StringComparison.Ordinal)) zoneRoots
  | None -> (normalizePath path).Contains(fixtureMarker, StringComparison.Ordinal)

let private zoneRelative (path: string) = zoneRelativePath path |> Option.defaultValue (normalizePath path)

// ---------------------------------------------------------------------------
// Entity classification (ANALYZER-POLICY Option A: default-refuse for BCL & FSharp.Core)
// ---------------------------------------------------------------------------
let private entityName (entity: FSharpEntity) =
  try
    match entity.TryFullName with
    | Some name -> name
    | None -> entity.DisplayName
  with _ -> entity.DisplayName

let private assemblyName (entity: FSharpEntity) =
  try entity.Assembly.SimpleName with _ -> ""

let private isPrimitiveCarrier (name: string) = primitiveCarriers.Contains name

let private startsUnder (name: string) (prefix: string) =
  name = prefix
  || name.StartsWith(prefix + ".", StringComparison.Ordinal)
  || name.StartsWith(prefix + "`", StringComparison.Ordinal)

let private isReflectionEntity (name: string) =
  startsUnder name "System.Reflection" || startsUnder name "Microsoft.FSharp.Reflection"
  || startsUnder name "Microsoft.FSharp.Quotations"
  || startsUnder name "Microsoft.FSharp.Text.StructuredPrintfImpl"
  || name = "System.Type" || name = "System.Reflection.TypeInfo"
  || name = "System.Activator"
  || startsUnder name "Microsoft.FSharp.Reflection.FSharpType"
  || startsUnder name "Microsoft.FSharp.Reflection.FSharpValue"

let private isAmbientStateEntity (name: string) =
  startsUnder name "System.Runtime.CompilerServices.ConditionalWeakTable"
  || startsUnder name "System.Threading.ThreadLocal"
  || startsUnder name "System.Threading.ThreadStaticAttribute"
  || startsUnder name "System.Threading.AsyncLocal"
  || startsUnder name "System.Threading.Interlocked"
  || startsUnder name "System.Threading.Volatile"
  || startsUnder name "System.Threading.Monitor"
  || startsUnder name "System.Threading.ConcurrentExclusiveSchedulerPair"
  || startsUnder name "System.Collections.Concurrent"
  || startsUnder name "System.Threading.Thread"
  || startsUnder name "Microsoft.FSharp.Control.FSharpMailboxProcessor"
  || startsUnder name "Microsoft.FSharp.Control.FSharpEvent"
  || startsUnder name "Microsoft.FSharp.Core.VolatileFieldAttribute"
  || startsUnder name "Clef.Compiler.Caches"
  || startsUnder name "Internal.Utilities.Collections.LruCache"
  || startsUnder name "Internal.Utilities.Library.Extras.WeakMap"
  || startsUnder name "Internal.Utilities.Library.StampedDictionary"

let private isHostProcessEntity (name: string) =
  startsUnder name "System.Environment"
  || startsUnder name "System.Diagnostics.Process" || startsUnder name "System.Diagnostics.ProcessStartInfo"
  || startsUnder name "System.Diagnostics.Stopwatch" || startsUnder name "System.Runtime.InteropServices"
  || startsUnder name "System.Diagnostics.Debug"

let private isHostIoEntity (name: string) =
  startsUnder name "System.IO" || startsUnder name "System.DateTime" || startsUnder name "System.TimeSpan"
  || startsUnder name "System.Console"
  || startsUnder name "Clef.Compiler.GraphChecking"
  || startsUnder name "Clef.Compiler.Project"
  || startsUnder name "Clef.Compiler.IO"
  || startsUnder name "Clef.Compiler.Diagnostics.Activity"
  || startsUnder name "Clef.Compiler.Utilities.HostTools"
  || startsUnder name "Clef.Compiler.Utilities.LinuxHostTools"

let private isExceptionEntity (name: string) =
  name = "System.Exception" || name = "Microsoft.FSharp.Core.exn"
  || startsUnder name "System.Runtime.ExceptionServices.ExceptionDispatchInfo"
  || startsUnder name "System.ArgumentException" || startsUnder name "System.ArgumentNullException"
  || startsUnder name "System.NullReferenceException" || startsUnder name "System.InvalidOperationException"
  || startsUnder name "System.NotImplementedException" || startsUnder name "System.FormatException"

let private isLegacyCollectionEntity (name: string) =
  startsUnder name "System.Collections.Generic.Dictionary"
  || startsUnder name "System.Collections.Generic.HashSet"
  || startsUnder name "System.Collections.Generic.List"
  || startsUnder name "System.Collections.Generic.Queue"
  || startsUnder name "System.Collections.Generic.Stack"

let private isReferenceIdentityEntity (name: string) =
  name = "Microsoft.FSharp.Core.ReferenceEqualityAttribute"
  || name = "Microsoft.FSharp.Core.AllowNullLiteralAttribute"
  || startsUnder name "Microsoft.FSharp.Core.Operators.Unchecked"

let private neutralRootNamespaces =
  Set.ofList [ "System"; "Microsoft"; "Microsoft.FSharp"; "Microsoft.FSharp.Core"
               "Microsoft.FSharp.Collections"; "FSharp"; "Core"; "Collections" ]

let private classifyEntity (entity: FSharpEntity) =
  let name = entityName entity
  let assembly = assemblyName entity
  if entity.IsNamespace && neutralRootNamespaces.Contains name then
    None
  elif entity.IsFSharpAbbreviation then
    match name with
    | "Microsoft.FSharp.Core.obj" -> Some ("AXC001", "untyped obj escape hatch")
    | "Microsoft.FSharp.Core.exn" -> Some ("AXC008", "CLR exception type")
    | "Microsoft.FSharp.Core.ResizeArray" -> Some ("AXC011", "legacy mutable BCL collection")
    | "Microsoft.FSharp.Core.ref" | "Microsoft.FSharp.Core.Ref" -> Some ("AXC011", "mutable ref cell")
    | _ -> None
  elif name = "System.Object" then
    Some ("AXC001", "untyped obj escape hatch")
  elif isHostIoEntity name then
    Some ("CLF002", "host I/O, wall-clock, HostTools, or Driver API")
  elif isAmbientStateEntity name then
    Some ("AXC010", "ambient or process-wide mutable state")
  elif isPrimitiveCarrier name && isBclAssembly assembly then
    None
  elif admittedEntities.Contains name then
    None
  elif isFSharpCoreAssembly assembly then
    if isReflectionEntity name then Some ("AXC009", "reflection or structural formatting")
    elif isReferenceIdentityEntity name then Some ("AXC004", "reference identity or null escape")
    elif isLegacyCollectionEntity name then Some ("AXC011", "legacy mutable BCL collection")
    elif startsUnder name "Microsoft.FSharp.Core.FSharpRef" then Some ("AXC011", "mutable ref cell")
    elif isAdmittedFSharpCoreEntity name then None
    else Some ("AXC002", "Zone A may not depend on unadmitted FSharp.Core surface")
  elif isBclAssembly assembly then
    if isReflectionEntity name then Some ("AXC009", "reflection or structural formatting")
    elif isExceptionEntity name then Some ("AXC008", "CLR exception type")
    elif isHostProcessEntity name then Some ("AXC006", "host, process or timing primitive")
    elif isLegacyCollectionEntity name then Some ("AXC011", "legacy mutable BCL collection")
    else Some ("AXC002", "Zone A may not depend on the .NET base class library")
  else
    None

let private declaringName (value: FSharpMemberOrFunctionOrValue) =
  match value.DeclaringEntity with
  | Some entity -> entityName entity
  | None -> ""

let private isAdmittedMember (value: FSharpMemberOrFunctionOrValue) =
  admittedMembers.Contains (declaringName value, value.CompiledName)

let private classifyMember (value: FSharpMemberOrFunctionOrValue) =
  match value.DeclaringEntity with
  | None -> None
  | Some entity ->
    let name = entityName entity
    let asm = assemblyName entity
    if isReflectionEntity name then Some ("AXC009", "reflection or structural formatting")
    elif isAmbientStateEntity name then Some ("AXC010", "ambient or process-wide mutable state")
    elif isReferenceIdentityEntity name then Some ("AXC004", "reference identity or null escape")
    elif isExceptionEntity name then Some ("AXC008", "CLR exception type")
    elif isHostProcessEntity name then Some ("AXC006", "host, process or timing primitive")
    elif isHostIoEntity name then Some ("CLF002", "host I/O, wall-clock, HostTools, or Driver API")
    elif isLegacyCollectionEntity name then Some ("AXC011", "legacy mutable BCL collection")
    elif startsUnder name "Microsoft.FSharp.Core.FSharpRef" then Some ("AXC011", "mutable ref cell")
    elif isFSharpCoreAssembly asm then
      if isAdmittedFSharpCoreEntity name then None
      else Some ("AXC002", "Zone A may not depend on unadmitted FSharp.Core surface")
    elif isPrimitiveCarrier name then Some ("AXC003", "direct BCL member on a primitive carrier")
    elif admittedEntities.Contains name then Some ("AXC003", "direct BCL member on an admitted carrier")
    elif isBclAssembly asm then
      Some ("AXC002", "Zone A may not depend on the .NET base class library")
    else None

// ---------------------------------------------------------------------------
// Named throwing, reflection, host, ambient-state, ref-cell, and escape members
// ---------------------------------------------------------------------------
let private isBoxEscape (value: FSharpMemberOrFunctionOrValue) =
  let declaring = declaringName value
  (value.CompiledName = "Box" || value.LogicalName = "box"
   || value.CompiledName = "Unbox" || value.LogicalName = "unbox")
  && (declaring = "Microsoft.FSharp.Core.Operators"
      || declaring = "Microsoft.FSharp.Core.Operators.OperatorFunctions")

let private isLockMember (value: FSharpMemberOrFunctionOrValue) =
  let declaring = declaringName value
  (value.CompiledName = "Lock" || value.LogicalName = "lock")
  && (declaring = "Microsoft.FSharp.Core.Operators"
      || declaring = "Microsoft.FSharp.Core.Operators.OperatorFunctions")

let private isRefCellOperator (value: FSharpMemberOrFunctionOrValue) =
  let declaring = declaringName value
  (declaring = "Microsoft.FSharp.Core.Operators"
   || declaring = "Microsoft.FSharp.Core.Operators.OperatorFunctions")
  && (value.CompiledName = "Ref" || value.LogicalName = "ref"
      || value.CompiledName = "op_ColonEquals" || value.LogicalName = "op_ColonEquals"
      || value.CompiledName = "op_Dereference" || value.LogicalName = "op_Dereference"
      || value.CompiledName = "Increment" || value.LogicalName = "incr"
      || value.CompiledName = "Decrement" || value.LogicalName = "decr")

let private isReferenceIdentity (value: FSharpMemberOrFunctionOrValue) =
  let declaring = declaringName value
  ((value.CompiledName = "PhysicalEquality" || value.LogicalName = "PhysicalEquality"
    || value.CompiledName = "PhysicalHash" || value.LogicalName = "PhysicalHash"
    || value.CompiledName = "ReferenceEquals" || value.LogicalName = "ReferenceEquals")
   && (declaring = "Microsoft.FSharp.Core.LanguagePrimitives" || declaring = "System.Object"))
  || ((value.CompiledName = "IsNull" || value.LogicalName = "isNull")
      && (declaring = "Microsoft.FSharp.Core.Operators"
          || declaring = "Microsoft.FSharp.Core.Operators.OperatorFunctions"))
  || ((value.CompiledName = "Reference" || value.LogicalName = "Reference")
      && declaring = "Microsoft.FSharp.Collections.HashIdentity")
  || ((value.CompiledName = "DefaultOf" || value.LogicalName = "defaultof")
      && declaring = "Microsoft.FSharp.Core.Operators.Unchecked")

let private isReflectionMember (value: FSharpMemberOrFunctionOrValue) =
  let declaring = declaringName value
  ((value.CompiledName = "TypeOf" || value.LogicalName = "typeof"
    || value.CompiledName = "TypeDefOf" || value.LogicalName = "typedefof")
   && declaring = "Microsoft.FSharp.Core.Operators")
  || (value.CompiledName = "GetType" && declaring = "System.Object")

/// Dedicated AXC010 ban on System.Lazy.IsValueCreated state branching (ADL
/// ZONE-A-ANALYZER-BOUNDARY).
let private isLazyStateBranchMember (value: FSharpMemberOrFunctionOrValue) =
  let declaring = declaringName value
  startsUnder declaring "System.Lazy"
  && (value.CompiledName = "get_IsValueCreated" || value.LogicalName = "IsValueCreated")

let private isImplicitThrow (value: FSharpMemberOrFunctionOrValue) =
  let declaring = declaringName value
  let coreThrow =
    (Set.ofList [ "FailWith"; "FailWithf"; "PrintFormatToStringThenFail"; "InvalidArg"; "InvalidOp"
                  "NullArg"; "NullArgCheck"; "Raise"; "Reraise"; "failwith"; "failwithf"; "invalidArg"
                  "invalidOp"; "nullArg"; "nullArgCheck"; "raise"; "reraise" ]
     |> Set.contains value.CompiledName
     || Set.ofList [ "failwith"; "failwithf"; "invalidArg"; "invalidOp"; "nullArg"; "nullArgCheck"
                     "raise"; "reraise" ]
        |> Set.contains value.LogicalName)
    && (declaring = "Microsoft.FSharp.Core.Operators"
        || declaring = "Microsoft.FSharp.Core.Operators.OperatorFunctions"
        || declaring = "Microsoft.FSharp.Core.ExtraTopLevelOperators")
  let optionThrow =
    (value.CompiledName = "GetValue" || value.LogicalName = "get" || value.CompiledName = "get_Value"
     || value.LogicalName.StartsWith("get.", StringComparison.Ordinal))
    && (declaring = "Microsoft.FSharp.Core.OptionModule"
        || startsUnder declaring "Microsoft.FSharp.Core.Option"
        || startsUnder declaring "Microsoft.FSharp.Core.FSharpOption")
  let listThrow =
    (value.CompiledName = "Head" || value.CompiledName = "head"
     || value.LogicalName = "head" || value.LogicalName = "max" || value.LogicalName = "min")
    && (declaring = "Microsoft.FSharp.Collections.ListModule"
        || startsUnder declaring "Microsoft.FSharp.Collections.List")
  let intrinsicThrow =
    value.CompiledName = "FailInit"
    && declaring = "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions"
  let clrThrow =
    value.CompiledName = "Throw"
    && declaring = "System.Runtime.ExceptionServices.ExceptionDispatchInfo"
  let guardThrow =
    value.CompiledName.StartsWith("ThrowIf", StringComparison.Ordinal)
    || value.CompiledName = "DebugAssert"
  coreThrow || optionThrow || listThrow || intrinsicThrow || clrThrow || guardThrow

let private isHostIoMember (value: FSharpMemberOrFunctionOrValue) =
  let declaring = declaringName value
  startsUnder declaring "System.Console"
  || startsUnder declaring "System.IO"
  || startsUnder declaring "Clef.Compiler.GraphChecking"
  || startsUnder declaring "Clef.Compiler.Project"
  || startsUnder declaring "Clef.Compiler.IO"
  || startsUnder declaring "Clef.Compiler.Diagnostics.Activity"
  || startsUnder declaring "Clef.Compiler.Utilities.HostTools"
  || startsUnder declaring "Clef.Compiler.Utilities.LinuxHostTools"
  || (value.CompiledName = "Start" && declaring = "System.Diagnostics.Process")
  || (value.LogicalName = "Now" && declaring = "System.DateTime")
  || (value.LogicalName = "UtcNow" && declaring = "System.DateTime")
  || (value.LogicalName = "Exit" && declaring = "System.Environment")
  || ((value.CompiledName = "Exit" || value.LogicalName = "exit")
      && declaring = "Microsoft.FSharp.Core.Operators")

let private isConsoleFormatMember (value: FSharpMemberOrFunctionOrValue) =
  let declaring = declaringName value
  (declaring.StartsWith("Microsoft.FSharp.Core.Operators", StringComparison.Ordinal)
   || declaring.StartsWith("Microsoft.FSharp.Core.Printf", StringComparison.Ordinal)
   || declaring.StartsWith("Microsoft.FSharp.Core.ExtraTopLevelOperators", StringComparison.Ordinal))
  && (value.LogicalName = "printfn" || value.LogicalName = "eprintfn"
      || value.LogicalName = "printf" || value.LogicalName = "eprintf"
      || value.LogicalName = "fprintf" || value.LogicalName = "fprintfn"
      || value.LogicalName = "print" || value.LogicalName = "println"
      || value.LogicalName = "stdout" || value.LogicalName = "stderr")

/// True when `value`'s declaring entity is defined in the exact same canonical
/// production source file (so internal calls inside a publication/resolution
/// owner file do not trigger cross-module CLF001, while any similarly named
/// file in another folder such as Baker/Recipes/ still triggers CLF001).
/// Disabled inside single-file fixture stubs so fixture modules remain active.
let private isSelfModule (currentFileName: string) (value: FSharpMemberOrFunctionOrValue) =
  let normCurrent = canonicalPath currentFileName
  if normCurrent.Contains(fixtureMarker, StringComparison.Ordinal) then
    false
  else
    match value.DeclaringEntity with
    | Some entity ->
      try
        let declFile = entity.DeclarationLocation.FileName
        not (String.IsNullOrWhiteSpace declFile) && canonicalPath declFile = normCurrent
      with _ -> false
    | None -> false

// CLF001: symbol-resolved re-invocation of publication/resolution entrypoints
// (clef #165 #12565, #12618, wiki section 3.3: covers all PlatformResolution.read*
// whole-graph readers as well as resolve, *Publication.project/check, and
// WitnessEmission).  Never counts definitions or same-file self-calls.
let private isReInvocation (currentFileName: string) (value: FSharpMemberOrFunctionOrValue) =
  if isSelfModule currentFileName value then
    false
  else
    let declaring = declaringName value
    let publication =
      declaring.EndsWith("Publication", StringComparison.Ordinal)
      && (value.LogicalName = "project" || value.LogicalName = "projectWithNumeric" || value.LogicalName = "check")
    let resolution =
      declaring.Contains("PlatformResolution", StringComparison.Ordinal)
      && (value.LogicalName.StartsWith("read", StringComparison.Ordinal) || value.LogicalName = "resolve")
    let witnessProjection =
      declaring.Contains("WitnessEmission", StringComparison.Ordinal)
      && value.IsModuleValueOrMember
    publication || resolution || witnessProjection

// CLF003 (wiki section 3.3): shrinking ratchet on NativeService.fs `.normalize*` calls.
let private isNormalizeTargetFile (relative: string) =
  relative.EndsWith("NativeTypedTree/NativeService.fs", StringComparison.Ordinal)
  || relative.Contains("NativeTypedTree/NormalizeCase.fs", StringComparison.Ordinal)

let private isNormalizeCall (value: FSharpMemberOrFunctionOrValue) =
  value.LogicalName.StartsWith("normalize", StringComparison.Ordinal)
  && match value.DeclaringEntity with
     | Some entity -> (entityName entity).StartsWith("Clef.Compiler", StringComparison.Ordinal)
     | None -> false

// ---------------------------------------------------------------------------
// Source slice helper & Printf format grammar (matching ClefCoreGuard.fsx:419)
// ---------------------------------------------------------------------------
let private rangeText (sourceText: ISourceText) (m: range) : string =
  try
    let startLine = max 1 m.StartLine
    let endLine = min (sourceText.GetLineCount()) m.EndLine
    if startLine > endLine then ""
    elif startLine = endLine then
      let line = sourceText.GetLineString(startLine - 1)
      let sCol = max 0 (min line.Length m.StartColumn)
      let eCol = max sCol (min line.Length m.EndColumn)
      line.Substring(sCol, eCol - sCol)
    else
      let sb = System.Text.StringBuilder()
      for ln in startLine .. endLine do
        let line = sourceText.GetLineString(ln - 1)
        if ln = startLine then
          let sCol = max 0 (min line.Length m.StartColumn)
          sb.Append(line.Substring(sCol)) |> ignore
        elif ln = endLine then
          let eCol = max 0 (min line.Length m.EndColumn)
          sb.Append('\n').Append(line.Substring(0, eCol)) |> ignore
        else
          sb.Append('\n').Append(line) |> ignore
      sb.ToString()
  with _ -> ""

/// Recognizes F# printf format specifiers ending in A, T, or O, including flags
/// (`0`, `+`, `-`, ` `), optional width (digits or `*`), and optional precision
/// (`.` followed by digits or `*`), skipping escaped `%%` pairs.
/// Matches `tools/ClefCoreGuard.fsx:419-430`.
let private reflectiveSpecifiersInString (s: string) : string list =
  [ let mutable i = 0
    let e = s.Length
    while i < e do
      if s.[i] = '%' then
        if i + 1 < e && s.[i + 1] = '%' then
          i <- i + 2
        else
          let mutable j = i + 1
          while j < e && (s.[j] = '+' || s.[j] = '-' || s.[j] = ' ' || s.[j] = '0') do
            j <- j + 1
          if j < e && s.[j] = '*' then
            j <- j + 1
          else
            while j < e && Char.IsDigit s.[j] do j <- j + 1
          if j < e && s.[j] = '.' then
            j <- j + 1
            if j < e && s.[j] = '*' then
              j <- j + 1
            else
              while j < e && Char.IsDigit s.[j] do j <- j + 1
          if j < e && (s.[j] = 'A' || s.[j] = 'T' || s.[j] = 'O') then
            yield s.Substring(i, j - i + 1)
            i <- j + 1
          else
            i <- i + 1
      else
        i <- i + 1 ]

// ---------------------------------------------------------------------------
// JSON & cached file hashing for the AXD000 completion/dependency receipt
// ---------------------------------------------------------------------------
let private jsonString (value: string) =
  let escaped = System.Text.StringBuilder()
  escaped.Append('"') |> ignore
  for character in value do
    match character with
    | '"' -> escaped.Append("\\\"") |> ignore
    | '\\' -> escaped.Append("\\\\") |> ignore
    | '\n' -> escaped.Append("\\n") |> ignore
    | '\r' -> escaped.Append("\\r") |> ignore
    | '\t' -> escaped.Append("\\t") |> ignore
    | c -> escaped.Append(c) |> ignore
  escaped.Append('"') |> ignore
  escaped.ToString()

let private jsonArray (values: seq<string>) =
  values |> Seq.map jsonString |> String.concat "," |> sprintf "[%s]"

let private jsonObject (fields: seq<string * string>) =
  fields |> Seq.map (fun (key, value) -> jsonString key + ":" + value) |> String.concat "," |> sprintf "{%s}"

let private sha256OfBytes (bytes: byte array) =
  use sha = System.Security.Cryptography.SHA256.Create() in
  Convert.ToHexString(sha.ComputeHash bytes).ToLowerInvariant()

let private sha256OfText (text: string) =
  sha256OfBytes (System.Text.Encoding.UTF8.GetBytes text)

let private sha256OfFileDirect (path: string) =
  try sha256OfBytes (File.ReadAllBytes path) with _ -> ""

// Per-process cache keyed by (path, length, lastWriteUtcTicks) strictly for
// read-only reference assemblies in this Zone-B analyzer tool so 256 files do
// not re-read and re-hash 174 reference DLLs ~44,000 times.
let private assemblyHashCache = ConcurrentDictionary<string * int64 * int64, string>()

let private sha256OfAssemblyFile (path: string) =
  if String.IsNullOrWhiteSpace path then ""
  else
    try
      let info = FileInfo(path)
      if not info.Exists then ""
      else
        let key = (path, info.Length, info.LastWriteTimeUtc.Ticks)
        assemblyHashCache.GetOrAdd(key, fun _ -> sha256OfBytes (File.ReadAllBytes path))
    with _ -> ""

let private buildDependencyReceipt (context: CliContext) (fileName: string) (boundaryDiagnosticCount: int) : Message =
  let options = context.ProjectOptions
  let assemblies =
    context.CheckFileResults.ProjectContext.GetReferencedAssemblies()
    |> Seq.toArray
  let records =
    assemblies
    |> Seq.map (fun assembly ->
      let file = match assembly.FileName with | Some path -> path | None -> ""
      (assembly.SimpleName, assembly.QualifiedName, file, sha256OfAssemblyFile file))
    |> Seq.distinctBy (fun (_, qualifiedName, file, _) -> qualifiedName, file)
    |> List.ofSeq
  let assemblyRecords =
    records
    |> List.map (fun (simpleName, qualifiedName, file, hash) ->
      jsonObject [ "simpleName", jsonString simpleName
                   "qualifiedName", jsonString qualifiedName
                   "file", jsonString file
                   "sha256", jsonString hash ])
    |> String.concat ","
    |> sprintf "[%s]"
  let orderedManifest =
    records
    |> List.map (fun (_, qualifiedName, file, _) -> sprintf "%s|%s" qualifiedName file)
    |> List.sort
    |> String.concat "\n"
  let record =
    jsonObject [ "project", jsonString (normalizePath options.ProjectFileName)
                 "sourceFiles", jsonArray (options.SourceFiles |> Seq.map normalizePath)
                 "referencedProjects", jsonArray (options.ReferencedProjectsPath |> Seq.map normalizePath)
                 "options", jsonArray options.OtherOptions
                 "assemblies", assemblyRecords ]
  let payload =
    jsonObject [ "context", record
                 "sourcePath", jsonString (canonicalPath fileName)
                 "sourceSha256", jsonString (sha256OfFileDirect fileName)
                 "assemblyCount", string records.Length
                 "referenceManifestSha256", jsonString (sha256OfText orderedManifest)
                 "boundaryAnalyzerCompleted", "true"
                 "boundaryDiagnosticCount", string boundaryDiagnosticCount ]
  { Type = "Clef zone-A boundary"
    Message = payload
    Code = "AXD000"
    Severity = Severity.Info
    Range = Range.mkRange fileName (Position.mkPos 1 0) (Position.mkPos 1 0)
    Fixes = [] }

// ---------------------------------------------------------------------------
// Iterative type & expression inspectors (zero silent depth truncation)
// ---------------------------------------------------------------------------
let private isRefCellType (rootType: FSharpType) : bool =
  let visited = HashSet<string>(StringComparer.Ordinal)
  let stack = Stack<FSharpType>()
  stack.Push(rootType)
  let mutable found = false
  while stack.Count > 0 && not found do
    let typ = stack.Pop()
    let key = (try typ.ToString() with _ -> "") |> Option.ofObj |> Option.defaultValue ""
    if key = "" || visited.Add(key) then
      let directHit =
        try
          if typ.HasTypeDefinition then
            let full = entityName typ.TypeDefinition
            let compiled = typ.TypeDefinition.CompiledName
            startsUnder full "Microsoft.FSharp.Core.FSharpRef"
            || full = "Microsoft.FSharp.Core.ref"
            || full = "Microsoft.FSharp.Core.Ref"
            || startsUnder compiled "FSharpRef"
          else false
        with _ -> false
      if directHit then
        found <- true
      else
        if typ.IsAbbreviation then
          try stack.Push(typ.AbbreviatedType) with _ -> ()
        if typ.IsTupleType || typ.HasTypeDefinition then
          try
            for arg in typ.GenericArguments do
              stack.Push(arg)
          with _ -> ()
  found

let private isObjectType (rootType: FSharpType) : bool =
  let visited = HashSet<string>(StringComparer.Ordinal)
  let mutable cur = rootType
  let mutable keepGoing = true
  let mutable result = false
  while keepGoing do
    let key = (try cur.ToString() with _ -> "") |> Option.ofObj |> Option.defaultValue ""
    if key <> "" && not (visited.Add(key)) then
      keepGoing <- false
    elif cur.IsAbbreviation then
      try cur <- cur.AbbreviatedType with _ -> keepGoing <- false
    else
      result <-
        try cur.HasTypeDefinition && cur.TypeDefinition.FullName = "System.Object"
        with _ -> false
      keepGoing <- false
  result

let private exprHasRefCell (rootExpr: FSharpExpr) : bool =
  let stack = Stack<FSharpExpr>()
  stack.Push(rootExpr)
  let mutable found = false
  while stack.Count > 0 && not found do
    let expr = stack.Pop()
    if isRefCellType expr.Type then
      found <- true
    else
      match expr with
      | FSharpExprPatterns.Let((letVal, bindExpr, _), bodyExpr) ->
        if letVal.IsRefCell || isRefCellType letVal.FullType then
          found <- true
        else
          stack.Push(bodyExpr)
          stack.Push(bindExpr)
      | _ ->
        for sub in expr.ImmediateSubExpressions do
          stack.Push(sub)
  found

// ---------------------------------------------------------------------------
// Zone A boundary analyzer (emits AXD000 strictly after parse-tree and
// typed-tree traversal complete with zero silent truncation)
// ---------------------------------------------------------------------------
[<CliAnalyzer("Clef zone-A boundary")>]
let clefZoneABoundary : Analyzer<CliContext> = fun context -> async {
  let fileName = context.FileName
  if not (isZoneAFile fileName) then
    return []
  else
    let diagnostics = ResizeArray<Message>()

    let add code reason range detail =
      diagnostics.Add {
        Type = "Clef zone-A boundary"
        Message = sprintf "%s: %s" reason detail
        Code = code
        Severity = Severity.Error
        Range = range
        Fixes = []
      }

    let relative = zoneRelative fileName
    let sourceText = context.SourceText

    // 1. Compiler-parsed AST checks via FSharp.Analyzers.SDK.ASTCollecting:
    //    eliminates hand-written lexer drift (whitespace in `( # ... # )`,
    //    `(* '"' *)`, `(* (*) *)`, interpolation holes, and verbatim strings).
    let astCollector =
      { new SyntaxCollectorBase() with
          override _.WalkExpr(_, expr) =
            match expr with
            | SynExpr.LibraryOnlyILAssembly(_, _, _, _, m) ->
              let snippet = rangeText sourceText m
              let reason =
                if snippet.Contains("throw", StringComparison.Ordinal) then
                  "inline MSIL CLR throw"
                else
                  "inline MSIL escape hatch"
              add "AXC007" reason m snippet
            | SynExpr.Null(m) ->
              add "AXC004" "null escape" m "null literal inside Zone A"
            | SynExpr.InterpolatedString(_, _, m) ->
              let snippet = rangeText sourceText m
              if snippet.StartsWith("$$", StringComparison.Ordinal) then
                add "AXC009" "extended interpolated string hole" m "$$ interpolated string"
            | SynExpr.Const(SynConst.String(strVal, _, _), m) ->
              for spec in reflectiveSpecifiersInString strVal do
                add "AXC009" "reflective structural formatting" m (spec + " format specifier")
            | _ -> ()
          override _.WalkInterpolatedStringPart(_, part) =
            match part with
            | SynInterpolatedStringPart.String(strVal, m) ->
              for spec in reflectiveSpecifiersInString strVal do
                add "AXC009" "reflective structural formatting" m (spec + " format specifier")
            | _ -> ()
          override _.WalkPat(_, pat) =
            match pat with
            | SynPat.Null(m) ->
              add "AXC004" "null escape" m "null pattern inside Zone A"
            | _ -> () }
    walkAst astCollector context.ParseFileResults.ParseTree

    match context.TypedTree with
    | None ->
      add "AXD001" "analysis incomplete"
        (Range.mkRange fileName (Position.mkPos 1 0) (Position.mkPos 1 0))
        "the typed tree is unavailable, so the Clef zone-A analyzer cannot run"
      return diagnostics
        |> Seq.distinctBy (fun message -> message.Code, message.Range.StartLine, message.Range.StartColumn, message.Message)
        |> List.ofSeq
    | Some tree ->
      for symbolUse in context.GetAllSymbolUsesOfFile() do
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
          if isBoxEscape value then
            add "AXC001" "untyped obj escape hatch" symbolUse.Range (sprintf "'%s' widens/unboxes via obj" value.LogicalName)
          elif isReflectionMember value then
            add "AXC009" "reflection or structural formatting" symbolUse.Range (sprintf "'%s.%s' uses CLR type inspection" (declaringName value) value.LogicalName)
          elif isLockMember value then
            add "AXC010" "ambient or process-wide mutable state" symbolUse.Range (sprintf "'%s.%s' synchronizes via CLR Monitor lock" (declaringName value) value.LogicalName)
          elif isLazyStateBranchMember value then
            add "AXC010" "ambient or process-wide mutable state" symbolUse.Range (sprintf "'%s.%s' branches on Lazy state" (declaringName value) value.LogicalName)
          elif isRefCellOperator value then
            add "AXC011" "mutable ref cell" symbolUse.Range (sprintf "'%s.%s' operates on a mutable ref cell" (declaringName value) value.LogicalName)
          elif isReferenceIdentity value then
            add "AXC004" "reference identity or null escape" symbolUse.Range (sprintf "'%s' uses reference identity, isNull, or Unchecked.defaultof" value.LogicalName)
          elif isImplicitThrow value then
            add "AXC008" "CLR throw" symbolUse.Range (sprintf "'%s' throws a CLR exception" value.LogicalName)
          elif isHostIoMember value then
            add "CLF002" "host I/O, wall-clock, HostTools, or Driver API" symbolUse.Range
              (sprintf "'%s.%s' touches the host" (declaringName value) value.LogicalName)
          elif isConsoleFormatMember value then
            add "CLF002" "host I/O, wall-clock, HostTools, or Driver API" symbolUse.Range
              (sprintf "'%s.%s' writes to the console" (declaringName value) value.LogicalName)
          elif not symbolUse.IsFromDefinition && isReInvocation fileName value && not (publicationDrivers.Contains relative) then
            add "CLF001" "re-invoked publication or platform resolution" symbolUse.Range
              (sprintf "'%s.%s' re-derives published state inside a recipe or pass"
                (declaringName value) value.LogicalName)
          elif not symbolUse.IsFromDefinition && isNormalizeCall value && isNormalizeTargetFile relative then
            add "CLF003" "normalize invocation ratchet" symbolUse.Range
              (sprintf "'%s.%s' re-normalizes the native typed tree" (declaringName value) value.LogicalName)
          elif value.IsMutable && not value.IsCompilerGenerated then
            if value.IsMember then
              add "AXC010" "ambient mutable state" symbolUse.Range
                (sprintf "mutable member '%s'" value.DisplayName)
            elif symbolUse.IsFromDefinition && not (value.IsProperty || value.IsMethod) then
              add "AXC011" "mutable cell ratchet" symbolUse.Range
                (sprintf "mutable binding '%s'" value.DisplayName)
            else
              ()
          elif isAdmittedMember value then
            ()
          else
            match classifyMember value with
            | Some (code, reason) ->
              add code reason symbolUse.Range (sprintf "'%s.%s'" (declaringName value) value.LogicalName)
            | None -> ()
        | :? FSharpField as field ->
          if field.IsMutable && not field.IsCompilerGenerated then
            add "AXC011" "mutable record or class field" symbolUse.Range (sprintf "mutable field '%s'" field.Name)
          elif symbolUse.IsFromDefinition && not field.IsCompilerGenerated && isRefCellType field.FieldType then
            add "AXC011" "mutable ref cell" symbolUse.Range (sprintf "ref-typed field '%s'" field.Name)
          // CLF004 (wiki section 3.3): forbid per-region segmentation folds from
          // unioning whole graph.Nodes.Keys or iterating unfiltered graph.Edges.
          // Keyed lookups like `graph.Nodes[id]` remain permitted clean lookups.
          if relative.Contains("Segmentation", StringComparison.OrdinalIgnoreCase) && not symbolUse.IsFromDefinition then
            if field.Name = "Edges" then
              add "CLF004" "segmentation unfiltered-edges ratchet" symbolUse.Range "unfiltered graph.Edges access in segmentation"
            elif field.Name = "Nodes" then
              let lineIdx = symbolUse.Range.StartLine - 1
              if lineIdx >= 0 && lineIdx < sourceText.GetLineCount()
                 && (sourceText.GetLineString(lineIdx)).Contains(".Nodes.Keys", StringComparison.Ordinal) then
                add "CLF004" "segmentation node-keys-union ratchet" symbolUse.Range "whole-graph .Nodes.Keys union in segmentation"
        | :? FSharpEntity as entity ->
          match classifyEntity entity with
          | Some (code, reason) -> add code reason symbolUse.Range (entityName entity)
          | None -> ()
        | _ -> ()

      // Counted opens: opening a refused namespace is itself a dependency.
      for declaration in context.CheckFileResults.OpenDeclarations do
        match declaration.Range with
        | Some range when not declaration.IsOwnNamespace ->
          for openedModule in declaration.Modules do
            match classifyEntity openedModule with
            | Some (code, reason) -> add code reason range (entityName openedModule)
            | None -> ()
          for typ in declaration.Types do
            if typ.HasTypeDefinition then
              match classifyEntity typ.TypeDefinition with
              | Some (code, reason) -> add code reason range (entityName typ.TypeDefinition)
              | None -> ()
        | _ -> ()

      // Iterative PrintfFormat inspection across all expressions (zero silent depth cap).
      let inspectPrintfFormats (rootExpr: FSharpExpr) =
        let stack = Stack<FSharpExpr>()
        stack.Push(rootExpr)
        while stack.Count > 0 do
          let expr = stack.Pop()
          match expr with
          | FSharpExprPatterns.NewObject(ctor, _, args) when startsUnder (declaringName ctor) "Microsoft.FSharp.Core.PrintfFormat" ->
            match args with
            | FSharpExprPatterns.Const(value, _) :: _ ->
              match value with
              | :? string as fmtText ->
                for spec in reflectiveSpecifiersInString fmtText do
                  add "AXC009" "reflective structural formatting" expr.Range
                    (sprintf "resolved PrintfFormat contains %s specifier" spec)
              | _ ->
                add "AXC009" "reflective structural formatting" expr.Range
                  "runtime PrintfFormat cannot be statically verified free of %A/%T/%O"
            | _ ->
              add "AXC009" "reflective structural formatting" expr.Range
                "runtime PrintfFormat cannot be statically verified free of %A/%T/%O"
          | _ -> ()
          for sub in expr.ImmediateSubExpressions do
            stack.Push(sub)

      // Iterative declaration walk: AXC010 module-level ref cells & closures,
      // AXC005 declared obj-typed values, and AXC009 typed PrintfFormat checks.
      let declStack = Stack<FSharpImplementationFileDeclaration>()
      for d in List.rev tree.Declarations do declStack.Push(d)
      while declStack.Count > 0 do
        match declStack.Pop() with
        | FSharpImplementationFileDeclaration.Entity(_, nested) ->
          for d in List.rev nested do declStack.Push(d)
        | FSharpImplementationFileDeclaration.MemberOrFunctionOrValue(value, args, body) ->
          inspectPrintfFormats body
          if isObjectType value.FullType then
            add "AXC005" "declared obj-typed value" value.DeclarationLocation value.DisplayName
          if value.IsMutable && not value.IsMember && not value.IsCompilerGenerated then
            add "AXC010" "ambient mutable state" value.DeclarationLocation
              (sprintf "module-level mutable binding '%s'" value.DisplayName)
          elif not value.IsCompilerGenerated
               && args.IsEmpty
               && (value.IsRefCell || exprHasRefCell body) then
            add "AXC010" "ambient mutable state" value.DeclarationLocation
              (if value.IsRefCell then sprintf "module-level ref cell '%s'" value.DisplayName
               else sprintf "module-level binding '%s' captures a ref cell" value.DisplayName)
        | FSharpImplementationFileDeclaration.InitAction(body) ->
          inspectPrintfFormats body

      let deduped =
        diagnostics
        |> Seq.distinctBy (fun message -> message.Code, message.Range.StartLine, message.Range.StartColumn, message.Message)
        |> List.ofSeq
      let boundaryCount =
        deduped
        |> List.filter (fun message ->
            message.Code.StartsWith("AXC", StringComparison.Ordinal)
            || message.Code.StartsWith("CLF", StringComparison.Ordinal))
        |> List.length
      let receipt = buildDependencyReceipt context fileName boundaryCount
      return deduped @ [ receipt ]
}
