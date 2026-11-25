// SPDX-License-Identifier: MIT
// Generates the closed, algebraic, reflection-free NodeId remapper for
// `Clef.Compiler.Nanopass.SSAAssignment` (`src/Compiler/Nanopass/NodeIdRemap.fs`).
//
// Every type transitively reachable from `SemanticGraph`'s remapped roots that
// contains `NodeId` (or `Fidelity.PSG.NodeId`) gets an explicit, compiler-checked
// mapper with full record construction and exhaustive union case matching (zero
// `_ ->` wildcards, zero `box`, zero `System.Reflection`, zero `Microsoft.FSharp.Reflection`).
// `SemanticKind` delegates directly to `Clef.Compiler.Nanopass.FoldIn.remapKind`
// so `SemanticKind` has a single exhaustive closed algebraic owner.
//
// Frozen historical provenance (`SpecializationTrace`, tracked separately under
// clef #198) and witness-preparation caches cleared on SSA invalidation
// (`WitnessEmission`, `WitnessSegmentation`, `WitnessLiveScope`, `ProofDispatch`,
// `WitnessPreparedRows`, `WitnessLiveRows`, `WitnessPublishedRows`, `SSAAssignment`,
// `WitnessProvenance`) are governed by explicit closed policies below so any new
// field, case, or leaf-type `NodeId` drift fails `--check` with a non-zero exit code.
//
// usage: dotnet fsi GenerateNodeIdRemapper.fsx [--check|--preview] <Clef.Compiler.Service.dll> <output.fs>

open System
open System.Collections.Generic
open System.IO
open System.Reflection
open Microsoft.FSharp.Reflection

let mode, ccsPath, outputPath =
    match fsi.CommandLineArgs |> Array.toList with
    | [ _; ccs; output ] -> "write", ccs, output
    | [ _; ("--check" | "--preview" as mode); ccs; output ] -> mode, ccs, output
    | _ -> failwith "usage: dotnet fsi GenerateNodeIdRemapper.fsx [--check|--preview] <Clef.Compiler.Service.dll> <output.fs>"

let probeDir = Path.GetDirectoryName ccsPath
AppDomain.CurrentDomain.add_AssemblyResolve(ResolveEventHandler(fun _ args ->
    let name = AssemblyName(args.Name).Name + ".dll"
    let candidate = Path.Combine(probeDir, name)
    if File.Exists candidate then Assembly.LoadFrom candidate else null))

let ccs = Assembly.LoadFrom ccsPath
let psgPath = Path.Combine(probeDir, "Fidelity.PSG.dll")
let psgAsm =
    if File.Exists psgPath then Assembly.LoadFrom psgPath
    else failwithf "Fidelity.PSG.dll not found beside %s" ccsPath
let flags = BindingFlags.Public ||| BindingFlags.NonPublic

let nodeIdType = ccs.GetType("Clef.Compiler.NativeTypedTree.NativeTypes+NodeId", true)
let psgNodeIdType = psgAsm.GetType("Fidelity.PSG.NodeId", true)
let sgType = ccs.GetType("Clef.Compiler.PSGSaturation.SemanticGraph.Types+SemanticGraph", true)
let codataType = ccs.GetType("Clef.Compiler.PSGSaturation.SemanticGraph.Types+Codata", true)
let semanticKindType = ccs.GetType("Clef.Compiler.PSGSaturation.SemanticGraph.Types+SemanticKind", true)
let obligationInfoType = ccs.GetType("Clef.Compiler.PSGSaturation.SemanticGraph.Types+ObligationInfo", true)

/// Explicit closed policy for `SemanticGraph` fields.
let sgRemappedFields =
    set [ "Nodes"; "DeclarationRoots"; "Modules"; "Types"; "ModuleClassifications"
          "StaticStringPool"; "LiteralStorage"; "Escaping"; "Codata"; "Edges"
          "SequenceRangeProvenance"; "RangeContextFacts" ]

let sgUnchangedFields =
    set [ "Platform"; "FieldRanges"; "ElementRanges"; "Layouts" ]

let sgClearedFields =
    set [ "WitnessProvenance" ]

/// Explicit closed policy for `Codata` witness-preparation / SSA-plan fields
/// cleared on SSA remapping (matching `Core.SemanticGraph.invalidateWitness`).
let codataClearedFields =
    set [ "WitnessEmission"; "WitnessSegmentation"; "WitnessLiveScope"; "ProofDispatch"
          "WitnessPreparedRows"; "WitnessLiveRows"; "WitnessPublishedRows"; "SSAAssignment" ]

/// Leaf types that MUST NEVER reach `NodeId` or `Fidelity.PSG.NodeId`.
/// Verified structurally below; `--check` fails if any gains a `NodeId`.
let nodeIdFreeLeafTypeNames =
    set [ "System.String"
          "System.Numerics.BigInteger"
          "System.Decimal"
          "System.Guid"
          "System.DateTime"
          "System.DateTimeOffset"
          "System.TimeSpan"
          "Clef.Compiler.NativeTypedTree.NativeTypes+NativeType"
          "Clef.Compiler.NativeTypedTree.NativeTypes+TypeIdentity"
          "Clef.Compiler.NativeTypedTree.NativeTypes+NominalTypeIdentity"
          "Clef.Compiler.NativeTypedTree.NativeTypes+ConstructorIdentity"
          "Clef.Compiler.NativeTypedTree.NativeTypes+SourceRange"
          "Clef.Compiler.NativeTypedTree.NativeTypes+ValueRange"
          "Clef.Compiler.NativeTypedTree.NativeTypes+PlatformContext" ]

/// Explicit frozen historical leaf types intentionally excluded from live remapping.
/// Pre-existing stale-ID handling tracked in clef #198:
/// https://forge.spkez.dev/FidelityFramework/clef/issues/198
let frozenHistoryLeafTypeNames =
    set [ "Clef.Compiler.PSGSaturation.SemanticGraph.Types+SpecializationTrace" ]

let isNodeIdType (ty: Type) = ty = nodeIdType || ty = psgNodeIdType

let isNodeIdFreeLeaf (ty: Type) =
    ty.IsPrimitive
    || ty.IsEnum
    || (not (isNull ty.FullName) && (nodeIdFreeLeafTypeNames.Contains ty.FullName || ty.FullName.StartsWith("BAREWire.", StringComparison.Ordinal)))

let isFrozenHistoryLeaf (ty: Type) =
    not (isNull ty.FullName) && frozenHistoryLeafTypeNames.Contains ty.FullName

let isLeaf (ty: Type) = isNodeIdFreeLeaf ty || isFrozenHistoryLeaf ty

let isStdContainer (ty: Type) =
    ty.IsGenericType &&
    let d = ty.GetGenericTypeDefinition()
    d = typedefof<option<_>>
    || d = typedefof<list<_>>
    || d = typedefof<Set<_>>
    || d = typedefof<Map<_, _>>
    || d = typedefof<Result<_, _>>
    || d = typedefof<Lazy<_>>

let isData (ty: Type) = FSharpType.IsRecord(ty, flags) || FSharpType.IsUnion(ty, flags)

/// Verify that a leaf type (and every type transitively referenced from it)
/// truly contains neither `NativeTypes.NodeId` nor `Fidelity.PSG.NodeId`.
let verifyNodeIdFreeLeaf (root: Type) =
    let seen = HashSet<Type>()
    let rec check (path: string list) (ty: Type) =
        if isNodeIdType ty then
            failwithf "Leaf type '%s' reaches %s via %s! Remove from nodeIdFreeLeafTypeNames or add explicit remapping."
                root.FullName ty.FullName (String.Join(" -> ", List.rev path))
        elif seen.Contains ty || ty.IsPrimitive || ty.IsEnum || ty = typeof<string> || ty = typeof<obj> then ()
        else
            seen.Add ty |> ignore
            if ty.IsArray then
                check ("[]" :: path) (ty.GetElementType())
            elif ty.IsGenericType then
                for arg in ty.GetGenericArguments() do
                    check (arg.Name :: path) arg
                if FSharpType.IsRecord(ty, flags) then
                    for f in FSharpType.GetRecordFields(ty, flags) do
                        check (f.Name :: path) f.PropertyType
                elif FSharpType.IsUnion(ty, flags) then
                    for c in FSharpType.GetUnionCases(ty, flags) do
                        for f in c.GetFields() do
                            check ((c.Name + "." + f.Name) :: path) f.PropertyType
            elif FSharpType.IsTuple ty then
                for elem in FSharpType.GetTupleElements ty do
                    check (elem.Name :: path) elem
            elif FSharpType.IsRecord(ty, flags) then
                for f in FSharpType.GetRecordFields(ty, flags) do
                    check (f.Name :: path) f.PropertyType
            elif FSharpType.IsUnion(ty, flags) then
                for c in FSharpType.GetUnionCases(ty, flags) do
                    for f in c.GetFields() do
                        check ((c.Name + "." + f.Name) :: path) f.PropertyType
            elif not (isNull ty.Namespace) && not (ty.Namespace.StartsWith("System", StringComparison.Ordinal)) then
                for f in ty.GetFields(BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic) do
                    check (f.Name :: path) f.FieldType
                for p in ty.GetProperties(BindingFlags.Instance ||| BindingFlags.Public ||| BindingFlags.NonPublic) do
                    if p.GetIndexParameters().Length = 0 then
                        check (p.Name :: path) p.PropertyType
    check [ root.Name ] root

let moduleAliases =
    Map.ofList
        [ "Clef.Compiler.PSGSaturation.SemanticGraph.Types", "S"
          "Clef.Compiler.NativeTypedTree.NativeTypes", "N"
          "Clef.Compiler.NativeTypedTree.DimensionAlgebra", "D" ]

let qualifiedTypeName (ty: Type) =
    if isNull ty.DeclaringType then
        failwithf "Unsupported top-level type in NodeId closure: %s" ty.FullName
    match moduleAliases.TryFind ty.DeclaringType.FullName with
    | Some alias -> alias + "." + ty.Name
    | None -> failwithf "Unsupported declaring module in NodeId closure: %s (%s)" ty.DeclaringType.FullName ty.FullName

// Verify SemanticGraph field policy is exhaustive and disjoint.
let sgFields = FSharpType.GetRecordFields(sgType, flags)
let sgFieldNames = sgFields |> Array.map _.Name |> Set.ofArray
let expectedSgFields = Set.unionMany [ sgRemappedFields; sgUnchangedFields; sgClearedFields ]
if sgFieldNames <> expectedSgFields then
    failwithf "SemanticGraph fields drifted! Actual=%A Policy=%A" sgFieldNames expectedSgFields

let codataFields = FSharpType.GetRecordFields(codataType, flags)
for name in codataClearedFields do
    if not (codataFields |> Array.exists (fun f -> f.Name = name)) then
        failwithf "Codata cleared-field policy names absent field '%s'" name

// Walk the transitive type graph from remapped roots (respecting cleared Codata fields).
let visited = HashSet<Type>()
let encounteredFreeLeaves = HashSet<Type>()
let deps = Dictionary<Type, HashSet<Type>>()
let addDep (a: Type) (b: Type) =
    let ok, s = deps.TryGetValue a
    let s = if ok then s else let ns = HashSet<Type>() in deps.[a] <- ns; ns
    s.Add b |> ignore

let rec walk (ty: Type) =
    if visited.Contains ty then ()
    else
        visited.Add ty |> ignore
        if isNodeIdType ty || isFrozenHistoryLeaf ty then ()
        elif isNodeIdFreeLeaf ty then
            encounteredFreeLeaves.Add ty |> ignore
        elif ty = semanticKindType then
            // SemanticKind delegates to FoldIn.remapKind remap (remapObligationInfo remap).
            // Record an unconditional direct dependency on NodeId so SemanticKind
            // never relies transitively on ObligationInfo to enter the remapper closure.
            addDep ty nodeIdType
            addDep ty obligationInfoType
            walk obligationInfoType
        elif ty.IsArray then
            let elem = ty.GetElementType()
            addDep ty elem
            walk elem
        elif isStdContainer ty then
            for arg in ty.GetGenericArguments() do
                addDep ty arg
                walk arg
        elif FSharpType.IsTuple ty then
            for elem in FSharpType.GetTupleElements ty do
                addDep ty elem
                walk elem
        elif ty = codataType then
            for f in FSharpType.GetRecordFields(ty, flags) do
                if not (codataClearedFields.Contains f.Name) then
                    addDep ty f.PropertyType
                    walk f.PropertyType
        elif FSharpType.IsRecord(ty, flags) then
            for f in FSharpType.GetRecordFields(ty, flags) do
                addDep ty f.PropertyType
                walk f.PropertyType
        elif FSharpType.IsUnion(ty, flags) then
            for c in FSharpType.GetUnionCases(ty, flags) do
                for f in c.GetFields() do
                    addDep ty f.PropertyType
                    walk f.PropertyType
        else
            if not (isNull ty.FullName) && (ty.FullName.Contains("NodeId") || ty.Assembly = ccs || ty.Assembly = psgAsm) then
                failwithf "Unsupported non-ADT type in SemanticGraph closure: %s" ty.FullName

for f in sgFields do
    if sgRemappedFields.Contains f.Name || sgUnchangedFields.Contains f.Name then
        walk f.PropertyType

// Verify every named and encountered free leaf truly never reaches NodeId or Fidelity.PSG.NodeId!
for name in nodeIdFreeLeafTypeNames do
    let ty =
        match ccs.GetType(name, false) with
        | null -> Type.GetType(name, false)
        | t -> t
    if not (isNull ty) then
        verifyNodeIdFreeLeaf ty

for ty in encounteredFreeLeaves do
    verifyNodeIdFreeLeaf ty

// Verify FoldIn.remapKind's unchanged SemanticKind leaf cases truly contain NO NodeId or Fidelity.PSG.NodeId!
let foldInLeafCases = set [ "Binding"; "Literal"; "PlatformBinding"; "Intrinsic"; "PatternBinding"; "Error" ]
for c in FSharpType.GetUnionCases(semanticKindType, flags) do
    if foldInLeafCases.Contains c.Name then
        for f in c.GetFields() do
            verifyNodeIdFreeLeaf f.PropertyType

// Compute exact fixpoint of types that transitively reach Clef NodeId or Fidelity.PSG.NodeId.
let reachesNodeId = HashSet<Type>([ nodeIdType; psgNodeIdType ])
let mutable changed = true
while changed do
    changed <- false
    for kv in deps do
        if not (reachesNodeId.Contains kv.Key) then
            if kv.Value |> Seq.exists reachesNodeId.Contains then
                reachesNodeId.Add kv.Key |> ignore
                changed <- true

// Verify unchanged SemanticGraph fields truly do NOT reach NodeId!
for f in sgFields do
    if sgUnchangedFields.Contains f.Name && reachesNodeId.Contains f.PropertyType then
        failwithf "SemanticGraph unchanged field '%s' now reaches NodeId; move to sgRemappedFields!" f.Name

let namedTypes =
    reachesNodeId
    |> Seq.filter (fun ty ->
        not (isNodeIdType ty)
        && not ty.IsArray
        && not (isStdContainer ty)
        && not (FSharpType.IsTuple ty))
    |> Seq.sortBy (fun ty -> ty.FullName)
    |> Seq.toList

for ty in namedTypes do
    if ty.IsGenericType then
        failwithf "Unsupported generic named type reaching NodeId: %s" ty.FullName
    if not (isData ty) then
        failwithf "Non-record/non-union named type reaching NodeId: %s" ty.FullName
    if not (isNull ty.Namespace) && ty.Namespace.StartsWith("Fidelity.PSG", StringComparison.Ordinal) then
        failwithf "Unexpected Fidelity.PSG type reachable after clearing WitnessPublishedRows: %s" ty.FullName

let mapperName (ty: Type) = "remap" + ty.Name
let namedSet = HashSet<Type>(namedTypes)

let keywords =
    set [ "type"; "val"; "module"; "end"; "to"; "begin"; "done"; "rec"; "fixed"; "base"
          "global"; "namespace"; "params"; "process"; "component"; "const"; "include"
          "parallel"; "pure"; "sig"; "trait"; "virtual"; "checked"; "function"; "member"; "default" ]
let escape (name: string) = if keywords.Contains name then "``" + name + "``" else name

let mutable tempCounter = 0
let freshVar prefix =
    tempCounter <- tempCounter + 1
    sprintf "%s%d" prefix tempCounter

let rec emitExpr (ty: Type) (valueExpr: string) : string option =
    if not (reachesNodeId.Contains ty) then None
    elif ty = nodeIdType then Some (sprintf "remap %s" valueExpr)
    elif ty = psgNodeIdType then failwithf "Unexpected Fidelity.PSG.NodeId reachable outside cleared WitnessPublishedRows (%s)" valueExpr
    elif namedSet.Contains ty then Some (sprintf "%s remap %s" (mapperName ty) valueExpr)
    elif ty.IsArray then
        let elem = ty.GetElementType()
        let v = freshVar "x"
        emitExpr elem v |> Option.map (fun body -> sprintf "(Array.map (fun %s -> %s) %s)" v body valueExpr)
    elif ty.IsGenericType && ty.GetGenericTypeDefinition() = typedefof<list<_>> then
        let elem = ty.GetGenericArguments().[0]
        let v = freshVar "x"
        emitExpr elem v |> Option.map (fun body -> sprintf "(List.map (fun %s -> %s) %s)" v body valueExpr)
    elif ty.IsGenericType && ty.GetGenericTypeDefinition() = typedefof<option<_>> then
        let elem = ty.GetGenericArguments().[0]
        let v = freshVar "x"
        emitExpr elem v |> Option.map (fun body -> sprintf "(Option.map (fun %s -> %s) %s)" v body valueExpr)
    elif ty.IsGenericType && ty.GetGenericTypeDefinition() = typedefof<Set<_>> then
        let elem = ty.GetGenericArguments().[0]
        let v = freshVar "x"
        emitExpr elem v |> Option.map (fun body -> sprintf "(Set.map (fun %s -> %s) %s)" v body valueExpr)
    elif ty.IsGenericType && ty.GetGenericTypeDefinition() = typedefof<Map<_, _>> then
        let args = ty.GetGenericArguments()
        let kv, vv = freshVar "k", freshVar "v"
        match emitExpr args.[0] kv, emitExpr args.[1] vv with
        | None, None -> None
        | None, Some vBody -> Some (sprintf "(Map.map (fun _ %s -> %s) %s)" vv vBody valueExpr)
        | kOpt, vOpt ->
            let kExpr = kOpt |> Option.defaultValue kv
            let vExpr = vOpt |> Option.defaultValue vv
            Some (sprintf "(%s |> Map.toSeq |> Seq.map (fun (%s, %s) -> %s, %s) |> Map.ofSeq)" valueExpr kv vv kExpr vExpr)
    elif ty.IsGenericType && ty.GetGenericTypeDefinition() = typedefof<Result<_, _>> then
        let args = ty.GetGenericArguments()
        let okV, errV = freshVar "ok", freshVar "err"
        match emitExpr args.[0] okV, emitExpr args.[1] errV with
        | None, None -> None
        | okOpt, errOpt ->
            let okBody = okOpt |> Option.defaultValue okV
            let errBody = errOpt |> Option.defaultValue errV
            Some (sprintf "(match %s with Result.Ok %s -> Result.Ok (%s) | Result.Error %s -> Result.Error (%s))" valueExpr okV okBody errV errBody)
    elif ty.IsGenericType && ty.GetGenericTypeDefinition() = typedefof<Lazy<_>> then
        let elem = ty.GetGenericArguments().[0]
        emitExpr elem (sprintf "%s.Value" valueExpr)
        |> Option.map (fun body -> sprintf "(lazy (%s))" body)
    elif FSharpType.IsTuple ty then
        let elems = FSharpType.GetTupleElements ty
        let vars = elems |> Array.mapi (fun _ _ -> freshVar "t")
        let mapped = Array.map2 (fun e v -> emitExpr e v |> Option.defaultValue v) elems vars
        let isStruct = ty.IsValueType
        let lhs = if isStruct then sprintf "struct (%s)" (String.Join(", ", vars)) else sprintf "(%s)" (String.Join(", ", vars))
        let rhs = if isStruct then sprintf "struct (%s)" (String.Join(", ", mapped)) else sprintf "(%s)" (String.Join(", ", mapped))
        Some (sprintf "(let %s = %s in %s)" lhs valueExpr rhs)
    else
        failwithf "Cannot emit remapper expression for type %s" ty.FullName

let emitRecord (ty: Type) =
    tempCounter <- 0
    let qname = qualifiedTypeName ty
    let fields = FSharpType.GetRecordFields(ty, flags)
    let lines =
        fields |> Array.map (fun f ->
            let fname = escape f.Name
            if ty = codataType && codataClearedFields.Contains f.Name then
                sprintf "        %s = None" fname
            else
                let read = sprintf "value.%s" fname
                let body = emitExpr f.PropertyType read |> Option.defaultValue read
                sprintf "        %s = %s" fname body)
    sprintf "%s (remap: N.NodeId -> N.NodeId) (value: %s) : %s =\n    ({\n%s\n    } : %s)"
        (mapperName ty) qname qname (String.Join("\n", lines)) qname

let emitUnion (ty: Type) =
    tempCounter <- 0
    let qname = qualifiedTypeName ty
    let cases = FSharpType.GetUnionCases(ty, flags)
    let lines =
        cases |> Array.map (fun c ->
            let fields = c.GetFields()
            let cname = sprintf "%s.%s" qname (escape c.Name)
            if fields.Length = 0 then
                sprintf "    | %s -> %s" cname cname
            else
                let vars = fields |> Array.mapi (fun i _ -> sprintf "a%d" i)
                let mapped = Array.map2 (fun (f: PropertyInfo) v -> emitExpr f.PropertyType v) fields vars
                let pat = String.Join(", ", vars)
                if mapped |> Array.forall Option.isNone then
                    sprintf "    | %s _ -> value" cname
                else
                    let args = Array.map2 (fun v m -> m |> Option.defaultValue v) vars mapped
                    sprintf "    | %s(%s) -> %s(%s)" cname pat cname (String.Join(", ", args)))
    sprintf "%s (remap: N.NodeId -> N.NodeId) (value: %s) : %s =\n    match value with\n%s"
        (mapperName ty) qname qname (String.Join("\n", lines))

let definitions =
    namedTypes
    |> List.mapi (fun i ty ->
        let prefix = if i = 0 then "let rec " else "and "
        let body =
            if ty = semanticKindType then
                "remapSemanticKind (remap: N.NodeId -> N.NodeId) (value: S.SemanticKind) : S.SemanticKind =\n    Clef.Compiler.Nanopass.FoldIn.remapKind remap (remapObligationInfo remap) value"
            elif FSharpType.IsRecord(ty, flags) then emitRecord ty
            else emitUnion ty
        prefix + body)

let sgLines =
    tempCounter <- 0
    sgFields |> Array.map (fun f ->
        let fname = escape f.Name
        if sgClearedFields.Contains f.Name then
            sprintf "        %s = None" fname
        elif sgUnchangedFields.Contains f.Name then
            sprintf "        %s = graph.%s" fname fname
        elif f.Name = "Edges" then
            "        Edges = remappedEdges"
        else
            let read = sprintf "graph.%s" fname
            let body = emitExpr f.PropertyType read |> Option.defaultValue read
            sprintf "        %s = %s" fname body)

let generated =
    String.concat "\n\n" (
        [ "// SPDX-License-Identifier: MIT"
          "// Generated by tools/PSGContract/GenerateNodeIdRemapper.fsx from SemanticGraph types."
          "// Pure Zone-A closed algebraic NodeId remapper; SemanticKind delegates to FoldIn.remapKind."
          "module internal Clef.Compiler.Nanopass.NodeIdRemap"
          "module S = Clef.Compiler.PSGSaturation.SemanticGraph.Types\nmodule N = Clef.Compiler.NativeTypedTree.NativeTypes" ]
        @ definitions
        @ [ sprintf "let remapGraphRoots (remap: N.NodeId -> N.NodeId) (remappedEdges: S.Hyperedge list) (graph: S.SemanticGraph) : S.SemanticGraph =\n    ({\n%s\n    } : S.SemanticGraph)" (String.Join("\n", sgLines)) ]
    ) + "\n"

match mode with
| "--preview" ->
    printfn "// Named NodeId-reaching types: %d" namedTypes.Length
    printfn "// Total lines: %d" (generated.Split('\n').Length)
| "--check" ->
    let existing = if File.Exists outputPath then File.ReadAllText outputPath else ""
    if existing <> generated then
        eprintfn "NodeIdRemap.fs is out of date with SemanticGraph types! Re-run GenerateNodeIdRemapper.fsx."
        exit 1
    else
        printfn "NodeIdRemap.fs matches exact closed SemanticGraph NodeId closure (%d named types; verified %d free leaf types + FoldIn.remapKind leaf cases)."
            namedTypes.Length (nodeIdFreeLeafTypeNames.Count + encounteredFreeLeaves.Count)
| _ ->
    File.WriteAllText(outputPath, generated)
    printfn "Wrote %s (%d named types, %d lines)." outputPath namedTypes.Length (generated.Split('\n').Length)
