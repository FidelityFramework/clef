// Generates the structural mappers from CCS publication types to the published
// PSG contract (Fidelity.PSG). The generated file is explicit F#: every mapped
// type, case and field is visible in it and checked by the compiler.
//
// An unclassified contract type, or an undeclared case/field difference,
// stops generation with the difference named. Explicit contract-only types
// and native-only record fields are
// listed and type-checked below. The native-only ObligationBody.Pending case
// generates an explicit refusal instead of a value.
//
// usage: dotnet fsi GenerateMappers.fsx [--check|--preview] <Clef.Compiler.Service.dll> <Fidelity.PSG.dll> <output.fs>

open System
open System.IO
open System.Reflection
open Microsoft.FSharp.Reflection

let mode, ccsPath, contractPath, outputPath =
    match fsi.CommandLineArgs |> Array.toList with
    | [ _; ccs; contract; output ] -> "write", ccs, contract, output
    | [ _; ("--check" | "--preview" as mode); ccs; contract; output ] -> mode, ccs, contract, output
    | _ -> failwith "usage: dotnet fsi GenerateMappers.fsx [--check|--preview] <Clef.Compiler.Service.dll> <Fidelity.PSG.dll> <output.fs>"

let probe = [ Path.GetDirectoryName ccsPath; Path.GetDirectoryName contractPath ]
AppDomain.CurrentDomain.add_AssemblyResolve(ResolveEventHandler(fun _ args ->
    let name = AssemblyName(args.Name).Name + ".dll"
    probe
    |> List.map (fun directory -> Path.Combine(directory, name))
    |> List.tryFind File.Exists
    |> Option.map Assembly.LoadFrom
    |> Option.toObj))

let ccs = Assembly.LoadFrom ccsPath
let contract = Assembly.LoadFrom contractPath

let flags = BindingFlags.Public ||| BindingFlags.NonPublic

/// Immutable leaf rows assembled by typed Baker recipes. The compiler checks
/// their record construction and exhaustive source-case mappings separately.
let assembledByHand =
    set [ "SemanticNode"; "Revision"; "RevisionHeader"; "Codata"; "PlatformWidths"; "IntegrityViolation"
          "BorrowedViewLayout"; "BorrowedViewOperation"; "MmioOperation"
          "ForeignStorageProjection"; "EagerDemandRelation"; "ExplicitDemandProjection"
          "WitnessSourceReadings"; "ChildDisposition"; "ChildTraversal"; "SupportKey"
          "NodeId" ]

/// Contract/receiver/transport authority has no native semantic-graph twin.
/// This is an explicit closed set: a new public contract type requires review.
let contractOnly =
    set [ "ArtifactHandle"; "ArtifactOwner"; "ArtifactOwnershipTransition"
          "BinaryError"; "BinaryLimits"; "BoundaryContractStamp"; "CheckedRevisionId"
          "DeliveryCursor"; "HistoricalNodeIdentity"; "LiveOccurrence"; "LiveOccurrenceSection"
          "LiveOccurrenceViolation"; "OccurrenceDelivery"; "OccurrenceDeliveryViolation"
          "ScopeAuthorization"; "ScopeChange"; "ScopeContentStamp"; "ScopeDescriptor"
          "ScopedCatalog"; "ScopedPublicationError"; "SourceScopeTransaction"; "SupportStamp" ]

/// Source-prefixed facts whose fields/cases remain structural twins. Renaming
/// does not bypass the same record-field and union-case checks as ordinary twins.
let renamedTwins =
    Map.ofList [ "BindingUseContract", "WitnessBindingUseContract"
                 "OccurrenceBreadcrumb", "WitnessOccurrenceBreadcrumb"
                 "OccurrencePort", "WitnessOccurrencePort"
                 "SourceBindingClass", "WitnessBindingClass"
                 "SourceContextHeader", "WitnessSourceContextHeader"
                 "SourceEntryReason", "WitnessEntryReason"
                 "SourcePortAccount", "WitnessSourcePortAccount"
                 "SourceWitnessEntry", "WitnessSourceEntry" ]

/// CCS modules whose declarations are published, with the alias the output uses.
let sourceModules =
    [ "Clef.Compiler.PSGSaturation.SemanticGraph.Types", "S"
      "Clef.Compiler.NativeTypedTree.NativeTypes", "N"
      "Clef.Compiler.NativeTypedTree.DimensionAlgebra", "D" ]

let isData (t: Type) = FSharpType.IsRecord(t, flags) || FSharpType.IsUnion(t, flags)

let allContractTypes =
    contract.GetTypes()
    |> Array.filter (fun t -> t.Namespace = "Fidelity.PSG" && not t.IsNested && isData t && not t.IsGenericType)
    |> Array.sortBy (fun t -> t.Name)

let contractNames = allContractTypes |> Array.map _.Name |> Set.ofArray
for name in Set.unionMany [assembledByHand; contractOnly; renamedTwins.Keys |> Set.ofSeq] do
    if not (contractNames.Contains name) then failwithf "Declared contract policy %s no longer names a public contract data type" name
if not (Set.intersect assembledByHand contractOnly).IsEmpty then failwith "Manual and contract-only policies overlap"
let contractTypes =
    allContractTypes |> Array.filter (fun t -> not (assembledByHand.Contains t.Name || contractOnly.Contains t.Name))

let twins =
    contractTypes
    |> Array.map (fun target ->
        let found =
            sourceModules |> List.tryPick (fun (moduleName, alias) ->
                let owner = ccs.GetType(moduleName, false)
                if isNull owner then None
                else
                    owner.GetNestedTypes(flags)
                    |> Array.tryFind (fun nested -> nested.Name = (renamedTwins.TryFind target.Name |> Option.defaultValue target.Name) && isData nested)
                    |> Option.map (fun source -> source, alias))
        match found with
        | Some (source, alias) -> target, source, alias
        | None -> failwithf "Contract type %s has no CCS twin in %A" target.Name (List.map fst sourceModules))

let twinOf = twins |> Array.map (fun (target, source, alias) -> source.FullName, (target, alias)) |> dict
let mapper (target: Type) = "map" + target.Name
let sourceName (source: Type) alias = alias + "." + source.Name
let targetName (target: Type) = "Fidelity.PSG." + target.Name

let nativeType = ccs.GetType("Clef.Compiler.NativeTypedTree.NativeTypes+NativeType", true)
let sourceNodeId = ccs.GetType("Clef.Compiler.NativeTypedTree.NativeTypes+NodeId", true)
let sourceSupport = ccs.GetType("Clef.Compiler.PSGSaturation.SemanticGraph.Types+WitnessScopeSupport", true)
let sourceSupportPolicy = ccs.GetType("Clef.Compiler.PSGSaturation.SemanticGraph.Types+WitnessScopeSupportPolicy", true)
let targetSupport = contract.GetType("Fidelity.PSG.SupportKey", true)
let supportFields = FSharpType.GetRecordFields(sourceSupport, flags) |> Array.map (fun field -> field.Name, field.PropertyType) |> Array.sortBy fst
if supportFields <> [| "Identity", typeof<string>; "Policy", sourceSupportPolicy |] then
    failwith "Whole-owner support record changed; review its explicit publication policy"
match FSharpType.GetUnionCases(sourceSupportPolicy, flags) with
| [| policy |] when policy.Name = "WholePreparedOwner" && policy.GetFields().Length = 0 -> ()
| _ -> failwith "Native support policy changed; review its explicit publication mapping"
match FSharpType.GetUnionCases(targetSupport, flags) |> Array.tryFind (fun case -> case.Name = "WholeOwningAnalysisRegion") with
| Some whole when whole.GetFields() |> Array.map _.PropertyType = [| typeof<string> |] -> ()
| _ -> failwith "Published whole-owner support changed its identity contract"

/// Baker's freshness guards are checked by NumericPublication before projection;
/// they are not published numeric facts. Keep each exclusion explicit and typed:
/// removing, changing or publishing one requires reviewing this policy too.
let nativeOnlyRecordFields =
    let semanticType name = ccs.GetType("Clef.Compiler.PSGSaturation.SemanticGraph.Types+" + name, true)
    let listOf element = typedefof<list<_>>.MakeGenericType [| element |]
    let optionOf element = typedefof<option<_>>.MakeGenericType [| element |]
    dict [
        "Clef.Compiler.PSGSaturation.SemanticGraph.Types+NumericDomain",
        [ "RequiresFiniteCellReview", typeof<bool>
          "FiniteCellRelations", optionOf (listOf (semanticType "FiniteCellSourceRelation"))
          "FiniteCellObligations", listOf (FSharpType.MakeTupleType [| sourceNodeId; semanticType "ObligationInfo" |])
          "RequiresSequenceReview", typeof<bool>
          "SequenceRangeAuthority", optionOf (semanticType "SequenceRangeAuthority")
          "RangeContextFacts", optionOf (semanticType "RangeContextFacts")
          "RequiresCaptureReview", typeof<bool>
          "CaptureRelations", listOf (FSharpType.MakeTupleType [| semanticType "EdgeClass"; typeof<bool>; typeof<int>; listOf sourceNodeId; sourceNodeId |]) ]
    ]

for sourceName in nativeOnlyRecordFields.Keys do
    if not (twins |> Array.exists (fun (target, source, _) ->
        source.FullName = sourceName && FSharpType.IsRecord(target, flags) && FSharpType.IsRecord(source, flags))) then
        failwithf "Native-only record policy %s has no mapped CCS record" sourceName

let isGeneric (definition: Type) (t: Type) = t.IsGenericType && t.GetGenericTypeDefinition() = definition

/// The expression converting `value` from its CCS type to the contract type, or
/// None where the two are the same type and the value crosses unchanged.
let rec convert (path: string) (source: Type) (target: Type) (value: string) : string option =
    if source = nativeType then
        if target.Name <> "TypeIdentity" then failwithf "%s: a native type may only be published as a type identity, not %s" path target.Name
        Some (sprintf "freeze %s" value)
    elif source = sourceNodeId then
        Some (sprintf "nodeId %s" value)
    elif source = sourceSupport then
        if target <> targetSupport then failwithf "%s: source support has no mapping as %s" path target.Name
        Some (sprintf "mapWitnessScopeSupport %s" value)
    elif twinOf.ContainsKey source.FullName then
        let expected, _ = twinOf.[source.FullName]
        if expected <> target then failwithf "%s: %s is published as %s, not %s" path source.Name expected.Name target.Name
        Some (sprintf "%s %s" (mapper expected) value)
    elif source = target then None
    elif FSharpType.IsTuple source && FSharpType.IsTuple target then
        let sources = FSharpType.GetTupleElements source
        let targets = FSharpType.GetTupleElements target
        if sources.Length <> targets.Length then failwithf "%s: tuple arity differs" path
        let names = sources |> Array.mapi (fun index _ -> sprintf "t%d" index)
        let converted = Array.map3 (fun s t name -> convert path s t name |> Option.defaultValue name) sources targets names
        Some (sprintf "(let (%s) = %s in (%s))" (String.Join(", ", names)) value (String.Join(", ", converted)))
    elif source.IsGenericType && target.IsGenericType
         && source.GetGenericTypeDefinition() = target.GetGenericTypeDefinition() then
        let sources = source.GetGenericArguments()
        let targets = target.GetGenericArguments()
        let element index = convert path sources.[index] targets.[index] "x"
        let orSame index = element index |> Option.defaultValue "x"
        let definition = source.GetGenericTypeDefinition()
        if definition = typedefof<list<_>> then
            element 0 |> Option.map (fun body -> sprintf "(%s |> List.map (fun x -> %s))" value body)
        elif definition = typedefof<option<_>> then
            element 0 |> Option.map (fun body -> sprintf "(%s |> Option.map (fun x -> %s))" value body)
        elif definition = typedefof<Set<_>> then
            element 0 |> Option.map (fun body -> sprintf "(%s |> Set.map (fun x -> %s))" value body)
        elif definition = typedefof<Map<_, _>> then
            match element 0, element 1 with
            | None, None -> None
            | None, Some body -> Some (sprintf "(%s |> Map.map (fun _ x -> %s))" value body)
            | Some _, _ ->
                let key = convert path sources.[0] targets.[0] "k" |> Option.defaultValue "k"
                let item = convert path sources.[1] targets.[1] "v" |> Option.defaultValue "v"
                Some (sprintf "(%s |> Map.toSeq |> Seq.map (fun (k, v) -> %s, %s) |> Map.ofSeq)" value key item)
        elif definition = typedefof<Result<_, _>> then
            match element 0, element 1 with
            | None, None -> None
            | _ ->
                Some (sprintf "(match %s with Ok x -> Ok (%s) | Error x -> Error (%s))" value (orSame 0) (orSame 1))
        else failwithf "%s: no published form for the generic type %s" path source.FullName
    elif source.IsArray && target.IsArray then
        convert path (source.GetElementType()) (target.GetElementType()) "x"
        |> Option.map (fun body -> sprintf "(%s |> Array.map (fun x -> %s))" value body)
    else
        failwithf "%s: %s has no published form as %s" path source.FullName target.FullName

let keyword = set [ "type"; "val"; "module"; "end"; "to"; "begin"; "done"; "rec"; "fixed"; "base"; "global"; "namespace"; "params"; "process"; "component"; "const"; "include"; "parallel"; "pure"; "sig"; "trait"; "virtual"; "checked"; "function"; "member"; "default" ]
let escape (name: string) = if keyword.Contains name then "``" + name + "``" else name

let recordMapper (target: Type) (source: Type) alias =
    let sources = FSharpType.GetRecordFields(source, flags) |> Array.map (fun field -> field.Name, field) |> dict
    let targets = FSharpType.GetRecordFields(target, flags)
    let nativeOnly =
        match nativeOnlyRecordFields.TryGetValue source.FullName with
        | true, fields ->
            for name, expected in fields do
                if not (sources.ContainsKey name) then
                    failwithf "Record %s: declared native-only field %s has no CCS field" target.Name name
                if sources.[name].PropertyType <> expected then
                    failwithf "Record %s: native-only field %s changed type from %s to %s"
                        target.Name name expected.FullName sources.[name].PropertyType.FullName
                if targets |> Array.exists (fun field -> field.Name = name) then
                    failwithf "Record %s: declared native-only field %s now has a published field" target.Name name
            fields |> List.map fst |> Set.ofList
        | _ -> Set.empty
    let unpublished =
        sources.Keys
        |> Seq.filter (fun name -> not (nativeOnly.Contains name) && (targets |> Array.forall (fun field -> field.Name <> name)))
        |> Seq.toList
    if not unpublished.IsEmpty then
        failwithf "Record %s: CCS fields %A have no published field" target.Name unpublished
    let fields =
        targets |> Array.map (fun field ->
            if not (sources.ContainsKey field.Name) then
                failwithf "Record %s: published field %s has no CCS field" target.Name field.Name
            let path = sprintf "%s.%s" target.Name field.Name
            let read = sprintf "value.%s" (escape field.Name)
            let body = convert path sources.[field.Name].PropertyType field.PropertyType read |> Option.defaultValue read
            sprintf "        %s = %s" (escape field.Name) body)
    sprintf "%s (value: %s) : %s =\n    ({\n%s\n    } : %s)"
        (mapper target) (sourceName source alias) (targetName target) (String.Join("\n", fields)) (targetName target)

let unionMapper (target: Type) (source: Type) alias =
    let sources = FSharpType.GetUnionCases(source, flags)
    let targets = FSharpType.GetUnionCases(target, flags) |> Array.map (fun case -> case.Name, case) |> dict
    let missing = targets.Keys |> Seq.filter (fun name -> sources |> Array.forall (fun case -> case.Name <> name)) |> Seq.toList
    if not missing.IsEmpty then failwithf "Union %s: published cases %A have no CCS case" target.Name missing
    let cases =
        sources |> Array.map (fun case ->
            if target.Name = "ObligationBody" && case.Name = "Pending" then
                let fields = case.GetFields()
                if targets.ContainsKey "Pending" || fields.Length <> 1 || fields[0].PropertyType <> typeof<string list> then
                    failwith "Pending obligations must remain a native-only list of missing-premise reasons"
                sprintf "    | %s.Pending reasons -> invalidOp (\"A pending obligation cannot be published: \" + String.concat \"; \" reasons)" (sourceName source alias)
            else
                if not (targets.ContainsKey case.Name) then
                    failwithf "Union %s: CCS case %s has no published case" target.Name case.Name
                let published = targets.[case.Name]
                let sourceFields = case.GetFields()
                let targetFields = published.GetFields()
                if sourceFields.Length <> targetFields.Length then
                    failwithf "Union %s.%s: field count differs" target.Name case.Name
                if sourceFields.Length = 0 then
                    sprintf "    | %s.%s -> %s.%s" (sourceName source alias) case.Name (targetName target) case.Name
                else
                    let names = sourceFields |> Array.mapi (fun index _ -> sprintf "a%d" index)
                    let converted =
                        Array.map3 (fun (s: PropertyInfo) (t: PropertyInfo) name ->
                            convert (sprintf "%s.%s" target.Name case.Name) s.PropertyType t.PropertyType name
                            |> Option.defaultValue name) sourceFields targetFields names
                    sprintf "    | %s.%s(%s) -> %s.%s(%s)"
                        (sourceName source alias) case.Name (String.Join(", ", names))
                        (targetName target) case.Name (String.Join(", ", converted)))
    sprintf "%s (value: %s) : %s =\n    match value with\n%s"
        (mapper target) (sourceName source alias) (targetName target) (String.Join("\n", cases))

let mappers =
    twins |> Array.map (fun (target, source, alias) ->
        if FSharpType.IsRecord(target, flags) then
            if not (FSharpType.IsRecord(source, flags)) then failwithf "%s is a record only in the contract" target.Name
            recordMapper target source alias
        else
            if not (FSharpType.IsUnion(source, flags)) then failwithf "%s is a union only in the contract" target.Name
            unionMapper target source alias)

let header =
    [ "// Generated by tools/PSGContract/GenerateMappers.fsx from the CCS publication types and"
      "// the published contract (Fidelity.PSG). Review --preview, then regenerate this block."
      ""
      "/// Baker freezes selected source facts into immutable PSG leaf rows. Native"
      "/// checker substitutions are observed here, before passive publication."
      "module Clef.Compiler.Baker.Ingredients.PublishedFactRows"
      ""
      "module S = Clef.Compiler.PSGSaturation.SemanticGraph.Types"
      "module N = Clef.Compiler.NativeTypedTree.NativeTypes"
      "module D = Clef.Compiler.NativeTypedTree.DimensionAlgebra"
      ""
      "let nodeId (N.NodeId value) : Fidelity.PSG.NodeId ="
      "    Fidelity.PSG.NodeId value"
      "" ]

let body =
    mappers
    |> Array.mapi (fun index text -> (if index = 0 then "let rec " else "and ") + text)
    |> fun all -> String.Join("\n\n", all)

let freeze =
    [ ""
      "/// A checker type crosses as its identity, with the current substitution applied."
      "and freeze (value: N.NativeType) : Fidelity.PSG.TypeIdentity ="
      "    mapTypeIdentity (Clef.Compiler.NativeTypedTree.TypeIdentities.ofType value)"
      ""
      "/// The source policy is explicit; this stamp grants no accepted proof authority."
      "and mapWitnessScopeSupport (value: S.WitnessScopeSupport) : Fidelity.PSG.SupportKey ="
      "    match value.Policy with"
      "    | S.WitnessScopeSupportPolicy.WholePreparedOwner -> Fidelity.PSG.SupportKey.WholeOwningAnalysisRegion value.Identity"
      "" ]

let generated = String.Join("\n", header) + body + "\n" + String.Join("\n", freeze)
let boundary = "// END GENERATED MAPPERS; typed Baker source-reading assembly follows."
if mode = "--preview" then
    File.WriteAllText(outputPath, generated + boundary + "\n")
    printfn "Previewed %d structural mappers into %s; no handwritten assembly copied" mappers.Length outputPath
else
    let existing = File.ReadAllText outputPath
    let split = existing.IndexOf(boundary, StringComparison.Ordinal)
    if split < 0 || existing.LastIndexOf(boundary, StringComparison.Ordinal) <> split then
        failwith "The mapper file must contain exactly one generated/manual boundary; refusing to erase handwritten assembly"
    if mode = "--check" then
        if existing.Substring(0, split) <> generated then
            failwithf "Generated structural mapper block differs from %s; review --preview before updating" outputPath
        printfn "Checked %d structural mappers; typed handwritten assembly remains outside generation" mappers.Length
    else
        File.WriteAllText(outputPath, generated + existing.Substring split)
        printfn "Generated %d structural mappers; preserved handwritten assembly in %s" mappers.Length outputPath
