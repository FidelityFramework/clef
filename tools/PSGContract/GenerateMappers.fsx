// Generates the structural mappers from CCS publication types to the published
// PSG contract (Fidelity.PSG). The generated file is explicit F#: every mapped
// type, case and field is visible in it and checked by the compiler.
//
// A contract type with no CCS twin, or whose cases or fields differ from its
// twin, stops generation with the difference named. The sole native-only case,
// ObligationBody.Pending, generates an explicit refusal instead of a value.
//
// usage: dotnet fsi GenerateMappers.fsx <Clef.Compiler.Service.dll> <Fidelity.PSG.dll> <output.fs>

open System
open System.IO
open System.Reflection
open Microsoft.FSharp.Reflection

let ccsPath, contractPath, outputPath =
    match fsi.CommandLineArgs |> Array.toList with
    | [ _; ccs; contract; output ] -> ccs, contract, output
    | _ -> failwith "usage: dotnet fsi GenerateMappers.fsx <Clef.Compiler.Service.dll> <Fidelity.PSG.dll> <output.fs>"

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

/// Contract types assembled by hand in RevisionPublication.fs.
let assembledByHand =
    set [ "SemanticNode"; "Revision"; "RevisionHeader"; "Codata"; "PlatformWidths"; "IntegrityViolation"
          "BorrowedViewLayout"; "BorrowedViewOperation"; "MmioOperation"
          "ForeignStorageProjection"; "EagerDemandRelation"; "ExplicitDemandProjection"
          "NodeId" ]

/// CCS modules whose declarations are published, with the alias the output uses.
let sourceModules =
    [ "Clef.Compiler.PSGSaturation.SemanticGraph.Types", "S"
      "Clef.Compiler.NativeTypedTree.NativeTypes", "N"
      "Clef.Compiler.NativeTypedTree.DimensionAlgebra", "D" ]

let isData (t: Type) = FSharpType.IsRecord(t, flags) || FSharpType.IsUnion(t, flags)

let contractTypes =
    contract.GetTypes()
    |> Array.filter (fun t -> t.Namespace = "Fidelity.PSG" && not t.IsNested && isData t && not t.IsGenericType)
    |> Array.filter (fun t -> not (assembledByHand.Contains t.Name))
    |> Array.sortBy (fun t -> t.Name)

let twins =
    contractTypes
    |> Array.map (fun target ->
        let found =
            sourceModules |> List.tryPick (fun (moduleName, alias) ->
                let owner = ccs.GetType(moduleName, false)
                if isNull owner then None
                else
                    owner.GetNestedTypes(flags)
                    |> Array.tryFind (fun nested -> nested.Name = target.Name && isData nested)
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

let isGeneric (definition: Type) (t: Type) = t.IsGenericType && t.GetGenericTypeDefinition() = definition

/// The expression converting `value` from its CCS type to the contract type, or
/// None where the two are the same type and the value crosses unchanged.
let rec convert (path: string) (source: Type) (target: Type) (value: string) : string option =
    if source = nativeType then
        if target.Name <> "TypeIdentity" then failwithf "%s: a native type may only be published as a type identity, not %s" path target.Name
        Some (sprintf "freeze %s" value)
    elif source = sourceNodeId then
        Some (sprintf "nodeId %s" value)
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
    let unpublished =
        sources.Keys |> Seq.filter (fun name -> targets |> Array.forall (fun field -> field.Name <> name)) |> Seq.toList
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
      "// the published contract (Fidelity.PSG). Regenerate after either changes; do not edit."
      ""
      "/// Structural transcription of CCS publication values into the published contract."
      "/// Each function copies one value field by field. None of them analyses, selects or repairs."
      "module Clef.Compiler.PSGSaturation.Publication.RevisionMappers"
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
      "" ]

File.WriteAllText(outputPath, String.Join("\n", header) + body + "\n" + String.Join("\n", freeze))
printfn "Generated %d mappers into %s" mappers.Length outputPath
