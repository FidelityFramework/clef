# Record Type Infrastructure Design for FNCS

> **Status**: IMPLEMENTED (January 2, 2026)

## Date: 2026-01-02
## Status: SPEC UPDATED - Implementation Ready

**Key Update**: The fsnative-spec (inference-procedures.md) has been updated with the complete 
Field Label Resolution algorithm including memory layout computation. The algorithm is now 
grounded in:
- OCaml's "last in scope" + type-directed disambiguation
- F#'s intersection-based multi-field resolution  
- fsnative's deterministic memory layout principle ("Fidelity dictates; LLVM implements")

## Problem Statement

Record type inference requires architectural support that is currently missing from FNCS:
1. No `FieldLabels` table (spec requirement)
2. Record field information not stored with type definitions
3. Memory layout not computed from field layouts

## Spec Requirements

### From F# Spec (expressions.md:454-464) - THE ALGORITHM

The F# spec defines the exact algorithm for record type inference:

```
Each field-label_i is a long-ident which must resolve to a field F_i 
in a unique record type R as follows:

1. If field-label_i is a single identifier `fld` AND the initial type is known 
   to be a record type R<_, ..., _> that has field F_i with name `fld`, 
   then the field label resolves to F_i.

2. If field-label_i is NOT a single identifier OR if the initial type is a 
   variable type, then the field label is resolved by performing 
   Field Label Resolution. This procedure results in a set of fields FSet_i. 
   Each element of this set has a corresponding record type, thus resulting 
   in a set of record types RSet_i. 
   
   THE INTERSECTION OF ALL RSet_i MUST YIELD A SINGLE RECORD TYPE R,
   and each field then resolves to the corresponding field in R.

3. The set of fields must be COMPLETE. That is, each field in record type R 
   must have exactly one field definition.
```

### OCaml Design Principles (From Gallium/INRIA Research)

**Core Strategy:** "Last record in scope" as baseline, with type-directed disambiguation when type info is available.

**Multi-Label Disambiguation:** "Instead of looking up each label independently, they are all considered together and the selected type is the last record in scope which has ALL these labels."

**Principality:** Prefer solutions that can be expressed without type annotations. When ambiguity requires type propagation, consider emitting a warning.

**Error Strategy:** Provide clear diagnostics when:
- No record type has all specified fields
- Multiple record types have all specified fields (ambiguity)
- Fields are inaccessible

### From fsnative-spec (inference-procedures.md)

**FieldLabels Table:**
> a table that maps names to sets of field references for record types

**Field Label Resolution:**
> 1. Look up all fields in the Types table and FieldLabels table
> 2. Return the set of field declarations

### From fsnative-spec (native-type-universe.md:334)

**Memory Layout Principle:**
> Field order: Declaration order determines memory layout

**No GC Header:** Unlike OCaml's 8-byte block header, fsnative records have no header.

## Architecture Design

### Data Structures

```fsharp
/// A reference to a field in a specific record type
type FieldRef = {
    /// The record type this field belongs to
    RecordType: TypeConRef
    /// The field name
    FieldName: string
    /// The field's type
    FieldType: NativeType
    /// Position in declaration/memory order (0-based)
    FieldIndex: int
}

/// Complete record type information
type RecordTypeInfo = {
    /// The type constructor (with layout)
    TypeCon: TypeConRef
    /// Fields in declaration order (= memory order)
    Fields: (string * NativeType) list
    /// Module path where defined
    Module: ModulePath
    /// Whether type has [<RequireQualifiedAccess>]
    RequireQualifiedAccess: bool
}
```

### TypeEnv Extensions

```fsharp
type TypeEnv = {
    // Existing...
    TypeDefs: Map<string, TypeConRef>
    TypeAbbrevs: Map<string, NativeType>
    
    // NEW: Complete record definitions
    RecordDefs: Map<string, RecordTypeInfo>
    
    // NEW: Field label table (spec: _FieldLabels_)
    // Maps field name -> list of record types having that field
    FieldLabels: Map<string, FieldRef list>
}
```

### Layout Computation

Per spec: field order = memory layout. Layout must be computed from fields:

```fsharp
/// Compute memory layout for a record from its fields
let computeRecordLayout (fields: (string * NativeType) list) : TypeLayout =
    let folder (offset, maxAlign) (_, fieldType) =
        let fieldLayout = layoutOf fieldType
        match fieldLayout with
        | TypeLayout.Inline(size, align) ->
            // Add padding for alignment
            let paddedOffset = 
                if align > 0 && offset % align <> 0 
                then offset + (align - offset % align)
                else offset
            (paddedOffset + size, max maxAlign align)
        | TypeLayout.Opaque -> (offset, maxAlign)  // Unknown at compile time
        | TypeLayout.Reference _ -> (offset + 8, max maxAlign 8)  // Pointer size
    
    let (totalSize, maxAlign) = List.fold folder (0, 1) fields
    // Final padding to alignment
    let alignedSize = 
        if maxAlign > 0 && totalSize % maxAlign <> 0
        then totalSize + (maxAlign - totalSize % maxAlign)
        else totalSize
    TypeLayout.Inline(alignedSize, maxAlign)
```

### Field Label Resolution Algorithm

Per F# spec (expressions.md:454-464), following OCaml principles:

```fsharp
/// Result of field label resolution
type FieldResolutionResult =
    | Resolved of TypeConRef * RecordTypeInfo
    | Ambiguous of TypeConRef list  // Multiple candidate types
    | NoMatch of string list        // Fields that matched no type
    | Incomplete of TypeConRef * string list  // Missing required fields

/// Infer record type from field labels (F# spec algorithm)
let resolveRecordType 
    (fieldNames: string list) 
    (knownType: NativeType option)  // Type context if available
    (env: TypeEnv) 
    (range: SourceRange) 
    : Result<TypeConRef * RecordTypeInfo, Diagnostic> =
    
    // STEP 1: If initial type is known, use it directly (spec line 456-457)
    match knownType with
    | Some (NativeType.TRecord(tyCon, _)) ->
        match Map.tryFind tyCon.Name env.RecordDefs with
        | Some info -> Ok (tyCon, info)
        | None -> Error (mkDiag "FS8703" $"Record type {tyCon.Name} not found" range)
    | _ ->
        // STEP 2: Field Label Resolution (spec line 458-462)
        // For each field, get candidate record types
        let candidateSets = 
            fieldNames 
            |> List.map (fun name ->
                match Map.tryFind name env.FieldLabels with
                | Some refs -> 
                    refs 
                    |> List.map (fun r -> r.RecordType.Name) 
                    |> Set.ofList
                | None -> Set.empty)
        
        // Find fields with no matches (for error reporting)
        let unmatchedFields = 
            List.zip fieldNames candidateSets
            |> List.choose (fun (name, candidates) -> 
                if Set.isEmpty candidates then Some name else None)
        
        if not (List.isEmpty unmatchedFields) then
            Error (mkDiag "FS8701" 
                $"No record type found with field(s): {String.concat ", " unmatchedFields}" 
                range)
        else
            // INTERSECTION of all candidate sets (spec: "must yield a single record type")
            let intersection = 
                candidateSets 
                |> List.reduce Set.intersect
            
            match Set.count intersection with
            | 0 -> 
                Error (mkDiag "FS8704" 
                    "No single record type contains all specified fields" range)
            | 1 -> 
                let typeName = Set.minElement intersection
                match Map.tryFind typeName env.RecordDefs with
                | Some info -> 
                    // STEP 3: Check completeness (spec line 463)
                    let missingFields = 
                        info.Fields 
                        |> List.map fst 
                        |> List.filter (fun f -> not (List.contains f fieldNames))
                    if not (List.isEmpty missingFields) then
                        Error (mkDiag "FS8705"
                            $"Record {typeName} requires field(s): {String.concat ", " missingFields}"
                            range)
                    else
                        Ok (info.TypeCon, info)
                | None -> 
                    Error (mkDiag "FS8703" $"Record type {typeName} not found" range)
            | _ ->
                // AMBIGUITY - multiple types have all fields
                let typeNames = intersection |> String.concat ", "
                Error (mkDiag "FS8702"
                    $"Ambiguous record type. Could be: {typeNames}. Use type annotation." 
                    range)
```

### Error Codes (OCaml/F# Style)

| Code | Condition | Message |
|------|-----------|---------|
| FS8701 | Field not found in any record | "No record type found with field(s): {fields}" |
| FS8702 | Multiple record types match | "Ambiguous record type. Could be: {types}. Use type annotation." |
| FS8703 | Record type lookup failed | "Record type {name} not found" |
| FS8704 | No intersection | "No single record type contains all specified fields" |
| FS8705 | Incomplete record | "Record {type} requires field(s): {fields}" |

## Implementation Plan

1. **Add data structures** to `NativeTypes.fs`:
   - `FieldRef` type
   - `RecordTypeInfo` type

2. **Extend TypeEnv** in `CheckExpressions.fs`:
   - Add `RecordDefs: Map<string, RecordTypeInfo>`
   - Add `FieldLabels: Map<string, FieldRef list>`
   - Add helper functions: `addRecordDef`, `addFieldLabels`

3. **Add layout computation** to `NativeTypes.fs`:
   - `computeRecordLayout` function

4. **Update record definition processing** in `NativeService.fs`:
   - Extract field info from `SynField`
   - Check field types
   - Compute layout
   - Populate RecordDefs and FieldLabels

5. **Implement record type inference** in `CheckExpressions.fs`:
   - `inferRecordTypeFromFields` function
   - Update `SynExpr.Record` handling to use it

## Error Codes

| Code | Message |
|------|---------|
| FS8700 | Empty record expression |
| FS8701 | No record type found with fields: {fields} |
| FS8702 | Ambiguous record type. Could be: {types}. Use type annotation to disambiguate. |

## Cross-References

- `native_type_checker_architecture` - Overall FNCS architecture
- `native_type_universe_structural` - Record type spec
- `fncs_fsnative_spec_audit` - Spec compliance audit
