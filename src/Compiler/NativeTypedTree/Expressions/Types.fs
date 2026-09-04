// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Type checking environment and helpers for Clef expression checking.
module Clef.Compiler.NativeTypedTree.Expressions.Types

open Clef.Compiler.Syntax
open Clef.Compiler.Text
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.NativeTypedTree.MeasureEnvironment
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

// Module aliases for qualified access
module NativeTypes = Clef.Compiler.NativeTypedTree.NativeTypes
module NR = Clef.Compiler.NativeTypedTree.NameResolution

//-------------------------------------------------------------------------
// Polymorphic Instantiation
//-------------------------------------------------------------------------

/// Instantiate a TForall type with fresh type variables.
/// This is critical for proper polymorphic type checking:
/// each use of a polymorphic binding must get FRESH type variables,
/// not the same ones (which would cause all uses to share one type).
let instantiateTForall (ty: NativeType) (range: SourceRange) : NativeType =
    match ty with
    | NativeType.TForall(typars, body) ->
        let freshVars = typars |> List.map (fun tp -> NativeType.TVar (freshTypeParamAuto tp.Kind range))
        NativeTypes.instantiate typars freshVars body
    | _ -> ty

//-------------------------------------------------------------------------
// Clef Diagnostic Codes (FS8xxx series)
//-------------------------------------------------------------------------

/// Error codes for Clef specific diagnostics.
/// These follow the FS8xxx range to distinguish from standard F# errors.
module DiagnosticCodes =
    // Type system (FS8000-FS8099)
    let FS8000_TypeMismatch = "FS8000"
    let FS8010_NullNotSupported = "FS8010"
    let FS8011_ObjNotSupported = "FS8011"
    let FS8012_BoxingNotSupported = "FS8012"
    let FS8013_DynamicNotSupported = "FS8013"

    // Null-freedom (FS8100-FS8199)
    let FS8100_NullLiteral = "FS8100"
    let FS8101_UninitializedValue = "FS8101"
    let FS8102_ExceptionPattern = "FS8102"
    let FS8103_TypeDoesNotSupportNull = "FS8103"
    let FS8104_UncheckedDefault = "FS8104"

    // Memory management (FS8200-FS8299)
    let FS8200_LifetimeError = "FS8200"
    let FS8201_RegionMismatch = "FS8201"
    let FS8202_EscapingReference = "FS8202"

    // Platform bindings (FS8300-FS8399)
    let FS8300_PlatformBindingError = "FS8300"
    let FS8301_UnsupportedPlatformOperation = "FS8301"

    // Code generation (FS8400-FS8499)
    let FS8400_CodeGenError = "FS8400"
    let FS8401_UnsupportedConstruct = "FS8401"

    // BCL rejection (FS8500-FS8599)
    // BCL types/namespaces are NEVER allowed in Clef
    let FS8500_BclReferenceNotAllowed = "FS8500"
    let FS8501_SystemNamespaceNotAllowed = "FS8501"
    let FS8502_MicrosoftNamespaceNotAllowed = "FS8502"

    // Platform binding resolution (FS8600-FS8699)
    let FS8600_PlatformBindingUndefined = "FS8600"

    // Record type resolution (FS8700-FS8799)
    // Per clef-lang-spec: Field Label Resolution Algorithm error codes
    let FS8701_NoFields = "FS8701"
    let FS8702_UndefinedField = "FS8702"
    let FS8703_ConflictingFields = "FS8703"
    let FS8704_AmbiguousFields = "FS8704"
    let FS8705_MissingFields = "FS8705"

    // Constraint-related errors (FS8710-FS8719)
    let FS8710_NullConstraint = "FS8710"
    let FS8711_UnsupportedConstraint = "FS8711"

    // Generic/fallback
    let FS0001_GenericError = "FS0001"
    let FS0002_GenericWarning = "FS0002"

    // CCS series, type system, width and seals (CCS8000-CCS8099):
    // docs/fidelity/phg/Dimensional_Step1_2_Design.md (f); allocation rule in the Plan's D3.
    let CCS8018_UnsupportedLiteralSuffix = "CCS8018"

    // CCS series, units of measure (CCS8040-CCS8050): design (f). CCS8040 and CCS8041 are minted
    // by the unifier when `solveDim` fails (CS-4); the rest by the measure environment and the
    // measure-syntax translator below, through `describeMeasureFailure`. CCS8047 is CS-6's.
    let CCS8040_MeasureMismatch = "CCS8040"
    let CCS8041_NoIntegerSolution = "CCS8041"
    let CCS8042_MeasureNotInScope = "CCS8042"
    let CCS8043_CyclicMeasureAbbreviation = "CCS8043"
    let CCS8044_MeasureVariableInLiteral = "CCS8044"
    let CCS8045_MeasureSortMismatch = "CCS8045"
    let CCS8046_NoDimension = "CCS8046"
    let CCS8048_RationalMeasureExponent = "CCS8048"
    let CCS8049_ParameterisedMeasureDefinition = "CCS8049"
    let CCS8050_MeasureArityMismatch = "CCS8050"

//-------------------------------------------------------------------------
// Type Environment
//-------------------------------------------------------------------------

/// The type checking environment
[<NoComparison; NoEquality>]
type TypeEnv = {
    /// Compositional name resolution context
    /// BCL is structurally impossible - only source-defined bindings exist
    Resolution: NR.ResolutionContext
    /// Type definitions (name -> TypeConRef)
    TypeDefs: Map<string, TypeConRef>
    /// Type abbreviations (name -> NativeType it expands to)
    TypeAbbrevs: Map<string, NativeType>
    /// The declared measures and their expansions (design a.3). Empty in every environment this
    /// changeset builds: the `[<Measure>] type` declaration arm in NativeService.fs is not yet
    /// redirected here (sequence CS-4), so declarations still fall through to `TypeDefs`.
    Measures: MeasureEnv
    /// Record type definitions with full field information
    /// Per spec: "Field order determines memory layout"
    RecordDefs: Map<string, RecordTypeInfo>
    /// Field label table for record type inference
    /// Per spec (inference-procedures.md): "maps names to sets of field references"
    FieldLabels: Map<string, FieldRef list>
    /// Current constraints being collected (ref cell to share across record copies)
    Constraints: Constraint list ref
    /// Accumulated diagnostics (errors, warnings) (ref cell to share across record copies)
    Diagnostics: Diagnostic list ref
    /// Current arena affinity
    CurrentArena: ArenaAffinity
    /// Enclosing function return type (for return checking)
    ExpectedReturnType: NativeType option
    /// Enclosing function name for nested bindings (None at module level)
    /// PRD-13: Used to qualify nested function names for MLIR emission
    EnclosingFunction: string option
    /// Enclosing seq expression (for yield checking)
    /// PRD-15: Used to track which sequence a yield belongs to
    EnclosingSeqExpr: NodeId option
}

//-------------------------------------------------------------------------
// CheckExpr Callback Type
//-------------------------------------------------------------------------

/// Type alias for the recursive checkExpr function.
/// Handler modules receive this as a parameter to enable recursive checking.
type CheckExprFn = TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode

/// Type alias for checking a match clause.
type CheckMatchClauseFn = TypeEnv -> NodeBuilder -> NativeType -> NativeType -> SynMatchClause -> MatchCase

/// Type alias for checking a pattern.
type CheckPatternFn = TypeEnv -> SynPat -> NativeType -> SourceRange -> Pattern * (string * NativeType) list

/// Type alias for checking let/use bindings.
type CheckLetOrUseFn = TypeEnv -> NodeBuilder -> SynLetOrUse -> SourceRange -> SemanticNode

/// Type alias for building lambda nodes.
type BuildLambdaNodeFn = TypeEnv -> NodeBuilder -> (string * NativeType) list -> SynExpr -> SourceRange -> SemanticNode

/// Type alias for extracting lambda parameters.
type ExtractLambdaParamsFn = TypeEnv -> SynSimplePats -> SourceRange -> (string * NativeType) list

/// Record holding all mutually recursive checker functions.
/// This enables handler modules to call any checker function they need.
type CheckerCallbacks = {
    CheckExpr: CheckExprFn
    CheckMatchClause: CheckMatchClauseFn
    CheckPattern: CheckPatternFn
    CheckLetOrUse: CheckLetOrUseFn
    BuildLambdaNode: BuildLambdaNodeFn
    ExtractLambdaParams: ExtractLambdaParamsFn
}

//-------------------------------------------------------------------------
// Built-in DU TypeConRefs
// Module-level so both createTypeEnv (constructor registration) and
// tryResolveBuiltinTypeConstructor (type annotation resolution) share the
// same canonical TypeConRef instances.
//-------------------------------------------------------------------------

/// Canonical TypeConRef for option<'T>.
let internal optionTycon  : TypeConRef = mkTypeConRef "option"  1 TypeLayout.Opaque
/// Canonical TypeConRef for voption<'T>.
let internal voptionTycon : TypeConRef = mkTypeConRef "voption" 1 TypeLayout.Opaque
/// Canonical TypeConRef for Result<'T,'E>. Capital R — matches F# annotation syntax.
let internal resultTycon  : TypeConRef = mkTypeConRef "Result"  2 TypeLayout.Opaque

//-------------------------------------------------------------------------
// Environment Creation
//-------------------------------------------------------------------------

/// Create a type environment, pre-populated with built-in DU constructors.
/// option<'T>, voption<'T>, and Result<'T,'E> constructors are registered here
/// so that unqualified `Some`, `None`, `Ok`, `Error`, `ValueSome`, `ValueNone`
/// resolve to properly-typed UnionCase nodes. Each use site gets fresh type
/// variables via instantiateTForall, so the PSG carries concrete TApp types
/// (e.g. TApp(option_tycon, [TVar ?fresh])) rather than bare unbound TVars.
let createTypeEnv () : TypeEnv =
    let baseEnv = {
        Resolution = NR.createContext ()
        TypeDefs = Map.empty
        TypeAbbrevs = Map.empty
        Measures = MeasureEnv.empty
        RecordDefs = Map.empty
        FieldLabels = Map.empty
        Constraints = ref []
        Diagnostics = ref []
        CurrentArena = ArenaAffinity.CurrentActor
        ExpectedReturnType = None
        EnclosingFunction = None
        EnclosingSeqExpr = None
    }
    // Inline registration: mirrors addUnionCaseBinding without forward-reference.
    let mkDU name ty caseIndex env =
        let caseInfo: NR.UnionCaseInfo = { CaseName = name; UnionType = ty; CaseIndex = caseIndex }
        let binding: NR.ResolvedBinding = {
            QualifiedName = name; Type = ty; IsMutable = false; NodeId = None
            InlineBody = None; UnionCaseInfo = Some caseInfo; NativeLiteral = None; IsModuleLevel = true }
        { env with Resolution = NR.registerBinding name binding env.Resolution }
    // option: None : option<'T>   Some : 'T -> option<'T>
    let optA   = freshTypeParamAuto TypeParamKind.Type dummyRange
    let optATy = NativeType.TVar optA
    let optionTy = NativeType.TApp(optionTycon, [optATy])
    // voption: ValueNone : voption<'T>   ValueSome : 'T -> voption<'T>
    let voptA   = freshTypeParamAuto TypeParamKind.Type dummyRange
    let voptATy = NativeType.TVar voptA
    let voptionTy = NativeType.TApp(voptionTycon, [voptATy])
    // result: Ok : 'T -> result<'T,'E>   Error : 'E -> result<'T,'E>
    let resOkA  = freshTypeParamAuto TypeParamKind.Type dummyRange
    let resErrA = freshTypeParamAuto TypeParamKind.Type dummyRange
    let resOkTy  = NativeType.TVar resOkA
    let resErrTy = NativeType.TVar resErrA
    let resultTy = NativeType.TApp(resultTycon, [resOkTy; resErrTy])
    baseEnv
    |> mkDU "None"      (NativeType.TForall([optA],              optionTy))                                                   0
    |> mkDU "Some"      (NativeType.TForall([optA],              NativeType.TFun(optATy,  optionTy)))                         1
    |> mkDU "ValueNone" (NativeType.TForall([voptA],             voptionTy))                                                  0
    |> mkDU "ValueSome" (NativeType.TForall([voptA],             NativeType.TFun(voptATy, voptionTy)))                        1
    |> mkDU "Ok"        (NativeType.TForall([resOkA; resErrA],   NativeType.TFun(resOkTy,  resultTy)))                        0
    |> mkDU "Error"     (NativeType.TForall([resOkA; resErrA],   NativeType.TFun(resErrTy, resultTy)))                        1

//-------------------------------------------------------------------------
// Diagnostics
//-------------------------------------------------------------------------

/// Add a diagnostic to the environment
let addDiagnostic (diag: Diagnostic) (env: TypeEnv) : unit =
    env.Diagnostics := diag :: !(env.Diagnostics)

/// Convert FCS range to our SourceRange
let rangeToSourceRange (r: range) : SourceRange = {
    File = r.FileName
    Start = { Line = r.StartLine; Column = r.StartColumn }
    End = { Line = r.EndLine; Column = r.EndColumn }
}

/// Create and add an error diagnostic with specific code
let addNativeError (code: string) (r: range) (message: string) (env: TypeEnv) : unit =
    addDiagnostic {
        Severity = NativeDiagnosticSeverity.Error
        Code = code
        Message = message
        Range = rangeToSourceRange r
        RelatedNodes = []
        Reachability = ReachabilityContext.Unknown
    } env

/// Create and add an error diagnostic (generic fallback - prefer addNativeError with specific code)
let addError (r: range) (message: string) (env: TypeEnv) : unit =
    addNativeError DiagnosticCodes.FS0001_GenericError r message env

/// Create and add a warning diagnostic with specific code
let addNativeWarning (code: string) (r: range) (message: string) (env: TypeEnv) : unit =
    addDiagnostic {
        Severity = NativeDiagnosticSeverity.Warning
        Code = code
        Message = message
        Range = rangeToSourceRange r
        RelatedNodes = []
        Reachability = ReachabilityContext.Unknown
    } env

/// Create and add a warning diagnostic (generic fallback)
let addWarning (r: range) (message: string) (env: TypeEnv) : unit =
    addNativeWarning DiagnosticCodes.FS0002_GenericWarning r message env

//-------------------------------------------------------------------------
// Native-Specific Error Helpers
//-------------------------------------------------------------------------

/// Emit FS8100: Cannot use 'null' in Clef
let addNullError (r: range) (env: TypeEnv) : unit =
    addNativeError DiagnosticCodes.FS8100_NullLiteral r
        "Cannot use 'null' in Clef; use 'ValueNone' for optional values" env

/// Emit FS8011: The type 'obj' is not available in Clef
let addObjError (r: range) (env: TypeEnv) : unit =
    addNativeError DiagnosticCodes.FS8011_ObjNotSupported r
        "The type 'obj' (System.Object) is not available in Clef; use discriminated unions or SRTP" env

/// Emit FS8012: Boxing is not supported
let addBoxingError (r: range) (env: TypeEnv) : unit =
    addNativeError DiagnosticCodes.FS8012_BoxingNotSupported r
        "Boxing is not supported in Clef; the native type system does not include 'obj'" env

/// Emit warning for null annotation - ignored in Clef
let addNullWarning (r: range) (env: TypeEnv) : unit =
    addNativeWarning DiagnosticCodes.FS8101_UninitializedValue r
        "Nullable annotation ignored in Clef; native types are null-free by design" env

//-------------------------------------------------------------------------
// Binding Management
//-------------------------------------------------------------------------

/// Add a binding to the environment using compositional resolution
/// PRD-14: Tracks IsModuleLevel for correct capture analysis
/// isModuleLevel must be explicitly specified by the caller based on binding semantics:
/// - Parameters (function, loop, inline) → false (always local)
/// - Let bindings → env.EnclosingFunction.IsNone (depends on scope)
/// - Type definitions → true (always module-level)
let addBinding (name: string) (ty: NativeType) (isMutable: bool) (nodeId: NodeId option) (isModuleLevel: bool) (env: TypeEnv) : TypeEnv =
    let binding: NR.ResolvedBinding = {
        QualifiedName = name
        Type = ty
        IsMutable = isMutable
        NodeId = nodeId
        InlineBody = None
        UnionCaseInfo = None
        NativeLiteral = None
        IsModuleLevel = isModuleLevel
    }
    { env with Resolution = NR.registerBinding name binding env.Resolution }

/// Add a binding with inline body for transparent function expansion
/// Only functions explicitly marked `inline` get their bodies captured
let addInlineBinding (name: string) (ty: NativeType) (nodeId: NodeId option) (inlineBody: NR.InlineBody) (env: TypeEnv) : TypeEnv =
    let binding: NR.ResolvedBinding = {
        QualifiedName = name
        Type = ty
        IsMutable = false
        NodeId = nodeId
        InlineBody = Some inlineBody
        UnionCaseInfo = None
        NativeLiteral = None
        IsModuleLevel = env.EnclosingFunction.IsNone
    }
    { env with Resolution = NR.registerBinding name binding env.Resolution }

/// Add a DU constructor binding with case info for proper UnionCase node creation
/// DU types are always defined at module scope, so constructors are module-level
let addUnionCaseBinding (name: string) (ty: NativeType) (caseInfo: NR.UnionCaseInfo) (env: TypeEnv) : TypeEnv =
    let binding: NR.ResolvedBinding = {
        QualifiedName = name
        Type = ty
        IsMutable = false
        NodeId = None
        InlineBody = None
        UnionCaseInfo = Some caseInfo
        NativeLiteral = None
        IsModuleLevel = true  // DU constructors are always module-level
    }
    { env with Resolution = NR.registerBinding name binding env.Resolution }

/// Add a [<Literal>] binding with compile-time constant value for substitution
/// Literal values are substituted at use sites during name resolution
let addLiteralBinding (name: string) (ty: NativeType) (nodeId: NodeId option) (litValue: NativeLiteral) (env: TypeEnv) : TypeEnv =
    let binding: NR.ResolvedBinding = {
        QualifiedName = name
        Type = ty
        IsMutable = false  // Literals are always immutable
        NodeId = nodeId
        InlineBody = None
        UnionCaseInfo = None
        NativeLiteral = Some litValue
        IsModuleLevel = env.EnclosingFunction.IsNone
    }
    { env with Resolution = NR.registerBinding name binding env.Resolution }

/// Look up a binding using compositional resolver
/// BCL is structurally impossible - only source-defined bindings exist
let tryLookupBinding (name: string) (env: TypeEnv) : NR.ResolvedBinding option =
    NR.resolve name env.Resolution

/// Add an open namespace declaration to the resolution context
/// This composes a resolver that prefixes lookups with the namespace
let addOpen (ns: string) (env: TypeEnv) : TypeEnv =
    { env with Resolution = NR.addOpen ns env.Resolution }

//-------------------------------------------------------------------------
// Type Definition Management
//-------------------------------------------------------------------------

/// Add a type definition to the environment. A definition shadows an earlier abbreviation of
/// the same name (`type FrameKind = byte` in a spliced dependency, then the program's own
/// `type FrameKind = | Tell | Ask`): resolution consults abbreviations first, so the later
/// declaration wins only if the earlier abbreviation is retired here.
let addTypeDef (name: string) (tyCon: TypeConRef) (env: TypeEnv) : TypeEnv =
    { env with TypeDefs = Map.add name tyCon env.TypeDefs; TypeAbbrevs = Map.remove name env.TypeAbbrevs }

/// Look up a type definition
let tryLookupTypeDef (name: string) (env: TypeEnv) : TypeConRef option =
    Map.tryFind name env.TypeDefs

/// Add a type abbreviation to the environment
let addTypeAbbrev (name: string) (ty: NativeType) (env: TypeEnv) : TypeEnv =
    { env with TypeAbbrevs = Map.add name ty env.TypeAbbrevs }

/// Look up a type abbreviation
let tryLookupTypeAbbrev (name: string) (env: TypeEnv) : NativeType option =
    Map.tryFind name env.TypeAbbrevs

//-------------------------------------------------------------------------
// Record Type Infrastructure
// Per clef-lang-spec inference-procedures.md Field Label Resolution
//-------------------------------------------------------------------------

/// Add a record type definition to the environment.
/// This populates RecordDefs and (unless RequireQualifiedAccess) FieldLabels.
let addRecordDef (info: RecordTypeInfo) (env: TypeEnv) : TypeEnv =
    // Add to RecordDefs
    let env = { env with RecordDefs = Map.add info.TypeCon.Name info env.RecordDefs }

    // Add field labels unless RequireQualifiedAccess
    if info.RequireQualifiedAccess then
        env
    else
        // For each field, add a FieldRef to the FieldLabels table
        let fieldRefs =
            info.Fields
            |> List.mapi (fun idx (fieldName, fieldType) ->
                fieldName, {
                    RecordType = info.TypeCon
                    FieldName = fieldName
                    FieldType = fieldType
                    FieldIndex = idx
                })

        let updatedLabels =
            fieldRefs
            |> List.fold (fun labels (fieldName, fieldRef) ->
                let existing = Map.tryFind fieldName labels |> Option.defaultValue []
                Map.add fieldName (fieldRef :: existing) labels
            ) env.FieldLabels

        { env with FieldLabels = updatedLabels }

/// Look up a record type definition by name
let tryLookupRecordDef (name: string) (env: TypeEnv) : RecordTypeInfo option =
    Map.tryFind name env.RecordDefs

/// Try to resolve a field's type from a record type.
/// Returns Some(fieldType) if the type is a record with the given field, None otherwise.
/// This is the canonical way to resolve record field types - no SRTP constraints needed.
let tryResolveRecordFieldType (ty: NativeType) (fieldName: string) (env: TypeEnv) : NativeType option =
    match applySubst ty with
    | NativeType.TApp(tycon, _typeArgs) ->
        // Try to find this type in RecordDefs
        match tryLookupRecordDef tycon.Name env with
        | Some recordInfo ->
            // Look up the field in the record's field list
            recordInfo.Fields
            |> List.tryFind (fun (name, _) -> name = fieldName)
            |> Option.map snd
        | None -> None
    | _ -> None

/// Look up field labels (all record types that have a field with this name)
let lookupFieldLabels (fieldName: string) (env: TypeEnv) : FieldRef list =
    Map.tryFind fieldName env.FieldLabels |> Option.defaultValue []

/// Resolve record type from field labels.
/// Per clef-lang-spec inference-procedures.md: Field Label Resolution Algorithm
///
/// Steps:
/// 1. For each field f_i in the expression, get C_i = candidates(f_i)
/// 2. Compute intersection: I = C_1 ∩ C_2 ∩ ... ∩ C_n
/// 3. Disambiguate based on |I|
///
/// Returns Ok(recordType) or Error(diagnosticCode, message)
let resolveRecordTypeFromFields
    (fieldNames: string list)
    (typeQualifier: string option)
    (_range: SourceRange)
    (env: TypeEnv)
    : Result<NativeType, string * string> =

    if List.isEmpty fieldNames then
        Result.Error((DiagnosticCodes.FS8701_NoFields, "Record expression must have at least one field"))
    else
        // Step 1: Get candidates for each field
        let candidateSets =
            fieldNames
            |> List.map (fun fieldName ->
                let candidates = lookupFieldLabels fieldName env
                (fieldName, candidates))

        // Check if any field has no candidates (undefined field label)
        let undefinedFields =
            candidateSets
            |> List.filter (fun (_, candidates) -> List.isEmpty candidates)
            |> List.map fst

        match undefinedFields with
        | first :: _ ->
            // FS8702: Undefined field label
            Result.Error((DiagnosticCodes.FS8702_UndefinedField,
                   sprintf "Field '%s' is not defined in any record type in scope" first))
        | [] ->
            // Step 2: Compute intersection
            // Extract record type names from each candidate set
            let typeNameSets =
                candidateSets
                |> List.map (fun (_, candidates) ->
                    candidates
                    |> List.map (fun fieldRef -> fieldRef.RecordType.Name)
                    |> Set.ofList)

            let intersection =
                match typeNameSets with
                | [] -> Set.empty
                | first :: rest -> List.fold Set.intersect first rest

            // Step 3: Apply type qualifier if present (e.g., { TypeName.field = value })
            let intersection =
                match typeQualifier with
                | Some qualifier ->
                    // Filter to types whose name ends with or equals the qualifier
                    intersection |> Set.filter (fun typeName ->
                        typeName = qualifier || typeName.EndsWith("." + qualifier))
                | None -> intersection

            // Step 4: Disambiguate
            match Set.count intersection with
            | 0 ->
                // FS8703: Conflicting fields - no record type has all fields
                let fieldListStr = fieldNames |> String.concat ", "
                Result.Error((DiagnosticCodes.FS8703_ConflictingFields,
                       sprintf "No record type has all fields: %s" fieldListStr))
            | 1 ->
                // Exactly one candidate - success!
                let typeName = Set.minElement intersection
                match Map.tryFind typeName env.RecordDefs with
                | Some recordInfo ->
                    // Spec Section 4.2: Use TApp for records (single representation invariant)
                    // ParamKinds is the single source of truth — fresh vars for generic records
                    let freshArgs = recordInfo.TypeCon.ParamKinds |> List.map (fun _kind -> freshTypeVar _range)
                    Result.Ok (NativeType.TApp(recordInfo.TypeCon, freshArgs))
                | None ->
                    // INTERNAL ERROR: Field label resolution found this type name,
                    // so it MUST exist in RecordDefs.
                    Result.Error((DiagnosticCodes.FS0001_GenericError,
                           sprintf "Internal error: field labels reference record type '%s' but it is not in RecordDefs" typeName))
            | _ ->
                // Multiple record types have all these fields. A fresh record expression must
                // set every field of its type, so a candidate with more fields than the
                // expression names is not admissible ({ Name; Count } is never an F when F also
                // has Extra). Among the exact matches, "last definition wins" (standard F#
                // behavior: the most recently defined/opened type takes precedence).
                // addRecordDef prepends new FieldRefs, so List.head = most recently defined
                let exactMatches =
                    intersection
                    |> Set.filter (fun typeName ->
                        match Map.tryFind typeName env.RecordDefs with
                        | Some info -> List.length info.Fields = List.length fieldNames
                        | None -> false)
                let admissible = if Set.isEmpty exactMatches then intersection else exactMatches
                let lastTypeName =
                    candidateSets
                    |> List.head |> snd
                    |> List.filter (fun fr -> Set.contains fr.RecordType.Name admissible)
                    |> List.head
                    |> fun fr -> fr.RecordType.Name
                match Map.tryFind lastTypeName env.RecordDefs with
                | Some recordInfo ->
                    let freshArgs = recordInfo.TypeCon.ParamKinds |> List.map (fun _kind -> freshTypeVar _range)
                    Result.Ok (NativeType.TApp(recordInfo.TypeCon, freshArgs))
                | None ->
                    let typeNames = intersection |> Set.toList |> String.concat ", "
                    Result.Error((DiagnosticCodes.FS8704_AmbiguousFields,
                           sprintf "Field labels are ambiguous; could be any of: %s. Use type annotation or qualified field access." typeNames))

//-------------------------------------------------------------------------
// Constraint Management
//-------------------------------------------------------------------------

/// Add a constraint to the environment
let addConstraint (c: Constraint) (env: TypeEnv) : unit =
    env.Constraints := c :: !(env.Constraints)


/// Resolve a field's type, handling records directly and falling back to SRTP constraints.
/// This is the SINGLE entry point for field type resolution - used by both Identity.fs and Coordinator.fs.
//-------------------------------------------------------------------------
// Type Predicate Helpers
// Shared utilities for checking common type forms
//-------------------------------------------------------------------------

/// Check if a type is the string type
let isStringType (ty: NativeType) : bool =
    match ty with
    | NativeType.TApp(tycon, []) when tycon.Name = "string" -> true
    | _ -> false

/// Check if a type is an array type
let isArrayType (ty: NativeType) : bool =
    match ty with
    | NativeType.TApp(tycon, [_]) when tycon.Name = "array" -> true
    | _ -> false

/// Get the element type of an array type
let tryGetArrayElementType (ty: NativeType) : NativeType option =
    match ty with
    | NativeType.TApp(tycon, [elemType]) when tycon.Name = "array" -> Some elemType
    | _ -> None

/// Resolve the element type for index operations (array, string, or via constraint)
let resolveIndexElementType (objType: NativeType) (env: TypeEnv) (range: SourceRange) : NativeType =
    match objType with
    | NativeType.TApp(tc, [elemType]) when tc.Name = "array" -> elemType
    | _ when isStringType objType -> Types.charType
    | NativeType.TVar _ ->
        let elemType = freshTypeVar range
        addConstraint (Constraint.Equals(objType, NativeTypes.Types.mkArrayType elemType, range)) env
        elemType
    | _ ->
        let resultType = freshTypeVar range
        addConstraint (Constraint.HasMember(objType, "Item", resultType, range)) env
        resultType

let resolveFieldType (baseType: NativeType) (fieldName: string) (env: TypeEnv) (range: SourceRange) : NativeType =
    let resolvedType = applySubst baseType

    // 1. Check intrinsic members (string.Pointer, string.Length, array.Length)
    match fieldName with
    | "Length" when isStringType resolvedType ->
        Types.intType
    | "Length" when isArrayType resolvedType ->
        Types.intType
    | _ ->
        // 2. Try record field lookup (no SRTP needed for records)
        match tryResolveRecordFieldType resolvedType fieldName env with
        | Some fieldType -> fieldType
        | None ->
            // 3. Fall back to SRTP constraint for generic types
            let ty = freshTypeVar range
            addConstraint (Constraint.HasMember(baseType, fieldName, ty, range)) env
            ty

//-------------------------------------------------------------------------
// Attribute Helpers
//-------------------------------------------------------------------------

/// Check if a binding has the [<EntryPoint>] attribute
/// Per F# spec: The entry point function should have signature: string[] -> int
let hasEntryPointAttribute (attrs: SynAttributes) : bool =
    attrs |> List.exists (fun attrList ->
        attrList.Attributes |> List.exists (fun attr ->
            match attr.TypeName.LongIdent with
            | [id] -> id.idText = "EntryPoint" || id.idText = "EntryPointAttribute"
            | _ -> false
        )
    )

/// Check if a binding has the [<HardwareModule>] attribute
/// Marks a binding as the top-level hardware module for FPGA targets.
let hasHardwareModuleAttribute (attrs: SynAttributes) : bool =
    attrs |> List.exists (fun attrList ->
        attrList.Attributes |> List.exists (fun attr ->
            match attr.TypeName.LongIdent with
            | [id] -> id.idText = "HardwareModule" || id.idText = "HardwareModuleAttribute"
            | _ -> false
        )
    )

/// Check if a binding has the [<KernelModule>] attribute
/// Marks a binding as the top-level compute kernel for NPU targets.
let hasKernelModuleAttribute (attrs: SynAttributes) : bool =
    attrs |> List.exists (fun attrList ->
        attrList.Attributes |> List.exists (fun attr ->
            match attr.TypeName.LongIdent with
            | [id] -> id.idText = "KernelModule" || id.idText = "KernelModuleAttribute"
            | _ -> false
        )
    )

/// Check if a binding has the [<Literal>] attribute
/// Per F# spec: Literal bindings must be initialized with constant expressions.
/// Values are substituted at use sites during name resolution.
let hasLiteralAttribute (attrs: SynAttributes) : bool =
    attrs |> List.exists (fun attrList ->
        attrList.Attributes |> List.exists (fun attr ->
            match attr.TypeName.LongIdent with
            | [id] -> id.idText = "Literal" || id.idText = "LiteralAttribute"
            | _ -> false
        )
    )

/// Extract pin logical name from [<Pin("name")>] attribute on a record field.
/// Returns a single-element list for consistency with extractPinsAttribute.
let extractPinAttribute (attrs: SynAttributes) : string list =
    attrs |> List.collect (fun attrList ->
        attrList.Attributes |> List.choose (fun attr ->
            match attr.TypeName.LongIdent with
            | [id] when id.idText = "Pin" || id.idText = "PinAttribute" ->
                match attr.ArgExpr with
                | SynExpr.Paren(SynExpr.Const(SynConst.String(pinName, _, _), _), _, _, _) -> Some pinName
                | SynExpr.Const(SynConst.String(pinName, _, _), _) -> Some pinName
                | _ -> None
            | _ -> None
        )
    )

/// Extract pin logical names from [<Pins("a","b","c")>] attribute on a record field.
/// Returns multiple names for multi-pin groups (e.g., RGB LED channels).
let extractPinsAttribute (attrs: SynAttributes) : string list =
    attrs |> List.collect (fun attrList ->
        attrList.Attributes |> List.collect (fun attr ->
            match attr.TypeName.LongIdent with
            | [id] when id.idText = "Pins" || id.idText = "PinsAttribute" ->
                match attr.ArgExpr with
                | SynExpr.Paren(SynExpr.Tuple(_, exprs, _, _), _, _, _) ->
                    exprs |> List.choose (fun expr ->
                        match expr with
                        | SynExpr.Const(SynConst.String(pinName, _, _), _) -> Some pinName
                        | _ -> None
                    )
                | SynExpr.Paren(SynExpr.Const(SynConst.String(pinName, _, _), _), _, _, _) ->
                    [pinName]
                | _ -> []
            | _ -> []
        )
    )

/// Extract all pin names from [<Pin>] or [<Pins>] attributes on a record field.
let extractFieldPinNames (attrs: SynAttributes) : string list =
    match extractPinAttribute attrs with
    | pins when not (List.isEmpty pins) -> pins
    | _ -> extractPinsAttribute attrs

/// Extract library and symbol from [<FidelityExtern("library", "symbol")>] attribute.
/// Returns (library, symbol) option. Used for Farscape-generated native bindings.
let extractFidelityExternAttribute (attrs: SynAttributes) : (string * string) option =
    attrs |> List.tryPick (fun attrList ->
        attrList.Attributes |> List.tryPick (fun attr ->
            match attr.TypeName.LongIdent with
            | [id] when id.idText = "FidelityExtern" || id.idText = "FidelityExternAttribute" ->
                match attr.ArgExpr with
                | SynExpr.Paren(SynExpr.Tuple(_, [SynExpr.Const(SynConst.String(library, _, _), _);
                                                   SynExpr.Const(SynConst.String(symbol, _, _), _)], _, _), _, _, _) ->
                    Some (library, symbol)
                | _ -> None
            | _ -> None
        )
    )

//-------------------------------------------------------------------------
// BCL Rejection - CRITICAL
// BCL types/namespaces are NEVER allowed in Clef
//-------------------------------------------------------------------------

/// Check if a name references BCL (Base Class Library) namespaces
/// BCL references are FORBIDDEN in Clef - they require .NET runtime
let isBclReference (name: string) : bool =
    // Only definitively BCL prefixes - no library-aware heuristics
    name.StartsWith("System.") ||
    name.StartsWith("Microsoft.") ||
    name.StartsWith("mscorlib.") ||
    name.StartsWith("netstandard.") ||
    // Unchecked module - commonly used without full qualification
    name.StartsWith("Unchecked.") ||
    name = "Unchecked"

/// Check if a name is specifically Unchecked.* (needs special error message)
let isUncheckedReference (name: string) : bool =
    name.StartsWith("Unchecked.") || name = "Unchecked"

/// Emit FS8104: Unchecked.defaultof not allowed in Clef
let addUncheckedError (name: string) (r: range) (env: TypeEnv) : unit =
    addNativeError DiagnosticCodes.FS8104_UncheckedDefault r
        $"'{name}' is not available in Clef. Unchecked.defaultof requires runtime type information. Use explicit initialization, CCS intrinsics, or NativeDefault.zeroed instead." env

/// Emit FS8500: BCL reference not allowed in Clef
let addBclError (name: string) (r: range) (env: TypeEnv) : unit =
    if isUncheckedReference name then
        addUncheckedError name r env
    else
        addNativeError DiagnosticCodes.FS8500_BclReferenceNotAllowed r
            $"BCL reference '{name}' is not available in Clef. The .NET Base Class Library requires the .NET runtime. Use Alloy library equivalents instead." env

//-------------------------------------------------------------------------
// SynType → NativeType Boundary Conversion
// This is the ONLY place SynType is converted to NativeType.
// SynType is transient - it exists only at the parser boundary.
// After conversion here, only NativeType propagates through type checking.
//-------------------------------------------------------------------------

/// Resolve a built-in type constructor to its NativeType factory.
/// These are NTU types with dedicated NativeType constructors (not TApp).
/// Returns None if not a built-in type constructor.
let private tryResolveBuiltinTypeConstructor (name: string) (args: NativeType list) : NativeType option =
    match name, args with
    // Byref family
    | "byref", [elem] -> Some (NativeType.TByref(elem, ByrefKind.InOut))
    | "inref", [elem] -> Some (NativeType.TByref(elem, ByrefKind.In))
    | "outref", [elem] -> Some (NativeType.TByref(elem, ByrefKind.Out))
    // Collection types with dedicated constructors
    | "Lazy", [elem] -> Some (NativeType.TLazy elem)
    | "seq", [elem] -> Some (NativeType.TSeq elem)
    | "list", [elem] -> Some (NativeType.TList elem)
    | "Map", [k; v] -> Some (NativeType.TMap(k, v))
    | "Set", [elem] -> Some (NativeType.TSet elem)
    // C-04: array is NTUarray/FatPointer — already carried by arrayTyCon and
    // every Array.* intrinsic; this makes it denotable in a signature.
    | "array", [elem] -> Some (NativeType.TApp(Types.arrayTyCon, [elem]))
    // Built-in discriminated union type constructors
    | "option",  [elem]      -> Some (NativeType.TApp(optionTycon,  [elem]))
    | "voption", [elem]      -> Some (NativeType.TApp(voptionTycon, [elem]))
    | "Result",  [ok; err]   -> Some (NativeType.TApp(resultTycon,  [ok; err]))
    // Not a built-in type constructor
    | _ -> None

/// Resolve a type name to NativeType via NTU lookup.
/// Checks: TypeAbbrevs, TypeDefs, then NTU primitives.
let private resolveTypeName (name: string) (env: TypeEnv) : NativeType option =
    // 1. Check type abbreviations first
    match tryLookupTypeAbbrev name env with
    | Some ty -> Some ty
    | None ->
        // 2. Check type definitions — ParamKinds is the single source of truth for arity
        match tryLookupTypeDef name env with
        | Some tyCon ->
            // A fresh variable per parameter, in the parameter's sort (design a.2).
            let args =
                tyCon.ParamKinds
                |> List.map (function
                    | TypeParamKind.Type -> freshTypeVar dummyRange
                    | TypeParamKind.Measure -> NativeType.TMeasure (Dimension.ofVar (freshMeasureVar None)))
            Some (NativeType.TApp(tyCon, args))
        | None ->
            // 3. NTU primitives: a numeric spelling reads the one spelling table (sequence CS-5);
            //    the non-numeric primitives are named here.
            match NativeTypes.Types.tryNumericTyConOfName name with
            | Some carrier -> Some (NativeTypes.Types.numericType carrier)
            | None ->
                match name with
                | "bool" -> Some NativeTypes.Types.boolType
                | "char" -> Some NativeTypes.Types.charType
                | "string" -> Some NativeTypes.Types.stringType
                | "unit" -> Some NativeTypes.Types.unitType
                | "decimal" -> Some NativeTypes.Types.decimalType
                | _ -> None

//-------------------------------------------------------------------------
// Measure syntax → Dimension: the one translator (design a.4)
//-------------------------------------------------------------------------
//
// Reached (sequence CS-4) from the type-position resolver below (`resolveSynType`: a numeric
// carrier applied to arguments, a measure-sorted constructor position), from the literal resolver
// (Literals.fs, `SynConst.Measure`) and from the `[<Measure>] type` declaration arm
// (NativeService.fs, abbreviation bodies), so that no two paths can disagree.

// The bound on a written or reached exponent is the algebra's, `measureExponentBound`
// (DimensionAlgebra.fs). Every product the translator forms adds two bounded exponents
// (|e1 + e2| <= 2^16) and every power multiplies a bounded exponent by a bounded written one
// (|n * e| <= 2^30), so no translation step can overflow before its result is checked against the
// bound again, and every stored expansion is within it. The unifier bounds the bindings `solveDim`
// produces and the resolved sides of every equation (Unify.fs). An exponent past the bound is
// refused with the CCS8048 family (`MeasureFailure.ExponentOutOfRange`), never wrapped.

/// The code (from `DiagnosticCodes`), the message (design (f), verbatim) and the range of a measure
/// failure: the one projection from the failure value to a diagnostic.
let describeMeasureFailure (failure: MeasureFailure) : string * string * range =
    match failure with
    | MeasureFailure.NotInScope(name, r) ->
        DiagnosticCodes.CCS8042_MeasureNotInScope,
        $"'{name}' is not a measure in scope",
        r
    | MeasureFailure.Cyclic(name, chain, r) ->
        let chainText = String.concat " -> " chain
        DiagnosticCodes.CCS8043_CyclicMeasureAbbreviation,
        $"Measure abbreviation '{name}' is cyclic: {chainText}",
        r
    | MeasureFailure.VariableInLiteral(_, r) ->
        DiagnosticCodes.CCS8044_MeasureVariableInLiteral,
        "A measure variable may not appear in a literal's measure annotation; use '_'",
        r
    | MeasureFailure.SortMismatch(arg, r) ->
        DiagnosticCodes.CCS8045_MeasureSortMismatch,
        $"'{arg}' is a type where a measure is required, or a measure where a type is required",
        r
    | MeasureFailure.NoDimension(ty, r) ->
        DiagnosticCodes.CCS8046_NoDimension,
        $"'{ty}' carries no dimension; a measure cannot be applied to it",
        r
    | MeasureFailure.RationalExponent(rational, r) ->
        DiagnosticCodes.CCS8048_RationalMeasureExponent,
        $"Rational measure exponent '{rational}' is not supported; exponents are integers",
        r
    | MeasureFailure.ExponentOutOfRange(n, r) ->
        DiagnosticCodes.CCS8048_RationalMeasureExponent,
        $"Measure exponent '{n}' is not representable; exponents are integers of magnitude at most {measureExponentBound}",
        r
    | MeasureFailure.Parameterised(_, r) ->
        DiagnosticCodes.CCS8049_ParameterisedMeasureDefinition,
        "A measure definition may not have type or measure parameters",
        r
    | MeasureFailure.ArityMismatch(tycon, given, r) ->
        DiagnosticCodes.CCS8050_MeasureArityMismatch,
        $"'{tycon}' takes one measure argument; {given} were given",
        r

/// Record a measure failure through the environment's diagnostics, at the failure's own range, the
/// way CCS8018 is recorded for a refused literal (Literals.fs).
let addMeasureFailure (failure: MeasureFailure) (env: TypeEnv) : unit =
    let code, message, r = describeMeasureFailure failure
    addNativeError code r message env

/// The syntax forms read in the measure sort (design a.4).
[<RequireQualifiedAccess>]
type MeasureSyntax =
    /// The annotation of a constant, `1.0<kg m / s^2>`: the `SynMeasure` of `SynConst.Measure`.
    | Measure of SynMeasure
    /// A type argument written where a measure is required, the argument of `float<kg m / s^2>`:
    /// read entirely in the measure sort, as every argument of a numeric carrier is.
    | Type of SynType
    /// The whole argument list written on a type constructor, `float<m>`, `bool<m>`. The constructor
    /// decides: a numeric carrier takes exactly one measure (CCS8050 otherwise), a constructor whose
    /// sole parameter is measure-sorted likewise, a constructor with no parameter carries no
    /// dimension (CCS8046), and one with a type-sorted position is a sort mismatch (CCS8045); a
    /// constructor with several measure-sorted positions is read positionally by the resolver,
    /// through `Type`, and never through this form.
    | Applied of tycon: TypeConRef * args: SynType list * range: range

/// What a translation threads: the named measure variables in scope (`'u` read twice is one
/// variable) and the supply of fresh ones. A value: every step returns the context it leaves.
type MeasureContext = { Scope: Map<string, MeasureVar>; Supply: MeasureSupply }

module MeasureContext =

    /// No named variable in scope; fresh variables numbered from `first`.
    let startingAt (first: int) : MeasureContext =
        { Scope = Map.empty; Supply = MeasureSupply.startingAt first }

/// A rational constant as written, for a message.
let rec private renderRational (c: SynRationalConst) : string =
    match c with
    | SynRationalConst.Integer(n, _) -> string n
    | SynRationalConst.Rational(n, _, _, d, _, _) -> $"{n}/{d}"
    | SynRationalConst.Negate(inner, _) -> "-" + renderRational inner
    | SynRationalConst.Paren(inner, _) -> "(" + renderRational inner + ")"

/// A type syntax node as a message names it. Presentation only; nothing reads it back.
let rec private renderSynType (t: SynType) : string =
    let idents (ids: Ident list) = ids |> List.map (fun i -> i.idText) |> String.concat "."
    let args (ts: SynType list) = ts |> List.map renderSynType |> String.concat ", "
    match t with
    | SynType.LongIdent(SynLongIdent(ids, _, _)) -> idents ids
    | SynType.App(head, _, typeArgs, _, _, true, _) ->
        typeArgs @ [ head ] |> List.map renderSynType |> String.concat " "
    | SynType.App(head, _, typeArgs, _, _, false, _) -> renderSynType head + "<" + args typeArgs + ">"
    | SynType.LongIdentApp(head, SynLongIdent(ids, _, _), _, typeArgs, _, _, _) ->
        renderSynType head + "." + idents ids + "<" + args typeArgs + ">"
    | SynType.Tuple(_, segments, _) ->
        segments
        |> List.map (function
            | SynTupleTypeSegment.Type ty -> renderSynType ty
            | SynTupleTypeSegment.Star _ -> "*"
            | SynTupleTypeSegment.Slash _ -> "/")
        |> String.concat " "
    | SynType.AnonRecd(_, fields, _) ->
        "{| " + (fields |> List.map (fun (id, ty) -> id.idText + ": " + renderSynType ty) |> String.concat "; ") + " |}"
    | SynType.Array(rank, elem, _) -> renderSynType elem + "[" + String.replicate (rank - 1) "," + "]"
    | SynType.Fun(a, r, _, _) -> renderSynType a + " -> " + renderSynType r
    | SynType.Var(SynTypar(id, _, _), _) -> "'" + id.idText
    | SynType.Anon _ -> "_"
    | SynType.WithGlobalConstraints(inner, _, _)
    | SynType.HashConstraint(inner, _)
    | SynType.WithNull(inner, _, _, _)
    | SynType.SignatureParameter(_, _, _, inner, _) -> renderSynType inner
    | SynType.MeasurePower(b, e, _) -> renderSynType b + "^" + renderRational e
    | SynType.StaticConstant(SynConst.Int32 n, _) -> string n
    | SynType.StaticConstant(_, _) -> "constant"
    | SynType.StaticConstantNull _ -> "null"
    | SynType.StaticConstantExpr _ -> "const expression"
    | SynType.StaticConstantNamed(SynType.LongIdent(SynLongIdent(ids, _, _)), value, _) -> idents ids + " = " + renderSynType value
    | SynType.StaticConstantNamed(_, value, _) -> renderSynType value
    | SynType.Paren(inner, _) -> "(" + renderSynType inner + ")"
    | SynType.Intersection(_, types, _, _) -> args types
    | SynType.Or(l, r, _, _) -> renderSynType l + " or " + renderSynType r
    | SynType.FromParseError _ -> "?"

/// The integer a written exponent denotes, within `measureExponentBound`. A rational form anywhere
/// in it is CCS8048; an integer past the bound is the CCS8048 family. Read in `int64` so that the
/// negation of any `int32` is exact before the bound is applied.
let private exponentOf (written: SynRationalConst) (r: range) : Result<int, MeasureFailure> =
    let rec value (c: SynRationalConst) : Result<int64, MeasureFailure> =
        match c with
        | SynRationalConst.Integer(n, _) -> Ok(int64 n)
        | SynRationalConst.Rational _ -> Result.Error(MeasureFailure.RationalExponent(renderRational written, r))
        | SynRationalConst.Negate(inner, _) -> value inner |> Result.map (fun v -> -v)
        | SynRationalConst.Paren(inner, _) -> value inner
    value written
    |> Result.bind (fun v ->
        if abs v > int64 measureExponentBound then
            Result.Error(MeasureFailure.ExponentOutOfRange(renderRational written, r))
        else
            Ok(int v))

/// The dimension unchanged if every exponent is within the bound, else the CCS8048 family naming the
/// exponent reached.
let private bounded (r: range) (d: Dimension) : Result<Dimension, MeasureFailure> =
    match exponentsOf d |> List.tryFind (fun e -> abs e > measureExponentBound) with
    | Some e -> Result.Error(MeasureFailure.ExponentOutOfRange(string e, r))
    | None -> Ok d

/// The bare names a measure syntax mentions, last segment of each written path: what registration
/// orders a declaration group by (`MeasureEnv.registerGroup`). Syntax-aware, so it lives beside the
/// translator; it reads the same forms the translator reads and nothing else.
let measureReferences (syntax: MeasureSyntax) : string list =
    let last (ids: Ident list) = ids |> List.tryLast |> Option.map (fun i -> i.idText) |> Option.toList
    let rec ofMeasure (m: SynMeasure) : string list =
        match m with
        | SynMeasure.Named(ids, _) -> last ids
        | SynMeasure.Product(m1, _, m2, _) -> ofMeasure m1 @ ofMeasure m2
        | SynMeasure.Seq(ms, _) -> ms |> List.collect ofMeasure
        | SynMeasure.Divide(m1, _, m2, _) -> (m1 |> Option.map ofMeasure |> Option.defaultValue []) @ ofMeasure m2
        | SynMeasure.Power(m1, _, _, _) -> ofMeasure m1
        | SynMeasure.Paren(inner, _) -> ofMeasure inner
        | SynMeasure.One _ | SynMeasure.Anon _ | SynMeasure.Var _ -> []
    let rec ofType (t: SynType) : string list =
        match t with
        | SynType.LongIdent(SynLongIdent(ids, _, _)) -> last ids
        | SynType.App(head, _, args, _, _, true, _) -> (args @ [ head ]) |> List.collect ofType
        | SynType.Tuple(_, segments, _) ->
            segments |> List.collect (function SynTupleTypeSegment.Type ty -> ofType ty | _ -> [])
        | SynType.MeasurePower(b, _, _) -> ofType b
        | SynType.Paren(inner, _) -> ofType inner
        | _ -> []
    match syntax with
    | MeasureSyntax.Measure m -> ofMeasure m
    | MeasureSyntax.Type t -> ofType t
    | MeasureSyntax.Applied(_, args, _) -> args |> List.collect ofType

/// One translation from measure syntax to a `Dimension`, covering every row of the design (a.4)
/// table, reached (from CS-4) by the type-position resolver, the literal resolver and the
/// abbreviation registration so that no two paths can disagree. Pure: the environment is read
/// (`Measures` for names, the type tables to tell CCS8045 from CCS8042), the context is threaded,
/// and every refusal is a `MeasureFailure` value; no dimension is ever fabricated.
///
/// Rows: a name → `Measures` lookup (absent: CCS8042; found as a type: CCS8045); juxtaposition,
/// `*`, and `,`-free tuple segments → `mul`; `/` and a `Slash` segment → `inv` of what follows it,
/// as F# reads `m / s / kg` as `m s^-1 kg^-1`; `^n` → `pow n` (rational: CCS8048; past the bound:
/// CCS8048 family); `1` → `one`; `_` → a fresh anonymous variable; `'u` → the in-scope variable of
/// that name, else a fresh named one that the rest of the translation shares; a numeric carrier
/// applied to other than one argument → CCS8050; a measure applied to a type that carries no
/// dimension → CCS8046; a type where a measure is required → CCS8045.
let dimensionOfSyntax
    (env: TypeEnv)
    (ctx: MeasureContext)
    (syntax: MeasureSyntax)
    : Result<Dimension * MeasureContext, MeasureFailure> =

    /// A reading of one syntax node against a context.
    let inverted (read: MeasureContext -> Result<Dimension * MeasureContext, MeasureFailure>) =
        fun ctx -> read ctx |> Result.map (fun (d, ctx) -> Dimension.inv d, ctx)

    /// The product of the readings, left to right, each result checked against the bound.
    let productOf (r: range) (ctx: MeasureContext) (reads: (MeasureContext -> Result<Dimension * MeasureContext, MeasureFailure>) list) =
        reads
        |> List.fold
            (fun acc read ->
                acc
                |> Result.bind (fun (d, ctx) ->
                    read ctx
                    |> Result.bind (fun (d', ctx) -> bounded r (Dimension.mul d d') |> Result.map (fun d -> d, ctx))))
            (Ok(Dimension.one, ctx))

    let powerOf (r: range) (written: SynRationalConst) (read: MeasureContext -> Result<Dimension * MeasureContext, MeasureFailure>) (ctx: MeasureContext) =
        exponentOf written r
        |> Result.bind (fun n ->
            read ctx
            |> Result.bind (fun (d, ctx) -> bounded r (Dimension.pow n d) |> Result.map (fun d -> d, ctx)))

    let named (path: string list) (r: range) (ctx: MeasureContext) =
        match MeasureEnv.tryFind path env.Measures with
        | Some def -> Ok(MeasureDef.dimension def, ctx)
        | None ->
            let name = String.concat "." path
            match resolveTypeName name env with
            | Some _ -> Result.Error(MeasureFailure.SortMismatch(name, r))
            | None -> Result.Error(MeasureFailure.NotInScope(name, r))

    let variable (ident: Ident) (ctx: MeasureContext) =
        match Map.tryFind ident.idText ctx.Scope with
        | Some v -> Ok(Dimension.ofVar v, ctx)
        | None ->
            let v, supply = MeasureSupply.fresh (Some ident.idText) ctx.Supply
            Ok(Dimension.ofVar v, { Scope = Map.add ident.idText v ctx.Scope; Supply = supply })

    let anonymous (ctx: MeasureContext) =
        let v, supply = MeasureSupply.fresh None ctx.Supply
        Ok(Dimension.ofVar v, { ctx with Supply = supply })

    let rec ofMeasure (ctx: MeasureContext) (m: SynMeasure) : Result<Dimension * MeasureContext, MeasureFailure> =
        match m with
        | SynMeasure.Named(ids, r) -> named (ids |> List.map (fun i -> i.idText)) r ctx
        | SynMeasure.Product(m1, _, m2, r) -> productOf r ctx [ read m1; read m2 ]
        | SynMeasure.Seq(ms, r) -> productOf r ctx (ms |> List.map read)
        | SynMeasure.Divide(Some m1, _, m2, r) -> productOf r ctx [ read m1; inverted (read m2) ]
        | SynMeasure.Divide(None, _, m2, _) -> inverted (read m2) ctx
        | SynMeasure.Power(m1, _, e, r) -> powerOf r e (read m1) ctx
        | SynMeasure.One _ -> Ok(Dimension.one, ctx)
        | SynMeasure.Anon _ -> anonymous ctx
        | SynMeasure.Var(SynTypar(id, _, _), r) ->
            // `SynMeasure` occurs only under `SynConst.Measure`, so this is a literal's annotation:
            // design (a.4) row `1.0<'u>` is CCS8044; `_` above is the form that mints a variable.
            Result.Error(MeasureFailure.VariableInLiteral(id.idText, r))
        | SynMeasure.Paren(inner, _) -> ofMeasure ctx inner

    and read (m: SynMeasure) = fun ctx -> ofMeasure ctx m

    let rec ofType (ctx: MeasureContext) (t: SynType) : Result<Dimension * MeasureContext, MeasureFailure> =
        match t with
        | SynType.LongIdent(SynLongIdent(ids, _, _)) -> named (ids |> List.map (fun i -> i.idText)) t.Range ctx
        | SynType.App(head, _, args, _, _, true, r) ->
            // Juxtaposition, `kg m`: the parser's postfix application, the head written last.
            productOf r ctx (args @ [ head ] |> List.map readType)
        | SynType.Tuple(_, segments, r) ->
            // `m * s`, `kg m / s^2`, `/ s`, `m / s / kg`: a `Slash` inverts the segment after it.
            let reads, _ =
                segments
                |> List.fold
                    (fun (reads, invertNext) segment ->
                        match segment with
                        | SynTupleTypeSegment.Type ty ->
                            (if invertNext then inverted (readType ty) else readType ty) :: reads, false
                        | SynTupleTypeSegment.Star _ -> reads, false
                        | SynTupleTypeSegment.Slash _ -> reads, true)
                    ([], false)
            productOf r ctx (List.rev reads)
        | SynType.MeasurePower(b, e, r) -> powerOf r e (readType b) ctx
        | SynType.StaticConstant(SynConst.Int32 1, _) -> Ok(Dimension.one, ctx)
        | SynType.Anon _ -> anonymous ctx
        | SynType.Var(SynTypar(id, _, _), _) -> variable id ctx
        | SynType.Paren(inner, _) -> ofType ctx inner
        | other ->
            // Every other type form, `float<m>` or `int -> int` or `2` among them, is a type where a
            // measure is required.
            Result.Error(MeasureFailure.SortMismatch(renderSynType other, other.Range))

    and readType (t: SynType) = fun ctx -> ofType ctx t

    let applied (tycon: TypeConRef) (args: SynType list) (r: range) =
        let oneMeasure () =
            match args with
            | [ arg ] -> ofType ctx arg
            | _ -> Result.Error(MeasureFailure.ArityMismatch(tycon.Name, List.length args, r))
        match tycon.NTUKind |> Option.map NTUKind.isNumeric with
        | Some true -> oneMeasure ()
        | _ ->
            match tycon.ParamKinds with
            | [ TypeParamKind.Measure ] -> oneMeasure ()
            | [] -> Result.Error(MeasureFailure.NoDimension(tycon.Name, r))
            | _ ->
                let written = tycon.Name + "<" + (args |> List.map renderSynType |> String.concat ", ") + ">"
                Result.Error(MeasureFailure.SortMismatch(written, r))

    match syntax with
    | MeasureSyntax.Measure m -> ofMeasure ctx m
    | MeasureSyntax.Type t -> ofType ctx t
    | MeasureSyntax.Applied(tycon, args, r) -> applied tycon args r

/// One translation against the union-find's supply of fresh measure variables: the context starts
/// at the counter and the ids the translation minted are reserved on success. A named variable
/// (`'u`) is one variable within the syntax translated here; sharing it across the annotations of
/// a binding, and generalising it, is CS-6's (design b.4).
let translateDimension (env: TypeEnv) (syntax: MeasureSyntax) : Result<Dimension, MeasureFailure> =
    let ctx = { Scope = Map.empty; Supply = freshMeasureSupply () }
    dimensionOfSyntax env ctx syntax
    |> Result.map (fun (d, ctx') ->
        commitMeasureSupply ctx'.Supply
        d)

/// Record a measure failure and recover with an error type carrying its message, the way the
/// resolver recovers from an unknown type: a diagnostic, never a fabricated type.
let private refuseMeasure (env: TypeEnv) (failure: MeasureFailure) : NativeType =
    addMeasureFailure failure env
    let _, message, _ = describeMeasureFailure failure
    NativeType.TError message

/// A numeric carrier applied to written arguments, `float<kg m / s^2>`: the arguments are read in
/// the measure sort through the one translator (design a.4; `float` has arity 0 in the type sort,
/// D4). A carrier that already carries a measure, an abbreviation such as `type metres = float<m>`,
/// takes no further argument: that is a sort mismatch, not a product.
let private numericApplication (env: TypeEnv) (carrier: TypeConRef) (dim: Dimension) (typeArgs: SynType list) (r: range) : NativeType =
    if dim <> Dimension.one then
        refuseMeasure env (MeasureFailure.SortMismatch(formatType (NativeType.TNum(carrier, dim)), r))
    else
        match translateDimension env (MeasureSyntax.Applied(carrier, typeArgs, r)) with
        | Ok d -> NativeType.TNum(carrier, d)
        | Result.Error failure -> refuseMeasure env failure

/// A written argument in a measure-sorted position of a non-numeric constructor, `Arena<'l>`.
let private measureArgument (env: TypeEnv) (arg: SynType) : NativeType =
    match translateDimension env (MeasureSyntax.Type arg) with
    | Ok d -> NativeType.TMeasure d
    | Result.Error failure -> refuseMeasure env failure

/// Convert SynType to NativeType at the parser/checker boundary.
/// This function is called directly at conversion sites - no callback threading.
/// SynType dies here; only NativeType propagates into type checking.
let rec resolveSynType (env: TypeEnv) (synType: SynType) : NativeType =
    /// The arguments of a constructor whose parameter kinds are known: a measure-sorted position
    /// is read through the one translator to a `TMeasure`, a type-sorted one as a type (design
    /// a.2). An argument count that disagrees with the constructor reads every argument as a type
    /// and leaves the arity error to unification, as before.
    let argumentsFor (tyCon: TypeConRef) (typeArgs: SynType list) : NativeType list =
        if List.length tyCon.ParamKinds = List.length typeArgs then
            List.map2
                (fun kind arg ->
                    match kind with
                    | TypeParamKind.Measure -> measureArgument env arg
                    | TypeParamKind.Type -> resolveSynType env arg)
                tyCon.ParamKinds
                typeArgs
        else
            typeArgs |> List.map (resolveSynType env)

    /// A resolved head applied to written arguments: a numeric carrier reads them in the measure
    /// sort (design a.4), a constructor in its parameters' sorts.
    let apply (head: NativeType) (typeArgs: SynType list) (r: range) : NativeType =
        match head with
        | NativeType.TNum(carrier, dim) -> numericApplication env carrier dim typeArgs r
        | NativeType.TApp(tyCon, _) -> NativeType.TApp(tyCon, argumentsFor tyCon typeArgs)
        | other -> other

    let hasMeasureParameter (tyCon: TypeConRef) = List.contains TypeParamKind.Measure tyCon.ParamKinds

    match synType with
    | SynType.LongIdent(SynLongIdent(idents, _, _)) ->
        // Simple type name: int, string, MyType, Module.Type
        let path = idents |> List.map (fun id -> id.idText)
        let name = String.concat "." path
        match resolveTypeName name env with
        | Some ty -> ty
        | None ->
            // A measure name where a type is required is a sort mismatch (design a.4, CCS8045),
            // never an unknown type; anything else is the unknown-type error as before.
            match MeasureEnv.tryFind path env.Measures with
            | Some _ -> refuseMeasure env (MeasureFailure.SortMismatch(name, synType.Range))
            | None -> NativeType.TError $"Unknown type: {name}"

    | SynType.App(typeName, _, typeArgs, _, _, _, r) ->
        // Generic type application: nativeptr<byte>, List<int>, Option<string>, float<m>
        match typeName with
        | SynType.LongIdent(SynLongIdent(idents, _, _)) ->
            let name = idents |> List.map (fun id -> id.idText) |> String.concat "."
            match resolveTypeName name env with
            // A numeric carrier or a measure-parameterised constructor reads its arguments in
            // their own sorts, before any built-in constructor is tried, so that no measure
            // argument is ever read as a type.
            | Some (NativeType.TNum _ as head) -> apply head typeArgs r
            | Some (NativeType.TApp(tyCon, _) as head) when hasMeasureParameter tyCon -> apply head typeArgs r
            | resolved ->
                let argTys = typeArgs |> List.map (resolveSynType env)
                // Try built-in type constructor first (nativeptr, byref, list, etc.)
                match tryResolveBuiltinTypeConstructor name argTys with
                | Some ty -> ty
                | None ->
                    // Fall back to regular type resolution (user-defined generics)
                    match resolved with
                    | Some (NativeType.TApp(tyCon, _)) -> NativeType.TApp(tyCon, argTys)
                    | Some ty -> ty
                    | None -> NativeType.TError $"Unknown type constructor: {name}"
        | _ ->
            // Complex type expression - recurse
            apply (resolveSynType env typeName) typeArgs r

    | SynType.LongIdentApp(typeName, SynLongIdent(idents, _, _), _, typeArgs, _, _, r) ->
        // Qualified generic: Module.List<int>
        let name = idents |> List.map (fun id -> id.idText) |> String.concat "."
        let baseTy = resolveSynType env typeName
        match baseTy with
        | NativeType.TNum _ -> apply baseTy typeArgs r
        | NativeType.TApp(tyCon, _) when hasMeasureParameter tyCon -> apply baseTy typeArgs r
        | _ ->
            let argTys = typeArgs |> List.map (resolveSynType env)
            // Try built-in type constructor first
            match tryResolveBuiltinTypeConstructor name argTys with
            | Some ty -> ty
            | None ->
                // Fall back to regular type resolution
                match baseTy with
                | NativeType.TApp(tyCon, _) -> NativeType.TApp(tyCon, argTys)
                | _ -> baseTy

    | SynType.Tuple(isStruct, segments, r) ->
        // Tuple type: int * string * bool. A `/` segment is measure syntax (`m / s`), which where
        // a type is required is a sort mismatch (design a.4, CCS8045); it is never dropped.
        let isSlash = function SynTupleTypeSegment.Slash _ -> true | _ -> false
        if segments |> List.exists isSlash then
            refuseMeasure env (MeasureFailure.SortMismatch(renderSynType synType, r))
        else
            let elemTys =
                segments
                |> List.choose (function
                    | SynTupleTypeSegment.Type ty -> Some (resolveSynType env ty)
                    | SynTupleTypeSegment.Star _ | SynTupleTypeSegment.Slash _ -> None)
            NativeType.TTuple(elemTys, isStruct)

    | SynType.Fun(argType, returnType, _, _) ->
        // Function type: int -> string
        let argTy = resolveSynType env argType
        let retTy = resolveSynType env returnType
        NativeType.TFun(argTy, retTy)

    | SynType.Var(SynTypar(ident, _, _), _) ->
        // Type variable: 'a, 'T
        let name = "'" + ident.idText
        let range = rangeToSourceRange ident.idRange
        NativeType.TVar(freshTypeParam name TypeParamKind.Type range)

    | SynType.Array(rank, elemType, _) ->
        // Array type: int[], int[,]
        let elemTy = resolveSynType env elemType
        if rank = 1 then
            NativeTypes.Types.mkArrayType elemTy
        else
            // Multi-dimensional arrays - use array of arrays for now
            List.fold (fun ty _ -> NativeTypes.Types.mkArrayType ty) elemTy [1..rank]

    | SynType.Paren(innerType, _) ->
        // Parenthesized type: (int)
        resolveSynType env innerType

    | SynType.Anon _ ->
        // Anonymous type - create fresh type variable
        freshTypeVar { File = ""; Start = { Line = 0; Column = 0 }; End = { Line = 0; Column = 0 } }

    | SynType.WithGlobalConstraints(innerType, _, _) ->
        // Type with constraints - resolve inner, constraints handled separately
        resolveSynType env innerType

    | SynType.HashConstraint(innerType, _) ->
        // Flexible type: #ISomething
        resolveSynType env innerType

    | SynType.WithNull(innerType, _, _, _) ->
        // Nullable annotation - ignored in Clef (null-free)
        resolveSynType env innerType

    | SynType.MeasurePower(_, _, r) ->
        // `m^2` is measure syntax; where a type is required it is a sort mismatch (design a.4,
        // CCS8045), never its base type.
        refuseMeasure env (MeasureFailure.SortMismatch(renderSynType synType, r))

    | SynType.StaticConstant(_, _)
    | SynType.StaticConstantNull _
    | SynType.StaticConstantExpr(_, _)
    | SynType.StaticConstantNamed(_, _, _) ->
        // Static constants in types - not supported in native
        NativeType.TError "Static constants in types not supported"

    | SynType.AnonRecd(isStruct, fields, _) ->
        // Anonymous record: {| X: int; Y: string |}
        let fieldTys = fields |> List.map (fun (id, ty) -> (id.idText, resolveSynType env ty))
        NativeType.TAnon(fieldTys, isStruct)

    | SynType.FromParseError _ ->
        // Parse error recovery - return error type
        NativeType.TError "Type from parse error"

    | SynType.Intersection(_, types, _, _) ->
        // Type intersection - resolve first type for now
        match types with
        | ty :: _ -> resolveSynType env ty
        | [] -> NativeType.TError "Empty type intersection"

    | SynType.Or(lhs, _rhs, _, _) ->
        // Type union/or - resolve to first type
        resolveSynType env lhs

    | SynType.SignatureParameter(_, _, _idOpt, ty, _) ->
        // Signature parameter - resolve the underlying type
        resolveSynType env ty

