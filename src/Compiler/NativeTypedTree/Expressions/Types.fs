// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Type checking environment and helpers for F# Native expression checking.
/// Extracted from CheckExpressions.fs for maintainability.
module FSharp.Native.Compiler.NativeTypedTree.Expressions.Types

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Text
open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.NativeTypedTree.NativeGlobals
open FSharp.Native.Compiler.NativeTypedTree.UnionFind
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Builder
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Diagnostics

// Module aliases for qualified access
module NativeTypes = FSharp.Native.Compiler.NativeTypedTree.NativeTypes
module NR = FSharp.Native.Compiler.NativeTypedTree.NameResolution

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
// F# Native Diagnostic Codes (FS8xxx series)
//-------------------------------------------------------------------------

/// Error codes for F# Native specific diagnostics.
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
    // BCL types/namespaces are NEVER allowed in F# Native
    let FS8500_BclReferenceNotAllowed = "FS8500"
    let FS8501_SystemNamespaceNotAllowed = "FS8501"
    let FS8502_MicrosoftNamespaceNotAllowed = "FS8502"

    // Platform binding resolution (FS8600-FS8699)
    let FS8600_PlatformBindingUndefined = "FS8600"

    // Record type resolution (FS8700-FS8799)
    // Per fsnative-spec: Field Label Resolution Algorithm error codes
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

//-------------------------------------------------------------------------
// Type Environment
//-------------------------------------------------------------------------

/// The type checking environment
[<NoComparison; NoEquality>]
type TypeEnv = {
    /// Global type information
    Globals: NativeGlobals
    /// Compositional name resolution context
    /// BCL is structurally impossible - only source-defined bindings exist
    Resolution: NR.ResolutionContext
    /// Type definitions (name -> TypeConRef)
    TypeDefs: Map<string, TypeConRef>
    /// Type abbreviations (name -> NativeType it expands to)
    TypeAbbrevs: Map<string, NativeType>
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
// Environment Creation
//-------------------------------------------------------------------------

/// Get UnionCaseInfo for known union case constructors
/// This follows the FCS TyconRef.Deref pattern - union case info is looked up, not embedded
let private tryGetUnionCaseInfo (name: string) (ty: NativeType) : NR.UnionCaseInfo option =
    // Unwrap TForall to get to the actual type
    let resultType =
        match ty with
        | NativeType.TForall(_, NativeType.TFun(_, ret)) -> ret  // Constructor with payload
        | NativeType.TForall(_, ret) -> ret  // Nullary constructor
        | NativeType.TFun(_, ret) -> ret  // Non-polymorphic constructor with payload
        | _ -> ty

    match name with
    // Option constructors (case 0 = None, case 1 = Some)
    | "None" -> Some { CaseName = "None"; UnionType = resultType; CaseIndex = 0 }
    | "Some" -> Some { CaseName = "Some"; UnionType = resultType; CaseIndex = 1 }
    // ValueOption constructors (case 0 = ValueNone, case 1 = ValueSome)
    | "ValueNone" -> Some { CaseName = "ValueNone"; UnionType = resultType; CaseIndex = 0 }
    | "ValueSome" -> Some { CaseName = "ValueSome"; UnionType = resultType; CaseIndex = 1 }
    // Result constructors (case 0 = Ok, case 1 = Error)
    | "Ok" -> Some { CaseName = "Ok"; UnionType = resultType; CaseIndex = 0 }
    | "Error" -> Some { CaseName = "Error"; UnionType = resultType; CaseIndex = 1 }
    | _ -> None

/// Create a type environment with built-in bindings from globals
let createTypeEnv (globals: NativeGlobals) : TypeEnv =
    // Convert built-in bindings from globals to ResolvedBindings and build resolver
    let baseResolver =
        globals.BuiltInBindings
        |> Map.fold (fun ctx name ty ->
            let binding: NR.ResolvedBinding = {
                QualifiedName = name
                Type = ty
                IsMutable = false
                NodeId = None
                InlineBody = None
                UnionCaseInfo = tryGetUnionCaseInfo name ty  // Detect union case constructors
                NativeLiteral = None
                IsModuleLevel = true  // Built-in/intrinsic bindings are always module-level
            }
            NR.registerBinding name binding ctx
        ) (NR.createContext ())
    {
        Globals = globals
        Resolution = baseResolver
        TypeDefs = Map.empty
        TypeAbbrevs = Map.empty
        RecordDefs = Map.empty
        FieldLabels = Map.empty
        Constraints = ref []
        Diagnostics = ref []
        CurrentArena = ArenaAffinity.CurrentActor
        ExpectedReturnType = None
        EnclosingFunction = None
        EnclosingSeqExpr = None
    }

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
    } env

/// Create and add a warning diagnostic (generic fallback)
let addWarning (r: range) (message: string) (env: TypeEnv) : unit =
    addNativeWarning DiagnosticCodes.FS0002_GenericWarning r message env

//-------------------------------------------------------------------------
// Native-Specific Error Helpers
//-------------------------------------------------------------------------

/// Emit FS8100: Cannot use 'null' in F# Native
let addNullError (r: range) (env: TypeEnv) : unit =
    addNativeError DiagnosticCodes.FS8100_NullLiteral r
        "Cannot use 'null' in F# Native; use 'ValueNone' for optional values" env

/// Emit FS8011: The type 'obj' is not available in F# Native
let addObjError (r: range) (env: TypeEnv) : unit =
    addNativeError DiagnosticCodes.FS8011_ObjNotSupported r
        "The type 'obj' (System.Object) is not available in F# Native; use discriminated unions or SRTP" env

/// Emit FS8012: Boxing is not supported
let addBoxingError (r: range) (env: TypeEnv) : unit =
    addNativeError DiagnosticCodes.FS8012_BoxingNotSupported r
        "Boxing is not supported in F# Native; the native type system does not include 'obj'" env

/// Emit warning for null annotation - ignored in F# Native
let addNullWarning (r: range) (env: TypeEnv) : unit =
    addNativeWarning DiagnosticCodes.FS8101_UninitializedValue r
        "Nullable annotation ignored in F# Native; native types are null-free by design" env

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

/// Add a type definition to the environment
let addTypeDef (name: string) (tyCon: TypeConRef) (env: TypeEnv) : TypeEnv =
    { env with TypeDefs = Map.add name tyCon env.TypeDefs }

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
// Per fsnative-spec inference-procedures.md Field Label Resolution
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
/// Per fsnative-spec inference-procedures.md: Field Label Resolution Algorithm
///
/// Steps:
/// 1. For each field f_i in the expression, get C_i = candidates(f_i)
/// 2. Compute intersection: I = C_1 ∩ C_2 ∩ ... ∩ C_n
/// 3. Disambiguate based on |I|
///
/// Returns Ok(recordType) or Error(diagnosticCode, message)
let resolveRecordTypeFromFields
    (fieldNames: string list)
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

            // Step 3: Disambiguate
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
                    // Fields accessed via tryGetRecordFields lookup per Section 7.2
                    Result.Ok (NativeType.TApp(recordInfo.TypeCon, []))
                | None ->
                    // INTERNAL ERROR: Field label resolution found this type name,
                    // so it MUST exist in RecordDefs.
                    Result.Error((DiagnosticCodes.FS0001_GenericError,
                           sprintf "Internal error: field labels reference record type '%s' but it is not in RecordDefs" typeName))
            | _ ->
                // FS8704: Ambiguous fields - multiple record types could match
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
let resolveFieldType (baseType: NativeType) (fieldName: string) (env: TypeEnv) (range: SourceRange) : NativeType =
    let isStringType ty =
        match ty with
        | NativeType.TApp(tycon, []) when tycon.Name = "string" -> true
        | _ -> false
    let isArrayType ty =
        match ty with
        | NativeType.TApp(tycon, [_]) when tycon.Name = "array" -> true
        | _ -> false

    let resolvedType = applySubst baseType

    // 1. Check intrinsic members (string.Pointer, string.Length, array.Length)
    match fieldName with
    | "Pointer" when isStringType resolvedType ->
        NativeType.TNativePtr(Types.uint8Type)
    | "Length" when isStringType resolvedType ->
        env.Globals.IntType
    | "Length" when isArrayType resolvedType ->
        env.Globals.IntType
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

//-------------------------------------------------------------------------
// BCL Rejection - CRITICAL
// BCL types/namespaces are NEVER allowed in F# Native
//-------------------------------------------------------------------------

/// Check if a name references BCL (Base Class Library) namespaces
/// BCL references are FORBIDDEN in F# Native - they require .NET runtime
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

/// Emit FS8104: Unchecked.defaultof not allowed in F# Native
let addUncheckedError (name: string) (r: range) (env: TypeEnv) : unit =
    addNativeError DiagnosticCodes.FS8104_UncheckedDefault r
        $"'{name}' is not available in F# Native. Unchecked.defaultof requires runtime type information. Use explicit initialization, FNCS intrinsics, or NativeDefault.zeroed instead." env

/// Emit FS8500: BCL reference not allowed in F# Native
let addBclError (name: string) (r: range) (env: TypeEnv) : unit =
    if isUncheckedReference name then
        addUncheckedError name r env
    else
        addNativeError DiagnosticCodes.FS8500_BclReferenceNotAllowed r
            $"BCL reference '{name}' is not available in F# Native. The .NET Base Class Library requires the .NET runtime. Use Alloy library equivalents instead." env
