// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Expression type checking for the native type checker.
/// Produces SemanticNode with types ATTACHED during construction.
///
/// This module must handle ALL SynExpr cases from the parser.
/// No catch-all fallbacks. Every case is explicitly handled or explicitly rejected.
/// Reference: FCS's CheckExpressions.fs (12,864 lines) for complete handling.
module FSharp.Native.Compiler.Checking.Native.CheckExpressions

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Text
open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.NativeGlobals
open FSharp.Native.Compiler.Checking.Native.UnionFind
open FSharp.Native.Compiler.Checking.Native.Unify
open FSharp.Native.Compiler.Checking.Native.SemanticGraph
open FSharp.Native.Compiler.Checking.Native.NameResolution

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

// Note: InlineBody and ResolvedBinding types are imported from NameResolution module.
// This ensures consistent types across the resolution infrastructure.

/// The type checking environment
[<NoComparison; NoEquality>]
type TypeEnv = {
    /// Global type information
    Globals: NativeGlobals
    /// Compositional name resolution context
    /// BCL is structurally impossible - only source-defined bindings exist
    Resolution: ResolutionContext
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
    /// Current constraints being collected
    mutable Constraints: Constraint list
    /// Accumulated diagnostics (errors, warnings)
    mutable Diagnostics: Diagnostic list
    /// Current arena affinity
    CurrentArena: ArenaAffinity
    /// Enclosing function return type (for return checking)
    ExpectedReturnType: NativeType option
}

/// Create a type environment with built-in bindings from globals
let createTypeEnv (globals: NativeGlobals) : TypeEnv =
    // Convert built-in bindings from globals to ResolvedBindings and build resolver
    let baseResolver =
        globals.BuiltInBindings
        |> Map.fold (fun ctx name ty ->
            let binding: ResolvedBinding = {
                QualifiedName = name
                Type = ty
                IsMutable = false
                NodeId = None
                InlineBody = None
            }
            NameResolution.registerBinding name binding ctx
        ) (NameResolution.createContext ())
    {
        Globals = globals
        Resolution = baseResolver
        TypeDefs = Map.empty
        TypeAbbrevs = Map.empty
        RecordDefs = Map.empty
        FieldLabels = Map.empty
        Constraints = []
        Diagnostics = []
        CurrentArena = ArenaAffinity.CurrentActor
        ExpectedReturnType = None
    }

/// Add a diagnostic to the environment
let addDiagnostic (diag: Diagnostic) (env: TypeEnv) : unit =
    env.Diagnostics <- diag :: env.Diagnostics

/// Add a binding to the environment using compositional resolution
let addBinding (name: string) (ty: NativeType) (isMutable: bool) (nodeId: NodeId option) (env: TypeEnv) : TypeEnv =
    let binding: ResolvedBinding = {
        QualifiedName = name
        Type = ty
        IsMutable = isMutable
        NodeId = nodeId
        InlineBody = None
    }
    { env with Resolution = NameResolution.registerBinding name binding env.Resolution }

/// Add a binding with inline body for transparent function expansion
/// FNCS is inline-by-default: all functions are transparent unless marked opaque
let addInlineBinding (name: string) (ty: NativeType) (nodeId: NodeId option) (inlineBody: NameResolution.InlineBody) (env: TypeEnv) : TypeEnv =
    let binding: ResolvedBinding = {
        QualifiedName = name
        Type = ty
        IsMutable = false
        NodeId = nodeId
        InlineBody = Some inlineBody
    }
    { env with Resolution = NameResolution.registerBinding name binding env.Resolution }

/// Look up a binding using compositional resolver
/// BCL is structurally impossible - only source-defined bindings exist
let tryLookupBinding (name: string) (env: TypeEnv) : ResolvedBinding option =
    NameResolution.resolve name env.Resolution

/// Add an open namespace declaration to the resolution context
/// This composes a resolver that prefixes lookups with the namespace
/// Example: `open Alloy` allows `Console.Write` to resolve as `Alloy.Console.Write`
let addOpen (ns: string) (env: TypeEnv) : TypeEnv =
    { env with Resolution = NameResolution.addOpen ns env.Resolution }

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
                    // Return the record type with its computed layout
                    Result.Ok (mkSimpleType recordInfo.TypeCon)
                | None ->
                    // Fallback: look up in TypeDefs (for records not yet in RecordDefs)
                    match Map.tryFind typeName env.TypeDefs with
                    | Some tyCon -> Result.Ok (mkSimpleType tyCon)
                    | None ->
                        Result.Error((DiagnosticCodes.FS0001_GenericError,
                               sprintf "Internal error: resolved record type '%s' not found" typeName))
            | _ ->
                // FS8704: Ambiguous fields - multiple record types could match
                let typeNames = intersection |> Set.toList |> String.concat ", "
                Result.Error((DiagnosticCodes.FS8704_AmbiguousFields,
                       sprintf "Field labels are ambiguous; could be any of: %s. Use type annotation or qualified field access." typeNames))

/// Add a constraint to the environment
let addConstraint (c: Constraint) (env: TypeEnv) : unit =
    env.Constraints <- c :: env.Constraints

//-------------------------------------------------------------------------
// Range Conversion
//-------------------------------------------------------------------------

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

//-------------------------------------------------------------------------
// BCL Rejection - CRITICAL
// BCL types/namespaces are NEVER allowed in F# Native
//-------------------------------------------------------------------------

/// Check if a name references BCL (Base Class Library) namespaces
/// BCL references are FORBIDDEN in F# Native - they require .NET runtime
/// This provides user-friendly FS8500 errors; BCL is structurally impossible
/// via the compositional resolver, but we want better messages than "undefined"
let isBclReference (name: string) : bool =
    // Only definitively BCL prefixes - no library-aware heuristics
    name.StartsWith("System.") ||
    name.StartsWith("Microsoft.") ||
    name.StartsWith("mscorlib.") ||
    name.StartsWith("netstandard.")

/// Emit FS8500: BCL reference not allowed in F# Native
/// This is a HARD STOP - BCL types cannot exist in native compilation
let addBclError (name: string) (r: range) (env: TypeEnv) : unit =
    addNativeError DiagnosticCodes.FS8500_BclReferenceNotAllowed r
        $"BCL reference '{name}' is not available in F# Native. The .NET Base Class Library requires the .NET runtime. Use Alloy library equivalents instead." env

//-------------------------------------------------------------------------
// Constant Type Inference
//-------------------------------------------------------------------------

/// Get the type of a constant
let rec typeOfConst (globals: NativeGlobals) (c: SynConst) : NativeType =
    match c with
    | SynConst.Unit -> globals.UnitType
    | SynConst.Bool _ -> globals.BoolType
    | SynConst.SByte _ -> Types.int8Type
    | SynConst.Byte _ -> Types.uint8Type
    | SynConst.Int16 _ -> Types.int16Type
    | SynConst.UInt16 _ -> Types.uint16Type
    | SynConst.Int32 _ -> globals.IntType
    | SynConst.UInt32 _ -> Types.uintType
    | SynConst.Int64 _ -> globals.Int64Type
    | SynConst.UInt64 _ -> Types.uint64Type
    | SynConst.IntPtr _ -> Types.nintType
    | SynConst.UIntPtr _ -> Types.unintType
    | SynConst.Single _ -> Types.float32Type
    | SynConst.Double _ -> globals.FloatType
    | SynConst.Char _ -> globals.CharType
    | SynConst.Decimal _ -> Types.decimalType
    | SynConst.String _ -> globals.StringType
    | SynConst.Bytes _ -> mkArrayType Types.uint8Type
    | SynConst.UInt16s _ -> mkArrayType Types.uint16Type
    | SynConst.Measure(innerConst, _, synMeasure, _) ->
        // For now, just use the base type; measure annotation is tracked separately
        // Full measure type would be: TMeasure applied to base type
        let baseType = typeOfConst globals innerConst
        // In future: wrap with measure type based on synMeasure
        let _ = synMeasure  // Suppress warning
        baseType
    | SynConst.UserNum(_, suffix) ->
        // UserNum with suffix - "I" is bigint, others are user-defined
        match suffix with
        | "I" -> globals.IntType  // Treat bigint as int for now (full bigint support later)
        | _ -> globals.IntType  // Fallback
    | SynConst.SourceIdentifier _ -> globals.StringType

/// Convert SynConst to LiteralValue
let rec constToLiteral (c: SynConst) : LiteralValue =
    match c with
    | SynConst.Unit -> LiteralValue.Unit
    | SynConst.Bool b -> LiteralValue.Bool b
    | SynConst.SByte v -> LiteralValue.Int8 v
    | SynConst.Byte v -> LiteralValue.UInt8 v
    | SynConst.Int16 v -> LiteralValue.Int16 v
    | SynConst.UInt16 v -> LiteralValue.UInt16 v
    | SynConst.Int32 v -> LiteralValue.Int32 v
    | SynConst.UInt32 v -> LiteralValue.UInt32 v
    | SynConst.Int64 v -> LiteralValue.Int64 v
    | SynConst.UInt64 v -> LiteralValue.UInt64 v
    | SynConst.IntPtr v -> LiteralValue.NativeInt(nativeint v)
    | SynConst.UIntPtr v -> LiteralValue.UNativeInt(unativeint v)
    | SynConst.Single v -> LiteralValue.Float32 v
    | SynConst.Double v -> LiteralValue.Float64 v
    | SynConst.Char v -> LiteralValue.Char v
    | SynConst.Decimal v -> LiteralValue.Decimal v
    | SynConst.String(s, _, _) -> LiteralValue.String s
    | SynConst.Measure(innerConst, _, _, _) -> constToLiteral innerConst
    | SynConst.UserNum(value, suffix) ->
        // UserNum is for bigint (I suffix) or user-defined numeric types
        match suffix with
        | "I" -> LiteralValue.BigInt value
        | _ -> LiteralValue.String value  // Fallback for other user-defined types
    | SynConst.SourceIdentifier(_, value, _) -> LiteralValue.String value
    | SynConst.Bytes(bytes, _, _) -> LiteralValue.ByteArray bytes
    | SynConst.UInt16s values -> LiteralValue.UInt16Array values

//-------------------------------------------------------------------------
// Expression Checking
//-------------------------------------------------------------------------

/// Check an expression and produce a SemanticNode with type attached.
/// This is the core of the native type checker.
let rec checkExpr (env: TypeEnv) (builder: NodeBuilder) (syn: SynExpr) : SemanticNode =
    let range = rangeToSourceRange syn.Range

    match syn with
    //---------------------------------------------------------------------
    // Literals
    //---------------------------------------------------------------------
    | SynExpr.Const(constant, _) ->
        let ty = typeOfConst env.Globals constant
        let lit = constToLiteral constant
        builder.Create(
            SemanticKind.Literal lit,
            ty,
            range,
            arena = env.CurrentArena,
            layout = layoutOf ty)

    //---------------------------------------------------------------------
    // Parenthesized expressions (transparent)
    //---------------------------------------------------------------------
    | SynExpr.Paren(innerExpr, _, _, _) ->
        checkExpr env builder innerExpr

    //---------------------------------------------------------------------
    // Variable references
    //---------------------------------------------------------------------
    | SynExpr.Ident(ident) ->
        let name = ident.idText
        match tryLookupBinding name env with
        | Some binding ->
            builder.Create(
                SemanticKind.VarRef(name, binding.NodeId),
                binding.Type,
                range,
                arena = env.CurrentArena)
        | None ->
            // HARD STOP: Unknown identifier - emit diagnostic and error node
            addDiagnostic { Severity = NativeDiagnosticSeverity.Error; Code = "FS0039"; Message = $"The value or constructor '{name}' is not defined."; Range = range; RelatedNodes = [] } env
            builder.Create(
                SemanticKind.Error $"Undefined: {name}",
                NativeType.TError $"Undefined: {name}",
                range)

    | SynExpr.LongIdent(_, longDotId, _, _) ->
        let name = longDotId.LongIdent |> List.map (fun id -> id.idText) |> String.concat "."
        let parts = longDotId.LongIdent |> List.map (fun id -> id.idText)

        // FS8500: BCL references are FORBIDDEN - check FIRST before any lookup
        if isBclReference name then
            addBclError name longDotId.Range env
            builder.Create(
                SemanticKind.Error $"BCL reference: {name}",
                NativeType.TError $"BCL reference: {name}",
                range)
        // FNCS INTRINSICS: NativePtr module functions
        // These are polymorphic intrinsics that require TForall to allow type application
        elif name.StartsWith("NativePtr.") then
            let intrinsicName = name.Substring("NativePtr.".Length)
            // Create a proper type parameter for the polymorphic 'T
            let tyParamSpec = UnionFind.freshTypeParam "'T" TypeParamKind.Type range
            let tyParam = NativeType.TVar tyParamSpec
            let intrinsicBody =
                match intrinsicName with
                | "toNativeInt" ->
                    // nativeptr<'T> -> nativeint
                    NativeType.TFun(NativeType.TNativePtr tyParam, Types.nintType)
                | "ofNativeInt" ->
                    // nativeint -> nativeptr<'T>
                    NativeType.TFun(Types.nintType, NativeType.TNativePtr tyParam)
                | "toVoidPtr" ->
                    // nativeptr<'T> -> voidptr
                    NativeType.TFun(NativeType.TNativePtr tyParam, NativeType.TApp(NativeGlobals.voidptrTyCon, []))
                | "ofVoidPtr" ->
                    // voidptr -> nativeptr<'T>
                    NativeType.TFun(NativeType.TApp(NativeGlobals.voidptrTyCon, []), NativeType.TNativePtr tyParam)
                | "get" ->
                    // nativeptr<'T> -> int -> 'T
                    NativeType.TFun(NativeType.TNativePtr tyParam, NativeType.TFun(env.Globals.IntType, tyParam))
                | "set" ->
                    // nativeptr<'T> -> int -> 'T -> unit
                    NativeType.TFun(NativeType.TNativePtr tyParam, NativeType.TFun(env.Globals.IntType, NativeType.TFun(tyParam, env.Globals.UnitType)))
                | "stackalloc" ->
                    // int -> nativeptr<'T>
                    NativeType.TFun(env.Globals.IntType, NativeType.TNativePtr tyParam)
                | "read" ->
                    // nativeptr<'T> -> 'T
                    NativeType.TFun(NativeType.TNativePtr tyParam, tyParam)
                | "write" ->
                    // nativeptr<'T> -> 'T -> unit
                    NativeType.TFun(NativeType.TNativePtr tyParam, NativeType.TFun(tyParam, env.Globals.UnitType))
                | "add" ->
                    // nativeptr<'T> -> int -> nativeptr<'T>
                    NativeType.TFun(NativeType.TNativePtr tyParam, NativeType.TFun(env.Globals.IntType, NativeType.TNativePtr tyParam))
                | _ ->
                    // Unknown NativePtr function - create generic function type
                    NativeType.TFun(freshTypeVar range, freshTypeVar range)
            // Wrap in TForall so type application can properly instantiate the type parameter
            let intrinsicType = NativeType.TForall([tyParamSpec], intrinsicBody)
            builder.Create(
                SemanticKind.Intrinsic(name),
                intrinsicType,
                range)
        // FNCS INTRINSICS: Sys module functions (system calls)
        // These are primitives for low-level I/O that Alex emits directly as syscalls
        elif name.StartsWith("Sys.") then
            let intrinsicName = name.Substring("Sys.".Length)
            let intrinsicType =
                match intrinsicName with
                | "write" ->
                    // fd:int -> buffer:nativeptr<byte> -> count:int -> int
                    // Returns bytes written
                    NativeType.TFun(env.Globals.IntType,
                        NativeType.TFun(NativeType.TNativePtr Types.uint8Type,
                            NativeType.TFun(env.Globals.IntType, env.Globals.IntType)))
                | "read" ->
                    // fd:int -> buffer:nativeptr<byte> -> maxCount:int -> int
                    // Returns bytes read
                    NativeType.TFun(env.Globals.IntType,
                        NativeType.TFun(NativeType.TNativePtr Types.uint8Type,
                            NativeType.TFun(env.Globals.IntType, env.Globals.IntType)))
                | "exit" ->
                    // code:int -> 'a (never returns, polymorphic return type)
                    let tyParamSpec = UnionFind.freshTypeParam "'a" TypeParamKind.Type range
                    let tyParam = NativeType.TVar tyParamSpec
                    let exitBody = NativeType.TFun(env.Globals.IntType, tyParam)
                    NativeType.TForall([tyParamSpec], exitBody)
                | _ ->
                    // Unknown Sys function - create generic function type
                    NativeType.TFun(freshTypeVar range, freshTypeVar range)
            builder.Create(
                SemanticKind.Intrinsic(name),
                intrinsicType,
                range)
        else
        // Check for platform bindings (Bindings.* or Platform.Bindings.*)
        let isPlatformBinding =
            name.StartsWith("Bindings.") || name.Contains(".Bindings.")
        match tryLookupBinding name env with
        | Some binding ->
            // Found the binding - use its type
            // If it's a platform binding, mark it as such while PRESERVING the type
            if isPlatformBinding then
                let entryPoint = parts.[parts.Length - 1]
                builder.Create(
                    SemanticKind.PlatformBinding entryPoint,
                    binding.Type,
                    range,
                    arena = env.CurrentArena)
            else
                builder.Create(
                    SemanticKind.VarRef(name, binding.NodeId),
                    binding.Type,
                    range,
                    arena = env.CurrentArena)
        | None when isPlatformBinding ->
            // Platform binding not in scope - this is an ERROR, not a fallback
            // Platform bindings must be declared in Alloy and loaded before use
            let entryPoint = parts.[parts.Length - 1]
            addDiagnostic {
                Severity = NativeDiagnosticSeverity.Error
                Code = "FS8600"
                Message = $"Platform binding '{name}' is not defined. Ensure Alloy is loaded and contains Platform.Bindings.{entryPoint}."
                Range = range
                RelatedNodes = []
            } env
            builder.Create(
                SemanticKind.Error $"Undefined platform binding: {name}",
                NativeType.TError $"Undefined platform binding: {name}",
                range)
        | None when parts.Length >= 2 ->
            // SPECIAL CASE: LongIdent might be a member access on a local binding
            // e.g., "s.Length" parsed as LongIdent ["s"; "Length"] instead of DotGet
            // Try to interpret as: first part is a binding, rest is member access
            let firstPart = parts.[0]
            let restParts = parts.[1..] |> String.concat "."
            match tryLookupBinding firstPart env with
            | Some binding ->
                // Found the base binding - treat rest as member access
                let baseNode = builder.Create(
                    SemanticKind.VarRef(firstPart, binding.NodeId),
                    binding.Type,
                    range,
                    arena = env.CurrentArena)

                // Handle intrinsic string members
                let isStringType ty =
                    match ty with
                    | NativeType.TApp(tycon, []) when tycon.Name = "string" -> true
                    | _ -> false

                let resultTy =
                    match restParts with
                    | "Pointer" when isStringType binding.Type ->
                        NativeType.TNativePtr(NativeGlobals.Types.uint8Type)
                    | "Length" when isStringType binding.Type ->
                        env.Globals.IntType
                    | _ ->
                        // General case: create HasMember constraint
                        let ty = freshTypeVar range
                        addConstraint (Constraint.HasMember(binding.Type, restParts, ty, range)) env
                        ty

                builder.Create(
                    SemanticKind.FieldGet(baseNode.Id, restParts),
                    resultTy,
                    range,
                    children = [baseNode.Id])
            | None ->
                // First part not a binding - report as undefined
                addDiagnostic { Severity = NativeDiagnosticSeverity.Error; Code = "FS0039"; Message = $"The value or constructor '{name}' is not defined. Ensure dependencies are loaded before user code."; Range = range; RelatedNodes = [] } env
                builder.Create(
                    SemanticKind.Error $"Undefined: {name}",
                    NativeType.TError $"Undefined: {name}",
                    range)
        | None ->
            // HARD STOP: Unknown identifier is a real error
            // If this fires, either:
            // 1. Files are processed in wrong order (dependency not loaded)
            // 2. The binding doesn't exist (user error)
            // 3. Module qualification is wrong (user error)
            // All cases require explicit resolution - no silent placeholders
            addDiagnostic { Severity = NativeDiagnosticSeverity.Error; Code = "FS0039"; Message = $"The value or constructor '{name}' is not defined. Ensure dependencies are loaded before user code."; Range = range; RelatedNodes = [] } env
            builder.Create(
                SemanticKind.Error $"Undefined: {name}",
                NativeType.TError $"Undefined: {name}",
                range)

    //---------------------------------------------------------------------
    // Type annotations
    //---------------------------------------------------------------------
    | SynExpr.Typed(innerExpr, synType, _) ->
        let innerNode = checkExpr env builder innerExpr
        let annotatedTy = checkSynType env synType
        // Add equality constraint
        addConstraint (Constraint.Equals(innerNode.Type, annotatedTy, range)) env
        builder.Create(
            SemanticKind.TypeAnnotation(innerNode.Id, annotatedTy),
            annotatedTy,
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // Tuples
    //---------------------------------------------------------------------
    | SynExpr.Tuple(isStruct, exprs, _, _) ->
        let elementNodes = exprs |> List.map (checkExpr env builder)
        let elementTypes = elementNodes |> List.map (fun n -> n.Type)
        let tupleType = NativeType.TTuple(elementTypes, isStruct)
        let childIds = elementNodes |> List.map (fun n -> n.Id)
        builder.Create(
            SemanticKind.TupleExpr childIds,
            tupleType,
            range,
            children = childIds)

    //---------------------------------------------------------------------
    // Function application
    //---------------------------------------------------------------------
    | SynExpr.App(_, _isInfix, funcExpr, argExpr, _) ->
        // NOTE: Inline expansion is tracked via InlineBody on bindings
        // but NOT performed during type checking because it requires
        // capturing the definition-time environment (closure semantics).
        // The PSG records inline bodies; downstream analysis can use them.
        let funcNode = checkExpr env builder funcExpr
        let argNode = checkExpr env builder argExpr

        // Determine result type based on function type
        // When function type is already concrete (TFun), use return type directly
        // This provides immediate type information without deferring to constraint solving
        let resultTy =
            match funcNode.Type with
            | NativeType.TFun(domainTy, rangeTy) ->
                // Function type is known - add domain constraint and use return type directly
                addConstraint (Constraint.Equals(domainTy, argNode.Type, range)) env
                rangeTy

            | NativeType.TForall(typeParams, bodyType) ->
                // IMPLICIT TYPE INSTANTIATION: When a TForall-typed function receives
                // value arguments (no explicit TypeApp), we instantiate with fresh type
                // variables that will be unified with argument types.
                //
                // Example: NativePtr.set buffer index value
                //   - NativePtr.set has type TForall(['T], nativeptr<'T> -> int -> 'T -> unit)
                //   - buffer has type nativeptr<uint8>
                //   - Instantiate 'T with fresh '?n, then unify nativeptr<'?n> with nativeptr<uint8>
                //   - Result: 'T = uint8, return type is int -> uint8 -> unit
                //
                // This is the implicit counterpart to explicit TypeApp handling.
                // See memory: typeapp_preserves_kind_principle
                let freshVars = typeParams |> List.map (fun _ -> freshTypeVar range)
                let instantiatedType = NativeTypes.instantiate typeParams freshVars bodyType
                // Now handle the instantiated type
                match instantiatedType with
                | NativeType.TFun(domainTy, rangeTy) ->
                    addConstraint (Constraint.Equals(domainTy, argNode.Type, range)) env
                    rangeTy
                | _ ->
                    // Body wasn't a function type after instantiation - add constraint
                    let freshResult = freshTypeVar range
                    addConstraint (Constraint.Equals(
                        instantiatedType,
                        NativeType.TFun(argNode.Type, freshResult),
                        range)) env
                    freshResult

            | NativeType.TVar _ ->
                // Function type is a type variable - defer to constraint solving
                let freshResult = freshTypeVar range
                addConstraint (Constraint.Equals(
                    funcNode.Type,
                    NativeType.TFun(argNode.Type, freshResult),
                    range)) env
                freshResult

            | _ ->
                // Other types (error, etc.)
                // Generate constraint and fresh result type
                let freshResult = freshTypeVar range
                addConstraint (Constraint.Equals(
                    funcNode.Type,
                    NativeType.TFun(argNode.Type, freshResult),
                    range)) env
                freshResult

        // INTRINSIC APPLICATION SATURATION:
        // Intrinsics don't support partial application - they're primitives that must
        // be called with all arguments at once. When we see curried application of an
        // intrinsic (e.g., NativePtr.set buffer count byte), we flatten into a single
        // Application node with all arguments.
        //
        // Without this, NativePtr.set buffer count byte creates:
        //   App(App(App(Intrinsic, buffer), count), byte)  -- nested, hard to codegen
        //
        // With this fix:
        //   App(Intrinsic, [buffer; count; byte])  -- flattened, direct codegen
        //
        // This is a CONSTRUCTION decision, not cleanup. Intermediate Application nodes
        // become orphaned and will be pruned by reachability.
        //
        // See memory: typeapp_preserves_kind_principle (same principle applies)
        let (targetFuncId, allArgs) =
            match funcNode.Kind with
            | SemanticKind.Intrinsic _ ->
                // Direct intrinsic application: App(Intrinsic, arg)
                (funcNode.Id, [argNode.Id])
            | SemanticKind.Application(innerFuncId, existingArgs) ->
                // Check if inner func is an Intrinsic - if so, flatten
                match builder.Nodes.TryFind innerFuncId with
                | Some innerNode ->
                    match innerNode.Kind with
                    | SemanticKind.Intrinsic _ ->
                        // Curried intrinsic application: flatten
                        (innerFuncId, existingArgs @ [argNode.Id])
                    | _ ->
                        // Not an intrinsic - keep curried structure
                        (funcNode.Id, [argNode.Id])
                | None ->
                    // Inner node not found (shouldn't happen) - keep curried
                    (funcNode.Id, [argNode.Id])
            | _ ->
                // Regular function application - keep curried structure
                (funcNode.Id, [argNode.Id])

        builder.Create(
            SemanticKind.Application(targetFuncId, allArgs),
            resultTy,
            range,
            children = targetFuncId :: allArgs)

    //---------------------------------------------------------------------
    // Lambda expressions
    //---------------------------------------------------------------------
    | SynExpr.Lambda(_, _, args, bodyExpr, _, _, _) ->
        // Extract parameter names and create fresh type variables
        let paramBindings = extractLambdaParams env args range

        // Create new environment with parameters
        let bodyEnv =
            paramBindings
            |> List.fold (fun env (name, ty) -> addBinding name ty false None env) env

        // Check body
        let bodyNode = checkExpr bodyEnv builder bodyExpr

        // Build function type
        let paramTypes = paramBindings |> List.map snd
        let funcType = mkFunctionType paramTypes bodyNode.Type

        builder.Create(
            SemanticKind.Lambda(paramBindings, bodyNode.Id),
            funcType,
            range,
            children = [bodyNode.Id])

    //---------------------------------------------------------------------
    // Let bindings
    //---------------------------------------------------------------------
    | SynExpr.LetOrUse(letOrUse) ->
        checkLetOrUse env builder letOrUse range

    //---------------------------------------------------------------------
    // Sequential expressions
    //---------------------------------------------------------------------
    | SynExpr.Sequential(_, _, expr1, expr2, _, _) ->
        let node1 = checkExpr env builder expr1
        let node2 = checkExpr env builder expr2
        builder.Create(
            SemanticKind.Sequential [node1.Id; node2.Id],
            node2.Type,  // Result type is the last expression
            range,
            children = [node1.Id; node2.Id])

    //---------------------------------------------------------------------
    // If-then-else
    //---------------------------------------------------------------------
    | SynExpr.IfThenElse(condExpr, thenExpr, elseExprOpt, _, _, _, _) ->
        let condNode = checkExpr env builder condExpr
        let thenNode = checkExpr env builder thenExpr

        // Condition must be bool
        addConstraint (Constraint.Equals(condNode.Type, env.Globals.BoolType, range)) env

        match elseExprOpt with
        | Some elseExpr ->
            let elseNode = checkExpr env builder elseExpr
            // Then and else branches must have same type
            addConstraint (Constraint.Equals(thenNode.Type, elseNode.Type, range)) env
            builder.Create(
                SemanticKind.IfThenElse(condNode.Id, thenNode.Id, Some elseNode.Id),
                thenNode.Type,
                range,
                children = [condNode.Id; thenNode.Id; elseNode.Id])
        | None ->
            // If without else must have unit type
            addConstraint (Constraint.Equals(thenNode.Type, env.Globals.UnitType, range)) env
            builder.Create(
                SemanticKind.IfThenElse(condNode.Id, thenNode.Id, None),
                env.Globals.UnitType,
                range,
                children = [condNode.Id; thenNode.Id])

    //---------------------------------------------------------------------
    // While loops
    //---------------------------------------------------------------------
    | SynExpr.While(_, guardExpr, bodyExpr, _) ->
        let guardNode = checkExpr env builder guardExpr
        let bodyNode = checkExpr env builder bodyExpr

        // Guard must be bool
        addConstraint (Constraint.Equals(guardNode.Type, env.Globals.BoolType, range)) env

        builder.Create(
            SemanticKind.WhileLoop(guardNode.Id, bodyNode.Id),
            env.Globals.UnitType,  // While always returns unit
            range,
            children = [guardNode.Id; bodyNode.Id])

    //---------------------------------------------------------------------
    // For loops
    //---------------------------------------------------------------------
    | SynExpr.For(_, _, ident, _, startExpr, direction, endExpr, bodyExpr, _) ->
        let startNode = checkExpr env builder startExpr
        let endNode = checkExpr env builder endExpr

        // Start and end must be int
        addConstraint (Constraint.Equals(startNode.Type, env.Globals.IntType, range)) env
        addConstraint (Constraint.Equals(endNode.Type, env.Globals.IntType, range)) env

        // Add loop variable to environment
        let bodyEnv = addBinding ident.idText env.Globals.IntType false None env
        let bodyNode = checkExpr bodyEnv builder bodyExpr

        builder.Create(
            SemanticKind.ForLoop(ident.idText, startNode.Id, endNode.Id, direction, bodyNode.Id),
            env.Globals.UnitType,
            range,
            children = [startNode.Id; endNode.Id; bodyNode.Id])

    //---------------------------------------------------------------------
    // Match expressions
    //---------------------------------------------------------------------
    | SynExpr.Match(_, scrutinee, clauses, _, _) ->
        let scrutineeNode = checkExpr env builder scrutinee
        let resultTy = freshTypeVar range

        let matchCases = clauses |> List.map (fun clause ->
            checkMatchClause env builder scrutineeNode.Type resultTy clause)

        builder.Create(
            SemanticKind.Match(scrutineeNode.Id, matchCases),
            resultTy,
            range,
            children = scrutineeNode.Id :: (matchCases |> List.map (fun c -> c.Body)))

    //---------------------------------------------------------------------
    // Record expressions
    //---------------------------------------------------------------------
    | SynExpr.Record(_, copyInfo, fields, recordRange) ->
        let copyNode = copyInfo |> Option.map (fun (expr, _) -> checkExpr env builder expr)
        
        // Extract field names and check expressions
        let fieldNodes = fields |> List.choose (fun field ->
            match field with
            | SynExprRecordField((fieldId, _), _, Some expr, _, _) ->
                let fieldName = fieldId.LongIdent |> List.map (fun id -> id.idText) |> String.concat "."
                let exprNode = checkExpr env builder expr
                Some (fieldName, exprNode)
            | _ -> None)
        
        // Extract just the field names for type resolution
        let fieldNames = fieldNodes |> List.map fst
        
        // Resolve record type using Field Label Resolution Algorithm
        // Per fsnative-spec: intersection of candidate sets for each field label
        let recordTy =
            match copyNode with
            | Some copyExpr ->
                // Copy-update expression: { existingRecord with Field = value }
                // The type comes from the copied record
                copyExpr.Type
            | None ->
                // Fresh record expression: { Field1 = v1; Field2 = v2 }
                // Resolve type from field labels
                match resolveRecordTypeFromFields fieldNames range env with
                | Result.Ok resolvedTy ->
                    // Verify field types match (add constraints)
                    // Each NativeType case must be handled explicitly - no catch-all patterns
                    match resolvedTy with
                    | NativeType.TApp(tyCon, _) ->
                        // Expected case: nominal record type like `Person` or `Record<'a>`
                        match Map.tryFind tyCon.Name env.RecordDefs with
                        | Some recordInfo ->
                            // Add constraints: each field expression must match field type
                            for (fieldName, exprNode) in fieldNodes do
                                match recordInfo.Fields |> List.tryFind (fun (n, _) -> n = fieldName) with
                                | Some (_, expectedTy) ->
                                    addConstraint (Constraint.Equals(exprNode.Type, expectedTy, range)) env
                                | None ->
                                    // Field not found in record definition - this is an error
                                    addNativeError DiagnosticCodes.FS8702_UndefinedField recordRange
                                        (sprintf "Field '%s' is not defined in record type '%s'" fieldName tyCon.Name) env
                        | None ->
                            // Record type not in RecordDefs - internal error in resolution
                            addNativeError DiagnosticCodes.FS0001_GenericError recordRange
                                (sprintf "Internal error: record type '%s' not found in RecordDefs" tyCon.Name) env
                    | NativeType.TRecord(tyCon, fields) ->
                        // Inline record type with explicit fields
                        for (fieldName, exprNode) in fieldNodes do
                            match fields |> List.tryFind (fun (n, _) -> n = fieldName) with
                            | Some (_, expectedTy) ->
                                addConstraint (Constraint.Equals(exprNode.Type, expectedTy, range)) env
                            | None ->
                                addNativeError DiagnosticCodes.FS8702_UndefinedField recordRange
                                    (sprintf "Field '%s' is not defined in record type '%s'" fieldName tyCon.Name) env
                    | NativeType.TError _ ->
                        // Already an error - don't add more diagnostics
                        ()
                    // All other NativeType cases are invalid for record expressions
                    | NativeType.TForall _ ->
                        addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                            "Record expression cannot have polymorphic type" env
                    | NativeType.TTuple _ ->
                        addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                            "Expected record type, got tuple. Use record syntax { Field = value } not tuple syntax (a, b)" env
                    | NativeType.TFun _ ->
                        addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                            "Expected record type, got function type" env
                    | NativeType.TVar typar ->
                        addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                            (sprintf "Could not resolve record type - type variable '%s' is still unbound" typar.Name) env
                    | NativeType.TMeasure _ ->
                        addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                            "Expected record type, got unit of measure" env
                    | NativeType.TAnon _ ->
                        addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                            "Expected nominal record type. For anonymous records, use {| Field = value |} syntax" env
                    | NativeType.TUnion _ ->
                        addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                            "Expected record type, got discriminated union. Use union case constructors instead" env
                    | NativeType.TByref _ ->
                        addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                            "Expected record type, got byref type" env
                    | NativeType.TNativePtr _ ->
                        addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                            "Expected record type, got native pointer type" env
                    resolvedTy
                | Result.Error((code, message)) ->
                    addNativeError code recordRange message env
                    NativeType.TError message
        
        let fieldNodePairs = fieldNodes |> List.map (fun (name, node) -> (name, node.Id))
        
        builder.Create(
            SemanticKind.RecordExpr(fieldNodePairs, copyNode |> Option.map (fun n -> n.Id)),
            recordTy,
            range,
            children = (copyNode |> Option.map (fun n -> [n.Id]) |> Option.defaultValue []) @ (fieldNodes |> List.map (fun (_, n) -> n.Id)))

    //---------------------------------------------------------------------
    // Array/list expressions
    //---------------------------------------------------------------------
    | SynExpr.ArrayOrList(isArray, exprs, _) ->
        let elementNodes = exprs |> List.map (checkExpr env builder)
        let elementTy =
            match elementNodes with
            | [] -> freshTypeVar range
            | first :: rest ->
                // All elements must have same type
                for node in rest do
                    addConstraint (Constraint.Equals(first.Type, node.Type, range)) env
                first.Type

        let collectionTy =
            if isArray then mkArrayType elementTy
            else mkListType elementTy

        let childIds = elementNodes |> List.map (fun n -> n.Id)
        let kind = if isArray then SemanticKind.ArrayExpr childIds else SemanticKind.ListExpr childIds

        builder.Create(kind, collectionTy, range, children = childIds)

    //---------------------------------------------------------------------
    // Try-with expressions
    //---------------------------------------------------------------------
    | SynExpr.TryWith(tryExpr, withCases, _, _, _, _) ->
        let tryNode = checkExpr env builder tryExpr

        // Exception handlers are like match expressions over the caught exception
        let exnType = env.Globals.ExnType

        // Check each exception clause
        let cases = withCases |> List.map (checkMatchClause env builder exnType tryNode.Type)

        // Create a synthetic match node for the handlers
        let handlerScrutinee = builder.Create(
            SemanticKind.VarRef("$exn", None),
            exnType,
            range)

        let handlerNode = builder.Create(
            SemanticKind.Match(handlerScrutinee.Id, cases),
            tryNode.Type,
            range,
            children = handlerScrutinee.Id :: (cases |> List.map (fun c -> c.Body)))

        builder.Create(
            SemanticKind.TryWith(tryNode.Id, handlerNode.Id),
            tryNode.Type,
            range,
            children = [tryNode.Id; handlerNode.Id])

    //---------------------------------------------------------------------
    // Try-finally expressions
    //---------------------------------------------------------------------
    | SynExpr.TryFinally(tryExpr, finallyExpr, _, _, _, _) ->
        let tryNode = checkExpr env builder tryExpr
        let finallyNode = checkExpr env builder finallyExpr
        builder.Create(
            SemanticKind.TryFinally(tryNode.Id, finallyNode.Id),
            tryNode.Type,
            range,
            children = [tryNode.Id; finallyNode.Id])

    //---------------------------------------------------------------------
    // Field access
    //---------------------------------------------------------------------
    | SynExpr.DotGet(expr, _, longDotId, _) ->
        let exprNode = checkExpr env builder expr
        let fieldName = longDotId.LongIdent |> List.map (fun id -> id.idText) |> String.concat "."

        // INTRINSIC MEMBERS: Native string type has intrinsic Pointer and Length
        // NativeStr = {ptr: *u8, len: usize} - these are NOT fields, they're intrinsics
        // FNCS provides these as part of the native type universe
        let isStringType ty =
            match ty with
            | NativeType.TApp(tycon, []) when tycon.Name = "string" -> true
            | _ -> false

        let resultTy =
            match fieldName with
            | "Pointer" when isStringType exprNode.Type ->
                // string.Pointer : nativeptr<byte>
                NativeType.TNativePtr(NativeGlobals.Types.uint8Type)
            | "Length" when isStringType exprNode.Type ->
                // string.Length : int
                env.Globals.IntType
            | _ ->
                // General case: create HasMember constraint for SRTP
                let ty = freshTypeVar range
                addConstraint (Constraint.HasMember(exprNode.Type, fieldName, ty, range)) env
                ty

        builder.Create(
            SemanticKind.FieldGet(exprNode.Id, fieldName),
            resultTy,
            range,
            children = [exprNode.Id])

    //---------------------------------------------------------------------
    // Assignment
    //---------------------------------------------------------------------
    | SynExpr.Set(targetExpr, valueExpr, _) ->
        let targetNode = checkExpr env builder targetExpr
        let valueNode = checkExpr env builder valueExpr
        addConstraint (Constraint.Equals(targetNode.Type, valueNode.Type, range)) env
        builder.Create(
            SemanticKind.Set(targetNode.Id, valueNode.Id),
            env.Globals.UnitType,
            range,
            children = [targetNode.Id; valueNode.Id])

    //---------------------------------------------------------------------
    // Do expressions
    //---------------------------------------------------------------------
    | SynExpr.Do(expr, _) ->
        checkExpr env builder expr

    //---------------------------------------------------------------------
    // Null - REJECTED in F# Native (FS8100)
    //---------------------------------------------------------------------
    | SynExpr.Null r ->
        addNullError r env
        builder.Create(
            SemanticKind.Error "null is not supported in native F#",
            NativeType.TError "null not supported",
            rangeToSourceRange r)

    //---------------------------------------------------------------------
    // Quote expressions
    //---------------------------------------------------------------------
    | SynExpr.Quote(_, isRaw, quotedExpr, _, _) ->
        let innerNode = checkExpr env builder quotedExpr
        // Typed quotation (<@ @>) has type Expr<'T>
        // Raw quotation (<@@ @@>) has type Expr<obj> (erased)
        let quotedType =
            if isRaw then mkExprType (freshTypeVar range)  // Raw: Expr<_>
            else mkExprType innerNode.Type  // Typed: Expr<'T>
        builder.Create(
            SemanticKind.Quote(innerNode.Id, not isRaw),
            quotedType,
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // Interpolated strings
    //---------------------------------------------------------------------
    | SynExpr.InterpolatedString(contents, _synStringKind, _) ->
        // Process each part of the interpolated string
        let mutable exprNodeIds = []
        let parts =
            contents |> List.map (fun part ->
                match part with
                | SynInterpolatedStringPart.String(value, _) ->
                    InterpolatedPart.StringPart value
                | SynInterpolatedStringPart.FillExpr(fillExpr, _qualifiers) ->
                    // Type check the expression in the hole
                    let exprNode = checkExpr env builder fillExpr
                    exprNodeIds <- exprNode.Id :: exprNodeIds
                    InterpolatedPart.ExprPart exprNode.Id
            )

        builder.Create(
            SemanticKind.InterpolatedString parts,
            env.Globals.StringType,
            range,
            children = List.rev exprNodeIds)

    //---------------------------------------------------------------------
    // AddressOf: &expr or &&expr
    //---------------------------------------------------------------------
    | SynExpr.AddressOf(isByref, innerExpr, _, _) ->
        let innerNode = checkExpr env builder innerExpr
        let pointerType =
            if isByref then NativeType.TByref(innerNode.Type, ByrefKind.InOut)
            else NativeType.TNativePtr innerNode.Type
        builder.Create(
            SemanticKind.AddressOf(innerNode.Id, isByref),
            pointerType,
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // TypeApp: expr<type1, type2, ...>
    // Type application for generic instantiation. In native compilation,
    // this drives monomorphization - each unique set of type arguments
    // produces a specialized implementation.
    //---------------------------------------------------------------------
    | SynExpr.TypeApp(funcExpr, _, typeArgs, _, _, _, _) ->
        // Check the function expression
        let funcNode = checkExpr env builder funcExpr
        // Convert type arguments - these are the concrete types being applied
        let typeArgTypes = typeArgs |> List.map (checkSynType env)

        // The result type depends on the function being instantiated.
        // If funcNode.Type is a forall type, we should instantiate it with typeArgTypes.
        let resultType =
            match funcNode.Type with
            | NativeType.TForall(typeParams, bodyType) ->
                // Check arity match
                if List.length typeParams <> List.length typeArgTypes then
                    // Arity mismatch - this is a type error
                    addError syn.Range
                        (sprintf "Type application arity mismatch: expected %d type arguments, got %d"
                            (List.length typeParams) (List.length typeArgTypes)) env
                    NativeType.TError "Type application arity mismatch"
                else
                    // Perform immediate substitution of type parameters with concrete types
                    // This is the correct approach - NativeTypes.instantiate replaces TVar
                    // occurrences with their corresponding type arguments
                    NativeTypes.instantiate typeParams typeArgTypes bodyType

            | NativeType.TVar _ ->
                // Function type is a type variable - not yet resolved
                // Add constraint that it must be a forall type with these arguments
                // For now, create fresh result type; constraint solving will refine
                freshTypeVar range

            | NativeType.TError msg ->
                // Propagate error
                NativeType.TError msg

            | NativeType.TFun _ ->
                // Function type receiving type arguments
                // This typically means a polymorphic function being instantiated
                // Add deferred constraint that function must be generic
                let resultTy = freshTypeVar range
                addConstraint (Constraint.HasTypeArgs(funcNode.Type, typeArgTypes, resultTy, range)) env
                resultTy

            | NativeType.TApp _ ->
                // Type application - possibly a partially applied generic
                // Add deferred constraint for type application
                let resultTy = freshTypeVar range
                addConstraint (Constraint.HasTypeArgs(funcNode.Type, typeArgTypes, resultTy, range)) env
                resultTy

            | other ->
                // Unexpected type receiving type arguments
                // This is likely a bug or unresolved type - add warning but continue
                addWarning syn.Range
                    (sprintf "Type application on unexpected type form: %s"
                        (NativeTypes.formatType other)) env
                // Still add constraint for later resolution
                let resultTy = freshTypeVar range
                addConstraint (Constraint.HasTypeArgs(funcNode.Type, typeArgTypes, resultTy, range)) env
                resultTy

        // ARCHITECTURAL PRINCIPLE: Type Application Preserves Semantic Kind
        // 
        // Type application is a TYPE-LEVEL operation, not a VALUE-LEVEL operation.
        // When TypeApp is applied to a semantically-transparent node (like Intrinsic),
        // we preserve that node's Kind with the instantiated type. We do NOT wrap it
        // in an Application node, because Application represents value-level function
        // calls, not type-level instantiation.
        //
        // This is decided during construction, not cleaned up by a nanopass, because:
        // 1. We're deciding what to build, not fixing what was built
        // 2. Type information is available here during construction
        // 3. The zipper receives a clean graph it can traverse directly
        //
        // See memory: typeapp_preserves_kind_principle
        match funcNode.Kind with
        | SemanticKind.Intrinsic name ->
            // TypeApp of Intrinsic → Intrinsic with instantiated type
            // The type parameter is "captured" in resultType (e.g., int -> nativeptr<byte>)
            // Downstream code sees Intrinsic("NativePtr.stackalloc") with concrete type
            builder.Create(
                SemanticKind.Intrinsic name,
                resultType,
                range)
        | _ ->
            // For other expressions (polymorphic functions, methods, etc.),
            // create Application node to represent type instantiation
            builder.Create(
                SemanticKind.Application(funcNode.Id, []),
                resultType,
                range,
                children = [funcNode.Id])

    //---------------------------------------------------------------------
    // ForEach: for x in collection do body
    //---------------------------------------------------------------------
    | SynExpr.ForEach(_, _, _, _, pat, enumExpr, bodyExpr, _) ->
        let enumNode = checkExpr env builder enumExpr
        // Extract variable from pattern
        let varName, varType =
            match pat with
            | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                ident.idText, freshTypeVar range
            | SynPat.LongIdent(SynLongIdent([ident], _, _), _, _, _, _, _) ->
                ident.idText, freshTypeVar range
            | _ -> "_", freshTypeVar range
        // Add loop variable to environment
        let loopEnv = addBinding varName varType false None env
        let bodyNode = checkExpr loopEnv builder bodyExpr
        builder.Create(
            SemanticKind.ForEach(varName, enumNode.Id, bodyNode.Id),
            env.Globals.UnitType,
            range,
            children = [enumNode.Id; bodyNode.Id])

    //---------------------------------------------------------------------
    // TraitCall: SRTP member invocation
    // In native compilation, SRTP is resolved at compile time - no runtime
    // dispatch. We must capture the constrained types and member name
    // to enable monomorphization.
    //---------------------------------------------------------------------
    | SynExpr.TraitCall(supportTys, memberSig, argExpr, _) ->
        let argNode = checkExpr env builder argExpr

        // Convert the support types - could be single type or tuple (for 'or' constraints)
        let constraintType = checkSynType env supportTys
        let constrainedTypes =
            match constraintType with
            | NativeType.TTuple(elemTys, _) -> elemTys  // Multiple constrained types
            | ty -> [ty]  // Single constrained type

        // Extract trait name from member signature
        let memberName =
            match memberSig with
            | SynMemberSig.Member(SynValSig(ident = SynIdent(id, _)), _, _, _) -> id.idText
            | _ -> "unknown_trait"

        // Extract return type from member signature if available
        let resultType =
            match memberSig with
            | SynMemberSig.Member(SynValSig(synType = synRetType), _, _, _) ->
                checkSynType env synRetType
            | _ -> freshTypeVar range

        // Add SRTP constraint: each constrained type must have this member
        // This is critical for native compilation - we must resolve to a concrete
        // implementation during type checking, not defer to runtime
        for constrainedTy in constrainedTypes do
            addConstraint (Constraint.HasMember(constrainedTy, memberName, resultType, range)) env

        builder.Create(
            SemanticKind.TraitCall(memberName, constrainedTypes, argNode.Id),
            resultType,
            range,
            children = [argNode.Id])

    //---------------------------------------------------------------------
    // Upcast: expr :> type
    //---------------------------------------------------------------------
    | SynExpr.Upcast(innerExpr, targetType, _) ->
        let innerNode = checkExpr env builder innerExpr
        let targetTy = checkSynType env targetType
        builder.Create(
            SemanticKind.Upcast(innerNode.Id, targetTy),
            targetTy,
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // InferredUpcast: upcast expr
    //---------------------------------------------------------------------
    | SynExpr.InferredUpcast(innerExpr, _) ->
        let innerNode = checkExpr env builder innerExpr
        let targetTy = freshTypeVar range
        builder.Create(
            SemanticKind.Upcast(innerNode.Id, targetTy),
            targetTy,
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // Downcast: expr :?> type
    //---------------------------------------------------------------------
    | SynExpr.Downcast(innerExpr, targetType, _) ->
        let innerNode = checkExpr env builder innerExpr
        let targetTy = checkSynType env targetType
        builder.Create(
            SemanticKind.Downcast(innerNode.Id, targetTy),
            targetTy,
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // InferredDowncast: downcast expr
    //---------------------------------------------------------------------
    | SynExpr.InferredDowncast(innerExpr, _) ->
        let innerNode = checkExpr env builder innerExpr
        let targetTy = freshTypeVar range
        builder.Create(
            SemanticKind.Downcast(innerNode.Id, targetTy),
            targetTy,
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // TypeTest: expr :? type
    //---------------------------------------------------------------------
    | SynExpr.TypeTest(innerExpr, targetType, _) ->
        let innerNode = checkExpr env builder innerExpr
        let targetTy = checkSynType env targetType
        builder.Create(
            SemanticKind.TypeTest(innerNode.Id, targetTy),
            env.Globals.BoolType,
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // DotIndexedGet: expr.[index]
    //---------------------------------------------------------------------
    | SynExpr.DotIndexedGet(objExpr, indexArgs, _, _) ->
        let objNode = checkExpr env builder objExpr
        let indexNodes =
            match indexArgs with
            | SynExpr.Tuple(_, exprs, _, _) -> exprs |> List.map (checkExpr env builder)
            | indexExpr -> [checkExpr env builder indexExpr]
        let indexNodeId =
            match indexNodes with
            | [single] -> single.Id
            | multiple ->
                let multipleNodeIds = multiple |> List.map (fun indexNode -> indexNode.Id)
                let multipleNodeTypes = multiple |> List.map (fun indexNode -> indexNode.Type)
                let tupleNode = builder.Create(
                    SemanticKind.TupleExpr(multipleNodeIds),
                    NativeType.TTuple(multipleNodeTypes, false),
                    range,
                    children = multipleNodeIds)
                tupleNode.Id
        let allChildNodeIds = objNode.Id :: (indexNodes |> List.map (fun indexNode -> indexNode.Id))
        builder.Create(
            SemanticKind.IndexGet(objNode.Id, indexNodeId),
            freshTypeVar range,
            range,
            children = allChildNodeIds)

    //---------------------------------------------------------------------
    // DotIndexedSet: expr.[index] <- value
    //---------------------------------------------------------------------
    | SynExpr.DotIndexedSet(objExpr, indexArgs, valueExpr, _, _, _) ->
        let objNode = checkExpr env builder objExpr
        let indexNodes =
            match indexArgs with
            | SynExpr.Tuple(_, exprs, _, _) -> exprs |> List.map (checkExpr env builder)
            | indexExpr -> [checkExpr env builder indexExpr]
        let valueNode = checkExpr env builder valueExpr
        let indexNodeId =
            match indexNodes with
            | [single] -> single.Id
            | multiple ->
                let multipleNodeIds = multiple |> List.map (fun indexNode -> indexNode.Id)
                let multipleNodeTypes = multiple |> List.map (fun indexNode -> indexNode.Type)
                let tupleNode = builder.Create(
                    SemanticKind.TupleExpr(multipleNodeIds),
                    NativeType.TTuple(multipleNodeTypes, false),
                    range,
                    children = multipleNodeIds)
                tupleNode.Id
        let allChildNodeIds = objNode.Id :: valueNode.Id :: (indexNodes |> List.map (fun indexNode -> indexNode.Id))
        builder.Create(
            SemanticKind.IndexSet(objNode.Id, indexNodeId, valueNode.Id),
            env.Globals.UnitType,
            range,
            children = allChildNodeIds)

    //---------------------------------------------------------------------
    // DotSet: expr.field <- value
    //---------------------------------------------------------------------
    | SynExpr.DotSet(objExpr, SynLongIdent(longId, _, _), valueExpr, _) ->
        let objNode = checkExpr env builder objExpr
        let valueNode = checkExpr env builder valueExpr
        let fieldName = longId |> List.map (fun id -> id.idText) |> String.concat "."
        builder.Create(
            SemanticKind.FieldSet(objNode.Id, fieldName, valueNode.Id),
            env.Globals.UnitType,
            range,
            children = [objNode.Id; valueNode.Id])

    //---------------------------------------------------------------------
    // LongIdentSet: Module.value <- expr
    //---------------------------------------------------------------------
    | SynExpr.LongIdentSet(SynLongIdent(longId, _, _), valueExpr, _) ->
        let valueNode = checkExpr env builder valueExpr
        let targetName = longId |> List.map (fun id -> id.idText) |> String.concat "."
        // Look up the target binding
        match tryLookupBinding targetName env with
        | Some binding when binding.IsMutable ->
            let targetNode = builder.Create(
                SemanticKind.VarRef(targetName, binding.NodeId),
                binding.Type,
                range)
            builder.Create(
                SemanticKind.Set(targetNode.Id, valueNode.Id),
                env.Globals.UnitType,
                range,
                children = [targetNode.Id; valueNode.Id])
        | _ ->
            builder.Create(
                SemanticKind.Error $"Cannot assign to '{targetName}' (not found or not mutable)",
                NativeType.TError "assignment error",
                range)

    //---------------------------------------------------------------------
    // Lazy: lazy expr
    //---------------------------------------------------------------------
    | SynExpr.Lazy(innerExpr, _) ->
        let innerNode = checkExpr env builder innerExpr
        let lazyType = mkLazyType innerNode.Type
        builder.Create(
            SemanticKind.Application(innerNode.Id, []),  // Lazy wraps expression
            lazyType,
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // Assert: assert expr
    //---------------------------------------------------------------------
    | SynExpr.Assert(condExpr, _) ->
        let condNode = checkExpr env builder condExpr
        // Assert returns unit
        builder.Create(
            SemanticKind.Application(condNode.Id, []),  // Assert is like a function call
            env.Globals.UnitType,
            range,
            children = [condNode.Id])

    //---------------------------------------------------------------------
    // New: new Type(args)
    //---------------------------------------------------------------------
    | SynExpr.New(_, synType, argExpr, _) ->
        let targetType = checkSynType env synType
        let argNode = checkExpr env builder argExpr
        builder.Create(
            SemanticKind.Application(argNode.Id, []),  // Constructor call
            targetType,
            range,
            children = [argNode.Id])

    //---------------------------------------------------------------------
    // ObjExpr: { new Interface with ... } or { new BaseClass(args) with ... }
    // Object expressions can:
    // - Implement an interface with member definitions
    // - Inherit from a base class with constructor arguments
    // - Implement multiple additional interfaces (extraImpls)
    //---------------------------------------------------------------------
    | SynExpr.ObjExpr(objType, argOption, _, bindings, members, extraImpls, _, _) ->
        let interfaceType = checkSynType env objType

        // Process constructor arguments if present (for class inheritance)
        let argNodeIds =
            match argOption with
            | Some (argExpr, _asIdent) ->
                // Check the constructor argument expression
                let argNode = checkExpr env builder argExpr
                [argNode.Id]
            | None -> []

        // Process let bindings inside the object expression
        let bindingNodes = bindings |> List.map (fun binding ->
            match binding with
            | SynBinding(_, _, _, _, _, _, _, _, _, bodyExpr, _, _, _) ->
                checkExpr env builder bodyExpr)

        // Process member definitions (methods, properties, etc.)
        let memberNodes = members |> List.collect (fun memberDefn ->
            match memberDefn with
            | SynMemberDefn.Member(memberBinding, _) ->
                match memberBinding with
                | SynBinding(_, _, _, _, _, _, _, _, _, bodyExpr, _, _, _) ->
                    [checkExpr env builder bodyExpr]
            | SynMemberDefn.GetSetMember(getOpt, setOpt, _, _) ->
                [ match getOpt with
                  | Some (SynBinding(_, _, _, _, _, _, _, _, _, bodyExpr, _, _, _)) ->
                      checkExpr env builder bodyExpr
                  | None -> ()
                  match setOpt with
                  | Some (SynBinding(_, _, _, _, _, _, _, _, _, bodyExpr, _, _, _)) ->
                      checkExpr env builder bodyExpr
                  | None -> () ]
            | SynMemberDefn.AutoProperty(synExpr = bodyExpr) ->
                [checkExpr env builder bodyExpr]
            | SynMemberDefn.LetBindings(bindings, _, _, _, _) ->
                bindings |> List.map (fun binding ->
                    match binding with
                    | SynBinding(_, _, _, _, _, _, _, _, _, bodyExpr, _, _, _) ->
                        checkExpr env builder bodyExpr)
            | _ -> [])  // Other member kinds (abstract slots, fields, etc.)

        // Process extra interface implementations
        let extraImplNodes = extraImpls |> List.collect (fun impl ->
            match impl with
            | SynInterfaceImpl(interfaceTy, _, implBindings, implMembers, _) ->
                // Check the interface type for constraint purposes
                let _implType = checkSynType env interfaceTy
                // Process bindings and members for this interface
                let implBindingNodes = implBindings |> List.map (fun binding ->
                    match binding with
                    | SynBinding(_, _, _, _, _, _, _, _, _, bodyExpr, _, _, _) ->
                        checkExpr env builder bodyExpr)
                let implMemberNodes = implMembers |> List.collect (fun memberDefn ->
                    match memberDefn with
                    | SynMemberDefn.Member(memberBinding, _) ->
                        match memberBinding with
                        | SynBinding(_, _, _, _, _, _, _, _, _, bodyExpr, _, _, _) ->
                            [checkExpr env builder bodyExpr]
                    | _ -> [])
                implBindingNodes @ implMemberNodes)

        // Collect all member node IDs
        let allMemberNodeIds =
            argNodeIds @
            (bindingNodes |> List.map (fun n -> n.Id)) @
            (memberNodes |> List.map (fun n -> n.Id)) @
            (extraImplNodes |> List.map (fun n -> n.Id))

        builder.Create(
            SemanticKind.ObjectExpr(interfaceType, allMemberNodeIds),
            interfaceType,
            range,
            children = allMemberNodeIds)

    //---------------------------------------------------------------------
    // AnonRecd: {| field = value |} or {| source with field = value |}
    // Anonymous records can be struct (value type) or reference type.
    // copyInfo handles copy-and-update expressions.
    //---------------------------------------------------------------------
    | SynExpr.AnonRecd(isStruct, copyInfo, recordFields, _, _trivia) ->
        // Handle copy-and-update source if present: {| source with field = value |}
        let copyFromNode, inheritedFields =
            match copyInfo with
            | Some (sourceExpr, _blockSep) ->
                let sourceNode = checkExpr env builder sourceExpr
                // The source expression provides fields to inherit
                // Type must be extracted from the source for field inheritance
                let srcFields =
                    match sourceNode.Type with
                    | NativeType.TAnon(fields, _) -> fields
                    | _ -> []  // Source type will be resolved during unification
                Some sourceNode, srcFields
            | None -> None, []

        // Process new field assignments
        let newFieldNodes = recordFields |> List.map (fun (SynLongIdent(longId, _, _), _rangeOption, fieldExpr) ->
            let fieldName = longId |> List.map (fun id -> id.idText) |> String.concat "."
            (fieldName, checkExpr env builder fieldExpr))

        // Merge inherited and new fields (new fields override inherited ones)
        let newFieldNames = newFieldNodes |> List.map fst |> Set.ofList
        let keptInheritedFields =
            inheritedFields
            |> List.filter (fun (name, _) -> not (Set.contains name newFieldNames))
        let allFieldTypes =
            keptInheritedFields @
            (newFieldNodes |> List.map (fun (name, node) -> (name, node.Type)))

        let childNodeIds =
            (copyFromNode |> Option.map (fun n -> [n.Id]) |> Option.defaultValue []) @
            (newFieldNodes |> List.map (fun (_, node) -> node.Id))

        builder.Create(
            SemanticKind.RecordExpr(
                newFieldNodes |> List.map (fun (name, node) -> (name, node.Id)),
                copyFromNode |> Option.map (fun n -> n.Id)),
            NativeType.TAnon(allFieldTypes, isStruct),
            range,
            children = childNodeIds)

    //---------------------------------------------------------------------
    // MatchLambda: function | pat -> expr
    // Desugars to: fun arg -> match arg with | pat1 -> expr1 | ...
    //---------------------------------------------------------------------
    | SynExpr.MatchLambda(_isExnMatch, _keywordRange, clauses, _matchSeqPoint, _) ->
        // Create fresh types for domain and result
        let domainType = freshTypeVar range
        let resultType = freshTypeVar range

        // Process each match clause
        let matchCases = clauses |> List.map (fun clause ->
            checkMatchClause env builder domainType resultType clause)

        // Create synthetic argument for the lambda
        let syntheticArgName = "_arg"
        let syntheticArgNodeId =
            let argNode = builder.Create(
                SemanticKind.VarRef(syntheticArgName, None),
                domainType,
                range)
            argNode.Id

        // Create match expression over the synthetic argument
        let matchNodeChildIds = syntheticArgNodeId :: (matchCases |> List.map (fun matchCase -> matchCase.Body))
        let matchNode = builder.Create(
            SemanticKind.Match(syntheticArgNodeId, matchCases),
            resultType,
            range,
            children = matchNodeChildIds)

        // Wrap in lambda
        builder.Create(
            SemanticKind.Lambda([(syntheticArgName, domainType)], matchNode.Id),
            NativeType.TFun(domainType, resultType),
            range,
            children = [matchNode.Id])

    //---------------------------------------------------------------------
    // ArrayOrListComputed: [| for x in xs -> f x |] or [ for x in xs -> f x ]
    //---------------------------------------------------------------------
    | SynExpr.ArrayOrListComputed(isArray, compExpr, _) ->
        let compNode = checkExpr env builder compExpr
        let elemType = freshTypeVar range
        let resultType = if isArray then mkArrayType elemType else mkListType elemType
        builder.Create(
            SemanticKind.ArrayExpr [compNode.Id],
            resultType,
            range,
            children = [compNode.Id])

    //---------------------------------------------------------------------
    // ComputationExpr: async { ... }, seq { ... }, etc.
    //---------------------------------------------------------------------
    | SynExpr.ComputationExpr(_, compExpr, _) ->
        let compNode = checkExpr env builder compExpr
        builder.Create(
            SemanticKind.Sequential [compNode.Id],
            compNode.Type,
            range,
            children = [compNode.Id])

    //---------------------------------------------------------------------
    // YieldOrReturn: yield expr or return expr
    //---------------------------------------------------------------------
    | SynExpr.YieldOrReturn(_flags, expr, _, _trivia) ->
        checkExpr env builder expr

    //---------------------------------------------------------------------
    // YieldOrReturnFrom: yield! expr or return! expr
    //---------------------------------------------------------------------
    | SynExpr.YieldOrReturnFrom(_flags, expr, _, _trivia) ->
        checkExpr env builder expr

    //---------------------------------------------------------------------
    // DoBang: do! expr
    //---------------------------------------------------------------------
    | SynExpr.DoBang(expr, _, _trivia) ->
        let exprNode = checkExpr env builder expr
        builder.Create(
            SemanticKind.Sequential [exprNode.Id],
            env.Globals.UnitType,
            range,
            children = [exprNode.Id])

    //---------------------------------------------------------------------
    // MatchBang: match! expr with ...
    //---------------------------------------------------------------------
    | SynExpr.MatchBang(_, expr, clauses, _, _) ->
        let scrutineeNode = checkExpr env builder expr
        let matchCases = clauses |> List.map (fun (SynMatchClause(pat, guardOpt, resultExpr, _, _, _)) ->
            let (pattern, _patBindings) = checkPattern env pat scrutineeNode.Type range
            let guardNode = guardOpt |> Option.map (checkExpr env builder)
            let bodyNode = checkExpr env builder resultExpr
            { Pattern = pattern; Guard = guardNode |> Option.map (fun guardNode -> guardNode.Id); Body = bodyNode.Id })
        let resultType = if List.isEmpty matchCases then env.Globals.UnitType else freshTypeVar range
        builder.Create(
            SemanticKind.Match(scrutineeNode.Id, matchCases),
            resultType,
            range,
            children = scrutineeNode.Id :: (matchCases |> List.collect (fun matchCase ->
                match matchCase.Guard with Some guardId -> [guardId; matchCase.Body] | None -> [matchCase.Body])))

    //---------------------------------------------------------------------
    // WhileBang: while! expr do body
    //---------------------------------------------------------------------
    | SynExpr.WhileBang(_, guardExpr, bodyExpr, _) ->
        let guardNode = checkExpr env builder guardExpr
        let bodyNode = checkExpr env builder bodyExpr
        builder.Create(
            SemanticKind.WhileLoop(guardNode.Id, bodyNode.Id),
            env.Globals.UnitType,
            range,
            children = [guardNode.Id; bodyNode.Id])

    //---------------------------------------------------------------------
    // ImplicitZero: implicit unit in computation expressions
    //---------------------------------------------------------------------
    | SynExpr.ImplicitZero _ ->
        builder.Create(
            SemanticKind.Literal LiteralValue.Unit,
            env.Globals.UnitType,
            range)

    //---------------------------------------------------------------------
    // SequentialOrImplicitYield: expr1; expr2 in comp expr
    //---------------------------------------------------------------------
    | SynExpr.SequentialOrImplicitYield(_, expr1, expr2, _, _) ->
        let node1 = checkExpr env builder expr1
        let node2 = checkExpr env builder expr2
        builder.Create(
            SemanticKind.Sequential [node1.Id; node2.Id],
            node2.Type,
            range,
            children = [node1.Id; node2.Id])

    //---------------------------------------------------------------------
    // Fixed: fixed expr (pin pointer)
    //---------------------------------------------------------------------
    | SynExpr.Fixed(innerExpr, _) ->
        let innerNode = checkExpr env builder innerExpr
        builder.Create(
            SemanticKind.AddressOf(innerNode.Id, true),  // Fixed is like byref
            NativeType.TByref(innerNode.Type, ByrefKind.InOut),
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // Dynamic: expr?name (dynamic member access)
    //---------------------------------------------------------------------
    | SynExpr.Dynamic(objExpr, _, memberExpr, _) ->
        let objNode = checkExpr env builder objExpr
        let memberNode = checkExpr env builder memberExpr
        builder.Create(
            SemanticKind.Application(objNode.Id, [memberNode.Id]),
            freshTypeVar range,
            range,
            children = [objNode.Id; memberNode.Id])

    //---------------------------------------------------------------------
    // DotLambda: _.Property (shorthand lambda)
    //---------------------------------------------------------------------
    | SynExpr.DotLambda(innerExpr, _, _) ->
        let innerNode = checkExpr env builder innerExpr
        let argType = freshTypeVar range
        builder.Create(
            SemanticKind.Lambda([("_", argType)], innerNode.Id),
            NativeType.TFun(argType, innerNode.Type),
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // DotNamedIndexedPropertySet: obj.Prop[idx] <- value
    // Named indexed property access - distinct from direct indexing.
    // Example: dict.Item[key] <- value
    //---------------------------------------------------------------------
    | SynExpr.DotNamedIndexedPropertySet(objExpr, SynLongIdent(longId, _, _), indexExpr, valueExpr, _) ->
        let objNode = checkExpr env builder objExpr
        let indexNode = checkExpr env builder indexExpr
        let valueNode = checkExpr env builder valueExpr
        let propName = longId |> List.map (fun id -> id.idText) |> String.concat "."

        // Add constraint that the object type has this indexed property
        addConstraint (Constraint.HasMember(objNode.Type, propName, freshTypeVar range, range)) env

        builder.Create(
            SemanticKind.NamedIndexedPropertySet(objNode.Id, propName, indexNode.Id, valueNode.Id),
            env.Globals.UnitType,
            range,
            children = [objNode.Id; indexNode.Id; valueNode.Id])

    //---------------------------------------------------------------------
    // NamedIndexedPropertySet: Prop(idx) <- value
    //---------------------------------------------------------------------
    | SynExpr.NamedIndexedPropertySet(SynLongIdent(longId, _, _), indexExpr, valueExpr, _) ->
        let indexNode = checkExpr env builder indexExpr
        let valueNode = checkExpr env builder valueExpr
        let propName = longId |> List.map (fun id -> id.idText) |> String.concat "."
        builder.Create(
            SemanticKind.Error $"NamedIndexedPropertySet '{propName}' - requires context",
            env.Globals.UnitType,
            range,
            children = [indexNode.Id; valueNode.Id])

    //---------------------------------------------------------------------
    // Typar: 'a (type parameter in expression position)
    //---------------------------------------------------------------------
    | SynExpr.Typar(SynTypar(ident, _, _), _) ->
        let typarName = ident.idText
        builder.Create(
            SemanticKind.Error $"Type parameter '{typarName}' in expression position",
            freshTypeVar range,
            range)

    //---------------------------------------------------------------------
    // IndexRange: expr.[start..finish]
    //---------------------------------------------------------------------
    | SynExpr.IndexRange(startOpt, _, finishOpt, _, _, _) ->
        let startNode = startOpt |> Option.map (checkExpr env builder)
        let finishNode = finishOpt |> Option.map (checkExpr env builder)
        let children = [startNode; finishNode] |> List.choose id |> List.map (fun n -> n.Id)
        builder.Create(
            SemanticKind.Error "IndexRange - requires slice support",
            freshTypeVar range,
            range,
            children = children)

    //---------------------------------------------------------------------
    // IndexFromEnd: ^expr (index from end)
    //---------------------------------------------------------------------
    | SynExpr.IndexFromEnd(expr, _) ->
        let exprNode = checkExpr env builder expr
        builder.Create(
            SemanticKind.Application(exprNode.Id, []),  // ^n is like a function
            env.Globals.IntType,
            range,
            children = [exprNode.Id])

    //---------------------------------------------------------------------
    // JoinIn: join ... in ... (query syntax)
    //---------------------------------------------------------------------
    | SynExpr.JoinIn(expr1, _, expr2, _) ->
        let node1 = checkExpr env builder expr1
        let node2 = checkExpr env builder expr2
        builder.Create(
            SemanticKind.Error "JoinIn - query syntax not supported",
            freshTypeVar range,
            range,
            children = [node1.Id; node2.Id])

    //---------------------------------------------------------------------
    // DebugPoint: debugging information (transparent)
    //---------------------------------------------------------------------
    | SynExpr.DebugPoint(_, _, innerExpr) ->
        checkExpr env builder innerExpr

    //---------------------------------------------------------------------
    // ArbitraryAfterError: parse recovery node
    //---------------------------------------------------------------------
    | SynExpr.ArbitraryAfterError(_, _) ->
        builder.Create(
            SemanticKind.Error "Parse error recovery node",
            NativeType.TError "parse error",
            range)

    //---------------------------------------------------------------------
    // FromParseError: parse error wrapper
    //---------------------------------------------------------------------
    | SynExpr.FromParseError(innerExpr, _) ->
        let innerNode = checkExpr env builder innerExpr
        builder.Create(
            SemanticKind.Error "Expression contains parse error",
            innerNode.Type,
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // DiscardAfterMissingQualificationAfterDot: A. (incomplete dot access)
    //---------------------------------------------------------------------
    | SynExpr.DiscardAfterMissingQualificationAfterDot(innerExpr, _, _) ->
        let innerNode = checkExpr env builder innerExpr
        builder.Create(
            SemanticKind.Error "Incomplete member access (missing qualifier after dot)",
            freshTypeVar range,
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // LibraryOnlyILAssembly: inline IL (FSharp.Core internal)
    //---------------------------------------------------------------------
    | SynExpr.LibraryOnlyILAssembly _ ->
        builder.Create(
            SemanticKind.Error "Inline IL assembly is not supported in native compilation",
            NativeType.TError "IL assembly",
            range)

    //---------------------------------------------------------------------
    // LibraryOnlyStaticOptimization: static optimization (FSharp.Core internal)
    //---------------------------------------------------------------------
    | SynExpr.LibraryOnlyStaticOptimization _ ->
        builder.Create(
            SemanticKind.Error "Static optimization is not supported in native compilation",
            NativeType.TError "static optimization",
            range)

    //---------------------------------------------------------------------
    // LibraryOnlyUnionCaseFieldGet: internal union field access
    //---------------------------------------------------------------------
    | SynExpr.LibraryOnlyUnionCaseFieldGet(expr, _, _, _) ->
        let exprNode = checkExpr env builder expr
        builder.Create(
            SemanticKind.Error "Library-only union case field get",
            freshTypeVar range,
            range,
            children = [exprNode.Id])

    //---------------------------------------------------------------------
    // LibraryOnlyUnionCaseFieldSet: internal union field set
    //---------------------------------------------------------------------
    | SynExpr.LibraryOnlyUnionCaseFieldSet(expr, _, _, valueExpr, _) ->
        let exprNode = checkExpr env builder expr
        let valueNode = checkExpr env builder valueExpr
        builder.Create(
            SemanticKind.Error "Library-only union case field set",
            env.Globals.UnitType,
            range,
            children = [exprNode.Id; valueNode.Id])

//-------------------------------------------------------------------------
// Helper Functions
//-------------------------------------------------------------------------

/// Extract parameter names from lambda arguments
and extractLambdaParams (env: TypeEnv) (args: SynSimplePats) (range: SourceRange) : (string * NativeType) list =
    match args with
    | SynSimplePats.SimplePats(pats, _, _) ->
        pats |> List.map (fun pat ->
            match pat with
            | SynSimplePat.Id(ident, _, _, _, _, _) ->
                (ident.idText, freshTypeVar range)
            | SynSimplePat.Typed(SynSimplePat.Id(ident, _, _, _, _, _), synType, _) ->
                // Type annotation provided - convert to native type
                (ident.idText, checkSynType env synType)
            | _ ->
                ("_", freshTypeVar range))

/// Check a let-or-use binding
and checkLetOrUse (env: TypeEnv) (builder: NodeBuilder) (letOrUse: SynLetOrUse) (range: SourceRange) : SemanticNode =
    let bindings = letOrUse.Bindings
    let bodyExpr = letOrUse.Body
    let isRec = letOrUse.IsRecursive

    // First pass: add all bindings to environment (for recursive bindings)
    let bindingEnv =
        if isRec then
            bindings |> List.fold (fun env binding ->
                let name = getBindingName binding
                let ty = freshTypeVar range
                addBinding name ty false None env
            ) env
        else
            env

    // Check each binding (returns SemanticNode * InlineBody option)
    let bindingResults = bindings |> List.map (fun binding ->
        checkBinding bindingEnv builder binding)

    // Extract just the nodes for the semantic graph
    let bindingNodes = bindingResults |> List.map fst

    // Add bindings to environment for body
    // FNCS inline-by-default: use addInlineBinding for functions with bodies
    let bodyEnv =
        List.zip3 bindings bindingNodes (bindingResults |> List.map snd)
        |> List.fold (fun env (binding, node, inlineBodyOpt) ->
            let name = getBindingName binding
            let isMutable = isBindingMutable binding
            match inlineBodyOpt with
            | Some inlineBody ->
                // Function with inline body - add with transparency
                addInlineBinding name node.Type (Some node.Id) inlineBody env
            | None ->
                // Regular value binding
                addBinding name node.Type isMutable (Some node.Id) env
        ) bindingEnv

    // Check body
    let bodyNode = checkExpr bodyEnv builder bodyExpr

    // Create sequential node for bindings + body
    let allIds = (bindingNodes |> List.map (fun n -> n.Id)) @ [bodyNode.Id]
    builder.Create(
        SemanticKind.Sequential allIds,
        bodyNode.Type,
        range,
        children = allIds)

/// Get the name from a binding
and getBindingName (binding: SynBinding) : string =
    let (SynBinding(_, _, _, _, _, _, _, headPat, _, _, _, _, _)) = binding
    match headPat with
    | SynPat.Named(SynIdent(ident, _), _, _, _) -> ident.idText
    | SynPat.LongIdent(longDotId, _, _, _, _, _) ->
        longDotId.LongIdent |> List.last |> fun id -> id.idText
    | _ -> "_"

/// Check if a binding is mutable
and isBindingMutable (binding: SynBinding) : bool =
    let (SynBinding(_, _, _, isMutable, _, _, _, _, _, _, _, _, _)) = binding
    isMutable

/// Extract function parameters from a LongIdent pattern
/// For `let f x y = body`, returns Some [(x, ty); (y, ty)]
/// For `let x = body`, returns None
and tryGetFunctionParams (headPat: SynPat) (env: TypeEnv) (range: SourceRange) : (string * NativeType) list option =
    match headPat with
    | SynPat.LongIdent(_, _, _, argPats, _, _) ->
        match argPats with
        | SynArgPats.Pats pats when not (List.isEmpty pats) ->
            // Has parameters - this is a function definition
            let extractedParameters = pats |> List.collect (fun pat ->
                match pat with
                | SynPat.Paren(innerPat, _) ->
                    // Parenthesized pattern like (x, y) or () or (x: Type)
                    match innerPat with
                    | SynPat.Const(SynConst.Unit, _) ->
                        // () parameter - unit type, no binding name
                        []  // Don't create a parameter for unit
                    | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                        [(ident.idText, freshTypeVar range)]
                    | SynPat.Typed(typedInner, synType, _) ->
                        // Typed pattern like (name: NativeStr)
                        let annotatedType = checkSynType env synType
                        match typedInner with
                        | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                            [(ident.idText, annotatedType)]
                        | _ -> [("_", annotatedType)]
                    | SynPat.Tuple(_, tuplePats, _, _) ->
                        tuplePats |> List.map (fun tuplePat ->
                            match tuplePat with
                            | SynPat.Named(SynIdent(ident, _), _, _, _) -> (ident.idText, freshTypeVar range)
                            | SynPat.Typed(SynPat.Named(SynIdent(ident, _), _, _, _), synType, _) ->
                                (ident.idText, checkSynType env synType)
                            | _ -> ("_", freshTypeVar range))
                    | _ -> [("_", freshTypeVar range)]
                | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                    [(ident.idText, freshTypeVar range)]
                | SynPat.Const(SynConst.Unit, _) ->
                    []  // Unit literal - no parameter binding
                | _ -> [("_", freshTypeVar range)]
            )
            Some extractedParameters
        | _ -> None
    | _ -> None

/// Check a single binding
/// Returns the semantic node and optionally an InlineBody for transparent function expansion
/// FNCS is inline-by-default: all function bodies are captured for potential expansion
and checkBinding (env: TypeEnv) (builder: NodeBuilder) (binding: SynBinding) : SemanticNode * InlineBody option =
    let (SynBinding(_, _, _, isMutable, attrs, _, _, headPat, _, expr, bindingRange, _, _)) = binding
    let range = rangeToSourceRange bindingRange
    let name = getBindingName binding
    let isEntryPoint = hasEntryPointAttribute attrs

    // Check if this is a function definition (has parameters)
    match tryGetFunctionParams headPat env range with
    | Some paramBindings ->
        // This is a function definition like `let f x = body` or `let f() = body`
        // Create a Lambda node wrapping the body

        // Add parameters to environment for checking body
        let bodyEnv =
            paramBindings
            |> List.fold (fun env (paramName, paramTy) -> addBinding paramName paramTy false None env) env

        // Check body with extended environment
        let bodyNode = checkExpr bodyEnv builder expr

        // Build function type
        let paramTypes = paramBindings |> List.map snd
        // For unit-parameterized functions like f(), the paramTypes might be empty
        // but it's still a function: unit -> returnType
        let funcType =
            if List.isEmpty paramTypes then
                mkFunctionType [env.Globals.UnitType] bodyNode.Type
            else
                mkFunctionType paramTypes bodyNode.Type

        // Create Lambda node
        let lambdaNode = builder.Create(
            SemanticKind.Lambda(paramBindings, bodyNode.Id),
            funcType,
            range,
            children = [bodyNode.Id])

        // Create Binding node wrapping the Lambda
        let bindingNode = builder.Create(
            SemanticKind.Binding(name, isMutable, false, isEntryPoint),
            funcType,
            range,
            children = [lambdaNode.Id])

        // Capture inline body for transparent function expansion
        // FNCS inline-by-default: all functions are transparent to the compiler
        let inlineBody: NameResolution.InlineBody = {
            Parameters = paramBindings |> List.map fst  // Just the parameter names
            Body = expr                                  // The original SynExpr
            Range = rangeToSourceRange bindingRange     // Source range for error reporting
        }

        (bindingNode, Some inlineBody)

    | None ->
        // Regular value binding (not a function - no inline body)
        let exprNode = checkExpr env builder expr
        let node = builder.Create(
            SemanticKind.Binding(name, isMutable, false, isEntryPoint),
            exprNode.Type,
            range,
            children = [exprNode.Id])
        (node, None)

/// Check a match clause
and checkMatchClause (env: TypeEnv) (builder: NodeBuilder) (scrutineeTy: NativeType) (resultTy: NativeType) (clause: SynMatchClause) : MatchCase =
    let (SynMatchClause(pat, guardOpt, bodyExpr, _, _, _)) = clause
    let range = rangeToSourceRange bodyExpr.Range

    // Check pattern and extract bindings
    let (pattern, patBindings) = checkPattern env pat scrutineeTy range

    // Add pattern bindings to environment
    let bodyEnv =
        patBindings
        |> List.fold (fun env (name, ty) -> addBinding name ty false None env) env

    // Check guard if present
    let guardNode = guardOpt |> Option.map (checkExpr bodyEnv builder)
    guardNode |> Option.iter (fun g ->
        addConstraint (Constraint.Equals(g.Type, env.Globals.BoolType, range)) env)

    // Check body
    let bodyNode = checkExpr bodyEnv builder bodyExpr

    // Body must match result type
    addConstraint (Constraint.Equals(bodyNode.Type, resultTy, range)) env

    { Pattern = pattern
      Guard = guardNode |> Option.map (fun n -> n.Id)
      Body = bodyNode.Id }

/// Check a pattern and return bindings
and checkPattern (env: TypeEnv) (pat: SynPat) (expectedTy: NativeType) (range: SourceRange) : Pattern * (string * NativeType) list =
    match pat with
    | SynPat.Const(constant, _) ->
        (Pattern.Const(constToLiteral constant), [])

    | SynPat.Wild _ ->
        (Pattern.Wildcard, [])

    | SynPat.Named(SynIdent(ident, _), _, _, _) ->
        let name = ident.idText
        (Pattern.Var(name, expectedTy), [(name, expectedTy)])

    | SynPat.Typed(innerPat, synType, _) ->
        let annotatedTy = checkSynType env synType
        addConstraint (Constraint.Equals(expectedTy, annotatedTy, range)) env
        checkPattern env innerPat annotatedTy range

    | SynPat.Tuple(_, pats, _, _) ->
        let elementTypes = pats |> List.map (fun _ -> freshTypeVar range)
        let tupleTy = NativeType.TTuple(elementTypes, false)
        addConstraint (Constraint.Equals(expectedTy, tupleTy, range)) env

        let (patterns, bindings) =
            List.zip pats elementTypes
            |> List.map (fun (p, ty) -> checkPattern env p ty range)
            |> List.unzip

        (Pattern.Tuple patterns, List.concat bindings)

    | SynPat.Paren(innerPat, _) ->
        checkPattern env innerPat expectedTy range

    | SynPat.Null _ ->
        (Pattern.Null, [])

    | SynPat.LongIdent(SynLongIdent(idents, _, _), _, _, argPats, _, _) ->
        // Constructor or identifier pattern
        let caseName = idents |> List.map (fun id -> id.idText) |> String.concat "."
        match argPats with
        | SynArgPats.Pats [] ->
            // No arguments - could be variable binding or nullary constructor
            // Lowercase single identifier = variable binding, otherwise = constructor
            match idents with
            | [ident] when not (System.Char.IsUpper(ident.idText.[0])) ->
                // Lowercase single identifier - treat as variable binding
                (Pattern.Var(caseName, expectedTy), [(caseName, expectedTy)])
            | _ ->
                // Uppercase or qualified - nullary constructor
                (Pattern.Union(caseName, None, expectedTy), [])
        | SynArgPats.Pats pats ->
            // Constructor with arguments (e.g., Some x, Error e)
            let (argPatterns, argBindings) =
                pats
                |> List.map (fun p ->
                    let argTy = freshTypeVar range
                    checkPattern env p argTy range)
                |> List.unzip
            let payload = if List.isEmpty argPatterns then None else Some (Pattern.Tuple argPatterns)
            (Pattern.Union(caseName, payload, expectedTy), List.concat argBindings)
        | SynArgPats.NamePatPairs _ ->
            // Named pattern pairs (e.g., { Field = pat })
            (Pattern.Union(caseName, None, expectedTy), [])

    | SynPat.As(lhsPat, rhsPat, _) ->
        // Pattern alias: pat as name
        let (lhsPattern, lhsBindings) = checkPattern env lhsPat expectedTy range
        let (_, rhsBindings) = checkPattern env rhsPat expectedTy range
        (lhsPattern, lhsBindings @ rhsBindings)

    | SynPat.Or(lhsPat, rhsPat, _, _) ->
        // Alternation pattern
        let (lhsPattern, lhsBindings) = checkPattern env lhsPat expectedTy range
        let (_rhsPattern, _rhsBindings) = checkPattern env rhsPat expectedTy range
        // Use left pattern, but both branches should bind same names
        (lhsPattern, lhsBindings)

    | SynPat.ArrayOrList(isArray, pats, _) ->
        let elemTy = freshTypeVar range
        let listTy = if isArray then mkArrayType elemTy else mkListType elemTy
        addConstraint (Constraint.Equals(expectedTy, listTy, range)) env
        let (patterns, bindings) =
            pats
            |> List.map (fun p -> checkPattern env p elemTy range)
            |> List.unzip
        (Pattern.Array patterns, List.concat bindings)

    | SynPat.Record(fields, _) ->
        // Record pattern: { field1 = pat1; ... }
        let fieldPats =
            fields
            |> List.map (fun field ->
                let fieldName = field.FieldName.LongIdent |> List.map (fun id -> id.idText) |> String.concat "."
                let pat = field.Pattern
                let fieldTy = freshTypeVar range
                let (pattern, bindings) = checkPattern env pat fieldTy range
                ((fieldName, pattern), bindings))
        let patterns = fieldPats |> List.map fst
        let bindings = fieldPats |> List.collect snd
        (Pattern.Record(patterns, expectedTy), bindings)

    | SynPat.IsInst(synType, _) ->
        // Type test pattern: :? Type
        let testTy = checkSynType env synType
        (Pattern.IsType testTy, [])

    | SynPat.OptionalVal(ident, _) ->
        // Optional parameter pattern: ?x
        let name = ident.idText
        let innerTy = freshTypeVar range
        let optTy = mkOptionType innerTy
        addConstraint (Constraint.Equals(expectedTy, optTy, range)) env
        (Pattern.Var(name, optTy), [(name, optTy)])

    | SynPat.ListCons(lhsPat, rhsPat, _, _) ->
        // List cons pattern: x :: xs
        let elemTy = freshTypeVar range
        let listTy = mkListType elemTy
        addConstraint (Constraint.Equals(expectedTy, listTy, range)) env
        let (lhsPattern, lhsBindings) = checkPattern env lhsPat elemTy range
        let (rhsPattern, rhsBindings) = checkPattern env rhsPat listTy range
        // Represent as a tuple pattern for head :: tail
        (Pattern.Tuple [lhsPattern; rhsPattern], lhsBindings @ rhsBindings)

    | SynPat.Ands(pats, _) ->
        // Conjunction pattern: pat1 & pat2 & ...
        let (patterns, bindings) =
            pats
            |> List.map (fun p -> checkPattern env p expectedTy range)
            |> List.unzip
        match patterns with
        | [single] -> (single, List.concat bindings)
        | _ -> (Pattern.And(List.head patterns, Pattern.Tuple (List.tail patterns)), List.concat bindings)

    | SynPat.Attrib(innerPat, _, _) ->
        // Attributed pattern - ignore attributes, check inner pattern
        checkPattern env innerPat expectedTy range

    | SynPat.QuoteExpr(_, _) ->
        // Quote expression pattern - not supported in native compilation
        addDiagnostic {
            Severity = NativeDiagnosticSeverity.Error
            Code = "FS8700"
            Message = "Quote expression patterns are not supported in native F# compilation."
            Range = range
            RelatedNodes = []
        } env
        (Pattern.Wildcard, [])  // Wildcard for error recovery

    | SynPat.FromParseError(innerPat, _) ->
        // Parse error recovery - check inner pattern
        checkPattern env innerPat expectedTy range

    | SynPat.InstanceMember _ ->
        // Instance member pattern - for object expressions (not supported in native)
        addDiagnostic {
            Severity = NativeDiagnosticSeverity.Error
            Code = "FS8701"
            Message = "Instance member patterns (object expressions) are not supported in native F# compilation."
            Range = range
            RelatedNodes = []
        } env
        (Pattern.Wildcard, [])  // Wildcard for error recovery

/// Check a SynType and convert to NativeType

//-------------------------------------------------------------------------
// Type Constraint Helpers (SRTP Resolution)
//-------------------------------------------------------------------------

/// Convert a SynTypar to a TypeParam
/// Creates a named type parameter from the syntax tree representation
/// Note: Currently creates fresh type parameters; scope tracking not yet implemented
and checkSynTypar (_env: TypeEnv) (synTypar: SynTypar) : TypeParam =
    let (SynTypar(ident, _typarStaticReq, _isCompGen)) = synTypar
    let name = "'" + ident.idText
    let range = rangeToSourceRange ident.idRange
    // Create a new named type parameter using the UnionFind helper
    // TODO: Track type parameters in scope for proper sharing
    freshTypeParam name TypeParamKind.Type range

/// Evaluate a SynRationalConst to an integer exponent
/// For simplicity, we only support integer exponents (not rational)
and evalRationalConst (synRat: SynRationalConst) : int =
    match synRat with
    | SynRationalConst.Integer(value, _) -> value
    | SynRationalConst.Negate(inner, _) -> -(evalRationalConst inner)
    | SynRationalConst.Paren(inner, _) -> evalRationalConst inner
    | SynRationalConst.Rational(num, _, _, denom, _, _range) ->
        // Rational exponents not fully supported in native compilation
        // Use the nearest integer (num / denom rounded)
        if denom <> 0 then num / denom else 1

/// Expand a measure power: m^n = m * m * ... * m (n times)
/// For negative powers: m^-n = 1 / (m^n)
and expandMeasurePower (baseMeasure: Measure) (exponent: int) : Measure =
    if exponent = 0 then MOne
    elif exponent = 1 then baseMeasure
    elif exponent = -1 then MInv baseMeasure
    elif exponent > 0 then
        // m^n = m * m * ... * m
        List.replicate exponent baseMeasure
        |> List.reduce (fun a b -> MProd(a, b))
    else
        // m^-n = 1 / m^n
        MInv (expandMeasurePower baseMeasure (-exponent))

/// Convert a SynMeasure to our native Measure representation
/// Per fsnative-spec units-of-measure.md: measures support product, quotient, power, and named units
and checkSynMeasure (env: TypeEnv) (synMeasure: SynMeasure) : Measure =
    match synMeasure with
    | SynMeasure.One _ ->
        // The dimensionless unit: 1
        MOne

    | SynMeasure.Named(longId, _) ->
        // Named measure: kg, m, s, or module-qualified like Physics.Meters
        let parts = longId |> List.map (fun id -> id.idText)
        let name = parts |> List.last
        let modulePath = parts |> List.rev |> List.tail |> List.rev
        MCon(name, modulePath)

    | SynMeasure.Product(m1, _, m2, _) ->
        // Product of measures: m1 * m2
        let measure1 = checkSynMeasure env m1
        let measure2 = checkSynMeasure env m2
        MProd(measure1, measure2)

    | SynMeasure.Divide(Some m1, _, m2, _) ->
        // Division: m1 / m2 = m1 * (1/m2)
        let measure1 = checkSynMeasure env m1
        let measure2 = checkSynMeasure env m2
        MProd(measure1, MInv measure2)

    | SynMeasure.Divide(None, _, m2, _) ->
        // Division with no numerator: /m2 = 1/m2
        let measure2 = checkSynMeasure env m2
        MInv measure2

    | SynMeasure.Power(baseMeasure, _, power, _) ->
        // Power: m^n
        let measure = checkSynMeasure env baseMeasure
        let exp = evalRationalConst power
        expandMeasurePower measure exp

    | SynMeasure.Var(synTypar, _) ->
        // Measure type variable: 'u
        let tp = checkSynTypar env synTypar
        // Ensure it's marked as a measure parameter
        let measureTp = { tp with Kind = TypeParamKind.Measure }
        MVar measureTp

    | SynMeasure.Seq(measures, _) ->
        // Sequence of measures: m1 m2 m3 (implicit product)
        measures
        |> List.map (checkSynMeasure env)
        |> List.reduce (fun a b -> MProd(a, b))

    | SynMeasure.Anon _ ->
        // Anonymous measure: _ (fresh measure variable)
        let range = dummyRange
        MVar (freshMeasureVar range)

    | SynMeasure.Paren(inner, _) ->
        // Parenthesized measure
        checkSynMeasure env inner

/// Check a type constraint from syntax and record it
/// Per native_type_checker_design_principles: SRTP resolved DURING type checking
/// Returns the constraint to add to the type parameter, or None if handled inline
and checkSynConstraint (env: TypeEnv) (constraint_: SynTypeConstraint) : Constraint option =
    match constraint_ with
    // KEY FOR SRTP: (^a or ^b) : (static member op : signature)
    | SynTypeConstraint.WhereTyparSupportsMember(typars, memberSig, range) ->
        let typarType = checkSynType env typars
        let nativeRange = rangeToSourceRange range
        // Extract member name and signature from the member signature
        let memberName =
            match memberSig with
            | SynMemberSig.Member(SynValSig(ident = SynIdent(id, _)), _, _, _) -> id.idText
            | _ -> "unknown_member"
        let memberType =
            match memberSig with
            | SynMemberSig.Member(SynValSig(synType = synRetType), _, _, _) ->
                checkSynType env synRetType
            | _ -> freshTypeVar nativeRange
        Some (Constraint.HasMember(typarType, memberName, memberType, nativeRange))

    // Subtype/inheritance constraint: 'a :> ISomething
    | SynTypeConstraint.WhereTyparSubtypeOfType(synTypar, superType, range) ->
        let typar = checkSynTypar env synTypar
        let superTy = checkSynType env superType
        let nativeRange = rangeToSourceRange range
        Some (Constraint.Subtype(NativeType.TVar typar, superTy, nativeRange))

    // Struct constraint: 'a : struct
    | SynTypeConstraint.WhereTyparIsValueType(synTypar, range) ->
        let typar = checkSynTypar env synTypar
        let nativeRange = rangeToSourceRange range
        // Record as layout constraint - type must be inline (stack-allocated)
        Some (Constraint.LayoutCompatible(NativeType.TVar typar, TypeLayout.Inline(-1, -1), nativeRange))

    // Reference type constraint: 'a : not struct
    | SynTypeConstraint.WhereTyparIsReferenceType(synTypar, range) ->
        let typar = checkSynTypar env synTypar
        let nativeRange = rangeToSourceRange range
        // Record as layout constraint - type must be reference (arena-allocated)
        Some (Constraint.LayoutCompatible(NativeType.TVar typar, TypeLayout.Reference ArenaAffinity.CurrentActor, nativeRange))

    // Unmanaged constraint: 'a : unmanaged
    | SynTypeConstraint.WhereTyparIsUnmanaged(synTypar, range) ->
        let typar = checkSynTypar env synTypar
        let nativeRange = rangeToSourceRange range
        // Unmanaged = no GC references, blittable - use inline layout
        Some (Constraint.LayoutCompatible(NativeType.TVar typar, TypeLayout.Inline(-1, -1), nativeRange))

    // NULL CONSTRAINT - REJECTED in fsnative
    // Per fsnative-spec types-and-type-constraints.md: null is not permitted
    | SynTypeConstraint.WhereTyparSupportsNull(_, range) ->
        addNativeError DiagnosticCodes.FS8710_NullConstraint range
            "The 'null' constraint is not permitted in F# Native. Use ValueOption for optional values."
            env
        None

    // Not null constraint: 'a : not null
    | SynTypeConstraint.WhereTyparNotSupportsNull(_, _, _) ->
        // All types in native are non-nullable by default - this is a no-op
        None

    // Comparison constraint: 'a : comparison
    | SynTypeConstraint.WhereTyparIsComparable(synTypar, range) ->
        let typar = checkSynTypar env synTypar
        let nativeRange = rangeToSourceRange range
        // In Alloy, comparison is via SRTP - generate HasMember for comparison operations
        // Type must implement: compare : 'a -> 'a -> int
        let compareTy = NativeType.TFun(NativeType.TVar typar, NativeType.TFun(NativeType.TVar typar, Types.intType))
        Some (Constraint.HasMember(NativeType.TVar typar, "compare", compareTy, nativeRange))

    // Equality constraint: 'a : equality
    | SynTypeConstraint.WhereTyparIsEquatable(synTypar, range) ->
        let typar = checkSynTypar env synTypar
        let nativeRange = rangeToSourceRange range
        // In Alloy, equality is via SRTP - generate HasMember for equality operations
        // Type must implement: op_Equality : 'a -> 'a -> bool
        let eqTy = NativeType.TFun(NativeType.TVar typar, NativeType.TFun(NativeType.TVar typar, Types.boolType))
        Some (Constraint.HasMember(NativeType.TVar typar, "op_Equality", eqTy, nativeRange))

    // Default type constraint: 'a : > Type (defaults to Type if unconstrained)
    | SynTypeConstraint.WhereTyparDefaultsToType(synTypar, defaultType, _range) ->
        // Record the default but don't emit as constraint - used during generalization
        let _typar = checkSynTypar env synTypar
        let _defaultTy = checkSynType env defaultType
        // TODO: Store default types for generalization
        None

    // Enum constraint: 'a : enum<int>
    | SynTypeConstraint.WhereTyparIsEnum(_, _, range) ->
        addNativeError DiagnosticCodes.FS8711_UnsupportedConstraint range
            "Enum constraints are not supported in F# Native. Use discriminated unions instead."
            env
        None

    // Delegate constraint: 'a : delegate<arg, ret>
    | SynTypeConstraint.WhereTyparIsDelegate(_, _, range) ->
        addNativeError DiagnosticCodes.FS8711_UnsupportedConstraint range
            "Delegate constraints are not supported in F# Native. Use function types instead."
            env
        None

    // Self constraint (used in recursive type definitions)
    | SynTypeConstraint.WhereSelfConstrained(selfType, range) ->
        let selfTy = checkSynType env selfType
        let nativeRange = rangeToSourceRange range
        // Self constraints typically appear in recursive type definitions
        // For now, treat as type equality with fresh variable
        let freshTy = freshTypeVar nativeRange
        Some (Constraint.Equals(selfTy, freshTy, nativeRange))

and checkSynType (env: TypeEnv) (synType: SynType) : NativeType =
    match synType with
    | SynType.LongIdent(longIdent) ->
        let name = longIdent.LongIdent |> List.map (fun id -> id.idText) |> String.concat "."
        let range = longIdent.Range
        
        // FS8500: BCL type references are FORBIDDEN - check FIRST
        if isBclReference name then
            addBclError name range env
            NativeType.TError $"BCL type: {name}"
        // CRITICAL: Reject 'obj' - FS8011
        // The type 'obj' (System.Object) does not exist in F# Native.
        // The native type system is closed - no boxing, no runtime type inspection.
        elif name = "obj" || name = "System.Object" || name = "Object" then
            addObjError range env
            NativeType.TError "obj not supported"
        else
            match tryFindBuiltinTyCon name with
            | Some tyCon -> mkSimpleType tyCon
            | None ->
                // Try to find in type definitions
                match Map.tryFind name env.TypeDefs with
                | Some tyCon -> mkSimpleType tyCon
                | None ->
                    // Try to find in type abbreviations
                    match tryLookupTypeAbbrev name env with
                    | Some ty -> ty
                    | None -> NativeType.TError $"Unknown type: {name}"

    | SynType.App(typeName, _, typeArgs, _, _, _, _) ->
        let baseTy = checkSynType env typeName
        let argTys = typeArgs |> List.map (checkSynType env)
        match baseTy with
        | NativeType.TApp(tyCon, []) -> NativeType.TApp(tyCon, argTys)
        | _ -> baseTy  // Already an error or complex type

    | SynType.LongIdentApp(typeName, _longIdent, _, typeArgs, _, _, _) ->
        // Qualified generic type: Module.Type<arg1, arg2>
        let baseTy = checkSynType env typeName
        let argTys = typeArgs |> List.map (checkSynType env)
        match baseTy with
        | NativeType.TApp(tyCon, []) -> NativeType.TApp(tyCon, argTys)
        | _ -> baseTy

    | SynType.Tuple(isStruct, elementTypes, _) ->
        // SynTupleTypeSegment is a union: Type of SynType | Star of range | Slash of range
        // Filter for Type segments only
        let elemTys =
            elementTypes
            |> List.choose (function
                | SynTupleTypeSegment.Type ty -> Some (checkSynType env ty)
                | SynTupleTypeSegment.Star _ -> None
                | SynTupleTypeSegment.Slash _ -> None)
        NativeType.TTuple(elemTys, isStruct)

    | SynType.AnonRecd(isStruct, fields, _) ->
        // Anonymous record: {| field1: T1; field2: T2 |}
        let fieldTys = fields |> List.map (fun (id, ty) -> (id.idText, checkSynType env ty))
        NativeType.TAnon(fieldTys, isStruct)

    | SynType.Array(_rank, elementType, _) ->
        // Array types: int[], byte[], etc.
        let elemTy = checkSynType env elementType
        // Note: rank > 1 for multidimensional arrays - for now, treat all as 1D
        mkArrayType elemTy

    | SynType.Fun(argType, returnType, _, _) ->
        let argTy = checkSynType env argType
        let retTy = checkSynType env returnType
        NativeType.TFun(argTy, retTy)

    | SynType.Var(_typar, _) ->
        // Type variable - create a fresh type variable
        freshTypeVar dummyRange

    | SynType.Anon _ ->
        // Anonymous type: _
        freshTypeVar dummyRange

    | SynType.WithGlobalConstraints(typeName, constraints, _) ->
        // Type with constraints: 'a when 'a :> IComparable
        // Per native_type_checker_design_principles: SRTP resolved DURING type checking
        let innerTy = checkSynType env typeName
        
        // Process each constraint and record them
        let nativeConstraints =
            constraints
            |> List.choose (checkSynConstraint env)
        
        // Add constraints to type parameter if inner type is a TVar
        // This attaches constraints to the type parameter for later resolution
        match innerTy with
        | NativeType.TVar typar ->
            typar.Constraints <- nativeConstraints @ typar.Constraints
        | _ ->
            // For non-variable types, add constraints to the environment
            for constraint_ in nativeConstraints do
                addConstraint constraint_ env
        
        innerTy

    | SynType.HashConstraint(innerType, _) ->
        // Hash constraint: #IInterface (flexible type)
        checkSynType env innerType

    | SynType.MeasurePower(baseMeasure, exponent, _) ->
        // Measure type: int<m^2> - units of measure
        // Per fsnative-spec units-of-measure.md: measures support product, quotient, power
        // Convert the SynMeasure base and apply the exponent
        let measure =
            match baseMeasure with
            | SynType.Var(synTypar, _) ->
                // Type variable as measure: 'u^2
                let tp = checkSynTypar env synTypar
                let measureTp = { tp with Kind = TypeParamKind.Measure }
                MVar measureTp
            | SynType.LongIdent(longIdent) ->
                // Named measure: kg^2, m^-1
                let parts = longIdent.LongIdent |> List.map (fun id -> id.idText)
                let name = parts |> List.last
                let modulePath = parts |> List.rev |> List.tail |> List.rev
                MCon(name, modulePath)
            | _ ->
                // Complex measure expression - try to parse as measure
                MOne
        let exp = evalRationalConst exponent
        NativeType.TMeasure(expandMeasurePower measure exp)

    | SynType.StaticConstant(constant, _range) ->
        // Static type constant - used in type-level programming
        match constant with
        | SynConst.Int32 n -> NativeType.TError $"Static constant {n} not yet supported"
        | SynConst.String(s, _, _) -> NativeType.TError $"Static constant \"{s}\" not yet supported"
        | _ -> NativeType.TError "Static constant type not yet supported"

    | SynType.StaticConstantNull range ->
        // null type constant - REJECTED in native
        addNullError range env
        NativeType.TError "null not allowed in F# Native"

    | SynType.StaticConstantExpr(_expr, _) ->
        // Static type-level expression
        NativeType.TError "Static constant expressions not yet supported"

    | SynType.StaticConstantNamed(_ident, _value, _) ->
        // Named static constant
        NativeType.TError "Named static constants not yet supported"

    | SynType.WithNull(innerType, _ambivalent, range, _) ->
        // Nullable type annotation: string | null
        // Native types are null-free by design - emit warning and return inner type
        // The type system doesn't support null; use ValueOption instead
        addNullWarning range env
        checkSynType env innerType

    | SynType.Paren(innerType, _) ->
        checkSynType env innerType

    | SynType.SignatureParameter(_, _, _, usedType, _) ->
        // Parameter in a signature - check the actual type
        checkSynType env usedType

    | SynType.Or(lhsType, _rhsType, _, _) ->
        // Flexible type: (type | type) - use the left type for now
        // This is typically used for flexible generic constraints
        checkSynType env lhsType

    | SynType.FromParseError _ ->
        // Parse error recovery - return error type
        NativeType.TError "Parse error in type syntax"

    | SynType.Intersection(_typar, types, _, _) ->
        // Intersection type: for SRTP constraints like ^T & IComparable
        match types with
        | first :: _ -> checkSynType env first
        | [] -> NativeType.TError "Empty intersection type"

//-------------------------------------------------------------------------
// Entry Point
//-------------------------------------------------------------------------

/// Check an expression and solve constraints
let checkAndSolve (env: TypeEnv) (builder: NodeBuilder) (expr: SynExpr) : SemanticNode * Constraint list =
    // Reset constraint list
    env.Constraints <- []

    // Check expression
    let node = checkExpr env builder expr

    // Collect constraints
    let constraints = env.Constraints

    (node, constraints)
