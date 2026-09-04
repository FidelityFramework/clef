// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// SRTP (Statically Resolved Type Parameters) resolution during type checking.
/// Unlike FCS where SRTP is resolved post-hoc, Clef resolves SRTP
/// during construction, making it intrinsic to the type checker.
module Clef.Compiler.NativeTypedTree.SRTPResolution

open Clef.Compiler.NativeTypedTree.NativeTypes

open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

//-------------------------------------------------------------------------
// SRTP Types (ordered for forward references)
//-------------------------------------------------------------------------

/// The kind of witness implementation
type WitnessKind =
    /// A static member on the type
    | StaticMember
    /// An instance member on the type
    | InstanceMember
    /// A module-level function (extension)
    | ModuleFunction
    /// A platform binding (requires special handling)
    | PlatformBinding

/// Pattern for matching types in witness lookup
type TypePattern =
    /// Exact match on a type constructor
    | Exact of TypeConRef
    /// Any type implementing a trait/interface
    | HasTrait of string
    /// Any numeric type
    | Numeric
    /// Any type
    | Any

/// Result of resolving an SRTP constraint
[<NoComparison; NoEquality>]
type WitnessResolution = {
    /// The original operator/member name
    Operator: string
    /// The concrete argument type after resolution
    ArgType: NativeType
    /// The resolved member (qualified name)
    ResolvedMember: string
    /// The module containing the implementation
    ImplementingModule: ModulePath
    /// The implementation kind
    Kind: WitnessKind
}

/// An entry in the witness table
[<NoComparison; NoEquality>]
type WitnessEntry = {
    /// The member name this witness provides
    MemberName: string
    /// The type this witness is for (or a type pattern)
    ForType: TypePattern
    /// The resolved implementation
    Resolution: WitnessResolution
}

/// Key for identifying an SRTP constraint (uses string representation for Map compatibility)
type SRTPKeyId = string

/// Key for identifying an SRTP constraint
[<NoComparison; NoEquality>]
type SRTPKey = {
    /// The operator or member name (e.g., "op_Dollar", "+", "ToString")
    MemberName: string
    /// The type being constrained
    ArgType: NativeType
    /// Source location for error reporting
    Range: SourceRange
}

/// Create a unique identifier for an SRTP key
let srtpKeyId (key: SRTPKey) : SRTPKeyId =
    $"{key.MemberName}@{key.Range.File}:{key.Range.Start.Line}:{key.Range.Start.Column}"

/// The witness table containing all known SRTP resolutions
[<NoComparison; NoEquality>]
type WitnessTable = {
    /// Witnesses indexed by member name
    ByMemberName: Map<string, WitnessEntry list>
    /// Built-in operator witnesses
    BuiltinOps: Map<string, (NativeType -> WitnessResolution option)>
}

//-------------------------------------------------------------------------
// Built-in SRTP Operators
//-------------------------------------------------------------------------

/// Create a witness resolution for numeric operators
let private numericOpWitness (op: string) (ty: NativeType) : WitnessResolution option =
    if Types.isNumericType ty then
        Some {
            Operator = op
            ArgType = ty
            ResolvedMember = $"op_{op}"
            ImplementingModule = ["Fidelity"; "Core"]
            Kind = WitnessKind.StaticMember
        }
    else
        None

/// Create a witness resolution for comparison operators
let private comparisonOpWitness (op: string) (ty: NativeType) : WitnessResolution option =
    // Most types support comparison
    match ty with
    | NativeType.TError _ -> None
    | _ ->
        Some {
            Operator = op
            ArgType = ty
            ResolvedMember = $"op_{op}"
            ImplementingModule = ["Fidelity"; "Core"]
            Kind = WitnessKind.StaticMember
        }

/// Create a witness resolution for equality operators
let private equalityOpWitness (op: string) (ty: NativeType) : WitnessResolution option =
    match ty with
    | NativeType.TError _ -> None
    | _ ->
        Some {
            Operator = op
            ArgType = ty
            ResolvedMember = $"op_{op}"
            ImplementingModule = ["Fidelity"; "Core"]
            Kind = WitnessKind.StaticMember
        }

/// Map of F# operator names to their internal names
let private operatorNameMap =
    Map.ofList [
        // Arithmetic
        ("+", "Addition")
        ("-", "Subtraction")
        ("*", "Multiply")
        ("/", "Division")
        ("%", "Modulus")
        ("~-", "UnaryNegation")
        ("~+", "UnaryPlus")

        // Bitwise
        ("&&&", "BitwiseAnd")
        ("|||", "BitwiseOr")
        ("^^^", "ExclusiveOr")
        ("~~~", "LogicalNot")
        ("<<<", "LeftShift")
        (">>>", "RightShift")

        // Comparison
        ("<", "LessThan")
        (">", "GreaterThan")
        ("<=", "LessThanOrEqual")
        (">=", "GreaterThanOrEqual")
        ("=", "Equality")
        ("<>", "Inequality")

        // Special Alloy operators
        ("$", "Dollar")  // String formatting in Alloy
        ("|>", "PipeRight")
        ("<|", "PipeLeft")
        (">>", "ComposeRight")
        ("<<", "ComposeLeft")
    ]

/// Built-in operator witnesses
let private builtinOps : Map<string, (NativeType -> WitnessResolution option)> =
    let arithmetic = ["+"; "-"; "*"; "/"; "%"; "~-"; "~+"]
    let bitwise = ["&&&"; "|||"; "^^^"; "~~~"; "<<<"; ">>>"]
    let comparison = ["<"; ">"; "<="; ">="]
    let equality = ["="; "<>"]

    let entries =
        [
            // Arithmetic operators - numeric types only
            for op in arithmetic do
                yield (op, numericOpWitness op)

            // Bitwise operators - integer types only
            for op in bitwise do
                yield (op, fun ty ->
                    if Types.isIntegerType ty then numericOpWitness op ty
                    else None)

            // Comparison operators - most types
            for op in comparison do
                yield (op, comparisonOpWitness op)

            // Equality operators - most types
            for op in equality do
                yield (op, equalityOpWitness op)
        ]

    Map.ofList entries

//-------------------------------------------------------------------------
// NTU Conversion Functions
// Must be defined before SRTP Resolution Logic due to forward reference
//-------------------------------------------------------------------------

/// Names of conversion functions (bare identifiers in F#)
/// Used by isSRTPOperator to include conversions in SRTP resolution
let private conversionFunctions =
    Set.ofList [
        // Integer conversions
        "int"; "int8"; "sbyte"; "int16"; "int32"; "int64"; "nativeint"
        // Unsigned integer conversions
        "byte"; "uint8"; "uint16"; "uint32"; "uint64"; "unativeint"
        // Floating point conversions
        "float"; "double"; "float32"; "single"; "decimal"
        // Other conversions
        "char"; "string"
    ]

/// Check if a name is a conversion function
let isConversionFunction (name: string) : bool =
    conversionFunctions.Contains name

//-------------------------------------------------------------------------
// SRTP Resolution Logic
//-------------------------------------------------------------------------

/// Check if a name is an SRTP operator
let isSRTPOperator (name: string) : bool =
    builtinOps.ContainsKey name ||
    name.StartsWith("op_") ||
    name = "$" ||  // Alloy's string formatting operator
    conversionFunctions.Contains name  // NTU conversion functions

/// Try to resolve an SRTP constraint for a built-in operator
let private tryResolveBuiltinOp (op: string) (argType: NativeType) : WitnessResolution option =
    match Map.tryFind op builtinOps with
    | Some resolver -> resolver argType
    | None -> None

/// Try to resolve SRTP via the witness table
let private tryResolveViaTable (table: WitnessTable) (memberName: string) (argType: NativeType) : WitnessResolution option =
    match Map.tryFind memberName table.ByMemberName with
    | None -> None
    | Some entries ->
        entries
        |> List.tryPick (fun entry ->
            match entry.ForType with
            | TypePattern.Any -> Some entry.Resolution
            | TypePattern.Exact tyCon ->
                match argType with
                | NativeType.TApp(tc, _) when tc.Name = tyCon.Name -> Some entry.Resolution
                | _ -> None
            | TypePattern.Numeric ->
                if Types.isNumericType argType then Some entry.Resolution
                else None
            | TypePattern.HasTrait traitName ->
                // Trait-based SRTP resolution is not yet implemented.
                // In native F#, traits are structural (type must have the member).
                // For now, this falls through to error handling which reports
                // "No witness found for <member> on type" - clear diagnostic.
                // If trait checking is needed, implement hasTraitMember here.
                eprintfn "[SRTP] Warning: HasTrait(%s) pattern not yet implemented for type %A" traitName argType
                None)

/// Resolve the Alloy $ operator for string formatting
let private resolveAlloyDollar (argType: NativeType) : WitnessResolution option =
    // $ is dispatched based on the argument type to find a WritableString implementation
    match argType with
    | NativeType.TApp(tyCon, _) ->
        Some {
            Operator = "$"
            ArgType = argType
            ResolvedMember = $"{tyCon.Name}.op_Dollar"
            ImplementingModule = ["Alloy"; "Text"]
            Kind = WitnessKind.StaticMember
        }
    | _ -> None

/// Check if a type has any unbound type variables
let private hasUnboundTypeVars (ty: NativeType) : bool =
    hasUnboundVars ty

//-------------------------------------------------------------------------
// NTU Conversion Resolution (placed before tryResolve due to F# ordering)
//
// Conversions follow the F# syntax: `float x`, `int y`, `string z`
// SRTP resolution determines the operation based on source type.
//
// See: clef-lang-spec/spec/drafts/NTU_Conversion_Model.md
//-------------------------------------------------------------------------

/// Conversion category determines semantics and MLIR operation
type ConversionCategory =
    | Widening      // Safe, no data loss (int→int64, int→float)
    | Narrowing     // May truncate (int64→int32, float→int)
    | CrossFamily   // Different representations (large int↔float)
    | Formatting    // To string
    | Parsing       // From string

/// Get the target type for a conversion function name
let private getConversionTargetType (funcName: string) : NativeType option =
    match funcName with
    | "int" -> Some Types.intType
    | "int8" | "sbyte" -> Some Types.int8Type
    | "int16" -> Some Types.int16Type
    | "int32" -> Some Types.int32Type
    | "int64" -> Some Types.int64Type
    | "nativeint" -> Some Types.nintType
    | "byte" | "uint8" -> Some Types.uint8Type
    | "uint16" -> Some Types.uint16Type
    | "uint32" -> Some Types.uint32Type
    | "uint64" -> Some Types.uint64Type
    | "unativeint" -> Some Types.unintType
    | "float" | "double" -> Some Types.floatType
    | "float32" | "single" -> Some Types.float32Type
    | "decimal" -> Some Types.decimalType
    | "char" -> Some Types.charType
    | "string" -> Some Types.stringType
    | _ -> None

/// Check if a type is signed (helper using NTUKind)
let private isSignedType (ty: NativeType) : bool =
    match ty with
    | NativeType.TApp(tc, []) ->
        match tc.NTUKind with
        | Some kind -> NTUKind.isSigned kind
        | None -> false
    | _ -> false

/// Check if a type is string
let private isStringType (ty: NativeType) : bool =
    match ty with
    | NativeType.TApp(tc, _) -> tc.Name = "string"
    | _ -> false

/// Determine conversion category based on source and target types
let private categorizeConversion (sourceType: NativeType) (targetType: NativeType) : ConversionCategory =
    match sourceType, targetType with
    // Formatting: any → string
    | _, t when isStringType t -> Formatting

    // Parsing: string → any
    | s, _ when isStringType s -> Parsing

    // Int → Float (widening, may lose precision for large ints)
    | s, t when Types.isIntegerType s && Types.isFloatType t -> Widening

    // Float → Int (narrowing, truncates fractional part)
    | s, t when Types.isFloatType s && Types.isIntegerType t -> Narrowing

    // Integer to integer - simplified categorization
    | s, t when Types.isIntegerType s && Types.isIntegerType t -> Widening

    // Float to float
    | s, t when Types.isFloatType s && Types.isFloatType t -> Widening

    // Default to narrowing (conservative)
    | _ -> Narrowing

/// Get the MLIR operation for a conversion
let private getConversionMLIROp (sourceType: NativeType) (targetType: NativeType) : string =
    match sourceType, targetType with
    // Int → Float
    | s, t when Types.isIntegerType s && Types.isFloatType t ->
        if isSignedType s then "arith.sitofp" else "arith.uitofp"

    // Float → Int
    | s, t when Types.isFloatType s && Types.isIntegerType t ->
        if isSignedType t then "arith.fptosi" else "arith.fptoui"

    // Int → Int (widening/narrowing)
    | s, t when Types.isIntegerType s && Types.isIntegerType t ->
        if isSignedType s then "arith.extsi" else "arith.extui"
        // Note: for narrowing, should be "arith.trunci" - need size comparison

    // Float → Float
    | s, t when Types.isFloatType s && Types.isFloatType t ->
        "arith.extf"  // or truncf depending on direction

    // Formatting
    | _, t when isStringType t -> "fidelity.format"

    // Parsing
    | s, _ when isStringType s -> "fidelity.parse"

    // Unknown
    | _ -> "fidelity.convert"

/// Resolve a conversion function application
/// Returns WitnessResolution if valid, None if invalid conversion
let private resolveConversion (funcName: string) (sourceType: NativeType) : WitnessResolution option =
    match getConversionTargetType funcName with
    | None -> None  // Not a conversion function
    | Some targetType ->
        let _category = categorizeConversion sourceType targetType
        let _mlirOp = getConversionMLIROp sourceType targetType

        // Create internal name following F* convention
        let sourceTypeName =
            match sourceType with
            | NativeType.TApp(tc, _) -> tc.Name
            | NativeType.TVar spec -> spec.Name
            | _ -> "unknown"

        Some {
            Operator = funcName
            ArgType = sourceType
            ResolvedMember = $"{sourceTypeName}_to_{funcName}"  // e.g., "int_to_float"
            ImplementingModule = ["Fidelity"; "Conversion"]
            Kind = WitnessKind.StaticMember
        }

/// The SRTP resolver
[<NoComparison; NoEquality>]
type SRTPResolver = {
    /// The witness table
    WitnessTable: WitnessTable
    /// Deferred SRTP constraints (waiting for type variables to be resolved)
    mutable Deferred: (SRTPKey * (WitnessResolution -> unit)) list
    /// Resolved SRTPs (keyed by string ID)
    mutable Resolutions: Map<SRTPKeyId, WitnessResolution>
    /// Errors encountered during resolution
    mutable Errors: (SRTPKey * string) list
}

/// Create a new SRTP resolver
let createResolver () : SRTPResolver = {
    WitnessTable = { ByMemberName = Map.empty; BuiltinOps = builtinOps }
    Deferred = []
    Resolutions = Map.empty
    Errors = []
}

/// Create a resolver with a custom witness table
let createResolverWithTable (table: WitnessTable) : SRTPResolver = {
    WitnessTable = table
    Deferred = []
    Resolutions = Map.empty
    Errors = []
}

/// Add a witness to the resolver's table
let addWitness (resolver: SRTPResolver) (entry: WitnessEntry) : unit =
    let existing = Map.tryFind entry.MemberName resolver.WitnessTable.ByMemberName |> Option.defaultValue []
    let _updated = { resolver.WitnessTable with ByMemberName = Map.add entry.MemberName (entry :: existing) resolver.WitnessTable.ByMemberName }
    // Note: This would need to be mutable in real use
    ()

/// Try to resolve an SRTP constraint immediately
/// Returns Some if resolved, None if deferred (type not yet concrete)
let tryResolve (resolver: SRTPResolver) (key: SRTPKey) : WitnessResolution option =
    // Apply any existing substitutions to get the concrete type
    let concreteType = applySubst key.ArgType

    // If type still has unbound variables, we can't resolve yet
    if hasUnboundTypeVars concreteType then
        None
    else
        // Try resolution in order:
        // 1. Built-in operators (arithmetic, comparison, etc.)
        // 2. Special Alloy operators ($)
        // 3. Conversion functions (float, int, string, etc.)
        // 4. Witness table

        let resolution =
            tryResolveBuiltinOp key.MemberName concreteType
            |> Option.orElseWith (fun () ->
                if key.MemberName = "$" then resolveAlloyDollar concreteType
                else None)
            |> Option.orElseWith (fun () ->
                if isConversionFunction key.MemberName then
                    resolveConversion key.MemberName concreteType
                else None)
            |> Option.orElseWith (fun () ->
                tryResolveViaTable resolver.WitnessTable key.MemberName concreteType)

        match resolution with
        | Some res ->
            // Cache the resolution using string key
            let keyId = srtpKeyId key
            resolver.Resolutions <- Map.add keyId res resolver.Resolutions
            Some res
        | None ->
            // No witness found for a concrete type - this is an error
            resolver.Errors <- (key, $"No witness found for '{key.MemberName}' on type") :: resolver.Errors
            None

/// Defer an SRTP constraint for later resolution
let deferConstraint (resolver: SRTPResolver) (key: SRTPKey) (callback: WitnessResolution -> unit) : unit =
    resolver.Deferred <- (key, callback) :: resolver.Deferred

/// Try to resolve all deferred constraints
/// Called after constraint solving when types are more concrete
let resolveDeferred (resolver: SRTPResolver) : unit =
    let stillDeferred =
        resolver.Deferred
        |> List.filter (fun (key, callback) ->
            let concreteType = applySubst key.ArgType
            let key' = { key with ArgType = concreteType }

            match tryResolve resolver key' with
            | Some res ->
                callback res
                false  // Resolved, remove from deferred
            | None ->
                if hasUnboundTypeVars concreteType then
                    true  // Still has type variables, keep deferred
                else
                    // Error case - no witness for concrete type
                    false  // Remove, error already recorded
        )

    resolver.Deferred <- stillDeferred

/// Get all resolution errors
let getErrors (resolver: SRTPResolver) : (SRTPKey * string) list =
    resolver.Errors

/// Check if there are any unresolved deferred constraints
let hasUnresolvedConstraints (resolver: SRTPResolver) : bool =
    not (List.isEmpty resolver.Deferred)

//-------------------------------------------------------------------------
// Integration with CheckExpr
//-------------------------------------------------------------------------

/// Try to resolve SRTP during expression checking
/// This is called from CheckExpr when checking function applications
let tryResolveSRTPForApp
    (resolver: SRTPResolver)
    (funcName: string)
    (argType: NativeType)
    (range: SourceRange)
    : WitnessResolution option =

    if not (isSRTPOperator funcName) then
        None
    else
        let key = { MemberName = funcName; ArgType = argType; Range = range }
        tryResolve resolver key

/// Create a HasMember constraint for SRTP
/// Used when the type isn't concrete enough to resolve immediately
let createHasMemberConstraint
    (memberName: string)
    (ty: NativeType)
    (resultTy: NativeType)
    (range: SourceRange)
    : Constraint =
    Constraint.HasMember(ty, memberName, resultTy, range)

//-------------------------------------------------------------------------
// Witness Table Construction
//-------------------------------------------------------------------------

/// Create a witness table from Alloy module definitions
/// This would be populated during module loading
let createAlloyWitnessTable () : WitnessTable =
    // For now, create an empty table with built-in ops
    // In real use, this would be populated from Alloy source analysis
    {
        ByMemberName = Map.empty
        BuiltinOps = builtinOps
    }

/// Add Alloy Console.Write witness
let addConsoleWriteWitness (table: WitnessTable) : WitnessTable =
    let entry = {
        MemberName = "Write"
        ForType = TypePattern.Any
        Resolution = {
            Operator = "Write"
            ArgType = Types.stringType  // Will be specialized
            ResolvedMember = "Alloy.Console.Write"
            ImplementingModule = ["Alloy"; "Console"]
            Kind = WitnessKind.ModuleFunction
        }
    }
    let existing = Map.tryFind "Write" table.ByMemberName |> Option.defaultValue []
    { table with ByMemberName = Map.add "Write" (entry :: existing) table.ByMemberName }

/// Add Alloy $ (WritableString) witnesses for common types
let addWritableStringWitnesses (table: WitnessTable) : WitnessTable =
    let stringEntry = {
        MemberName = "$"
        ForType = TypePattern.Exact Types.stringTyCon
        Resolution = {
            Operator = "$"
            ArgType = Types.stringType
            ResolvedMember = "NativeStr.op_Dollar"
            ImplementingModule = ["Alloy"; "Text"]
            Kind = WitnessKind.StaticMember
        }
    }

    let intEntry = {
        MemberName = "$"
        ForType = TypePattern.Exact Types.intTyCon
        Resolution = {
            Operator = "$"
            ArgType = Types.intType
            ResolvedMember = "Int32.op_Dollar"
            ImplementingModule = ["Alloy"; "Text"]
            Kind = WitnessKind.StaticMember
        }
    }

    let existing = Map.tryFind "$" table.ByMemberName |> Option.defaultValue []
    { table with ByMemberName = Map.add "$" (stringEntry :: intEntry :: existing) table.ByMemberName }
