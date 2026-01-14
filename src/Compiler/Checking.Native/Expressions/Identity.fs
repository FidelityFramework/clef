// Copyright (c) 2025 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Unified identifier resolution for F# Native.
/// This module provides ONE code path for both SynExpr.Ident and SynExpr.LongIdent,
/// eliminating the duplicate resolution logic that existed before restructuring.
///
/// ARCHITECTURAL PRINCIPLE: Single resolution path.
/// Both simple identifiers (Ident) and qualified identifiers (LongIdent) flow through
/// the same resolveIdentifier function, ensuring consistent intrinsic and binding handling.
///
/// NOTE: This module also handles the case where LongIdent represents member access
/// (e.g., "s.Pointer" parsed as LongIdent instead of DotGet). This is a parser ambiguity
/// that should eventually be resolved via a proper nanopass architecture.
/// TODO: Factor member access normalization into a dedicated nanopass.
module FSharp.Native.Compiler.Checking.Native.Expressions.Identity

open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.SemanticGraph
open FSharp.Native.Compiler.Checking.Native.Expressions.Types
open FSharp.Native.Compiler.Checking.Native.Expressions.Intrinsics
open FSharp.Native.Compiler.Checking.Native.UnionFind
module NR = FSharp.Native.Compiler.Checking.Native.NameResolution
module NativeGlobals = FSharp.Native.Compiler.Checking.Native.NativeGlobals

//-------------------------------------------------------------------------
// Identifier Resolution Result
//-------------------------------------------------------------------------

/// Result of resolving an identifier - used internally
type private IdentifierResolution =
    | IntrinsicNode of IntrinsicInfo * NativeType
    | BindingNode of string * NativeType * NodeId option
    | LiteralSubstitution of LiteralValue * NativeType
    | UnionCaseNode of string * NativeType * NR.UnionCaseInfo
    | MemberAccessNode of baseBinding: NR.ResolvedBinding * baseName: string * memberName: string * resultType: NativeType
    | ErrorNode of string * NativeType

//-------------------------------------------------------------------------
// Core Resolution Logic
//-------------------------------------------------------------------------

/// Resolve an identifier to its meaning.
/// This is the SINGLE code path for both Ident and LongIdent.
let rec private resolveIdentifierCore
    (parts: string list)
    (env: TypeEnv)
    (range: SourceRange)
    : IdentifierResolution =

    let fullName = String.concat "." parts

    // 1. BCL rejection - FIRST, fail fast
    if isBclReference fullName then
        ErrorNode ($"BCL: {fullName}", NativeType.TError $"BCL: {fullName}")

    // 2. Simple identifier (single part)
    elif parts.Length = 1 then
        let name = parts.[0]

        // 2a. Try operator intrinsics (not, op_BooleanAnd, etc.)
        match tryResolveOperator name range with
        | Some (info, ty) -> IntrinsicNode (info, ty)
        | None ->

        // 2b. Try conversion intrinsics (float, int, etc.)
        match tryResolveConversion name env.Globals range with
        | Some (info, ty) -> IntrinsicNode (info, ty)
        | None ->

        // 2c. Check for unhandled operators - HARD FAIL
        if isOperatorName name then
            ErrorNode ($"Operator '{name}' missing intrinsic handler", NativeType.TError $"Missing operator: {name}")

        // 2d. Binding lookup
        else
            match tryLookupBinding name env with
            | Some binding ->
                // Check for [<Literal>] substitution
                match binding.LiteralValue with
                | Some litVal -> LiteralSubstitution (litVal, binding.Type)
                | None ->
                    // Check for union case
                    match binding.UnionCaseInfo with
                    | Some caseInfo ->
                        UnionCaseNode (name, instantiateTForall binding.Type range, caseInfo)
                    | None ->
                        // Regular binding - instantiate TForall for polymorphism
                        let actualType = instantiateTForall binding.Type range
                        BindingNode (name, actualType, binding.NodeId)
            | None ->
                ErrorNode ($"The value or constructor '{name}' is not defined.", NativeType.TError $"Undefined: {name}")

    // 3. Two-part identifier (Module.operation) - check for module intrinsics
    elif parts.Length = 2 then
        // 3a. Try module-qualified intrinsic
        match tryParseModuleQualified fullName with
        | Some (modl, op) ->
            match resolveModuleIntrinsic modl op env.Globals range with
            | Resolved (info, ty) -> IntrinsicNode (info, ty)
            | UnknownOperation msg -> ErrorNode (msg, NativeType.TError msg)
            | NotAnIntrinsic ->
                // Not an intrinsic module operation - fall through to binding lookup
                resolveBinding parts fullName env range
        | None ->
            // 3b. Not an intrinsic module prefix - just binding lookup
            resolveBinding parts fullName env range

    // 4. Longer paths - binding lookup only
    else
        resolveBinding parts fullName env range

/// Resolve a name as a binding, with member access handling for parser ambiguity
and private resolveBinding (parts: string list) (fullName: string) (env: TypeEnv) (range: SourceRange) : IdentifierResolution =
    match tryLookupBinding fullName env with
    | Some binding ->
        match binding.LiteralValue with
        | Some litVal -> LiteralSubstitution (litVal, binding.Type)
        | None ->
            match binding.UnionCaseInfo with
            | Some caseInfo ->
                UnionCaseNode (fullName, instantiateTForall binding.Type range, caseInfo)
            | None ->
                let actualType = instantiateTForall binding.Type range
                BindingNode (fullName, actualType, binding.NodeId)
    | None ->
        // PARSER AMBIGUITY: LongIdent might be member access on a local binding.
        // F# parser can produce LongIdent ["s"; "Pointer"] instead of DotGet
        // when it doesn't know if the first part is a module or a value.
        // Try: first part as binding, rest as member access.
        // TODO: Factor this into a proper nanopass for cleaner architecture.
        if parts.Length >= 2 then
            let firstPart = parts.[0]
            let restParts = parts.[1..] |> String.concat "."
            match tryLookupBinding firstPart env with
            | Some binding ->
                // Found base binding - determine member type
                let resolvedType = applySubst binding.Type
                let resultTy = resolveMemberType resolvedType restParts env range
                MemberAccessNode (binding, firstPart, restParts, resultTy)
            | None ->
                ErrorNode ($"The value or constructor '{fullName}' is not defined.", NativeType.TError $"Undefined: {fullName}")
        else
            ErrorNode ($"The value or constructor '{fullName}' is not defined.", NativeType.TError $"Undefined: {fullName}")

/// Determine the type of a member access (intrinsic string/array members or SRTP constraint)
and private resolveMemberType (baseType: NativeType) (memberName: string) (env: TypeEnv) (range: SourceRange) : NativeType =
    let isStringType ty =
        match ty with
        | NativeType.TApp(tycon, []) when tycon.Name = "string" -> true
        | _ -> false
    let isArrayType ty =
        match ty with
        | NativeType.TApp(tycon, [_]) when tycon.Name = "array" -> true
        | _ -> false

    match memberName with
    | "Pointer" when isStringType baseType ->
        NativeType.TNativePtr(NativeGlobals.Types.uint8Type)
    | "Length" when isStringType baseType ->
        env.Globals.IntType
    | "Length" when isArrayType baseType ->
        env.Globals.IntType
    | _ ->
        // General case: create HasMember constraint for SRTP
        let ty = freshTypeVar range
        addConstraint (Constraint.HasMember(baseType, memberName, ty, range)) env
        ty

//-------------------------------------------------------------------------
// Public API - Used by CheckExpressions
//-------------------------------------------------------------------------

/// Resolve an identifier and create the appropriate SemanticNode.
/// This is the UNIFIED entry point for both SynExpr.Ident and SynExpr.LongIdent.
///
/// Usage in CheckExpressions.fs:
///   | SynExpr.Ident(ident) ->
///       Identity.resolveIdentifier [ident.idText] env builder range synRange
///
///   | SynExpr.LongIdent(_, longDotId, _, _) ->
///       let parts = longDotId.LongIdent |> List.map (fun id -> id.idText)
///       Identity.resolveIdentifier parts env builder range synRange
let resolveIdentifier
    (parts: string list)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (range: SourceRange)
    (synRange: FSharp.Native.Compiler.Text.range)
    : SemanticNode =

    match resolveIdentifierCore parts env range with
    | IntrinsicNode (info, ty) ->
        builder.Create(
            SemanticKind.Intrinsic info,
            ty,
            range,
            arena = env.CurrentArena)

    | BindingNode (name, ty, nodeId) ->
        builder.Create(
            SemanticKind.VarRef(name, nodeId),
            ty,
            range,
            arena = env.CurrentArena)

    | LiteralSubstitution (litVal, ty) ->
        builder.Create(
            SemanticKind.Literal litVal,
            ty,
            range,
            arena = env.CurrentArena)

    | UnionCaseNode (_name, ty, caseInfo) ->
        // UnionCase in SemanticKind: caseName * caseIndex * payload option
        builder.Create(
            SemanticKind.UnionCase(caseInfo.CaseName, caseInfo.CaseIndex, None),
            ty,
            range,
            arena = env.CurrentArena)

    | MemberAccessNode (baseBinding, baseName, memberName, resultTy) ->
        // LongIdent parsed as member access - create base VarRef then FieldGet
        let baseNode = builder.Create(
            SemanticKind.VarRef(baseName, baseBinding.NodeId),
            baseBinding.Type,
            range,
            arena = env.CurrentArena)
        builder.Create(
            SemanticKind.FieldGet(baseNode.Id, memberName),
            resultTy,
            range,
            children = [baseNode.Id])

    | ErrorNode (msg, ty) ->
        let fullName = String.concat "." parts
        // Emit appropriate diagnostic
        if isBclReference fullName then
            addBclError fullName synRange env
        else
            addNativeError DiagnosticCodes.FS0001_GenericError synRange msg env
        builder.Create(
            SemanticKind.Error msg,
            ty,
            range)
