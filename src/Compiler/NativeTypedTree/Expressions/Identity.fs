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
module Clef.Compiler.NativeTypedTree.Expressions.Identity

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Builder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.NativeTypedTree.Expressions.Types
open Clef.Compiler.NativeTypedTree.Expressions.Intrinsics
open Clef.Compiler.NativeTypedTree.UnionFind
module NR = Clef.Compiler.NativeTypedTree.NameResolution

//-------------------------------------------------------------------------
// Identifier Resolution Result
//-------------------------------------------------------------------------

type private IdentifierResolution =
    | IntrinsicNode of IntrinsicInfo * NativeType
    | BindingNode of string * NativeType * NodeId option
    | LiteralSubstitution of NativeLiteral * NativeType
    | UnionCaseNode of string * NativeType * NR.UnionCaseInfo
    | MemberAccessNode of baseBinding: NR.ResolvedBinding * baseName: string * memberPath: string list * resultTypes: NativeType list
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
        match tryResolveConversion name range with
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
                match binding.NativeLiteral with
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
            match resolveModuleIntrinsic modl op range with
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
        match binding.NativeLiteral with
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
        // F# parser can produce LongIdent ["r"; "Length"] instead of DotGet
        // when it doesn't know if the first part is a module or a value.
        // Try: first part as binding, rest as member access.
        // TODO: Factor this into a proper nanopass for cleaner architecture.
        if parts.Length >= 2 then
            let firstPart = parts.[0]
            let restParts = parts.[1..]  // Keep as list for nested FieldGets
            match tryLookupBinding firstPart env with
            | Some binding ->
                // Found base binding - resolve member path to get types at each step
                let resolvedType = applySubst binding.Type
                let resultTypes = resolveMemberPath resolvedType restParts env range
                MemberAccessNode (binding, firstPart, restParts, resultTypes)
            | None ->
                ErrorNode ($"The value or constructor '{fullName}' is not defined.", NativeType.TError $"Undefined: {fullName}")
        else
            ErrorNode ($"The value or constructor '{fullName}' is not defined.", NativeType.TError $"Undefined: {fullName}")

/// Determine the type of a member access.
/// Delegates to Types.resolveFieldType which handles:
/// 1. Intrinsic members (string.Pointer, string.Length, array.Length)
/// 2. Record field lookup (no SRTP needed)
/// 3. SRTP constraint fallback for generic types
and private resolveMemberType (baseType: NativeType) (memberName: string) (env: TypeEnv) (range: SourceRange) : NativeType =
    Types.resolveFieldType baseType memberName env range

/// Resolve a path of member accesses, returning the type at each step.
/// For c.Person.Name with c:Contact, returns:
///   [PersonType; StringType] - types of each field access
and private resolveMemberPath (baseType: NativeType) (memberPath: string list) (env: TypeEnv) (range: SourceRange) : NativeType list =
    // Fold over the path, accumulating (currentType, typesList)
    let (_, types) =
        memberPath
        |> List.fold (fun (currentType, acc) memberName ->
            let memberType = resolveMemberType currentType memberName env range
            (memberType, acc @ [memberType])
        ) (baseType, [])
    types

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
    (synRange: Clef.Compiler.Text.range)
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

    | MemberAccessNode (baseBinding, baseName, memberPath, resultTypes) ->
        // LongIdent parsed as member access - create base VarRef then nested FieldGets
        // For c.Person.Name: creates VarRef(c), then FieldGet(c, Person), then FieldGet(_, Name)
        let baseNode = builder.Create(
            SemanticKind.VarRef(baseName, baseBinding.NodeId),
            baseBinding.Type,
            range,
            arena = env.CurrentArena)
        // Fold over member path and types to create nested FieldGets
        let (finalNode, _) =
            (memberPath, resultTypes)
            ||> List.zip
            |> List.fold (fun (currentNode: SemanticNode, _) (fieldName, fieldType) ->
                let fieldNode = builder.Create(
                    SemanticKind.FieldGet(currentNode.Id, fieldName),
                    fieldType,
                    range,
                    children = [currentNode.Id])
                (fieldNode, ())
            ) (baseNode, ())
        finalNode

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
