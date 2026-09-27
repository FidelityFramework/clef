// Copyright (c) 2025 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Type operation handlers for Clef.
/// Handles: Typed (annotation), Upcast, Downcast, TypeTest, AddressOf, Quote
module Clef.Compiler.NativeTypedTree.Expressions.TypeOperations

open Clef.Compiler.Syntax
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.NativeTypedTree.Expressions.Types

//-------------------------------------------------------------------------
// Callback Types
//-------------------------------------------------------------------------

/// Callback for checking expressions
type CheckExprFn = TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode

/// A type-directed cast or test (`:>`, `:?>`, `:?`, `upcast`, `downcast`) has no native graph
/// form: there is no subtyping and no run-time type information to test. The operand is checked
/// for its own diagnostics; the cast is refused at its range, never carried as an unrelated
/// Upcast, Downcast or TypeTest node that nothing below can realize.
let private refuseCast (builder: NodeBuilder) (env: TypeEnv) (form: string) (innerNode: SemanticNode) (range: SourceRange) : SemanticNode =
    let message = $"CCS source checking did not settle an elaboration for this {form}: type casts and type tests have no native graph form."
    addDiagnostic {
        Severity = NativeDiagnosticSeverity.Error
        Code = DiagnosticCodes.CCS8401_UnsupportedConstruct
        Message = message
        Range = range
        RelatedNodes = [innerNode.Id]
        Reachability = ReachabilityContext.Unknown
    } env
    builder.Create(SemanticKind.Error message, NativeType.TError message, range, children = [innerNode.Id])

//-------------------------------------------------------------------------
// Type Annotation
//-------------------------------------------------------------------------

let checkTyped
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (innerExpr: SynExpr)
    (synType: SynType)
    (range: SourceRange)
    : SemanticNode =

    let annotatedTy = resolveSynType env synType
    let rec isRecordLiteral = function
        | SynExpr.Record _ -> true
        | SynExpr.Paren(inner, _, _, _) | SynExpr.DebugPoint(_, _, inner) -> isRecordLiteral inner
        | _ -> false
    let innerEnv =
        { env with ExpectedRecordType = if isRecordLiteral innerExpr then Some annotatedTy else None }
    let innerNode = checkExpr innerEnv builder innerExpr
    // Add equality constraint
    addConstraint (Constraint.Equals(innerNode.Type, annotatedTy, range)) env
    let node = builder.Create(
        SemanticKind.TypeAnnotation(innerNode.Id, annotatedTy),
        annotatedTy,
        range,
        children = [innerNode.Id])
    // PRD-13: Set bidirectional parent link for scope chain
    builder.SetParent(innerNode.Id, node.Id)
    node

//-------------------------------------------------------------------------
// AddressOf: &expr or &&expr
//-------------------------------------------------------------------------

let checkAddressOf
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (isByref: bool)
    (innerExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =

    let innerNode = checkExpr env builder innerExpr

    // Check if inner expression is already a byref type.
    // In F#, &byrefExpr means "pass this byref", not "create byref of byref".
    // This is the idiomatic pattern: let foo (x: byref<T>) = bar &x
    // where bar also takes byref<T>. We don't create nested byrefs.
    let innerTy = applySubst innerNode.Type
    let isAlreadyByref =
        match innerTy with
        | NativeType.TByref _ -> true
        | NativeType.TApp(tc, _) when tc.Name = "byref" || tc.Name = "inref" || tc.Name = "outref" -> true
        | _ -> false

    let pointerType =
        if isAlreadyByref then
            // Already a byref - just pass through, don't create nested byref
            innerTy
        elif isByref then
            NativeType.TByref(innerNode.Type, ByrefKind.InOut)
        else
            NativeType.TNativePtr innerNode.Type

    builder.Create(
        SemanticKind.AddressOf(innerNode.Id, isByref),
        pointerType,
        range,
        children = [innerNode.Id])

//-------------------------------------------------------------------------
// Upcast: expr :> type
//-------------------------------------------------------------------------

let checkUpcast
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (innerExpr: SynExpr)
    (targetType: SynType)
    (range: SourceRange)
    : SemanticNode =

    let innerNode = checkExpr env builder innerExpr
    let _targetTy = resolveSynType env targetType
    refuseCast builder env "upcast ':>'" innerNode range

//-------------------------------------------------------------------------
// InferredUpcast: upcast expr
//-------------------------------------------------------------------------

let checkInferredUpcast
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (innerExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =

    let innerNode = checkExpr env builder innerExpr
    refuseCast builder env "'upcast'" innerNode range

//-------------------------------------------------------------------------
// Downcast: expr :?> type
//-------------------------------------------------------------------------

let checkDowncast
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (innerExpr: SynExpr)
    (targetType: SynType)
    (range: SourceRange)
    : SemanticNode =

    let innerNode = checkExpr env builder innerExpr
    let _targetTy = resolveSynType env targetType
    refuseCast builder env "downcast ':?>'" innerNode range

//-------------------------------------------------------------------------
// InferredDowncast: downcast expr
//-------------------------------------------------------------------------

let checkInferredDowncast
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (innerExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =

    let innerNode = checkExpr env builder innerExpr
    refuseCast builder env "'downcast'" innerNode range

//-------------------------------------------------------------------------
// TypeTest: expr :? type
//-------------------------------------------------------------------------

let checkTypeTest
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (innerExpr: SynExpr)
    (targetType: SynType)
    (range: SourceRange)
    : SemanticNode =

    let innerNode = checkExpr env builder innerExpr
    let _targetTy = resolveSynType env targetType
    refuseCast builder env "type test ':?'" innerNode range


//-------------------------------------------------------------------------
// Quotations
//-------------------------------------------------------------------------

/// Check Quote: <@ expr @> or <@@ expr @@>
let checkQuote
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (isRaw: bool)
    (quotedExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let innerNode = checkExpr env builder quotedExpr
    let quotedType =
        if isRaw then Types.mkExprType (freshTypeVar range)
        else Types.mkExprType innerNode.Type
    builder.Create(
        SemanticKind.Quote(innerNode.Id, not isRaw),
        quotedType,
        range,
        children = [innerNode.Id])
