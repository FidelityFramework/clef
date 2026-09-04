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

    let innerNode = checkExpr env builder innerExpr
    let annotatedTy = resolveSynType env synType
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
    let targetTy = resolveSynType env targetType
    builder.Create(
        SemanticKind.Upcast(innerNode.Id, targetTy),
        targetTy,
        range,
        children = [innerNode.Id])

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
    let targetTy = freshTypeVar range
    builder.Create(
        SemanticKind.Upcast(innerNode.Id, targetTy),
        targetTy,
        range,
        children = [innerNode.Id])

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
    let targetTy = resolveSynType env targetType
    builder.Create(
        SemanticKind.Downcast(innerNode.Id, targetTy),
        targetTy,
        range,
        children = [innerNode.Id])

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
    let targetTy = freshTypeVar range
    builder.Create(
        SemanticKind.Downcast(innerNode.Id, targetTy),
        targetTy,
        range,
        children = [innerNode.Id])

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
    let targetTy = resolveSynType env targetType
    builder.Create(
        SemanticKind.TypeTest(innerNode.Id, targetTy),
        Types.boolType,
        range,
        children = [innerNode.Id])


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
