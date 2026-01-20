// Copyright (c) 2025 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Type operation handlers for F# Native.
/// Handles: Typed (annotation), Upcast, Downcast, TypeTest, AddressOf
module FSharp.Native.Compiler.Checking.Native.Expressions.TypeOperations

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.UnionFind
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph
open FSharp.Native.Compiler.Checking.Native.Expressions.Types

//-------------------------------------------------------------------------
// Callback Types
//-------------------------------------------------------------------------

/// Callback for checking expressions
type CheckExprFn = TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode

/// Callback for checking SynType
type CheckSynTypeFn = TypeEnv -> SynType -> NativeType

//-------------------------------------------------------------------------
// Type Annotation
//-------------------------------------------------------------------------

let checkTyped
    (checkExpr: CheckExprFn)
    (checkSynType: CheckSynTypeFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (innerExpr: SynExpr)
    (synType: SynType)
    (range: SourceRange)
    : SemanticNode =

    let innerNode = checkExpr env builder innerExpr
    let annotatedTy = checkSynType env synType
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
    (checkSynType: CheckSynTypeFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (innerExpr: SynExpr)
    (targetType: SynType)
    (range: SourceRange)
    : SemanticNode =

    let innerNode = checkExpr env builder innerExpr
    let targetTy = checkSynType env targetType
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
    (checkSynType: CheckSynTypeFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (innerExpr: SynExpr)
    (targetType: SynType)
    (range: SourceRange)
    : SemanticNode =

    let innerNode = checkExpr env builder innerExpr
    let targetTy = checkSynType env targetType
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
    (checkSynType: CheckSynTypeFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (innerExpr: SynExpr)
    (targetType: SynType)
    (range: SourceRange)
    : SemanticNode =

    let innerNode = checkExpr env builder innerExpr
    let targetTy = checkSynType env targetType
    builder.Create(
        SemanticKind.TypeTest(innerNode.Id, targetTy),
        env.Globals.BoolType,
        range,
        children = [innerNode.Id])
