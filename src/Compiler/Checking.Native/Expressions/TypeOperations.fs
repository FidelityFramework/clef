// Copyright (c) 2025 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Type operation handlers for F# Native.
/// Handles: Typed (annotation), Upcast, Downcast, TypeTest, AddressOf
module FSharp.Native.Compiler.Checking.Native.Expressions.TypeOperations

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.UnionFind
open FSharp.Native.Compiler.Checking.Native.SemanticGraph
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
    builder.Create(
        SemanticKind.TypeAnnotation(innerNode.Id, annotatedTy),
        annotatedTy,
        range,
        children = [innerNode.Id])

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
    let pointerType =
        if isByref then NativeType.TByref(innerNode.Type, ByrefKind.InOut)
        else NativeType.TNativePtr innerNode.Type
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
