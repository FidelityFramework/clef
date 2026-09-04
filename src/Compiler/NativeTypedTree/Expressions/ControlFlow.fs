// Copyright (c) 2025 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Control flow expression handlers for Clef.
/// Handles: If-then-else, While, For, ForEach, Match, Try-with, Try-finally, Assert, MatchBang
module Clef.Compiler.NativeTypedTree.Expressions.ControlFlow

open Clef.Compiler.Syntax
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.NativeTypedTree.Expressions.Types

//-------------------------------------------------------------------------
// If-then-else
//-------------------------------------------------------------------------

let checkIfThenElse
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (condExpr: SynExpr)
    (thenExpr: SynExpr)
    (elseExprOpt: SynExpr option)
    (range: SourceRange)
    : SemanticNode =

    let condNode = checkExpr env builder condExpr
    let thenNode = checkExpr env builder thenExpr

    // Condition must be bool
    addConstraint (Constraint.Equals(condNode.Type, Types.boolType, range)) env

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
        addConstraint (Constraint.Equals(thenNode.Type, Types.unitType, range)) env
        builder.Create(
            SemanticKind.IfThenElse(condNode.Id, thenNode.Id, None),
            Types.unitType,
            range,
            children = [condNode.Id; thenNode.Id])

//-------------------------------------------------------------------------
// While loops
//-------------------------------------------------------------------------

let checkWhile
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (guardExpr: SynExpr)
    (bodyExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =

    let guardNode = checkExpr env builder guardExpr
    let bodyNode = checkExpr env builder bodyExpr

    // Guard must be bool
    addConstraint (Constraint.Equals(guardNode.Type, Types.boolType, range)) env

    builder.Create(
        SemanticKind.WhileLoop(guardNode.Id, bodyNode.Id),
        Types.unitType,  // While always returns unit
        range,
        children = [guardNode.Id; bodyNode.Id])

//-------------------------------------------------------------------------
// For loops
//-------------------------------------------------------------------------

let checkFor
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (ident: Ident)
    (startExpr: SynExpr)
    (direction: bool)
    (endExpr: SynExpr)
    (bodyExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =

    let startNode = checkExpr env builder startExpr
    let endNode = checkExpr env builder endExpr

    // Start and end must be int
    addConstraint (Constraint.Equals(startNode.Type, Types.intType, range)) env
    addConstraint (Constraint.Equals(endNode.Type, Types.intType, range)) env

    // A counted loop is a while loop over a mutable cell:
    //   let __for_end = <end>            (the bound is evaluated once)
    //   let mutable i = <start>
    //   while i <= __for_end do           (>= for downto)
    //       <body>
    //       i <- i + 1                    (- 1 for downto)
    // The loop variable is a real binding node, so every VarRef to it resolves, and the
    // lowering reuses the while/mutable-cell machinery instead of a dedicated for form.
    let loopVar = ident.idText
    let endName = sprintf "__for_end_%d" (NodeId.value (NodeId.fresh()))
    let endBinding = builder.Create(
        SemanticKind.Binding(endName, false, false, None),
        Types.intType,
        range,
        children = [endNode.Id])
    builder.SetParent(endNode.Id, endBinding.Id)
    let varBinding = builder.Create(
        SemanticKind.Binding(loopVar, true, false, None),
        Types.intType,
        range,
        children = [startNode.Id])
    builder.SetParent(startNode.Id, varBinding.Id)

    // Body sees the loop variable (mutability is unobservable inside the body)
    let bodyEnv = addBinding loopVar Types.intType true (Some varBinding.Id) false env
    let bodyNode = checkExpr bodyEnv builder bodyExpr

    let mkVarRef (name: string) (defId: NodeId) =
        builder.Create(SemanticKind.VarRef(name, Some defId), Types.intType, range, arena = env.CurrentArena)
    let mkOperator (opName: string) (resultTy: NativeType) =
        match Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.tryResolveOperator opName range with
        | Some (info, opTy) ->
            // Pin the operator's type variable to int so no unbound variable survives
            addConstraint (Constraint.Equals(opTy, NativeType.TFun(Types.intType, NativeType.TFun(Types.intType, resultTy)), range)) env
            builder.Create(SemanticKind.Intrinsic info, opTy, range, arena = env.CurrentArena)
        | None -> failwith ("for loop desugaring: operator intrinsic missing: " + opName)

    // Guard: i <= end (or i >= end for downto)
    let cmpNode = mkOperator (if direction then "op_LessThanOrEqual" else "op_GreaterThanOrEqual") Types.boolType
    let guardVar = mkVarRef loopVar varBinding.Id
    let guardEnd = mkVarRef endName endBinding.Id
    let guardNode = builder.Create(
        SemanticKind.Application(cmpNode.Id, [guardVar.Id; guardEnd.Id]),
        Types.boolType,
        range,
        children = [cmpNode.Id; guardVar.Id; guardEnd.Id])
    for cid in guardNode.Children do builder.SetParent(cid, guardNode.Id)

    // Step: i <- i + 1 (or i - 1 for downto)
    let stepOp = mkOperator (if direction then "op_Addition" else "op_Subtraction") Types.intType
    let stepVar = mkVarRef loopVar varBinding.Id
    let oneNode = builder.Create(
        SemanticKind.Literal (NativeLiteral.Int(1L, NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register))),
        Types.intType,
        range)
    let stepValue = builder.Create(
        SemanticKind.Application(stepOp.Id, [stepVar.Id; oneNode.Id]),
        Types.intType,
        range,
        children = [stepOp.Id; stepVar.Id; oneNode.Id])
    for cid in stepValue.Children do builder.SetParent(cid, stepValue.Id)
    let setTarget = mkVarRef loopVar varBinding.Id
    let setNode = builder.Create(
        SemanticKind.Set(setTarget.Id, stepValue.Id),
        Types.unitType,
        range,
        children = [setTarget.Id; stepValue.Id])
    for cid in setNode.Children do builder.SetParent(cid, setNode.Id)

    let loopBody = builder.Create(
        SemanticKind.Sequential [bodyNode.Id; setNode.Id],
        Types.unitType,
        range,
        children = [bodyNode.Id; setNode.Id])
    for cid in loopBody.Children do builder.SetParent(cid, loopBody.Id)
    let whileNode = builder.Create(
        SemanticKind.WhileLoop(guardNode.Id, loopBody.Id),
        Types.unitType,
        range,
        children = [guardNode.Id; loopBody.Id])
    for cid in whileNode.Children do builder.SetParent(cid, whileNode.Id)
    let result = builder.Create(
        SemanticKind.Sequential [endBinding.Id; varBinding.Id; whileNode.Id],
        Types.unitType,
        range,
        children = [endBinding.Id; varBinding.Id; whileNode.Id])
    for cid in result.Children do builder.SetParent(cid, result.Id)
    result

//-------------------------------------------------------------------------
// Try-finally
//-------------------------------------------------------------------------

let checkTryFinally
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (tryExpr: SynExpr)
    (finallyExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =

    let tryNode = checkExpr env builder tryExpr
    let finallyNode = checkExpr env builder finallyExpr
    builder.Create(
        SemanticKind.TryFinally(tryNode.Id, finallyNode.Id),
        tryNode.Type,
        range,
        children = [tryNode.Id; finallyNode.Id])


//-------------------------------------------------------------------------
// Sequential expressions
//-------------------------------------------------------------------------

let checkSequential
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (expr1: SynExpr)
    (expr2: SynExpr)
    (range: SourceRange)
    : SemanticNode =

    let node1 = checkExpr env builder expr1
    let node2 = checkExpr env builder expr2
    builder.Create(
        SemanticKind.Sequential [node1.Id; node2.Id],
        node2.Type,  // Result type is the last expression
        range,
        children = [node1.Id; node2.Id])

//-------------------------------------------------------------------------
// Match expressions
//-------------------------------------------------------------------------

/// Callback for checking match clauses
/// Now includes scrutinee NodeId to enable field extraction for record patterns
type CheckMatchClauseFn = TypeEnv -> NodeBuilder -> NodeId -> NativeType -> NativeType -> SynMatchClause -> MatchCase

let checkMatch
    (checkExpr: CheckExprFn)
    (checkMatchClause: CheckMatchClauseFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (scrutinee: SynExpr)
    (clauses: SynMatchClause list)
    (range: SourceRange)
    : SemanticNode =

    let scrutineeNode = checkExpr env builder scrutinee
    let resultTy = freshTypeVar range

    let matchCases = clauses |> List.map (fun clause ->
        checkMatchClause env builder scrutineeNode.Id scrutineeNode.Type resultTy clause)

    builder.Create(
        SemanticKind.Match(scrutineeNode.Id, matchCases),
        resultTy,
        range,
        children = scrutineeNode.Id :: (matchCases |> List.collect (fun c ->
            let guardAndBody = match c.Guard with Some g -> [g; c.Body] | None -> [c.Body]
            c.PatternBindings @ guardAndBody)))

//-------------------------------------------------------------------------
// Try-with expressions
//-------------------------------------------------------------------------

let checkTryWith
    (checkExpr: CheckExprFn)
    (checkMatchClause: CheckMatchClauseFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (tryExpr: SynExpr)
    (withCases: SynMatchClause list)
    (range: SourceRange)
    : SemanticNode =

    let tryNode = checkExpr env builder tryExpr

    // Exception handlers are like match expressions over the caught exception
    // TODO: Define proper exception type for native. Using string as placeholder.
    let exnType = Types.stringType

    // Create a synthetic match node for the handlers (create scrutinee first so we have its ID)
    let handlerScrutinee = builder.Create(
        SemanticKind.VarRef("$exn", None),
        exnType,
        range)

    // Check each exception clause with scrutinee ID for pattern binding extraction
    let cases = withCases |> List.map (checkMatchClause env builder handlerScrutinee.Id exnType tryNode.Type)

    let handlerNode = builder.Create(
        SemanticKind.Match(handlerScrutinee.Id, cases),
        tryNode.Type,
        range,
        children = handlerScrutinee.Id :: (cases |> List.collect (fun c ->
            let guardAndBody = match c.Guard with Some g -> [g; c.Body] | None -> [c.Body]
            c.PatternBindings @ guardAndBody)))

    builder.Create(
        SemanticKind.TryWith(tryNode.Id, handlerNode.Id),
        tryNode.Type,
        range,
        children = [tryNode.Id; handlerNode.Id])

//-------------------------------------------------------------------------
// ForEach loops
//-------------------------------------------------------------------------

let checkForEach
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (pat: SynPat)
    (enumExpr: SynExpr)
    (bodyExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =

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
    let loopEnv = addBinding varName varType false None false env  // Loop vars are local
    let bodyNode = checkExpr loopEnv builder bodyExpr
    builder.Create(
        SemanticKind.ForEach(varName, enumNode.Id, bodyNode.Id),
        Types.unitType,
        range,
        children = [enumNode.Id; bodyNode.Id])


//-------------------------------------------------------------------------
// Assert
//-------------------------------------------------------------------------

/// Check Assert: assert expr
let checkAssert
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (condExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let condNode = checkExpr env builder condExpr
    addConstraint (Constraint.Equals(condNode.Type, Types.boolType, range)) env
    builder.Create(
        SemanticKind.Application(condNode.Id, []),
        Types.unitType,
        range,
        children = [condNode.Id])

//-------------------------------------------------------------------------
// MatchBang (computation expression match)
//-------------------------------------------------------------------------

/// Type alias for pattern checking callback
type CheckPatternFn = TypeEnv -> SynPat -> NativeType -> SourceRange -> Pattern * (string * NativeType) list

/// Check MatchBang: match! expr with ...
let checkMatchBang
    (checkExpr: CheckExprFn)
    (checkPattern: CheckPatternFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (expr: SynExpr)
    (clauses: SynMatchClause list)
    (range: SourceRange)
    : SemanticNode =
    let scrutineeNode = checkExpr env builder expr
    let matchCases = clauses |> List.map (fun (SynMatchClause(pat, guardOpt, resultExpr, _, _, _)) ->
        let (pattern, _patBindings) = checkPattern env pat scrutineeNode.Type range
        let guardNode = guardOpt |> Option.map (checkExpr env builder)
        let bodyNode = checkExpr env builder resultExpr
        { Pattern = pattern; PatternBindings = []; Guard = guardNode |> Option.map (fun g -> g.Id); Body = bodyNode.Id })
    let resultType = if List.isEmpty matchCases then Types.unitType else freshTypeVar range
    builder.Create(
        SemanticKind.Match(scrutineeNode.Id, matchCases),
        resultType,
        range,
        children = scrutineeNode.Id :: (matchCases |> List.collect (fun mc ->
            let guardAndBody = match mc.Guard with Some gid -> [gid; mc.Body] | None -> [mc.Body]
            mc.PatternBindings @ guardAndBody)))
