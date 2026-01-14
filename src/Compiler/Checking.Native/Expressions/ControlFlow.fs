// Copyright (c) 2025 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Control flow expression handlers for F# Native.
/// Handles: If-then-else, While, For, Match, Try-with, Try-finally
module FSharp.Native.Compiler.Checking.Native.Expressions.ControlFlow

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.UnionFind
open FSharp.Native.Compiler.Checking.Native.SemanticGraph
open FSharp.Native.Compiler.Checking.Native.Expressions.Types

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
    addConstraint (Constraint.Equals(guardNode.Type, env.Globals.BoolType, range)) env

    builder.Create(
        SemanticKind.WhileLoop(guardNode.Id, bodyNode.Id),
        env.Globals.UnitType,  // While always returns unit
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
type CheckMatchClauseFn = TypeEnv -> NodeBuilder -> NativeType -> NativeType -> SynMatchClause -> MatchCase

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
        checkMatchClause env builder scrutineeNode.Type resultTy clause)

    builder.Create(
        SemanticKind.Match(scrutineeNode.Id, matchCases),
        resultTy,
        range,
        children = scrutineeNode.Id :: (matchCases |> List.map (fun c -> c.Body)))

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
    let loopEnv = addBinding varName varType false None env
    let bodyNode = checkExpr loopEnv builder bodyExpr
    builder.Create(
        SemanticKind.ForEach(varName, enumNode.Id, bodyNode.Id),
        env.Globals.UnitType,
        range,
        children = [enumNode.Id; bodyNode.Id])
