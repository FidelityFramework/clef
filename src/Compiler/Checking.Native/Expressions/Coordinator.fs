// Copyright (c) 2025 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Expression type checking coordinator for F# Native.
/// Thin dispatcher that routes SynExpr cases to handler modules.
/// This module provides the entry point for expression checking.
module FSharp.Native.Compiler.Checking.Native.Expressions.Coordinator

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Text
open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.NativeGlobals
open FSharp.Native.Compiler.Checking.Native.UnionFind
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph
open FSharp.Native.Compiler.Checking.Native.NameResolution

// Import handler modules
open FSharp.Native.Compiler.Checking.Native.Expressions.Types
open FSharp.Native.Compiler.Checking.Native.Expressions.Literals
open FSharp.Native.Compiler.Checking.Native.Expressions.Identity
open FSharp.Native.Compiler.Checking.Native.Expressions.Intrinsics
open FSharp.Native.Compiler.Checking.Native.Expressions.Applications
open FSharp.Native.Compiler.Checking.Native.Expressions.Bindings
open FSharp.Native.Compiler.Checking.Native.Expressions.Collections
open FSharp.Native.Compiler.Checking.Native.Expressions.ControlFlow
open FSharp.Native.Compiler.Checking.Native.Expressions.TypeOperations
open FSharp.Native.Compiler.Checking.Native.Expressions.Patterns
open FSharp.Native.Compiler.Checking.Native.Expressions.SynTypes

//-------------------------------------------------------------------------
// Main Expression Checker - Entry Point
//-------------------------------------------------------------------------

/// Main expression checker. Routes SynExpr to appropriate handlers.
let rec checkExpr (env: TypeEnv) (builder: NodeBuilder) (syn: SynExpr) : SemanticNode =
    let range = rangeToSourceRange syn.Range

    match syn with
    //---------------------------------------------------------------------
    // Literals
    //---------------------------------------------------------------------
    | SynExpr.Const(constant, _) ->
        let ty = Literals.typeOfConst env.Globals constant
        let litVal = Literals.constToLiteral constant
        builder.Create(SemanticKind.Literal litVal, ty, range)

    //---------------------------------------------------------------------
    // Parenthesized expressions (transparent)
    //---------------------------------------------------------------------
    | SynExpr.Paren(innerExpr, _, _, _) ->
        checkExpr env builder innerExpr

    //---------------------------------------------------------------------
    // Variable references (includes intrinsic dispatch)
    //---------------------------------------------------------------------
    | SynExpr.Ident(ident) ->
        Identity.resolveIdentifier [ident.idText] env builder range ident.idRange

    | SynExpr.LongIdent(_, longDotId, _, _) ->
        let parts = longDotId.LongIdent |> List.map (fun id -> id.idText)
        Identity.resolveIdentifier parts env builder range syn.Range

    //---------------------------------------------------------------------
    // Type annotations
    //---------------------------------------------------------------------
    | SynExpr.Typed(innerExpr, synType, _) ->
        TypeOperations.checkTyped checkExpr checkSynType env builder innerExpr synType range

    //---------------------------------------------------------------------
    // Tuples
    //---------------------------------------------------------------------
    | SynExpr.Tuple(isStruct, exprs, _, _) ->
        Collections.checkTuple checkExpr env builder isStruct exprs range

    //---------------------------------------------------------------------
    // F# 6 dotless indexer syntax: expr[index]
    //---------------------------------------------------------------------
    | SynExpr.App(_, _, objExpr, SynExpr.ArrayOrListComputed(false, indexExpr, _), _) ->
        checkDotlessIndexGet checkExpr env builder objExpr indexExpr range

    //---------------------------------------------------------------------
    // Sequence expression: seq { ... }
    // PRD-15: Parser produces App(Ident("seq"), ComputationExpr(false, body))
    // The F# spec says seq expressions are "directly elaborated" - not via builder lookup
    //---------------------------------------------------------------------
    | SynExpr.App(_, _, SynExpr.Ident(ident), SynExpr.ComputationExpr(_, compExpr, _), _)
        when ident.idText = "seq" ->
        checkSeq checkExpr env builder compExpr range

    //---------------------------------------------------------------------
    // Function application
    //---------------------------------------------------------------------
    | SynExpr.App(_, _isInfix, funcExpr, argExpr, _) ->
        Applications.checkApp checkExpr env builder funcExpr argExpr syn.Range range

    //---------------------------------------------------------------------
    // Lambda expressions
    //---------------------------------------------------------------------
    | SynExpr.Lambda(_, _, args, bodyExpr, _, _, _) ->
        Applications.checkLambda checkExpr (Bindings.extractLambdaParams checkSynType) env builder args bodyExpr range

    //---------------------------------------------------------------------
    // Let bindings
    //---------------------------------------------------------------------
    | SynExpr.LetOrUse(letOrUse) ->
        Bindings.checkLetOrUse checkExpr checkSynType env builder letOrUse range

    //---------------------------------------------------------------------
    // Sequential expressions
    //---------------------------------------------------------------------
    | SynExpr.Sequential(_, _, expr1, expr2, _, _) ->
        ControlFlow.checkSequential checkExpr env builder expr1 expr2 range

    //---------------------------------------------------------------------
    // If-then-else
    //---------------------------------------------------------------------
    | SynExpr.IfThenElse(condExpr, thenExpr, elseExprOpt, _, _, _, _) ->
        ControlFlow.checkIfThenElse checkExpr env builder condExpr thenExpr elseExprOpt range

    //---------------------------------------------------------------------
    // While loops
    //---------------------------------------------------------------------
    | SynExpr.While(_, guardExpr, bodyExpr, _) ->
        ControlFlow.checkWhile checkExpr env builder guardExpr bodyExpr range

    //---------------------------------------------------------------------
    // For loops
    //---------------------------------------------------------------------
    | SynExpr.For(_, _, ident, _, startExpr, direction, endExpr, bodyExpr, _) ->
        ControlFlow.checkFor checkExpr env builder ident startExpr direction endExpr bodyExpr range

    //---------------------------------------------------------------------
    // Match expressions
    //---------------------------------------------------------------------
    | SynExpr.Match(_, scrutinee, clauses, _, _) ->
        ControlFlow.checkMatch checkExpr checkMatchClause env builder scrutinee clauses range

    //---------------------------------------------------------------------
    // Record expressions
    //---------------------------------------------------------------------
    | SynExpr.Record(_, copyInfo, fields, recordRange) ->
        Collections.checkRecord checkExpr env builder copyInfo fields recordRange range

    //---------------------------------------------------------------------
    // Array/list expressions
    //---------------------------------------------------------------------
    | SynExpr.ArrayOrList(isArray, exprs, _) ->
        Collections.checkArrayOrList checkExpr env builder isArray exprs range

    //---------------------------------------------------------------------
    // Try-with expressions
    //---------------------------------------------------------------------
    | SynExpr.TryWith(tryExpr, withCases, _, _, _, _) ->
        ControlFlow.checkTryWith checkExpr checkMatchClause env builder tryExpr withCases range

    //---------------------------------------------------------------------
    // Try-finally expressions
    //---------------------------------------------------------------------
    | SynExpr.TryFinally(tryExpr, finallyExpr, _, _, _, _) ->
        ControlFlow.checkTryFinally checkExpr env builder tryExpr finallyExpr range

    //---------------------------------------------------------------------
    // Field access
    //---------------------------------------------------------------------
    | SynExpr.DotGet(expr, _, longDotId, _) ->
        checkDotGet checkExpr env builder expr longDotId range

    //---------------------------------------------------------------------
    // Assignment - F# 6 dotless indexer set: expr[index] <- value
    //---------------------------------------------------------------------
    | SynExpr.Set(SynExpr.App(_, _, objExpr, SynExpr.ArrayOrListComputed(false, indexExpr, _), _), valueExpr, _) ->
        checkDotlessIndexSet checkExpr env builder objExpr indexExpr valueExpr range

    //---------------------------------------------------------------------
    // Assignment - General case
    //---------------------------------------------------------------------
    | SynExpr.Set(targetExpr, valueExpr, _) ->
        checkSet checkExpr env builder targetExpr valueExpr range

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
        checkQuote checkExpr env builder isRaw quotedExpr range

    //---------------------------------------------------------------------
    // Interpolated strings
    //---------------------------------------------------------------------
    | SynExpr.InterpolatedString(contents, _synStringKind, synRange) ->
        checkInterpolatedString checkExpr env builder contents synRange range

    //---------------------------------------------------------------------
    // AddressOf: &expr or &&expr
    //---------------------------------------------------------------------
    | SynExpr.AddressOf(isByref, innerExpr, _, _) ->
        TypeOperations.checkAddressOf checkExpr env builder isByref innerExpr range

    //---------------------------------------------------------------------
    // TypeApp: expr<type1, type2, ...>
    //---------------------------------------------------------------------
    | SynExpr.TypeApp(funcExpr, _, typeArgs, _, _, _, _) ->
        Applications.checkTypeApp checkExpr checkSynType env builder funcExpr typeArgs syn.Range range

    //---------------------------------------------------------------------
    // ForEach: for x in collection do body
    //---------------------------------------------------------------------
    | SynExpr.ForEach(_, _, _, _, pat, enumExpr, bodyExpr, _) ->
        ControlFlow.checkForEach checkExpr env builder pat enumExpr bodyExpr range

    //---------------------------------------------------------------------
    // TraitCall: SRTP member invocation
    //---------------------------------------------------------------------
    | SynExpr.TraitCall(supportTys, memberSig, argExpr, _) ->
        checkTraitCall checkExpr checkSynType env builder supportTys memberSig argExpr range

    //---------------------------------------------------------------------
    // Upcast: expr :> type
    //---------------------------------------------------------------------
    | SynExpr.Upcast(innerExpr, targetType, _) ->
        TypeOperations.checkUpcast checkExpr checkSynType env builder innerExpr targetType range

    //---------------------------------------------------------------------
    // InferredUpcast: upcast expr
    //---------------------------------------------------------------------
    | SynExpr.InferredUpcast(innerExpr, _) ->
        TypeOperations.checkInferredUpcast checkExpr env builder innerExpr range

    //---------------------------------------------------------------------
    // Downcast: expr :?> type
    //---------------------------------------------------------------------
    | SynExpr.Downcast(innerExpr, targetType, _) ->
        TypeOperations.checkDowncast checkExpr checkSynType env builder innerExpr targetType range

    //---------------------------------------------------------------------
    // InferredDowncast: downcast expr
    //---------------------------------------------------------------------
    | SynExpr.InferredDowncast(innerExpr, _) ->
        TypeOperations.checkInferredDowncast checkExpr env builder innerExpr range

    //---------------------------------------------------------------------
    // TypeTest: expr :? type
    //---------------------------------------------------------------------
    | SynExpr.TypeTest(innerExpr, targetType, _) ->
        TypeOperations.checkTypeTest checkExpr checkSynType env builder innerExpr targetType range

    //---------------------------------------------------------------------
    // DotIndexedGet: expr.[index]
    //---------------------------------------------------------------------
    | SynExpr.DotIndexedGet(objExpr, indexArgs, _, _) ->
        checkDotIndexedGet checkExpr env builder objExpr indexArgs range

    //---------------------------------------------------------------------
    // DotIndexedSet: expr.[index] <- value
    //---------------------------------------------------------------------
    | SynExpr.DotIndexedSet(objExpr, indexArgs, valueExpr, _, _, _) ->
        checkDotIndexedSet checkExpr env builder objExpr indexArgs valueExpr range

    //---------------------------------------------------------------------
    // DotSet: expr.field <- value
    //---------------------------------------------------------------------
    | SynExpr.DotSet(objExpr, SynLongIdent(longId, _, _), valueExpr, _) ->
        checkDotSet checkExpr env builder objExpr longId valueExpr range

    //---------------------------------------------------------------------
    // LongIdentSet: Module.value <- expr
    //---------------------------------------------------------------------
    | SynExpr.LongIdentSet(SynLongIdent(longId, _, _), valueExpr, _) ->
        checkLongIdentSet checkExpr env builder longId valueExpr range

    //---------------------------------------------------------------------
    // Lazy: lazy expr
    //---------------------------------------------------------------------
    | SynExpr.Lazy(innerExpr, _) ->
        checkLazy checkExpr env builder innerExpr range

    //---------------------------------------------------------------------
    // Assert: assert expr
    //---------------------------------------------------------------------
    | SynExpr.Assert(condExpr, _) ->
        checkAssert checkExpr env builder condExpr range

    //---------------------------------------------------------------------
    // New: new Type(args)
    //---------------------------------------------------------------------
    | SynExpr.New(_, synType, argExpr, _) ->
        checkNew checkExpr checkSynType env builder synType argExpr range

    //---------------------------------------------------------------------
    // ObjExpr: { new Interface with ... }
    //---------------------------------------------------------------------
    | SynExpr.ObjExpr(objType, argOption, _, bindings, members, extraImpls, _, _) ->
        checkObjExpr checkExpr checkSynType env builder objType argOption bindings members extraImpls range

    //---------------------------------------------------------------------
    // AnonRecd: {| field = value |}
    //---------------------------------------------------------------------
    | SynExpr.AnonRecd(isStruct, copyInfo, recordFields, _, _trivia) ->
        Collections.checkAnonRecd checkExpr env builder isStruct copyInfo recordFields range

    //---------------------------------------------------------------------
    // MatchLambda: function | pat -> expr
    //---------------------------------------------------------------------
    | SynExpr.MatchLambda(_isExnMatch, _keywordRange, clauses, _matchSeqPoint, _) ->
        Collections.checkMatchLambda checkExpr checkMatchClause env builder clauses range

    //---------------------------------------------------------------------
    // ArrayOrListComputed: [| for x in xs -> f x |] or [ for x in xs -> f x ]
    //---------------------------------------------------------------------
    | SynExpr.ArrayOrListComputed(isArray, compExpr, _) ->
        Collections.checkArrayOrListComputed checkExpr env builder isArray compExpr range

    //---------------------------------------------------------------------
    // ComputationExpr: async { ... }, seq { ... }, etc.
    //---------------------------------------------------------------------
    // ComputationExpr: seq { ... } or other { ... }
    // PRD-15: Built-in seq expressions use hasSeqBuilder=true
    //---------------------------------------------------------------------
    | SynExpr.ComputationExpr(hasSeqBuilder, compExpr, _) ->
        if hasSeqBuilder then
            // seq { ... } - built-in sequence expression
            checkSeq checkExpr env builder compExpr range
        else
            // Other computation expressions (async, task, etc.) - treat as passthrough for now
            let compNode = checkExpr env builder compExpr
            builder.Create(
                SemanticKind.Sequential [compNode.Id],
                compNode.Type,
                range,
                children = [compNode.Id])

    //---------------------------------------------------------------------
    // YieldOrReturn: yield expr or return expr
    // PRD-15: In seq context, yield creates a Yield node
    //---------------------------------------------------------------------
    | SynExpr.YieldOrReturn((isYield, _isReturn), expr, _, _trivia) ->
        if isYield && env.EnclosingSeqExpr.IsSome then
            checkYield checkExpr env builder expr range
        else
            // return expr or yield outside seq - just evaluate the expression
            checkExpr env builder expr

    //---------------------------------------------------------------------
    // YieldOrReturnFrom: yield! expr or return! expr
    // PRD-15: In seq context, yield! creates a YieldBang node
    //---------------------------------------------------------------------
    | SynExpr.YieldOrReturnFrom((isYield, _isReturn), expr, _, _trivia) ->
        if isYield && env.EnclosingSeqExpr.IsSome then
            checkYieldBang checkExpr env builder expr range
        else
            // return! expr or yield! outside seq - just evaluate the expression
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
        checkMatchBang checkExpr checkPattern env builder expr clauses range

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
            SemanticKind.AddressOf(innerNode.Id, true),
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
        // Create PatternBinding for the implicit _ parameter
        let paramNode = builder.Create(
            SemanticKind.PatternBinding("_"),
            argType,
            range)
        // DotLambda (_.Property) - synthetic lambda, no captures from outer scope
        // Children includes parameter PatternBinding + body for proper traversal
        // Inherit enclosing function context for nested function qualification
        let lambdaNode = builder.Create(
            SemanticKind.Lambda([("_", argType, paramNode.Id)], innerNode.Id, [], env.EnclosingFunction, LambdaContext.RegularClosure),
            NativeType.TFun(argType, innerNode.Type),
            range,
            children = [paramNode.Id; innerNode.Id])
        // Architectural fix (January 2026): Mark Lambda body as SeparateFunction
        // DotLambda is synthetic with no captures
        builder.SetEmissionStrategy(innerNode.Id, EmissionStrategy.SeparateFunction 0)
        lambdaNode

    //---------------------------------------------------------------------
    // DotNamedIndexedPropertySet: obj.Prop[idx] <- value
    //---------------------------------------------------------------------
    | SynExpr.DotNamedIndexedPropertySet(objExpr, SynLongIdent(longId, _, _), indexExpr, valueExpr, _) ->
        checkDotNamedIndexedPropertySet checkExpr env builder objExpr longId indexExpr valueExpr range

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
            SemanticKind.Application(exprNode.Id, []),
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
// SynType Checker
//-------------------------------------------------------------------------

/// Check a SynType and convert to NativeType
and checkSynType (env: TypeEnv) (synType: SynType) : NativeType =
    SynTypes.checkSynType env synType

//-------------------------------------------------------------------------
// Pattern Checker
//-------------------------------------------------------------------------

/// Check a pattern and return bindings
and checkPattern (env: TypeEnv) (pat: SynPat) (expectedTy: NativeType) (range: SourceRange) : Pattern * (string * NativeType) list =
    Patterns.checkPattern checkSynType env pat expectedTy range

//-------------------------------------------------------------------------
// Match Clause Checker
//-------------------------------------------------------------------------

/// Check a match clause
and checkMatchClause (env: TypeEnv) (builder: NodeBuilder) (scrutineeTy: NativeType) (resultTy: NativeType) (clause: SynMatchClause) : MatchCase =
    Bindings.checkMatchClause checkExpr checkPattern env builder scrutineeTy resultTy clause

//-------------------------------------------------------------------------
// Inline Helper Functions (simple cases not worth extracting)
//-------------------------------------------------------------------------

/// Check dotless indexer get: expr[index]
and checkDotlessIndexGet (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (objExpr: SynExpr) (indexExpr: SynExpr) (range: SourceRange) : SemanticNode =
    let objNode = checkExpr env builder objExpr
    let indexNodes =
        match indexExpr with
        | SynExpr.Tuple(_, exprs, _, _) -> exprs |> List.map (checkExpr env builder)
        | _ -> [checkExpr env builder indexExpr]
    
    match indexNodes with
    | [single] ->
        addConstraint (Constraint.Equals(single.Type, env.Globals.IntType, range)) env
    | _ -> ()
    
    let indexNodeId =
        match indexNodes with
        | [single] -> single.Id
        | multiple ->
            let multipleNodeIds = multiple |> List.map (fun n -> n.Id)
            let multipleNodeTypes = multiple |> List.map (fun n -> n.Type)
            let tupleNode = builder.Create(
                SemanticKind.TupleExpr(multipleNodeIds),
                NativeType.TTuple(multipleNodeTypes, false),
                range,
                children = multipleNodeIds)
            tupleNode.Id
    
    let isStringType ty =
        match ty with
        | NativeType.TApp(tc, []) when tc.Name = "string" -> true
        | _ -> false
    let elementType =
        let objType = applySubst objNode.Type
        match objType with
        | NativeType.TApp(tc, [elemType]) when tc.Name = "array" -> elemType
        | _ when isStringType objType -> env.Globals.CharType
        | NativeType.TVar _ ->
            let elemType = freshTypeVar range
            addConstraint (Constraint.Equals(objType, mkArrayType elemType, range)) env
            elemType
        | _ ->
            let resultType = freshTypeVar range
            addConstraint (Constraint.HasMember(objType, "Item", resultType, range)) env
            resultType
    
    let allChildNodeIds = objNode.Id :: (indexNodes |> List.map (fun n -> n.Id))
    builder.Create(
        SemanticKind.IndexGet(objNode.Id, indexNodeId),
        elementType,
        range,
        children = allChildNodeIds)

/// Check dotless indexer set: expr[index] <- value
and checkDotlessIndexSet (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (objExpr: SynExpr) (indexExpr: SynExpr) (valueExpr: SynExpr) (range: SourceRange) : SemanticNode =
    let objNode = checkExpr env builder objExpr
    let valueNode = checkExpr env builder valueExpr
    let indexNodes =
        match indexExpr with
        | SynExpr.Tuple(_, exprs, _, _) -> exprs |> List.map (checkExpr env builder)
        | _ -> [checkExpr env builder indexExpr]
    
    match indexNodes with
    | [single] ->
        addConstraint (Constraint.Equals(single.Type, env.Globals.IntType, range)) env
    | _ -> ()
    
    let indexNodeId =
        match indexNodes with
        | [single] -> single.Id
        | multiple ->
            let multipleNodeIds = multiple |> List.map (fun n -> n.Id)
            let multipleNodeTypes = multiple |> List.map (fun n -> n.Type)
            let tupleNode = builder.Create(
                SemanticKind.TupleExpr(multipleNodeIds),
                NativeType.TTuple(multipleNodeTypes, false),
                range,
                children = multipleNodeIds)
            tupleNode.Id
    
    let isStringType ty =
        match ty with
        | NativeType.TApp(tc, []) when tc.Name = "string" -> true
        | _ -> false
    let elementType =
        let objType = applySubst objNode.Type
        match objType with
        | NativeType.TApp(tc, [elemType]) when tc.Name = "array" -> elemType
        | _ when isStringType objType -> env.Globals.CharType
        | NativeType.TVar _ ->
            let elemType = freshTypeVar range
            addConstraint (Constraint.Equals(objType, mkArrayType elemType, range)) env
            elemType
        | _ ->
            let resultType = freshTypeVar range
            addConstraint (Constraint.HasMember(objType, "Item", resultType, range)) env
            resultType
    
    addConstraint (Constraint.Equals(valueNode.Type, elementType, range)) env
    
    let allChildNodeIds = objNode.Id :: (indexNodes |> List.map (fun n -> n.Id)) @ [valueNode.Id]
    builder.Create(
        SemanticKind.IndexSet(objNode.Id, indexNodeId, valueNode.Id),
        env.Globals.UnitType,
        range,
        children = allChildNodeIds)

/// Check DotGet: expr.field
and checkDotGet (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (expr: SynExpr) (longDotId: SynLongIdent) (range: SourceRange) : SemanticNode =
    let exprNode = checkExpr env builder expr
    let fieldName = longDotId.LongIdent |> List.map (fun id -> id.idText) |> String.concat "."
    
    let resolvedType = applySubst exprNode.Type
    let isStringType ty =
        match ty with
        | NativeType.TApp(tycon, []) when tycon.Name = "string" -> true
        | _ -> false
    let isArrayType ty =
        match ty with
        | NativeType.TApp(tycon, [_]) when tycon.Name = "array" -> true
        | _ -> false
    
    let resultTy =
        match fieldName with
        | "Pointer" when isStringType resolvedType ->
            NativeType.TNativePtr(Types.uint8Type)
        | "Length" when isStringType resolvedType ->
            env.Globals.IntType
        | "Length" when isArrayType resolvedType ->
            env.Globals.IntType
        | _ ->
            let ty = freshTypeVar range
            addConstraint (Constraint.HasMember(exprNode.Type, fieldName, ty, range)) env
            ty
    
    builder.Create(
        SemanticKind.FieldGet(exprNode.Id, fieldName),
        resultTy,
        range,
        children = [exprNode.Id])

/// Check Set: target <- value
and checkSet (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (targetExpr: SynExpr) (valueExpr: SynExpr) (range: SourceRange) : SemanticNode =
    let targetNode = checkExpr env builder targetExpr
    let valueNode = checkExpr env builder valueExpr
    addConstraint (Constraint.Equals(targetNode.Type, valueNode.Type, range)) env
    builder.Create(
        SemanticKind.Set(targetNode.Id, valueNode.Id),
        env.Globals.UnitType,
        range,
        children = [targetNode.Id; valueNode.Id])

/// Check Quote: <@ expr @> or <@@ expr @@>
and checkQuote (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (isRaw: bool) (quotedExpr: SynExpr) (range: SourceRange) : SemanticNode =
    let innerNode = checkExpr env builder quotedExpr
    let quotedType =
        if isRaw then mkExprType (freshTypeVar range)
        else mkExprType innerNode.Type
    builder.Create(
        SemanticKind.Quote(innerNode.Id, not isRaw),
        quotedType,
        range,
        children = [innerNode.Id])

/// Check InterpolatedString
and checkInterpolatedString (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (contents: SynInterpolatedStringPart list) (synRange: range) (range: SourceRange) : SemanticNode =
    let partExprs =
        contents |> List.choose (fun part ->
            match part with
            | SynInterpolatedStringPart.String(value, partRange) ->
                if System.String.IsNullOrEmpty(value) then None
                else Some (SynExpr.Const(SynConst.String(value, SynStringKind.Regular, partRange), partRange))
            | SynInterpolatedStringPart.FillExpr(fillExpr, _qualifiers) ->
                Some fillExpr)
    
    match partExprs with
    | [] ->
        builder.Create(
            SemanticKind.Literal(LiteralValue.String ""),
            env.Globals.StringType,
            range)
    | [single] ->
        checkExpr env builder single
    | first :: rest ->
        let concat2Ident =
            SynExpr.LongIdent(
                false,
                SynLongIdent([Ident("String", synRange); Ident("concat2", synRange)], [synRange], [None; None]),
                None,
                synRange)
        let resultExpr =
            rest |> List.fold (fun accExpr nextExpr ->
                let app1 = SynExpr.App(ExprAtomicFlag.NonAtomic, false, concat2Ident, accExpr, synRange)
                SynExpr.App(ExprAtomicFlag.NonAtomic, false, app1, nextExpr, synRange)
            ) first
        checkExpr env builder resultExpr

/// Check TraitCall (SRTP)
and checkTraitCall (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (checkSynType: TypeEnv -> SynType -> NativeType) (env: TypeEnv) (builder: NodeBuilder) (supportTys: SynType) (memberSig: SynMemberSig) (argExpr: SynExpr) (range: SourceRange) : SemanticNode =
    let argNode = checkExpr env builder argExpr
    let constraintType = checkSynType env supportTys
    let constrainedTypes =
        match constraintType with
        | NativeType.TTuple(elemTys, _) -> elemTys
        | ty -> [ty]
    
    let memberName =
        match memberSig with
        | SynMemberSig.Member(SynValSig(ident = SynIdent(id, _)), _, _, _) -> id.idText
        | _ -> "unknown_trait"
    
    let resultType =
        match memberSig with
        | SynMemberSig.Member(SynValSig(synType = synRetType), _, _, _) ->
            checkSynType env synRetType
        | _ -> freshTypeVar range
    
    for constrainedTy in constrainedTypes do
        addConstraint (Constraint.HasMember(constrainedTy, memberName, resultType, range)) env
    
    builder.Create(
        SemanticKind.TraitCall(memberName, constrainedTypes, argNode.Id),
        resultType,
        range,
        children = [argNode.Id])

/// Check DotIndexedGet: expr.[index]
and checkDotIndexedGet (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (objExpr: SynExpr) (indexArgs: SynExpr) (range: SourceRange) : SemanticNode =
    let objNode = checkExpr env builder objExpr
    let indexNodes =
        match indexArgs with
        | SynExpr.Tuple(_, exprs, _, _) -> exprs |> List.map (checkExpr env builder)
        | indexExpr -> [checkExpr env builder indexExpr]
    
    match indexNodes with
    | [single] ->
        addConstraint (Constraint.Equals(single.Type, env.Globals.IntType, range)) env
    | _ -> ()
    
    let indexNodeId =
        match indexNodes with
        | [single] -> single.Id
        | multiple ->
            let multipleNodeIds = multiple |> List.map (fun n -> n.Id)
            let multipleNodeTypes = multiple |> List.map (fun n -> n.Type)
            let tupleNode = builder.Create(
                SemanticKind.TupleExpr(multipleNodeIds),
                NativeType.TTuple(multipleNodeTypes, false),
                range,
                children = multipleNodeIds)
            tupleNode.Id
    
    let isStringType ty =
        match ty with
        | NativeType.TApp(tc, []) when tc.Name = "string" -> true
        | _ -> false
    let elementType =
        let objType = applySubst objNode.Type
        match objType with
        | NativeType.TApp(tc, [elemType]) when tc.Name = "array" -> elemType
        | _ when isStringType objType -> env.Globals.CharType
        | NativeType.TVar _ ->
            let elemType = freshTypeVar range
            addConstraint (Constraint.Equals(objType, mkArrayType elemType, range)) env
            elemType
        | _ ->
            let resultType = freshTypeVar range
            addConstraint (Constraint.HasMember(objType, "Item", resultType, range)) env
            resultType
    
    let allChildNodeIds = objNode.Id :: (indexNodes |> List.map (fun n -> n.Id))
    builder.Create(
        SemanticKind.IndexGet(objNode.Id, indexNodeId),
        elementType,
        range,
        children = allChildNodeIds)

/// Check DotIndexedSet: expr.[index] <- value
and checkDotIndexedSet (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (objExpr: SynExpr) (indexArgs: SynExpr) (valueExpr: SynExpr) (range: SourceRange) : SemanticNode =
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
            let multipleNodeIds = multiple |> List.map (fun n -> n.Id)
            let multipleNodeTypes = multiple |> List.map (fun n -> n.Type)
            let tupleNode = builder.Create(
                SemanticKind.TupleExpr(multipleNodeIds),
                NativeType.TTuple(multipleNodeTypes, false),
                range,
                children = multipleNodeIds)
            tupleNode.Id
    let allChildNodeIds = objNode.Id :: valueNode.Id :: (indexNodes |> List.map (fun n -> n.Id))
    builder.Create(
        SemanticKind.IndexSet(objNode.Id, indexNodeId, valueNode.Id),
        env.Globals.UnitType,
        range,
        children = allChildNodeIds)

/// Check DotSet: expr.field <- value
and checkDotSet (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (objExpr: SynExpr) (longId: Ident list) (valueExpr: SynExpr) (range: SourceRange) : SemanticNode =
    let objNode = checkExpr env builder objExpr
    let valueNode = checkExpr env builder valueExpr
    let fieldName = longId |> List.map (fun id -> id.idText) |> String.concat "."
    builder.Create(
        SemanticKind.FieldSet(objNode.Id, fieldName, valueNode.Id),
        env.Globals.UnitType,
        range,
        children = [objNode.Id; valueNode.Id])

/// Check LongIdentSet: Module.value <- expr
and checkLongIdentSet (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (longId: Ident list) (valueExpr: SynExpr) (range: SourceRange) : SemanticNode =
    let valueNode = checkExpr env builder valueExpr
    let targetName = longId |> List.map (fun id -> id.idText) |> String.concat "."
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

/// Check Lazy: lazy expr
/// PRD-14: Creates LazyExpr node with a thunk (unit -> 'T) wrapping the body
/// Thunk calling convention (Option B): thunk receives lazy struct pointer and extracts its own captures
/// Captures are computed using the same analysis as Lambda (MLKit-style flat closures)
and checkLazy (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (innerExpr: SynExpr) (range: SourceRange) : SemanticNode =
    let innerNode = checkExpr env builder innerExpr
    let lazyType = mkLazyType innerNode.Type

    // Capture analysis: find VarRefs in body that are NOT the unit parameter
    // These are variables captured from the enclosing scope
    // PRD-14: Lazy values are "extended flat closures" with inlined captures
    let unitParamName = "_unit"
    let captures = computeCaptures builder env innerNode.Id (Set.singleton unitParamName)

    // Create a thunk Lambda: unit -> 'T
    // The thunk takes a unit parameter and returns the lazy body
    // Thunk captures the same variables as the lazy expression
    let thunkType = NativeType.TFun(env.Globals.UnitType, innerNode.Type)
    let thunkLambda = builder.Create(
        SemanticKind.Lambda([("_unit", env.Globals.UnitType, NodeId -1)], innerNode.Id, captures, env.EnclosingFunction, LambdaContext.LazyThunk),
        thunkType,
        range,
        children = [innerNode.Id])
    
    // Architectural fix (January 2026): Mark Lambda body as SeparateFunction
    // Pass capture count so SSA assignment starts body SSAs after capture extraction
    builder.SetEmissionStrategy(innerNode.Id, EmissionStrategy.SeparateFunction (List.length captures))

    // Create LazyExpr with the thunk as the body
    // LazyExpr stores the same captures (they're inlined in the lazy struct)
    builder.Create(
        SemanticKind.LazyExpr(thunkLambda.Id, captures),
        lazyType,
        range,
        children = [thunkLambda.Id])

/// Check seq expression: seq { ... }
/// PRD-15: Creates a SeqExpr with a MoveNext thunk (LambdaContext.SeqGenerator)
and checkSeq (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (bodyExpr: SynExpr) (range: SourceRange) : SemanticNode =
    // Check the body with EnclosingSeqExpr set as a marker (NodeId -1 = inside seq)
    // This enables checkYield to validate that yield appears inside a seq
    let bodyEnv = { env with EnclosingSeqExpr = Some (NodeId -1) }
    let bodyNode = checkExpr bodyEnv builder bodyExpr

    // Infer element type from Yield nodes in the body
    // yield returns unit, so we look at the type of the VALUE being yielded
    let rec findYieldValueType (nodeId: NodeId) : NativeType option =
        match Map.tryFind nodeId builder.Nodes with
        | None -> None
        | Some node ->
            match node.Kind with
            | SemanticKind.Yield valueId ->
                // Found a yield - get the type of the value expression
                match Map.tryFind valueId builder.Nodes with
                | Some valueNode -> Some valueNode.Type
                | None -> None
            | _ ->
                // Recurse into children
                node.Children |> List.tryPick findYieldValueType

    let elementType =
        match findYieldValueType bodyNode.Id with
        | Some ty -> ty
        | None -> freshTypeVar range  // No yields found, use type variable
    let seqType = mkSeqType elementType
    
    // Capture analysis: find VarRefs in body that are NOT local to the seq
    // PRD-15: Seq values are "extended flat closures" with inlined captures
    let captures = computeCaptures builder env bodyNode.Id Set.empty
    
    // Create MoveNext thunk: (seq_ptr: nativeptr<Seq<T>>) -> bool
    // The thunk receives pointer to the seq struct, extracts its captures
    // Returns true if a value was yielded, false if exhausted
    let seqPtrType = NativeType.TNativePtr seqType
    let moveNextType = NativeType.TFun(seqPtrType, env.Globals.BoolType)
    let moveNextLambda = builder.Create(
        SemanticKind.Lambda([("_seq_ptr", seqPtrType, NodeId -1)], bodyNode.Id, captures, env.EnclosingFunction, LambdaContext.SeqGenerator),
        moveNextType,
        range,
        children = [bodyNode.Id])
    
    // Architectural fix (January 2026): Mark Lambda body as SeparateFunction
    // Pass capture count so SSA assignment starts body SSAs after capture extraction
    builder.SetEmissionStrategy(bodyNode.Id, EmissionStrategy.SeparateFunction (List.length captures))

    // Create SeqExpr with the MoveNext thunk as body
    builder.Create(
        SemanticKind.SeqExpr(moveNextLambda.Id, captures),
        seqType,
        range,
        children = [moveNextLambda.Id])

/// Check yield: yield value
/// PRD-15: Produces a single value in the sequence
and checkYield (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (valueExpr: SynExpr) (range: SourceRange) : SemanticNode =
    // Validate that yield appears inside a seq expression
    match env.EnclosingSeqExpr with
    | None ->
        // Return error node - yield outside seq context
        builder.Create(
            SemanticKind.Error "yield may only appear directly in a seq expression",
            env.Globals.UnitType,
            range)
    | Some _ ->
        let valueNode = checkExpr env builder valueExpr
        // yield is an effectful operation - it stores the value but returns unit
        // The value's type is captured in the Yield node for codegen, but the
        // expression type is unit (yield doesn't return a value to the caller)
        builder.Create(
            SemanticKind.Yield valueNode.Id,
            env.Globals.UnitType,
            range,
            children = [valueNode.Id])

/// Check yield!: yield! seq
/// PRD-15: Flattens another sequence into this one
and checkYieldBang (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (seqExpr: SynExpr) (range: SourceRange) : SemanticNode =
    // Validate that yield! appears inside a seq expression
    match env.EnclosingSeqExpr with
    | None ->
        // Return error node - yield! outside seq context
        builder.Create(
            SemanticKind.Error "yield! may only appear directly in a seq expression",
            env.Globals.UnitType,
            range)
    | Some _ ->
        let seqNode = checkExpr env builder seqExpr
        // yield! is an effectful operation - it flattens a seq but returns unit
        // The element type is inferred from the seqNode for codegen purposes
        builder.Create(
            SemanticKind.YieldBang seqNode.Id,
            env.Globals.UnitType,
            range,
            children = [seqNode.Id])

/// Check Assert: assert expr
and checkAssert (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (condExpr: SynExpr) (range: SourceRange) : SemanticNode =
    let condNode = checkExpr env builder condExpr
    builder.Create(
        SemanticKind.Application(condNode.Id, []),
        env.Globals.UnitType,
        range,
        children = [condNode.Id])

/// Check New: new Type(args)
and checkNew (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (checkSynType: TypeEnv -> SynType -> NativeType) (env: TypeEnv) (builder: NodeBuilder) (synType: SynType) (argExpr: SynExpr) (range: SourceRange) : SemanticNode =
    let targetType = checkSynType env synType
    let argNode = checkExpr env builder argExpr
    builder.Create(
        SemanticKind.Application(argNode.Id, []),
        targetType,
        range,
        children = [argNode.Id])

/// Check ObjExpr: { new Interface with ... }
and checkObjExpr (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (checkSynType: TypeEnv -> SynType -> NativeType) (env: TypeEnv) (builder: NodeBuilder) (objType: SynType) (argOption: (SynExpr * Ident option) option) (bindings: SynBinding list) (members: SynMemberDefn list) (extraImpls: SynInterfaceImpl list) (range: SourceRange) : SemanticNode =
    let interfaceType = checkSynType env objType
    
    let argNodeIds =
        match argOption with
        | Some (argExpr, _asIdent) ->
            let argNode = checkExpr env builder argExpr
            [argNode.Id]
        | None -> []
    
    let bindingNodes = bindings |> List.map (fun binding ->
        match binding with
        | SynBinding(_, _, _, _, _, _, _, _, _, bodyExpr, _, _, _) ->
            checkExpr env builder bodyExpr)
    
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
        | _ -> [])
    
    let extraImplNodes = extraImpls |> List.collect (fun impl ->
        match impl with
        | SynInterfaceImpl(interfaceTy, _, implBindings, implMembers, _) ->
            let _implType = checkSynType env interfaceTy
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

/// Check MatchBang: match! expr with ...
and checkMatchBang (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (checkPattern: TypeEnv -> SynPat -> NativeType -> SourceRange -> Pattern * (string * NativeType) list) (env: TypeEnv) (builder: NodeBuilder) (expr: SynExpr) (clauses: SynMatchClause list) (range: SourceRange) : SemanticNode =
    let scrutineeNode = checkExpr env builder expr
    let matchCases = clauses |> List.map (fun (SynMatchClause(pat, guardOpt, resultExpr, _, _, _)) ->
        let (pattern, _patBindings) = checkPattern env pat scrutineeNode.Type range
        let guardNode = guardOpt |> Option.map (checkExpr env builder)
        let bodyNode = checkExpr env builder resultExpr
        { Pattern = pattern; PatternBindings = []; Guard = guardNode |> Option.map (fun g -> g.Id); Body = bodyNode.Id })
    let resultType = if List.isEmpty matchCases then env.Globals.UnitType else freshTypeVar range
    builder.Create(
        SemanticKind.Match(scrutineeNode.Id, matchCases),
        resultType,
        range,
        children = scrutineeNode.Id :: (matchCases |> List.collect (fun mc ->
            let guardAndBody = match mc.Guard with Some gid -> [gid; mc.Body] | None -> [mc.Body]
            mc.PatternBindings @ guardAndBody)))

/// Check DotNamedIndexedPropertySet: obj.Prop[idx] <- value
and checkDotNamedIndexedPropertySet (checkExpr: TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode) (env: TypeEnv) (builder: NodeBuilder) (objExpr: SynExpr) (longId: Ident list) (indexExpr: SynExpr) (valueExpr: SynExpr) (range: SourceRange) : SemanticNode =
    let objNode = checkExpr env builder objExpr
    let indexNode = checkExpr env builder indexExpr
    let valueNode = checkExpr env builder valueExpr
    let propName = longId |> List.map (fun id -> id.idText) |> String.concat "."
    
    addConstraint (Constraint.HasMember(objNode.Type, propName, freshTypeVar range, range)) env
    
    builder.Create(
        SemanticKind.NamedIndexedPropertySet(objNode.Id, propName, indexNode.Id, valueNode.Id),
        env.Globals.UnitType,
        range,
        children = [objNode.Id; indexNode.Id; valueNode.Id])
