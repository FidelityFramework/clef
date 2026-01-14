// Copyright (c) 2025 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Binding handling for F# Native.
/// Handles: Let, LetRec, Lambda, pattern bindings
module FSharp.Native.Compiler.Checking.Native.Expressions.Bindings

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.NativeGlobals
open FSharp.Native.Compiler.Checking.Native.UnionFind
open FSharp.Native.Compiler.Checking.Native.SemanticGraph
open FSharp.Native.Compiler.Checking.Native.NameResolution
open FSharp.Native.Compiler.Checking.Native.Expressions.Types
open FSharp.Native.Compiler.Checking.Native.Expressions.Literals

//-------------------------------------------------------------------------
// Callback Types
//-------------------------------------------------------------------------

/// Callback for checking expressions (to avoid circular dependency)
type CheckExprFn = TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode

/// Callback for checking SynType
type CheckSynTypeFn = TypeEnv -> SynType -> NativeType

/// Callback for checking patterns
type CheckPatternFn = TypeEnv -> SynPat -> NativeType -> SourceRange -> Pattern * (string * NativeType) list

//-------------------------------------------------------------------------
// Lambda Parameter Extraction
//-------------------------------------------------------------------------

/// Extract parameter names from lambda arguments
let extractLambdaParams
    (checkSynType: CheckSynTypeFn)
    (env: TypeEnv)
    (args: SynSimplePats)
    (range: SourceRange)
    : (string * NativeType) list =
    match args with
    | SynSimplePats.SimplePats(pats, _, _) ->
        pats |> List.map (fun pat ->
            match pat with
            | SynSimplePat.Id(ident, _, _, _, _, _) ->
                (ident.idText, freshTypeVar range)
            | SynSimplePat.Typed(SynSimplePat.Id(ident, _, _, _, _, _), synType, _) ->
                // Type annotation provided - convert to native type
                (ident.idText, checkSynType env synType)
            | _ ->
                ("_", freshTypeVar range))

//-------------------------------------------------------------------------
// Binding Name Extraction
//-------------------------------------------------------------------------

/// Get the name from a binding
let getBindingName (binding: SynBinding) : string =
    let (SynBinding(_, _, _, _, _, _, _, headPat, _, _, _, _, _)) = binding
    match headPat with
    | SynPat.Named(SynIdent(ident, _), _, _, _) -> ident.idText
    | SynPat.LongIdent(longDotId, _, _, _, _, _) ->
        longDotId.LongIdent |> List.last |> fun id -> id.idText
    | _ -> "_"

/// Check if a binding is mutable
let isBindingMutable (binding: SynBinding) : bool =
    let (SynBinding(_, _, _, isMutable, _, _, _, _, _, _, _, _, _)) = binding
    isMutable

//-------------------------------------------------------------------------
// Function Parameter Extraction
//-------------------------------------------------------------------------

/// Extract function parameters from a LongIdent pattern
/// For `let f x y = body`, returns Some [(x, ty); (y, ty)]
/// For `let x = body`, returns None
let tryGetFunctionParams
    (checkSynType: CheckSynTypeFn)
    (headPat: SynPat)
    (env: TypeEnv)
    (range: SourceRange)
    : (string * NativeType) list option =
    match headPat with
    | SynPat.LongIdent(_, _, _, argPats, _, _) ->
        match argPats with
        | SynArgPats.Pats pats when not (List.isEmpty pats) ->
            // Has parameters - this is a function definition
            let extractedParameters = pats |> List.collect (fun pat ->
                match pat with
                | SynPat.Paren(innerPat, _) ->
                    // Parenthesized pattern like (x, y) or () or (x: Type)
                    match innerPat with
                    | SynPat.Const(SynConst.Unit, _) ->
                        // Unit literal - bind to dummy name
                        [("_", env.Globals.UnitType)]
                    | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                        [(ident.idText, freshTypeVar range)]
                    | SynPat.Typed(typedInner, synType, _) ->
                        // Typed pattern like (name: NativeStr)
                        let annotatedType = checkSynType env synType
                        match typedInner with
                        | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                            [(ident.idText, annotatedType)]
                        | _ -> [("_", annotatedType)]
                    | SynPat.Tuple(_, tuplePats, _, _) ->
                        tuplePats |> List.map (fun tuplePat ->
                            match tuplePat with
                            | SynPat.Named(SynIdent(ident, _), _, _, _) -> (ident.idText, freshTypeVar range)
                            | SynPat.Typed(SynPat.Named(SynIdent(ident, _), _, _, _), synType, _) ->
                                (ident.idText, checkSynType env synType)
                            | _ -> ("_", freshTypeVar range))
                    | _ -> [("_", freshTypeVar range)]
                | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                    [(ident.idText, freshTypeVar range)]
                | SynPat.Const(SynConst.Unit, _) ->
                    // Unit literal - bind to dummy name
                    [("_", env.Globals.UnitType)]
                | _ -> [("_", freshTypeVar range)]
            )
            Some extractedParameters
        | _ -> None
    | _ -> None

//-------------------------------------------------------------------------
// Binding Checking
//-------------------------------------------------------------------------

/// Check a single binding
/// Returns the semantic node, optionally an InlineBody for transparent function expansion,
/// the isMutable flag, and optionally a LiteralValue for [<Literal>] bindings.
/// FNCS is inline-by-default: all function bodies are captured for potential expansion.
let checkBinding
    (checkExpr: CheckExprFn)
    (checkSynType: CheckSynTypeFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (binding: SynBinding)
    : SemanticNode * InlineBody option * bool * LiteralValue option =

    let (SynBinding(_, _, _, isMutable, attrs, _, _, headPat, _, expr, bindingRange, _, _)) = binding
    let range = rangeToSourceRange bindingRange
    let name = getBindingName binding
    let isEntryPoint = hasEntryPointAttribute attrs
    let isLiteral = hasLiteralAttribute attrs

    // Extract literal value if this is a [<Literal>] binding with a constant expression
    let literalValue =
        if isLiteral then
            match expr with
            | SynExpr.Const(constant, _) -> Some (Literals.constToLiteral constant)
            | _ -> None  // Non-constant [<Literal>] - will be caught by type checker
        else
            None

    // Check if this is a function definition (has parameters)
    match tryGetFunctionParams checkSynType headPat env range with
    | Some paramBindings ->
        // This is a function definition like `let f x = body` or `let f() = body`
        // Create a Lambda node wrapping the body

        // Create PatternBinding nodes for parameters and collect (name, type, nodeId)
        // These nodes are needed for SSA assignment to map parameters to %argN
        let paramNodesAndEnv =
            paramBindings
            |> List.fold (fun (acc, env) (paramName, paramTy) ->
                let paramNode = builder.Create(
                    SemanticKind.PatternBinding(paramName),
                    paramTy,
                    range,
                    arena = env.CurrentArena)
                let newEnv = addBinding paramName paramTy false (Some paramNode.Id) env
                ((paramName, paramTy, paramNode.Id) :: acc, newEnv)
            ) ([], env)

        let lambdaParams = List.rev (fst paramNodesAndEnv)
        let bodyEnv = snd paramNodesAndEnv

        // Check body with extended environment
        let bodyNode = checkExpr bodyEnv builder expr

        // Entry point constraint: string[] -> int
        // Per F# spec, [<EntryPoint>] functions must have signature: string[] -> int
        if isEntryPoint then
            // Constrain parameter to string[] (argv)
            match lambdaParams with
            | [(_, paramTy, _)] ->
                let stringArrayType = mkArrayType env.Globals.StringType
                addConstraint (Constraint.Equals(paramTy, stringArrayType, range)) env
            | _ -> ()  // Multiple or no params - unusual for entry point
            // Constrain return type to int
            addConstraint (Constraint.Equals(bodyNode.Type, env.Globals.IntType, range)) env

        // Build function type
        let paramTypes = lambdaParams |> List.map (fun (_, ty, _) -> ty)
        // For unit-parameterized functions like f(), the paramTypes might be empty
        // but it's still a function: unit -> returnType
        let funcType =
            if List.isEmpty paramTypes then
                mkFunctionType [env.Globals.UnitType] bodyNode.Type
            else
                mkFunctionType paramTypes bodyNode.Type

        // NOTE: Generalization disabled - it was causing type mismatches.
        // The proper fix requires smarter generalization (only top-level, not nested).
        // For now, rely on primitive operators having TForall in NativeGlobals.

        // Create Lambda node with parameter NodeIds for SSA assignment
        let lambdaNode = builder.Create(
            SemanticKind.Lambda(lambdaParams, bodyNode.Id),
            funcType,
            range,
            children = [bodyNode.Id])

        // Create Binding node wrapping the Lambda
        let bindingNode = builder.Create(
            SemanticKind.Binding(name, isMutable, false, isEntryPoint),
            funcType,
            range,
            children = [lambdaNode.Id])

        // Establish bidirectional parent-child link
        // Lambda's Parent field must point back to Binding for SSA name assignment
        builder.SetParent(lambdaNode.Id, bindingNode.Id)

        // Capture inline body for transparent function expansion
        // FNCS inline-by-default: all functions are transparent to the compiler
        let inlineBody: InlineBody = {
            Parameters = lambdaParams |> List.map (fun (name, _, _) -> name)  // Just the parameter names
            Body = expr                                  // The original SynExpr
            Range = rangeToSourceRange bindingRange     // Source range for error reporting
        }

        (bindingNode, Some inlineBody, isMutable, literalValue)

    | None ->
        // Regular value binding (not a function - no inline body)
        let exprNode = checkExpr env builder expr
        let node = builder.Create(
            SemanticKind.Binding(name, isMutable, false, isEntryPoint),
            exprNode.Type,
            range,
            children = [exprNode.Id])
        // Establish bidirectional parent-child link
        builder.SetParent(exprNode.Id, node.Id)
        (node, None, isMutable, literalValue)

//-------------------------------------------------------------------------
// Let/LetRec Handling
//-------------------------------------------------------------------------

/// Check a let-or-use binding
let checkLetOrUse
    (checkExpr: CheckExprFn)
    (checkSynType: CheckSynTypeFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (letOrUse: SynLetOrUse)
    (range: SourceRange)
    : SemanticNode =

    let bindings = letOrUse.Bindings
    let bodyExpr = letOrUse.Body
    let isRec = letOrUse.IsRecursive

    // First pass: add all bindings to environment (for recursive bindings)
    let bindingEnv =
        if isRec then
            bindings |> List.fold (fun env binding ->
                let name = getBindingName binding
                let ty = freshTypeVar range
                addBinding name ty false None env
            ) env
        else
            env

    // Check each binding (returns SemanticNode * InlineBody option * bool * LiteralValue option)
    let bindingResults = bindings |> List.map (fun binding ->
        checkBinding checkExpr checkSynType bindingEnv builder binding)

    // Extract just the nodes for the semantic graph
    let bindingNodes = bindingResults |> List.map (fun (node, _, _, _) -> node)

    // Add bindings to environment for body
    // FNCS inline-by-default: use addInlineBinding for functions with bodies
    let bodyEnv =
        List.zip bindings bindingResults
        |> List.fold (fun env (binding, (node, inlineBodyOpt, isMutable, literalValueOpt)) ->
            let name = getBindingName binding
            match inlineBodyOpt, literalValueOpt with
            | Some inlineBody, _ ->
                // Function with inline body - add with transparency
                addInlineBinding name node.Type (Some node.Id) inlineBody env
            | None, Some litVal ->
                // [<Literal>] binding - add for compile-time substitution
                addLiteralBinding name node.Type (Some node.Id) litVal env
            | None, None ->
                // Regular value binding - use the isMutable flag from checkBinding
                addBinding name node.Type isMutable (Some node.Id) env
        ) bindingEnv

    // Check body
    let bodyNode = checkExpr bodyEnv builder bodyExpr

    // Create sequential node for bindings + body
    let allIds = (bindingNodes |> List.map (fun n -> n.Id)) @ [bodyNode.Id]
    builder.Create(
        SemanticKind.Sequential allIds,
        bodyNode.Type,
        range,
        children = allIds)

//-------------------------------------------------------------------------
// Match Clause Handling
//-------------------------------------------------------------------------

/// Check a match clause
let checkMatchClause
    (checkExpr: CheckExprFn)
    (checkPattern: CheckPatternFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (scrutineeTy: NativeType)
    (resultTy: NativeType)
    (clause: SynMatchClause)
    : MatchCase =

    let (SynMatchClause(pat, guardOpt, bodyExpr, _, _, _)) = clause
    let range = rangeToSourceRange bodyExpr.Range

    // Check pattern and extract bindings
    let (pattern, patBindings) = checkPattern env pat scrutineeTy range

    // Create PSG nodes for pattern bindings and add to environment
    // Following ML/FStar convention: pattern binding IS the definition
    let bodyEnv =
        patBindings
        |> List.fold (fun env (name, ty) ->
            let patternBindingNode = builder.Create(
                SemanticKind.PatternBinding(name),
                ty,
                range,
                arena = env.CurrentArena)
            addBinding name ty false (Some patternBindingNode.Id) env
        ) env

    // Check guard if present
    let guardNode = guardOpt |> Option.map (checkExpr bodyEnv builder)
    guardNode |> Option.iter (fun g ->
        addConstraint (Constraint.Equals(g.Type, env.Globals.BoolType, range)) env)

    // Check body
    let bodyNode = checkExpr bodyEnv builder bodyExpr

    // Body must match result type
    addConstraint (Constraint.Equals(bodyNode.Type, resultTy, range)) env

    { Pattern = pattern
      Guard = guardNode |> Option.map (fun n -> n.Id)
      Body = bodyNode.Id }
