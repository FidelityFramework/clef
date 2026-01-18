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
open FSharp.Native.Compiler.Checking.Native.Expressions.Applications

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
/// InlineBody is captured only for functions explicitly marked `inline` - this enables
/// escape analysis where allocations are lifted to the caller's frame.
/// PRD-13: preCreatedBinding allows recursive bindings to provide a pre-created Binding node
/// so that VarRefs can resolve to it before the body is checked.
let checkBinding
    (checkExpr: CheckExprFn)
    (checkSynType: CheckSynTypeFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (binding: SynBinding)
    (preCreatedBinding: SemanticNode option)
    : SemanticNode * InlineBody option * bool * LiteralValue option =

    let (SynBinding(_, _, isInline, isMutable, attrs, _, _, headPat, _, expr, bindingRange, _, _)) = binding
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
                let newEnv = addBinding paramName paramTy false (Some paramNode.Id) false env  // Parameters are always local
                ((paramName, paramTy, paramNode.Id) :: acc, newEnv)
            ) ([], env)

        let lambdaParams = List.rev (fst paramNodesAndEnv)
        let bodyEnvWithParams = snd paramNodesAndEnv
        
        // PRD-13: Set this function as the enclosing function for nested bindings
        // This enables qualified names like "factorialTail_loop" for nested functions
        let bodyEnv = { bodyEnvWithParams with EnclosingFunction = Some name }

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
        // Children includes parameter PatternBindings + body for proper traversal
        // PRD-13: Pass enclosingFunction for qualified name generation in Alex
        let paramNodeIds = lambdaParams |> List.map (fun (_, _, nodeId) -> nodeId)
        let lambdaChildren = paramNodeIds @ [bodyNode.Id]

        // PRD-13: Compute captures for nested functions
        // Top-level functions (env.EnclosingFunction = None) never capture.
        // Nested functions may capture variables from enclosing scope.
        // Exclude: the function's own parameters AND the function's own name (for recursive self-reference)
        let paramNames = lambdaParams |> List.map (fun (pname, _, _) -> pname) |> Set.ofList
        let excludeNames = Set.add name paramNames
        let captures =
            if env.EnclosingFunction.IsSome then
                computeCaptures builder env bodyNode.Id excludeNames
            else
                []

        let lambdaNode = builder.Create(
            SemanticKind.Lambda(lambdaParams, bodyNode.Id, captures, env.EnclosingFunction, LambdaContext.RegularClosure),
            funcType,
            range,
            children = lambdaChildren)

        // PRD-13: Set parent on all children (params and body) for scope chain
        for childId in lambdaChildren do
            builder.SetParent(childId, lambdaNode.Id)

        // PRD-13: Use pre-created Binding if provided (for recursive bindings)
        // Otherwise create a new Binding node wrapping the Lambda
        let bindingNode =
            match preCreatedBinding with
            | Some preCreated ->
                // Link pre-created Binding to the Lambda we just created
                builder.SetChildren(preCreated.Id, [lambdaNode.Id])
                preCreated
            | None ->
                builder.Create(
                    SemanticKind.Binding(name, isMutable, false, isEntryPoint),
                    funcType,
                    range,
                    children = [lambdaNode.Id])

        // Establish bidirectional parent-child link
        // Lambda's Parent field must point back to Binding for SSA name assignment
        builder.SetParent(lambdaNode.Id, bindingNode.Id)

        // Capture inline body only for functions explicitly marked `inline`
        // This enables escape analysis - inline functions have their allocations
        // moved to the caller's frame, ensuring pointers remain valid.
        let inlineBodyOpt =
            if isInline then
                Some {
                    Parameters = lambdaParams |> List.map (fun (name, _, _) -> name)
                    Body = expr
                    Range = rangeToSourceRange bindingRange
                }
            else
                None

        (bindingNode, inlineBodyOpt, isMutable, literalValue)

    | None ->
        // Regular value binding (not a function - no inline body)
        let exprNode = checkExpr env builder expr

        // ETA-EXPANSION for partial applications:
        // When a binding's value has function type (TFun), it's a partial application
        // that should be eta-expanded to a proper Lambda. This enables Alex to emit
        // it as a callable function rather than an opaque value.
        //
        // Example: let helloGreeter = greet "Hello"
        //   - greet has type: string -> string -> unit
        //   - greet "Hello" has type: string -> unit
        //   - This should become: let helloGreeter name = greet "Hello" name
        //
        // We recursively expand all function arguments:
        //   TFun(a, TFun(b, c)) expands to: fun x y -> (expr x y)
        //
        // CRITICAL: We do NOT flatten applications across currying boundaries.
        // If makeCounter : int -> (unit -> int), then:
        //   makeCounter 0 : unit -> int  (returns a closure)
        // Eta-expanding this creates: fun _eta0 -> (makeCounter 0) _eta0
        // NOT: fun _eta0 -> makeCounter 0 _eta0  (which would pass 2 args to makeCounter)

        let rec etaExpand (funcExprId: NodeId) (funcType: NativeType) (accParams: (string * NativeType * NodeId) list) (counter: int) : SemanticNode =
            match funcType with
            | NativeType.TFun(domainTy, rangeTy) ->
                // Create synthetic parameter for this currying level
                let paramName = sprintf "_eta%d" counter
                let paramNode = builder.Create(
                    SemanticKind.PatternBinding(paramName),
                    domainTy,
                    range,
                    arena = env.CurrentArena)

                // Create VarRef to the parameter
                let paramVarRef = builder.Create(
                    SemanticKind.VarRef(paramName, Some paramNode.Id),
                    domainTy,
                    range,
                    arena = env.CurrentArena)

                // Apply ONE eta parameter to the current expression
                // Do NOT flatten - each currying level is a separate application
                // This preserves: (makeCounter 0) _eta0 as App(App(makeCounter,[0]), [_eta0])
                let appNode = builder.Create(
                    SemanticKind.Application(funcExprId, [paramVarRef.Id]),
                    rangeTy,
                    range,
                    children = [funcExprId; paramVarRef.Id])

                // Recursively expand if result is still a function type
                etaExpand appNode.Id rangeTy ((paramName, domainTy, paramNode.Id) :: accParams) (counter + 1)

            | _ ->
                // Base case: not a function type anymore
                // Build Lambda with all accumulated parameters
                let lambdaParams = List.rev accParams
                let bodyId = funcExprId

                if List.isEmpty lambdaParams then
                    // No eta-expansion needed - return original expression
                    builder.Nodes.[funcExprId]
                else
                    // Build the function type from parameters
                    let paramTypes = lambdaParams |> List.map (fun (_, ty, _) -> ty)
                    let funcType = mkFunctionType paramTypes funcType

                    // Eta-expanded lambdas don't capture anything new
                    // Children includes parameter PatternBindings + body for proper traversal
                    // Eta-expanded lambdas are synthetic - no enclosingFunction context
                    let paramNodeIds = lambdaParams |> List.map (fun (_, _, nodeId) -> nodeId)
                    let lambdaChildren = paramNodeIds @ [bodyId]
                    let lambdaNode = builder.Create(
                        SemanticKind.Lambda(lambdaParams, bodyId, [], None, LambdaContext.RegularClosure),
                        funcType,
                        range,
                        children = lambdaChildren)
                    // PRD-13: Set parent on all children for scope chain
                    for childId in lambdaChildren do
                        builder.SetParent(childId, lambdaNode.Id)
                    lambdaNode

        // Check if eta-expansion is needed
        // CRITICAL: Only eta-expand VarRefs to functions (true partial application)
        // Do NOT eta-expand Applications that return functions (closure factories)
        // e.g., `let counter = makeCounter 0` should NOT become `fun () -> makeCounter 0 ()`
        //       because makeCounter 0 returns a closure that should be stored directly
        let finalExprNode =
            match exprNode.Type, exprNode.Kind with
            | NativeType.TFun _, SemanticKind.VarRef _ ->
                // VarRef with function type = partial application, needs eta-expansion
                etaExpand exprNode.Id exprNode.Type [] 0
            | NativeType.TFun _, SemanticKind.Application _ ->
                // Application returning function = closure factory, store result directly
                exprNode
            | NativeType.TFun _, SemanticKind.Lambda _ ->
                // Lambda with function type = higher-order function, store directly
                exprNode
            | _ ->
                // Not a function type or other cases - use as-is
                exprNode

        // PRD-13: Use pre-created Binding if provided (for recursive bindings)
        let node =
            match preCreatedBinding with
            | Some preCreated ->
                builder.SetChildren(preCreated.Id, [finalExprNode.Id])
                preCreated
            | None ->
                builder.Create(
                    SemanticKind.Binding(name, isMutable, false, isEntryPoint),
                    finalExprNode.Type,
                    range,
                    children = [finalExprNode.Id])
        // Establish bidirectional parent-child link
        builder.SetParent(finalExprNode.Id, node.Id)
        (node, None, isMutable, literalValue)

//-------------------------------------------------------------------------
// Let/LetRec Handling
//-------------------------------------------------------------------------

/// Check a let-or-use binding
/// PRD-13: For recursive bindings (let rec), pre-create Binding nodes to get NodeIds
/// so that self-referential VarRefs can resolve correctly.
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

    // Helper: extend environment with binding results
    let extendEnvWithResults baseEnv bindingList (results: (SemanticNode * InlineBody option * bool * LiteralValue option) list) =
        List.zip bindingList results
        |> List.fold (fun env (binding, (node: SemanticNode, inlineBodyOpt, isMutable, literalValueOpt)) ->
            let name = getBindingName binding
            match inlineBodyOpt, literalValueOpt with
            | Some inlineBody, _ ->
                addInlineBinding name node.Type (Some node.Id) inlineBody env
            | None, Some litVal ->
                addLiteralBinding name node.Type (Some node.Id) litVal env
            | None, None ->
                addBinding name node.Type isMutable (Some node.Id) env.EnclosingFunction.IsNone env
        ) baseEnv

    // Helper: build final Sequential node
    // PRD-13: Sets bidirectional parent-child links so nested bindings know their scope
    let buildSequential bindingNodes bodyNode =
        let allIds = (bindingNodes |> List.map (fun (n: SemanticNode) -> n.Id)) @ [bodyNode.Id]
        let seqNode = builder.Create(
            SemanticKind.Sequential allIds,
            bodyNode.Type,
            range,
            children = allIds)
        // Set parent on all children (bidirectional link)
        for childId in allIds do
            builder.SetParent(childId, seqNode.Id)
        seqNode

    match letOrUse.IsRecursive with
    | true ->
        // PRD-13: RECURSIVE BINDINGS
        // Pre-create Binding nodes to get NodeIds before checking bodies
        let preCreatedBindings =
            bindings |> List.map (fun binding ->
                let name = getBindingName binding
                let ty = freshTypeVar range
                let (SynBinding(_, _, _, isMutable, attrs, _, _, _, _, _, _, _, _)) = binding
                let isEntryPoint = hasEntryPointAttribute attrs
                let node = builder.Create(
                    SemanticKind.Binding(name, isMutable, true, isEntryPoint),
                    ty,
                    range,
                    children = [])
                (binding, name, ty, node))

        // Add all bindings to environment WITH their NodeIds
        let envWithBindings =
            preCreatedBindings
            |> List.fold (fun env (_, name, ty, node) ->
                addBinding name ty false (Some node.Id) env.EnclosingFunction.IsNone env
            ) env

        // Check each binding body - VarRefs now resolve to pre-created NodeIds
        let bindingResults =
            preCreatedBindings
            |> List.map (fun (binding, _, _, preCreatedNode) ->
                checkBinding checkExpr checkSynType envWithBindings builder binding (Some preCreatedNode))

        let bindingNodes = bindingResults |> List.map (fun (node, _, _, _) -> node)
        let bodyEnv = extendEnvWithResults envWithBindings bindings bindingResults
        let bodyNode = checkExpr bodyEnv builder bodyExpr
        buildSequential bindingNodes bodyNode

    | false ->
        // NON-RECURSIVE BINDINGS: Standard sequential processing
        let bindingResults =
            bindings |> List.map (fun binding ->
                checkBinding checkExpr checkSynType env builder binding None)

        let bindingNodes = bindingResults |> List.map (fun (node, _, _, _) -> node)
        let bodyEnv = extendEnvWithResults env bindings bindingResults
        let bodyNode = checkExpr bodyEnv builder bodyExpr
        buildSequential bindingNodes bodyNode

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
    // Collect NodeIds for inclusion in MatchCase (enables SSA assignment traversal)
    let (bodyEnv, patternBindingIds) =
        patBindings
        |> List.fold (fun (env, ids) (name, ty) ->
            let patternBindingNode = builder.Create(
                SemanticKind.PatternBinding(name),
                ty,
                range,
                arena = env.CurrentArena)
            let env' = addBinding name ty false (Some patternBindingNode.Id) env.EnclosingFunction.IsNone env
            (env', patternBindingNode.Id :: ids)
        ) (env, [])
    let patternBindingIds = List.rev patternBindingIds  // Preserve order

    // Check guard if present
    let guardNode = guardOpt |> Option.map (checkExpr bodyEnv builder)
    guardNode |> Option.iter (fun g ->
        addConstraint (Constraint.Equals(g.Type, env.Globals.BoolType, range)) env)

    // Check body
    let bodyNode = checkExpr bodyEnv builder bodyExpr

    // Body must match result type
    addConstraint (Constraint.Equals(bodyNode.Type, resultTy, range)) env

    { Pattern = pattern
      PatternBindings = patternBindingIds
      Guard = guardNode |> Option.map (fun n -> n.Id)
      Body = bodyNode.Id }
