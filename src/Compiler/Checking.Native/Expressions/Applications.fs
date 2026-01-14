// Copyright (c) 2025 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Application expression handlers for F# Native.
/// Handles: App (function application), TypeApp (type application)
/// Includes: Pipe operator reduction, intrinsic saturation, DU constructor detection
module FSharp.Native.Compiler.Checking.Native.Expressions.Applications

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Text
open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.NativeGlobals
open FSharp.Native.Compiler.Checking.Native.UnionFind
open FSharp.Native.Compiler.Checking.Native.SemanticGraph
open FSharp.Native.Compiler.Checking.Native.Expressions.Types

// Module alias for qualified access
module NativeTypes = FSharp.Native.Compiler.Checking.Native.NativeTypes

//-------------------------------------------------------------------------
// Callback Types
//-------------------------------------------------------------------------

/// Callback for checking expressions
type CheckExprFn = TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode

/// Callback for checking SynType
type CheckSynTypeFn = TypeEnv -> SynType -> NativeType

//-------------------------------------------------------------------------
// Helper Functions
//-------------------------------------------------------------------------

/// Check if name is forward pipe operator
let private isPipeRight name = name = "op_PipeRight"

/// Extract function name from SynExpr for inline lookup
/// Used to check if a function application target has InlineBody before checking
let private tryGetFunctionName (expr: SynExpr) : string option =
    match expr with
    | SynExpr.Ident(ident) -> Some ident.idText
    | SynExpr.LongIdent(_, SynLongIdent(ids, _, _), _, _) ->
        Some (ids |> List.map (fun id -> id.idText) |> String.concat ".")
    | _ -> None

/// Check if name is backward pipe operator
let private isPipeLeft name = name = "op_PipeLeft"

/// Check if an intrinsic is a forward pipe operator
let private isIntrinsicPipeRight (info: IntrinsicInfo) = 
    info.Operation = "op_PipeRight"

/// Check if an intrinsic is a backward pipe operator
let private isIntrinsicPipeLeft (info: IntrinsicInfo) = 
    info.Operation = "op_PipeLeft"

//-------------------------------------------------------------------------
// Function Application: SynExpr.App
//-------------------------------------------------------------------------

/// Check function application.
/// Handles: inline expansion (escape analysis), pipe operator reduction,
/// intrinsic saturation, DU constructor detection.
let checkApp
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (funcExpr: SynExpr)
    (argExpr: SynExpr)
    (_synRange: range)
    (range: SourceRange)
    : SemanticNode =

    // INLINE EXPANSION: Check if this is a call to a function with InlineBody
    // This is critical for escape analysis - when a function allocates on stack
    // and returns a reference, inlining moves the allocation to the caller's frame.
    //
    // Example: `Console.readln()` allocates a buffer and returns a fat pointer.
    // Without inlining: buffer is in readln's frame, pointer dangles after return.
    // With inlining: buffer is in caller's frame, pointer valid through caller's scope.
    let inlineExpansionResult =
        match tryGetFunctionName funcExpr with
        | Some funcName ->
            match tryLookupBinding funcName env with
            | Some binding when binding.InlineBody.IsSome ->
                let inlineBody = binding.InlineBody.Value
                // Check the argument first (always needed for substitution)
                let argNode = checkExpr env builder argExpr

                // Create environment with parameter bound to argument's value
                // This substitutes the argument for the parameter in the body
                match inlineBody.Parameters with
                | [paramName] ->
                    // Single-parameter function - direct substitution
                    let inlineEnv = addBinding paramName argNode.Type false (Some argNode.Id) env
                    // Check the body in the new environment - allocations now in caller's frame
                    Some (checkExpr inlineEnv builder inlineBody.Body)
                | [] ->
                    // No parameters (shouldn't happen for unit - unit has a parameter)
                    Some (checkExpr env builder inlineBody.Body)
                | _ ->
                    // Multi-parameter function - partial application
                    // For now, don't inline partial applications (would need closure handling)
                    None
            | _ -> None
        | None -> None

    // If we successfully inlined, return the expanded result
    match inlineExpansionResult with
    | Some expandedNode -> expandedNode
    | None ->

    // Normal path: no inline expansion (either no InlineBody or multi-arg partial application)
    let funcNode = checkExpr env builder funcExpr
    let argNode = checkExpr env builder argExpr

    // Determine result type based on function type
    // When function type is already concrete (TFun), use return type directly
    // This provides immediate type information without deferring to constraint solving
    let resultTy =
        match funcNode.Type with
        | NativeType.TFun(domainTy, rangeTy) ->
            // Function type is known - add domain constraint and use return type directly
            addConstraint (Constraint.Equals(domainTy, argNode.Type, range)) env
            rangeTy

        | NativeType.TForall(typeParams, bodyType) ->
            // IMPLICIT TYPE INSTANTIATION: When a TForall-typed function receives
            // value arguments (no explicit TypeApp), we instantiate with fresh type
            // variables that will be unified with argument types.
            //
            // Example: NativePtr.set buffer index value
            //   - NativePtr.set has type TForall(['T], nativeptr<'T> -> int -> 'T -> unit)
            //   - buffer has type nativeptr<uint8>
            //   - Instantiate 'T with fresh '?n, then unify nativeptr<'?n> with nativeptr<uint8>
            //   - Result: 'T = uint8, return type is int -> uint8 -> unit
            //
            // This is the implicit counterpart to explicit TypeApp handling.
            // See memory: typeapp_preserves_kind_principle
            let freshVars = typeParams |> List.map (fun _ -> freshTypeVar range)
            let instantiatedType = NativeTypes.instantiate typeParams freshVars bodyType
            // Now handle the instantiated type
            match instantiatedType with
            | NativeType.TFun(domainTy, rangeTy) ->
                addConstraint (Constraint.Equals(domainTy, argNode.Type, range)) env
                rangeTy
            | _ ->
                // Body wasn't a function type after instantiation - add constraint
                let freshResult = freshTypeVar range
                addConstraint (Constraint.Equals(
                    instantiatedType,
                    NativeType.TFun(argNode.Type, freshResult),
                    range)) env
                freshResult

        | NativeType.TVar _ ->
            // Function type is a type variable - defer to constraint solving
            let freshResult = freshTypeVar range
            addConstraint (Constraint.Equals(
                funcNode.Type,
                NativeType.TFun(argNode.Type, freshResult),
                range)) env
            freshResult

        | _ ->
            // Other types (error, etc.)
            // Generate constraint and fresh result type
            let freshResult = freshTypeVar range
            addConstraint (Constraint.Equals(
                funcNode.Type,
                NativeType.TFun(argNode.Type, freshResult),
                range)) env
            freshResult

    // PIPE OPERATOR REDUCTION:
    // F# pipe operators (|>, <|) are syntactic sugar that FNCS reduces during
    // type checking. This is a SEMANTIC TRANSFORM that belongs in FNCS, not
    // downstream in Firefly.
    //
    // Forward pipe: App(App(|>, x), f) -> App(f, [x])
    //   - The value x flows into function f
    //   - Inner App: (|>, x) where existingArgs = [xId]
    //   - argNode is f
    //
    // Backward pipe: App(App(<|, f), x) -> App(f, [x])
    //   - Function f is applied to value x
    //   - Inner App: (<|, f) where existingArgs = [fId]
    //   - argNode is x

    // INTRINSIC APPLICATION SATURATION:
    // Intrinsics don't support partial application - they're primitives that must
    // be called with all arguments at once. When we see curried application of an
    // intrinsic (e.g., NativePtr.set buffer count byte), we flatten into a single
    // Application node with all arguments.
    //
    // Without this, NativePtr.set buffer count byte creates:
    //   App(App(App(Intrinsic, buffer), count), byte)  -- nested, hard to codegen
    //
    // With this fix:
    //   App(Intrinsic, [buffer; count; byte])  -- flattened, direct codegen
    //
    // This is a CONSTRUCTION decision, not cleanup. Intermediate Application nodes
    // become orphaned and will be pruned by reachability.
    //
    // See memory: typeapp_preserves_kind_principle (same principle applies)
    let (targetFuncId, allArgs) =
        match funcNode.Kind with
        | SemanticKind.Intrinsic _ ->
            // Direct intrinsic application: App(Intrinsic, arg)
            (funcNode.Id, [argNode.Id])
        | SemanticKind.Application(innerFuncId, existingArgs) ->
            // Check what the inner function is
            match builder.Nodes.TryFind innerFuncId with
            | Some innerNode ->
                match innerNode.Kind with
                // PIPE REDUCTION: Forward pipe (|>) - VarRef form
                // App(App(|>, x), f) -> App(f, [x])
                | SemanticKind.VarRef(name, _) when isPipeRight name ->
                    match existingArgs with
                    | [valueId] ->
                        // argNode is the function, valueId is the value
                        // Transform: f(x) instead of (|>)(x)(f)
                        (argNode.Id, [valueId])
                    | _ ->
                        // Unexpected structure - keep as-is
                        (funcNode.Id, [argNode.Id])
                // PIPE REDUCTION: Forward pipe (|>) - Intrinsic form
                // When pipe is recognized as intrinsic during type checking
                | SemanticKind.Intrinsic info when isIntrinsicPipeRight info ->
                    match existingArgs with
                    | [valueId] ->
                        // argNode is the function, valueId is the value
                        // Transform: f(x) instead of (|>)(x)(f)
                        (argNode.Id, [valueId])
                    | _ ->
                        // Unexpected structure - keep as-is
                        (funcNode.Id, [argNode.Id])
                // PIPE REDUCTION: Backward pipe (<|) - VarRef form
                // App(App(<|, f), x) -> App(f, [x])
                | SemanticKind.VarRef(name, _) when isPipeLeft name ->
                    match existingArgs with
                    | [funcRefId] ->
                        // funcRefId is the function, argNode is the value
                        // Transform: f(x) instead of (<|)(f)(x)
                        (funcRefId, [argNode.Id])
                    | _ ->
                        // Unexpected structure - keep as-is
                        (funcNode.Id, [argNode.Id])
                // PIPE REDUCTION: Backward pipe (<|) - Intrinsic form
                | SemanticKind.Intrinsic info when isIntrinsicPipeLeft info ->
                    match existingArgs with
                    | [funcRefId] ->
                        // funcRefId is the function, argNode is the value
                        // Transform: f(x) instead of (<|)(f)(x)
                        (funcRefId, [argNode.Id])
                    | _ ->
                        // Unexpected structure - keep as-is
                        (funcNode.Id, [argNode.Id])
                // APPLICATION SATURATION: Flatten ALL curried applications
                // This is a SEMANTIC TRANSFORM that belongs in FNCS, enabling direct
                // emission as multi-arg calls. Without flattening:
                //   App(App(f, a), b) - nested, requires closure handling
                // With flattening:
                //   App(f, [a, b]) - flat, direct multi-arg call
                //
                // Note: Partial application is still preserved by the type system.
                // A function expecting 3 args called with 2 creates a closure-typed result.
                | SemanticKind.Intrinsic _
                | SemanticKind.PlatformBinding _
                | SemanticKind.VarRef _
                | SemanticKind.Lambda _
                | SemanticKind.Application _ ->
                    // Flatten curried application: accumulate args
                    (innerFuncId, existingArgs @ [argNode.Id])
                | _ ->
                    // Unknown node kind - keep as-is (shouldn't happen)
                    (funcNode.Id, [argNode.Id])
            | None ->
                // Inner node not found (shouldn't happen) - keep curried
                (funcNode.Id, [argNode.Id])
        | _ ->
            // Regular function application - keep curried structure
            (funcNode.Id, [argNode.Id])

    // RECURSIVE FLATTENING:
    // After pipe reduction, the targetFuncId may itself be an Application node.
    // For example: `readln() |> greet prefix` after pipe reduction becomes:
    //   targetFuncId = App(greet, [prefix])  (an Application!)
    //   allArgs = [readln_result]
    //
    // This must be flattened to: App(greet, [prefix; readln_result])
    //
    // Without this, Alex sees "Application as function" which it can't handle.
    // See memory: curried_call_flattening_insight
    let rec flattenApplication (funcId: NodeId) (args: NodeId list) : NodeId * NodeId list =
        match builder.Nodes.TryFind funcId with
        | Some node ->
            match node.Kind with
            | SemanticKind.Application(innerFuncId, innerArgs) ->
                // Recursively flatten: App(App(f, a), b) -> App(f, [a; b])
                flattenApplication innerFuncId (innerArgs @ args)
            | _ ->
                // Base case: not an Application, return as-is
                (funcId, args)
        | None ->
            // Node not found, return as-is
            (funcId, args)

    let (targetFuncId, allArgs) = flattenApplication targetFuncId allArgs

    // DU CONSTRUCTOR DETECTION:
    // If the target function is a DU constructor (has UnionCaseInfo), create
    // SemanticKind.UnionCase instead of Application. This enables Alex to
    // witness the DU construction directly without string matching.
    //
    // Check if targetFuncId is a VarRef to a DU constructor binding
    let isUnionCaseConstruction =
        match builder.Nodes.TryFind targetFuncId with
        | Some targetNode ->
            match targetNode.Kind with
            | SemanticKind.VarRef(name, _) ->
                match tryLookupBinding name env with
                | Some binding -> binding.UnionCaseInfo
                | None -> None
            | _ -> None
        | None -> None

    match isUnionCaseConstruction with
    | Some caseInfo ->
        // DU constructor application: create UnionCase node
        // For single-arg case like `IntVal 42`, payload is the argument
        // For multi-arg case like `Node(1, 2)`, payload is a tuple (handled by arg flattening)
        let payloadOpt =
            match allArgs with
            | [singleArg] -> Some singleArg  // Common case: single payload
            | _ -> None  // Multi-arg or nullary (shouldn't reach here for nullary)
        builder.Create(
            SemanticKind.UnionCase(caseInfo.CaseName, caseInfo.CaseIndex, payloadOpt),
            resultTy,
            range,
            children = allArgs)
    | None ->
        // Regular function application
        builder.Create(
            SemanticKind.Application(targetFuncId, allArgs),
            resultTy,
            range,
            children = targetFuncId :: allArgs)

//-------------------------------------------------------------------------
// Type Application: SynExpr.TypeApp
//-------------------------------------------------------------------------

/// Check type application: expr<type1, type2, ...>
/// Type application for generic instantiation. In native compilation,
/// this drives monomorphization - each unique set of type arguments
/// produces a specialized implementation.
let checkTypeApp
    (checkExpr: CheckExprFn)
    (checkSynType: CheckSynTypeFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (funcExpr: SynExpr)
    (typeArgs: SynType list)
    (synRange: range)
    (range: SourceRange)
    : SemanticNode =

    // Check the function expression
    let funcNode = checkExpr env builder funcExpr
    // Convert type arguments - these are the concrete types being applied
    let typeArgTypes = typeArgs |> List.map (checkSynType env)

    // The result type depends on the function being instantiated.
    // If funcNode.Type is a forall type, we should instantiate it with typeArgTypes.
    let resultType =
        match funcNode.Type with
        | NativeType.TForall(typeParams, bodyType) ->
            // Check arity match
            if List.length typeParams <> List.length typeArgTypes then
                // Arity mismatch - this is a type error
                addError synRange
                    (sprintf "Type application arity mismatch: expected %d type arguments, got %d"
                        (List.length typeParams) (List.length typeArgTypes)) env
                NativeType.TError "Type application arity mismatch"
            else
                // Perform immediate substitution of type parameters with concrete types
                // This is the correct approach - NativeTypes.instantiate replaces TVar
                // occurrences with their corresponding type arguments
                NativeTypes.instantiate typeParams typeArgTypes bodyType

        | NativeType.TVar _ ->
            // Function type is a type variable - not yet resolved
            // Add constraint that it must be a forall type with these arguments
            // For now, create fresh result type; constraint solving will refine
            freshTypeVar range

        | NativeType.TError msg ->
            // Propagate error
            NativeType.TError msg

        | NativeType.TFun _ ->
            // Function type receiving type arguments
            // This typically means a polymorphic function being instantiated
            // Add deferred constraint that function must be generic
            let resultTy = freshTypeVar range
            addConstraint (Constraint.HasTypeArgs(funcNode.Type, typeArgTypes, resultTy, range)) env
            resultTy

        | NativeType.TApp _ ->
            // Type application - possibly a partially applied generic
            // Add deferred constraint for type application
            let resultTy = freshTypeVar range
            addConstraint (Constraint.HasTypeArgs(funcNode.Type, typeArgTypes, resultTy, range)) env
            resultTy

        | other ->
            // Unexpected type receiving type arguments
            // This is likely a bug or unresolved type - add warning but continue
            addWarning synRange
                (sprintf "Type application on unexpected type form: %s"
                    (NativeTypes.formatType other)) env
            // Still add constraint for later resolution
            let resultTy = freshTypeVar range
            addConstraint (Constraint.HasTypeArgs(funcNode.Type, typeArgTypes, resultTy, range)) env
            resultTy

    // Create TypeAnnotation node to record the type application
    // This preserves the type argument information for monomorphization
    builder.Create(
        SemanticKind.TypeAnnotation(funcNode.Id, resultType),
        resultType,
        range,
        children = [funcNode.Id])

//-------------------------------------------------------------------------
// Lambda Expression
//-------------------------------------------------------------------------

/// Check lambda expression: fun args -> body
let checkLambda
    (checkExpr: CheckExprFn)
    (extractLambdaParams: TypeEnv -> SynSimplePats -> SourceRange -> (string * NativeType) list)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (args: SynSimplePats)
    (bodyExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =

    // Extract parameter names and create fresh type variables
    let paramBindings = extractLambdaParams env args range

    // Create PatternBinding nodes for parameters and collect (name, type, nodeId)
    // These nodes are needed for SSA assignment to map parameters to %argN
    let paramNodesAndEnv =
        paramBindings
        |> List.fold (fun (acc, env) (name, ty) ->
            let paramNode = builder.Create(
                SemanticKind.PatternBinding(name),
                ty,
                range,
                arena = env.CurrentArena)
            let newEnv = addBinding name ty false (Some paramNode.Id) env
            ((name, ty, paramNode.Id) :: acc, newEnv)
        ) ([], env)

    let lambdaParams = List.rev (fst paramNodesAndEnv)
    let bodyEnv = snd paramNodesAndEnv

    // Check body
    let bodyNode = checkExpr bodyEnv builder bodyExpr

    // Build function type
    let paramTypes = lambdaParams |> List.map (fun (_, ty, _) -> ty)
    let funcType = mkFunctionType paramTypes bodyNode.Type

    builder.Create(
        SemanticKind.Lambda(lambdaParams, bodyNode.Id),
        funcType,
        range,
        children = [bodyNode.Id])
