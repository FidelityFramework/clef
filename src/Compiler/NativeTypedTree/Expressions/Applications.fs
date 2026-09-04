// Copyright (c) 2025 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Application expression handlers for Clef.
/// Handles: App (function application), Lambda, TypeApp, New, ObjExpr, TraitCall
/// Includes: Pipe operator reduction, intrinsic saturation, DU constructor detection
module Clef.Compiler.NativeTypedTree.Expressions.Applications

open Clef.Compiler.Syntax
open Clef.Compiler.Text
open Clef.Compiler.NativeTypedTree.NativeTypes

open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.NativeTypedTree.Expressions.Types

// Module alias for qualified access
module NativeTypes = Clef.Compiler.NativeTypedTree.NativeTypes

//-------------------------------------------------------------------------
// Callback Types
//-------------------------------------------------------------------------

/// Callback for checking expressions
type CheckExprFn = TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode

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
                    let inlineEnv = addBinding paramName argNode.Type false (Some argNode.Id) false env  // Inline params are local
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
            // Fresh variables of each parameter's kind (design b.4 step 4), from the one minting place.
            let freshVars = typeParams |> List.map (fun tp -> freshInstanceOf tp range)
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
    // F# pipe operators (|>, <|) are syntactic sugar that CCS reduces during
    // type checking. This is a SEMANTIC TRANSFORM that belongs in CCS, not
    // downstream in Composer.
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
                // This is a SEMANTIC TRANSFORM that belongs in CCS, enabling direct
                // emission as multi-arg calls. Without flattening:
                //   App(App(f, a), b) - nested, requires closure handling
                // With flattening:
                //   App(f, [a, b]) - flat, direct multi-arg call
                //
                // Note: Partial application is still preserved by the type system.
                // A function expecting 3 args called with 2 creates a closure-typed result.
                //
                // INTRINSIC NODE FRESHNESS: Create a fresh Intrinsic node for saturated
                // applications to prevent node sharing. When an intrinsic like String.concat2
                // is partially applied then saturated, we need separate Intrinsic nodes:
                //   App(Intrinsic_A, [arg1]) - partial (unreachable)
                //   App(Intrinsic_B, [arg1, arg2]) - saturated (reachable)
                // Without fresh nodes, both Applications share Intrinsic_A, causing
                // orphaned parent links after intrinsic elaboration.
                | SemanticKind.Intrinsic info ->
                    // Create fresh Intrinsic node for this saturated application
                    let innerNode = Option.get (builder.Nodes.TryFind innerFuncId)
                    let freshIntrinsic = builder.Create(
                        SemanticKind.Intrinsic info,
                        innerNode.Type,
                        innerNode.Range,
                        arena = env.CurrentArena)
                    (freshIntrinsic.Id, existingArgs @ [argNode.Id])
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
        | SemanticKind.VarRef(_, Some defId) ->
            // PARTIAL APPLICATION SATURATION (within same scope only):
            // VarRef with definition - check if the definition is a partial application
            // that was created in the SAME expression context.
            //
            // This handles: (f x) y -> f x y  (nested applications in same expression)
            //
            // We do NOT flatten across binding boundaries because:
            // 1. The argument nodes from a module-level binding are in a different scope
            // 2. Their SSA values wouldn't be available in the call context
            //
            // For module-level partial applications like:
            //   let partial = f x
            //   partial y
            // The partial application needs to be emitted as a wrapper function or closure,
            // which is handled separately (TODO: PartialApplication SemanticKind).
            match builder.Nodes.TryFind defId with
            | Some defNode ->
                match defNode.Kind with
                | SemanticKind.Application(innerFuncId, existingArgs) ->
                    // Direct Application node (same expression context) - safe to flatten
                    (innerFuncId, existingArgs @ [argNode.Id])
                | SemanticKind.Binding _ ->
                    // Module-level binding - do NOT flatten across scope boundary
                    // The partial application is in a different scope; its arguments
                    // won't be available in the current context.
                    (funcNode.Id, [argNode.Id])
                | _ ->
                    // Definition is not an Application - regular call
                    (funcNode.Id, [argNode.Id])
            | None ->
                // Definition not found - regular call
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
            | SemanticKind.VarRef(_, Some defId) ->
                // Only follow VarRef if the definition is a direct Application
                // Do NOT follow through Binding nodes (different scope)
                match builder.Nodes.TryFind defId with
                | Some defNode ->
                    match defNode.Kind with
                    | SemanticKind.Application(innerFuncId, innerArgs) ->
                        flattenApplication innerFuncId (innerArgs @ args)
                    | _ ->
                        // Not a direct Application - stop here
                        (funcId, args)
                | None -> (funcId, args)
            | _ ->
                // Base case: not an Application or VarRef to Application
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
    // Two cases to handle:
    // 1. VarRef to a constructor binding (e.g., first use of IntVal)
    // 2. Existing UnionCase with None payload (e.g., IntVal created by Identity.fs,
    //    now being applied with an argument)
    let unionCaseInfo =
        match builder.Nodes.TryFind targetFuncId with
        | Some targetNode ->
            match targetNode.Kind with
            | SemanticKind.VarRef(name, _) ->
                // Case 1: VarRef to constructor binding
                match tryLookupBinding name env with
                | Some binding -> binding.UnionCaseInfo
                | None -> None
            | SemanticKind.UnionCase(caseName, caseIndex, None) ->
                // Case 2: Existing UnionCase with no payload - we're applying the argument
                // Extract UnionType from node's type (which is TFun(payloadType, unionType))
                let unionType =
                    match targetNode.Type with
                    | NativeType.TFun(_, retTy) -> retTy  // Return type is the union type
                    | ty -> ty  // Fallback to the type itself
                Some { CaseName = caseName; UnionType = unionType; CaseIndex = caseIndex }
            | _ -> None
        | None -> None

    match unionCaseInfo with
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
        // Check for semantic intrinsics that should become specific SemanticKinds
        // PRD-14: Lazy.force becomes LazyForce
        match builder.Nodes.TryFind targetFuncId with
        | Some targetNode ->
            match targetNode.Kind with
            | SemanticKind.Intrinsic info when info.Module = IntrinsicModule.Lazy && info.Operation = "force" ->
                // Lazy.force lazyVal -> LazyForce(lazyVal)
                match allArgs with
                | [lazyValId] ->
                    builder.Create(
                        SemanticKind.LazyForce(lazyValId),
                        resultTy,
                        range,
                        children = [lazyValId])
                | _ ->
                    // Unexpected arity - fall through to regular Application
                    builder.Create(
                        SemanticKind.Application(targetFuncId, allArgs),
                        resultTy,
                        range,
                        children = targetFuncId :: allArgs)
            | _ ->
                // Regular function application
                builder.Create(
                    SemanticKind.Application(targetFuncId, allArgs),
                    resultTy,
                    range,
                    children = targetFuncId :: allArgs)
        | None ->
            // Target not found - regular application
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
    let typeArgTypes = typeArgs |> List.map (resolveSynType env)

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

/// Collect all VarRef names from a semantic node tree (recursive traversal)
/// Made public for reuse in checkLazy (PRD-14)
let collectVarRefs (builder: NodeBuilder) (nodeId: NodeId) : Set<string> =
    let nodes = builder.Nodes
    let rec collect (nodeId: NodeId) (acc: Set<string>) : Set<string> =
        match Map.tryFind nodeId nodes with
        | None -> acc
        | Some node ->
            let acc =
                match node.Kind with
                | SemanticKind.VarRef(name, _) -> Set.add name acc
                | _ -> acc
            // Recurse into children
            node.Children |> List.fold (fun a childId -> collect childId a) acc
    collect nodeId Set.empty

/// Compute captures for a body node, excluding given parameter names
/// Reusable for Lambda (checkLambda) and Lazy (checkLazy) capture analysis
/// PRD-14: Both Lambda and Lazy use MLKit-style flat closures with inlined captures
/// CRITICAL: Only LOCAL bindings are captured; module-level bindings are referenced by address
let computeCaptures (builder: NodeBuilder) (env: TypeEnv) (bodyNodeId: NodeId) (excludeNames: Set<string>) : CaptureInfo list =
    let bodyVarRefs = collectVarRefs builder bodyNodeId
    let capturedNames = Set.difference bodyVarRefs excludeNames
    capturedNames
    |> Set.toList
    |> List.choose (fun name ->
        match tryLookupBinding name env with
        | Some binding ->
            // PRD-14: Module-level bindings are NOT captured - they're referenced by address
            // Only local bindings (from enclosing function scopes) become closure captures
            if binding.IsModuleLevel then
                None  // Reference by address, not capture
            else
                Some {
                    CaptureInfo.Name = name
                    Type = binding.Type
                    IsMutable = binding.IsMutable
                    SourceNodeId = binding.NodeId
                }
        | None ->
            // Not found in environment - could be a global/intrinsic, not a capture
            None)

/// Check lambda expression: fun args -> body
/// Includes capture analysis for closure generation (MLKit-style flat closures).
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
            let newEnv = addBinding name ty false (Some paramNode.Id) false env  // Parameters are always local
            ((name, ty, paramNode.Id) :: acc, newEnv)
        ) ([], env)

    let lambdaParams = List.rev (fst paramNodesAndEnv)
    let bodyEnv = snd paramNodesAndEnv
    let paramNames = lambdaParams |> List.map (fun (name, _, _) -> name) |> Set.ofList

    // Check body
    let bodyNode = checkExpr bodyEnv builder bodyExpr

    // Capture analysis: find VarRefs in body that are NOT lambda parameters
    // These are variables captured from the enclosing scope (closure captures)
    // Use computeCaptures helper (PRD-14: shared with checkLazy)
    let captures = computeCaptures builder env bodyNode.Id paramNames

    // Build function type
    // For unit-parameterized lambdas (fun () -> body), paramTypes is empty
    // but we still need to create unit -> bodyType, not just bodyType
    let paramTypes = lambdaParams |> List.map (fun (_, ty, _) -> ty)
    let funcType =
        if List.isEmpty paramTypes then
            NativeType.TFun(Types.unitType, bodyNode.Type)
        else
            mkFunctionType paramTypes bodyNode.Type

    // Children includes parameter PatternBindings + body for proper traversal
    // Anonymous lambdas inherit the current enclosing function context
    let paramNodeIds = lambdaParams |> List.map (fun (_, _, nodeId) -> nodeId)
    let lambdaNode = builder.Create(
        SemanticKind.Lambda(lambdaParams, bodyNode.Id, captures, env.EnclosingFunction, LambdaContext.RegularClosure),
        funcType,
        range,
        children = paramNodeIds @ [bodyNode.Id])
    
    // Architectural fix (January 2026): Mark Lambda body as SeparateFunction
    // Pass capture count so SSA assignment starts body SSAs after capture extraction
    builder.SetEmissionStrategy(bodyNode.Id, EmissionStrategy.SeparateFunction (List.length captures))

    lambdaNode


//-------------------------------------------------------------------------
// New Expression: new Type(args)
//-------------------------------------------------------------------------

/// Check New: new Type(args)
let checkNew
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (synType: SynType)
    (argExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let targetType = resolveSynType env synType
    let argNode = checkExpr env builder argExpr
    builder.Create(
        SemanticKind.Application(argNode.Id, []),
        targetType,
        range,
        children = [argNode.Id])

//-------------------------------------------------------------------------
// Object Expression: { new Interface with ... }
//-------------------------------------------------------------------------

/// Check ObjExpr: { new Interface with ... }
let checkObjExpr
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (objType: SynType)
    (argOption: (SynExpr * Ident option) option)
    (bindings: SynBinding list)
    (members: SynMemberDefn list)
    (extraImpls: SynInterfaceImpl list)
    (range: SourceRange)
    : SemanticNode =
    let interfaceType = resolveSynType env objType

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
            let _implType = resolveSynType env interfaceTy
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

//-------------------------------------------------------------------------
// Trait Call: SRTP member invocation
//-------------------------------------------------------------------------

/// Check TraitCall (SRTP)
let checkTraitCall
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (supportTys: SynType)
    (memberSig: SynMemberSig)
    (argExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let argNode = checkExpr env builder argExpr
    let constraintType = resolveSynType env supportTys
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
            resolveSynType env synRetType
        | _ -> freshTypeVar range

    for constrainedTy in constrainedTypes do
        addConstraint (Constraint.HasMember(constrainedTy, memberName, resultType, range)) env

    builder.Create(
        SemanticKind.TraitCall(memberName, constrainedTypes, argNode.Id),
        resultType,
        range,
        children = [argNode.Id])
