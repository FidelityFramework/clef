// Copyright (c) 2025 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Binding handling for Clef.
/// Handles: Let, LetRec, Lambda, pattern bindings, Set operations
module Clef.Compiler.NativeTypedTree.Expressions.Bindings

open Clef.Compiler.Syntax
open Clef.Compiler.NativeTypedTree.NativeTypes

open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.NativeTypedTree.NameResolution
open Clef.Compiler.NativeTypedTree.Expressions.Types
open Clef.Compiler.NativeTypedTree.Expressions.Literals
open Clef.Compiler.NativeTypedTree.Expressions.Applications

// Module alias for qualified access to shared utilities
module Types = Clef.Compiler.NativeTypedTree.Expressions.Types

//-------------------------------------------------------------------------
// Callback Types
//-------------------------------------------------------------------------

/// Callback for checking expressions (to avoid circular dependency)
type CheckExprFn = TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode

/// Callback for checking patterns
type CheckPatternFn = TypeEnv -> SynPat -> NativeType -> SourceRange -> Pattern * (string * NativeType) list

//-------------------------------------------------------------------------
// Lambda Parameter Extraction
//-------------------------------------------------------------------------

/// Extract parameter names from lambda arguments
let extractLambdaParams
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
                (ident.idText, resolveSynType env synType)
            | SynSimplePat.Typed(SynSimplePat.Typed _, _, _) ->
                // Double-typed pattern - unusual but handle gracefully
                failwith "Double type annotation in lambda parameter not supported"
            | SynSimplePat.Typed(SynSimplePat.Attrib(innerInner, _, _), synType, _) ->
                // Typed attributed pattern - (name: Type) with attributes
                match innerInner with
                | SynSimplePat.Id(ident, _, _, _, _, _) ->
                    (ident.idText, resolveSynType env synType)
                | other ->
                    failwith ("Unsupported typed attributed lambda parameter: " + other.GetType().Name)
            | SynSimplePat.Attrib(innerPat, _, _) ->
                // Attributed pattern - extract the inner identifier
                match innerPat with
                | SynSimplePat.Id(ident, _, _, _, _, _) ->
                    (ident.idText, freshTypeVar range)
                | SynSimplePat.Typed(SynSimplePat.Id(ident, _, _, _, _, _), synType, _) ->
                    (ident.idText, resolveSynType env synType)
                | other ->
                    failwith ("Unsupported attributed lambda parameter: " + other.GetType().Name))

//-------------------------------------------------------------------------
// Binding Name Extraction
//-------------------------------------------------------------------------

/// Marker returned by getBindingName for tuple patterns
/// This tells checkBinding to use special tuple destructuring logic
[<Literal>]
let TuplePatternMarker = "__TUPLE_PATTERN__"

/// Get the name from a binding
/// NOTE: For tuple patterns, returns TuplePatternMarker to trigger special handling in checkBinding.
let getBindingName (binding: SynBinding) : string =
    let (SynBinding(_, _, _, _, _, _, _, headPat, _, _, _, _, _)) = binding
    let rec getNameFromPat pat =
        match pat with
        | SynPat.Named(SynIdent(ident, _), _, _, _) -> ident.idText
        | SynPat.LongIdent(longDotId, _, _, _, _, _) ->
            longDotId.LongIdent |> List.last |> fun id -> id.idText
        | SynPat.Paren(innerPat, _) ->
            // Unwrap parentheses - (name) is the same as name
            getNameFromPat innerPat
        | SynPat.Typed(innerPat, _, _) ->
            // Type annotation - (name : Type) extracts name
            getNameFromPat innerPat
        | SynPat.Tuple _ ->
            // Return marker to trigger tuple destructuring in checkBinding
            TuplePatternMarker
        | SynPat.Wild _ ->
            // Wildcard pattern: let _ = expr
            "_"
        | SynPat.Const(SynConst.Unit, _) ->
            // Unit pattern: let () = expr
            "_"
        | other ->
            // Explicit diagnostic for unhandled patterns
            // This should never reach here for valid F# - if it does, we need to add support
            failwith ("Unsupported pattern in let binding: " + other.GetType().Name + ". Please report this as a bug with your source code.")
    getNameFromPat headPat

/// Check if a binding is mutable
let isBindingMutable (binding: SynBinding) : bool =
    let (SynBinding(_, _, _, isMutable, _, _, _, _, _, _, _, _, _)) = binding
    isMutable

/// Extract element names from a tuple pattern (for tuple destructuring)
/// Returns list of (name, isWildcard) pairs
let rec extractTupleElements (pat: SynPat) : (string * bool) list =
    match pat with
    | SynPat.Tuple(_, elements, _, _) ->
        elements |> List.collect extractTupleElements
    | SynPat.Paren(inner, _) ->
        extractTupleElements inner
    | SynPat.Typed(inner, _, _) ->
        extractTupleElements inner
    | SynPat.Named(SynIdent(ident, _), _, _, _) ->
        [(ident.idText, false)]
    | SynPat.Wild _ ->
        [("_", true)]
    | SynPat.Const(SynConst.Unit, _) ->
        [("_", true)]
    | other ->
        failwith ("Unsupported pattern in tuple destructuring: " + other.GetType().Name)

/// Get the head pattern from a binding, unwrapping Paren
let getHeadPattern (binding: SynBinding) : SynPat =
    let (SynBinding(_, _, _, _, _, _, _, headPat, _, _, _, _, _)) = binding
    let rec unwrap pat =
        match pat with
        | SynPat.Paren(inner, _) -> unwrap inner
        | other -> other
    unwrap headPat

//-------------------------------------------------------------------------
// Function Parameter Extraction
//-------------------------------------------------------------------------

/// Extract function parameters from a LongIdent pattern
/// For `let f x y = body`, returns Some [(x, ty); (y, ty)]
/// For `let x = body`, returns None
let tryGetFunctionParams
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
                        [("_", Types.unitType)]
                    | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                        [(ident.idText, freshTypeVar range)]
                    | SynPat.Typed(typedInner, synType, _) ->
                        // Typed pattern like (name: NativeStr)
                        let annotatedType = resolveSynType env synType
                        match typedInner with
                        | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                            [(ident.idText, annotatedType)]
                        | _ -> [("_", annotatedType)]
                    | SynPat.Tuple(_, tuplePats, _, _) ->
                        tuplePats |> List.map (fun tuplePat ->
                            match tuplePat with
                            | SynPat.Named(SynIdent(ident, _), _, _, _) -> (ident.idText, freshTypeVar range)
                            | SynPat.Typed(SynPat.Named(SynIdent(ident, _), _, _, _), synType, _) ->
                                (ident.idText, resolveSynType env synType)
                            | _ -> ("_", freshTypeVar range))
                    | _ -> [("_", freshTypeVar range)]
                | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                    [(ident.idText, freshTypeVar range)]
                | SynPat.Const(SynConst.Unit, _) ->
                    // Unit literal - bind to dummy name
                    [("_", Types.unitType)]
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
/// the isMutable flag, and optionally a NativeLiteral for [<Literal>] bindings.
/// InlineBody is captured only for functions explicitly marked `inline` - this enables
/// escape analysis where allocations are lifted to the caller's frame.
/// PRD-13: preCreatedBinding allows recursive bindings to provide a pre-created Binding node
/// so that VarRefs can resolve to it before the body is checked.
let checkBinding
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (binding: SynBinding)
    (preCreatedBinding: SemanticNode option)
    : SemanticNode * InlineBody option * bool * NativeLiteral option =

    let (SynBinding(_, _, isInline, isMutable, attrs, _, _, headPat, returnInfo, expr, bindingRange, _, _)) = binding
    let range = rangeToSourceRange bindingRange
    let name = getBindingName binding
    // One measure variable per name for the whole binding (spec §Generalization of Measure
    // Variables): the names written in the parameter and return annotations are minted here, so
    // `(y: float<'u>) (z: float<'u>)` share `'u` and a use at two dimensions is CCS8040.
    let env =
        let rec annotations (p: SynPat) : SynType list =
            match p with
            | SynPat.Typed(inner, ty, _) -> ty :: annotations inner
            | SynPat.Paren(inner, _) -> annotations inner
            | SynPat.Tuple(_, ps, _, _) -> ps |> List.collect annotations
            | SynPat.LongIdent(_, _, _, SynArgPats.Pats ps, _, _) -> ps |> List.collect annotations
            | SynPat.Attrib(inner, _, _) -> annotations inner
            | _ -> []
        let returnAnnotation =
            match returnInfo with
            | Some (SynBindingReturnInfo(typeName = synType)) -> [ synType ]
            | None -> []
        let names = (annotations headPat @ returnAnnotation) |> List.collect (measureVariableNames env)
        withMeasureScope env names
    let declRoot =
        if hasEntryPointAttribute attrs then Some DeclRoot.EntryPoint
        elif hasHardwareModuleAttribute attrs then Some DeclRoot.HardwareModule
        elif hasKernelModuleAttribute attrs then Some DeclRoot.KernelModule
        else None
    let isLiteral = hasLiteralAttribute attrs
    let fidelityExtern = extractFidelityExternAttribute attrs

    // Extract literal value if this is a [<Literal>] binding with a constant expression
    let literalValue =
        if isLiteral then
            match expr with
            | SynExpr.Const(constant, _) ->
                match Literals.checkConst env constant with
                | Result.Ok (_, literal) -> Some literal
                | Result.Error _ -> None  // the failure is reported where the body is checked below
            | _ -> None  // Non-constant [<Literal>] - will be caught by type checker
        else
            None

    //-------------------------------------------------------------------------
    // PRD-13a: Tuple Destructuring
    // let (a, b) = expr  desugars to:
    //   let __tuple_N = expr
    //   let a = TupleGet(__tuple_N, 0)
    //   let b = TupleGet(__tuple_N, 1)
    //-------------------------------------------------------------------------
    let checkTupleDestructure () =
        // Extract element names from the tuple pattern
        let elementInfo = extractTupleElements (getHeadPattern binding)

        // Check the RHS expression - this gives us the tuple value
        let tupleExprNode = checkExpr env builder expr

        // Create fresh type variables for each tuple element
        let elementTypes = elementInfo |> List.map (fun (_, _) -> freshTypeVar range)

        // Constrain the RHS to be a tuple of the correct arity (reference tuple, not struct)
        let expectedTupleType = NativeType.TTuple(elementTypes, false)
        addConstraint (Constraint.Equals(tupleExprNode.Type, expectedTupleType, range)) env

        // Create a hidden binding for the tuple
        // Use NodeId.fresh() to get a unique identifier for the hidden name
        let hiddenName = sprintf "__tuple_%d" (NodeId.value (NodeId.fresh()))
        let hiddenBinding = builder.Create(
            SemanticKind.Binding(hiddenName, isMutable, false, None),
            tupleExprNode.Type,
            range,
            children = [tupleExprNode.Id])
        builder.SetParent(tupleExprNode.Id, hiddenBinding.Id)

        // Create TupleGet nodes and bindings for each element
        let elementBindings =
            elementInfo |> List.mapi (fun i (elemName, isWildcard) ->
                let elemType = elementTypes.[i]

                // Create VarRef to the hidden tuple
                let tupleRef = builder.Create(
                    SemanticKind.VarRef(hiddenName, Some hiddenBinding.Id),
                    tupleExprNode.Type,
                    range,
                    arena = env.CurrentArena)

                // Create TupleGet node
                let tupleGetNode = builder.Create(
                    SemanticKind.TupleGet(tupleRef.Id, i),
                    elemType,
                    range,
                    children = [tupleRef.Id])
                builder.SetParent(tupleRef.Id, tupleGetNode.Id)

                // Create binding for the element (unless wildcard)
                let bindingName = if isWildcard then sprintf "_discard_%d" i else elemName
                let elemBinding = builder.Create(
                    SemanticKind.Binding(bindingName, isMutable, false, None),
                    elemType,
                    range,
                    children = [tupleGetNode.Id])
                builder.SetParent(tupleGetNode.Id, elemBinding.Id)

                (elemName, elemType, elemBinding, isWildcard))

        // Create Sequential containing all bindings
        let allBindingNodes = hiddenBinding :: (elementBindings |> List.map (fun (_, _, b, _) -> b))
        let allBindingIds = allBindingNodes |> List.map (fun n -> n.Id)

        // The type of the Sequential is unit (the bindings introduce names but produce no value)
        let seqNode = builder.Create(
            SemanticKind.Sequential allBindingIds,
            Types.unitType,
            range,
            children = allBindingIds)

        // Set parents
        for bindingId in allBindingIds do
            builder.SetParent(bindingId, seqNode.Id)

        // Store element binding info in metadata for environment extension
        // Format: comma-separated "name:nodeId" pairs
        let elementBindingInfo =
            elementBindings
            |> List.filter (fun (_, _, _, isWildcard) -> not isWildcard)
            |> List.map (fun (name, _, binding, _) -> sprintf "%s:%d" name (NodeId.value binding.Id))
            |> String.concat ","
        let seqNodeWithMeta = builder.SetMetadata(seqNode.Id, "TupleBindings", MetadataValue.String elementBindingInfo)

        (seqNodeWithMeta, None, isMutable, None)

    // Check if this is a tuple pattern - handle it specially
    if name = TuplePatternMarker then
        checkTupleDestructure ()
    else

    // Check if this is a function definition (has parameters)
    match tryGetFunctionParams headPat env range with
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
        // For [<FidelityExtern>] bindings, the body is a placeholder (Unchecked.defaultof<T>)
        // that would be rejected by BCL filtering. Skip body checking and create a
        // placeholder node using the return type annotation. Alex resolves these via ExternCall.
        let bodyNode =
            match fidelityExtern with
            | Some _ ->
                let retType =
                    match returnInfo with
                    | Some (SynBindingReturnInfo(typeName = synType)) -> resolveSynType env synType
                    | None -> freshTypeVar range
                builder.Create(
                    SemanticKind.Literal(NativeLiteral.Unit),
                    retType,
                    range)
            | None ->
                checkExpr bodyEnv builder expr

        // Entry point constraint: string[] -> int
        // Per F# spec, [<EntryPoint>] functions must have signature: string[] -> int
        if declRoot = Some DeclRoot.EntryPoint then
            // Constrain parameter to string[] (argv)
            match lambdaParams with
            | [(_, paramTy, _)] ->
                let stringArrayType = NativeType.TApp(Types.arrayTyCon, [Types.stringType])
                addConstraint (Constraint.Equals(paramTy, stringArrayType, range)) env
            | _ -> ()  // Multiple or no params - unusual for entry point
            // Constrain return type to int
            addConstraint (Constraint.Equals(bodyNode.Type, Types.intType, range)) env

        // Build function type
        let paramTypes = lambdaParams |> List.map (fun (_, ty, _) -> ty)
        // For unit-parameterized functions like f(), the paramTypes might be empty
        // but it's still a function: unit -> returnType
        let funcType =
            if List.isEmpty paramTypes then
                mkFunctionType [Types.unitType] bodyNode.Type
            else
                mkFunctionType paramTypes bodyNode.Type

        // NOTE: Generalization disabled - it was causing type mismatches.
        // The proper fix requires smarter generalization (only top-level, not nested).
        // For now, rely on primitive operators having TForall in Intrinsics.

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
        
        // Architectural fix (January 2026): Mark Lambda body as SeparateFunction
        // The Lambda witness handles body emission; Alex's walk should skip it.
        // Pass capture count so SSA assignment starts body SSAs after capture extraction
        builder.SetEmissionStrategy(bodyNode.Id, EmissionStrategy.SeparateFunction (List.length captures))

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
                    SemanticKind.Binding(name, isMutable, false, declRoot),
                    funcType,
                    range,
                    children = [lambdaNode.Id])

        // Establish bidirectional parent-child link
        // Lambda's Parent field must point back to Binding for SSA name assignment
        builder.SetParent(lambdaNode.Id, bindingNode.Id)

        // Propagate [<FidelityExtern>] metadata for Farscape-generated native bindings
        match fidelityExtern with
        | Some (library, symbol) ->
            builder.SetMetadata(bindingNode.Id, "FidelityExtern.Library", MetadataValue.String library) |> ignore
            builder.SetMetadata(bindingNode.Id, "FidelityExtern.Symbol", MetadataValue.String symbol) |> ignore
        | None -> ()

        // An `inline` function's own body is never emitted: it is re-checked at every expansion
        // site with the site's types, so the variables its definition leaves open are quantified
        // by expansion. The marker lets the residual check (NativeService) skip its subtree.
        if isInline then
            builder.SetMetadata(bindingNode.Id, "Inline", MetadataValue.Bool true) |> ignore

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
                    // Architectural fix (January 2026): Mark Lambda body as SeparateFunction
                    // Eta-expanded lambdas have no captures
                    builder.SetEmissionStrategy(bodyId, EmissionStrategy.SeparateFunction 0)
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
                    SemanticKind.Binding(name, isMutable, false, declRoot),
                    finalExprNode.Type,
                    range,
                    children = [finalExprNode.Id])
        // Establish bidirectional parent-child link
        builder.SetParent(finalExprNode.Id, node.Id)

        // Propagate [<FidelityExtern>] metadata for Farscape-generated native bindings
        match fidelityExtern with
        | Some (library, symbol) ->
            builder.SetMetadata(node.Id, "FidelityExtern.Library", MetadataValue.String library) |> ignore
            builder.SetMetadata(node.Id, "FidelityExtern.Symbol", MetadataValue.String symbol) |> ignore
        | None -> ()

        // Module-level value bindings need MainPrologue strategy for SSA scoping.
        // These are emitted at the start of main - SSAs flow into main's body.
        // A quotation is not a value (D9): it is compile-time data the compiler reads, so a
        // binding that holds one is a declaration, never a module-init slot.
        let rec holdsQuotation (id: NodeId) =
            match Map.tryFind id builder.Nodes with
            | Some { Kind = SemanticKind.Quote _ } -> true
            | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> holdsQuotation inner
            | _ -> false
        if env.EnclosingFunction.IsNone && declRoot.IsNone && not (holdsQuotation finalExprNode.Id) then
            builder.SetEmissionStrategy(node.Id, EmissionStrategy.MainPrologue)

        (node, None, isMutable, literalValue)

//-------------------------------------------------------------------------
// Let/LetRec Handling
//-------------------------------------------------------------------------

/// Check a let-or-use binding
/// PRD-13: For recursive bindings (let rec), pre-create Binding nodes to get NodeIds
/// so that self-referential VarRefs can resolve correctly.
let checkLetOrUse
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (letOrUse: SynLetOrUse)
    (range: SourceRange)
    : SemanticNode =

    let bindings = letOrUse.Bindings
    let bodyExpr = letOrUse.Body

    // Helper: extend environment with binding results
    let extendEnvWithResults baseEnv bindingList (results: (SemanticNode * InlineBody option * bool * NativeLiteral option) list) =
        List.zip bindingList results
        |> List.fold (fun env (binding, (node: SemanticNode, inlineBodyOpt, isMutable, literalValueOpt)) ->
            let name = getBindingName binding
            // PRD-13a: Handle tuple destructuring
            if name = TuplePatternMarker then
                // Read tuple binding info from metadata
                match node.Metadata.TryFind "TupleBindings" with
                | Some (MetadataValue.String bindingInfo) when bindingInfo <> "" ->
                    // Parse "name1:nodeId1,name2:nodeId2,..."
                    bindingInfo.Split(',')
                    |> Array.fold (fun env part ->
                        let parts = part.Split(':')
                        if parts.Length = 2 then
                            let elemName = parts.[0]
                            let nodeIdVal = int parts.[1]
                            let elemNodeId = NodeId nodeIdVal
                            // Get the element type from the binding node
                            let elemType =
                                match builder.Nodes.TryFind elemNodeId with
                                | Some elemNode -> elemNode.Type
                                | None -> freshTypeVar node.Range  // Fallback
                            addBinding elemName elemType isMutable (Some elemNodeId) env.EnclosingFunction.IsNone env
                        else
                            env
                    ) env
                | _ ->
                    // No bindings to add (all wildcards)
                    env
            else
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
                let declRoot =
                    if hasEntryPointAttribute attrs then Some DeclRoot.EntryPoint
                    elif hasHardwareModuleAttribute attrs then Some DeclRoot.HardwareModule
                    elif hasKernelModuleAttribute attrs then Some DeclRoot.KernelModule
                    else None
                let node = builder.Create(
                    SemanticKind.Binding(name, isMutable, true, declRoot),
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
                checkBinding checkExpr envWithBindings builder binding (Some preCreatedNode))

        let bindingNodes = bindingResults |> List.map (fun (node, _, _, _) -> node)
        let bodyEnv = extendEnvWithResults envWithBindings bindings bindingResults
        let bodyNode = checkExpr bodyEnv builder bodyExpr
        buildSequential bindingNodes bodyNode

    | false ->
        // NON-RECURSIVE BINDINGS: Standard sequential processing
        let bindingResults =
            bindings |> List.map (fun binding ->
                checkBinding checkExpr env builder binding None)

        let bindingNodes = bindingResults |> List.map (fun (node, _, _, _) -> node)
        let bodyEnv = extendEnvWithResults env bindings bindingResults
        let bodyNode = checkExpr bodyEnv builder bodyExpr
        buildSequential bindingNodes bodyNode

//-------------------------------------------------------------------------
// Match Clause Handling
//-------------------------------------------------------------------------

/// Generate field extraction nodes for record pattern bindings
/// Returns list of (bindingName, extractionNodeId) pairs
let rec private generatePatternExtractions
    (builder: NodeBuilder)
    (pattern: Pattern)
    (sourceNodeId: NodeId)
    (range: SourceRange)
    (arena: ArenaAffinity)
    : (string * NodeId) list =

    match pattern with
    | Pattern.Var (name, _ty) ->
        // Simple variable binding - the source IS the value
        [(name, sourceNodeId)]

    | Pattern.Record (fields, _recordType) ->
        // Record pattern: extract each field and recurse into nested patterns
        fields
        |> List.collect (fun (fieldName, fieldPattern) ->
            // Create FieldGet to extract this field from the source
            // Type will be inferred from the nested pattern
            let fieldType =
                match fieldPattern with
                | Pattern.Var (_, ty) -> ty
                | _ -> freshTypeVar range  // Fresh type var for nested patterns
            let fieldGetNode = builder.Create(
                SemanticKind.FieldGet(sourceNodeId, fieldName),
                fieldType,
                range,
                arena = arena,
                children = [sourceNodeId])
            // Recurse into the field pattern with the FieldGet as the new source
            generatePatternExtractions builder fieldPattern fieldGetNode.Id range arena)

    | Pattern.Tuple _elements ->
        // Tuple pattern: would need TupleGet (not yet implemented for pattern matching)
        // For now, fall through to simple binding
        []

    | Pattern.Union (_caseName, _tagIndex, payloadOpt, _unionType) ->
        // Union pattern: would need payload extraction
        // For now, handle payload if present
        match payloadOpt with
        | Some payload -> generatePatternExtractions builder payload sourceNodeId range arena
        | None -> []

    | Pattern.As (inner, _name) ->
        // As pattern: recurse into inner
        generatePatternExtractions builder inner sourceNodeId range arena

    | Pattern.Or (left, _right) ->
        // Or pattern: both branches bind same vars, use left
        generatePatternExtractions builder left sourceNodeId range arena

    | Pattern.And (left, right) ->
        // And pattern: combine bindings from both
        generatePatternExtractions builder left sourceNodeId range arena @
        generatePatternExtractions builder right sourceNodeId range arena

    | Pattern.Array elements ->
        // Array pattern: would need indexed access
        elements
        |> List.collect (fun elem -> generatePatternExtractions builder elem sourceNodeId range arena)

    | Pattern.Const _ | Pattern.Wildcard | Pattern.Null | Pattern.IsType _ | Pattern.Exception _ ->
        // No bindings for these patterns
        []

/// Check a match clause with scrutinee ID for record pattern field extraction
let checkMatchClause
    (checkExpr: CheckExprFn)
    (checkPattern: CheckPatternFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (scrutineeId: NodeId)
    (scrutineeTy: NativeType)
    (resultTy: NativeType)
    (clause: SynMatchClause)
    : MatchCase =

    let (SynMatchClause(pat, guardOpt, bodyExpr, _, _, _)) = clause
    let range = rangeToSourceRange bodyExpr.Range

    // Check pattern and extract bindings
    let (pattern, patBindings) = checkPattern env pat scrutineeTy range

    // Generate field extraction nodes for record patterns
    // This creates FieldGet nodes that provide values for pattern bindings
    let extractions = generatePatternExtractions builder pattern scrutineeId range env.CurrentArena

    // Create a map from binding name to extraction NodeId
    let extractionMap = extractions |> Map.ofList

    // Create PSG nodes for pattern bindings and add to environment
    // For record patterns, the PatternBinding's "value" comes from the FieldGet
    // Following ML/FStar convention: pattern binding IS the definition
    // Collect NodeIds for inclusion in MatchCase (enables SSA assignment traversal)
    let (bodyEnv, patternBindingIds, _fieldGetIds) =
        patBindings
        |> List.fold (fun (env, bindingIds, fieldIds) (name, ty) ->
            // Check if this binding has a field extraction
            let (patternBindingNode, newFieldIds) =
                match Map.tryFind name extractionMap with
                | Some fieldGetId ->
                    // Create PatternBinding as a child of the FieldGet
                    // This connects the binding to its extracted value
                    let node = builder.Create(
                        SemanticKind.PatternBinding(name),
                        ty,
                        range,
                        arena = env.CurrentArena,
                        children = [fieldGetId])
                    (node, fieldGetId :: fieldIds)
                | None ->
                    // No extraction needed (e.g., simple variable pattern matching scrutinee directly)
                    let node = builder.Create(
                        SemanticKind.PatternBinding(name),
                        ty,
                        range,
                        arena = env.CurrentArena)
                    (node, fieldIds)
            let env' = addBinding name ty false (Some patternBindingNode.Id) env.EnclosingFunction.IsNone env
            (env', patternBindingNode.Id :: bindingIds, newFieldIds)
        ) (env, [], [])
    let patternBindingIds = List.rev patternBindingIds  // Preserve order

    // Check guard if present
    let guardNode = guardOpt |> Option.map (checkExpr bodyEnv builder)
    guardNode |> Option.iter (fun g ->
        addConstraint (Constraint.Equals(g.Type, Types.boolType, range)) env)

    // Check body
    let bodyNode = checkExpr bodyEnv builder bodyExpr

    // Body must match result type
    addConstraint (Constraint.Equals(bodyNode.Type, resultTy, range)) env

    { Pattern = pattern
      PatternBindings = patternBindingIds
      Guard = guardNode |> Option.map (fun n -> n.Id)
      Body = bodyNode.Id }


//-------------------------------------------------------------------------
// Set Operations: Assignment expressions
//-------------------------------------------------------------------------

/// Check Set: target <- value (general assignment)
let checkSet
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (targetExpr: SynExpr)
    (valueExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let targetNode = checkExpr env builder targetExpr
    let valueNode = checkExpr env builder valueExpr
    addConstraint (Constraint.Equals(targetNode.Type, valueNode.Type, range)) env
    builder.Create(
        SemanticKind.Set(targetNode.Id, valueNode.Id),
        Types.unitType,
        range,
        children = [targetNode.Id; valueNode.Id])

/// Check DotSet: expr.field <- value
let checkDotSet
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (objExpr: SynExpr)
    (longId: Ident list)
    (valueExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let objNode = checkExpr env builder objExpr
    let valueNode = checkExpr env builder valueExpr
    let fieldName = longId |> List.map (fun id -> id.idText) |> String.concat "."
    builder.Create(
        SemanticKind.FieldSet(objNode.Id, fieldName, valueNode.Id),
        Types.unitType,
        range,
        children = [objNode.Id; valueNode.Id])

/// Check LongIdentSet: Module.value <- expr
let checkLongIdentSet
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (longId: Ident list)
    (valueExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let valueNode = checkExpr env builder valueExpr
    let parts = longId |> List.map (fun id -> id.idText)
    let targetName = parts |> String.concat "."
    match tryLookupBinding targetName env with
    | Some binding when binding.IsMutable ->
        let targetNode = builder.Create(
            SemanticKind.VarRef(targetName, binding.NodeId),
            binding.Type,
            range)
        builder.Create(
            SemanticKind.Set(targetNode.Id, valueNode.Id),
            Types.unitType,
            range,
            children = [targetNode.Id; valueNode.Id])
    | _ ->
        // `r.Field <- v` (or `Module.r.Field <- v`): the longest proper prefix that names a
        // binding is the record, the remaining parts are a field path. Records are memref-
        // backed, so the store mutates the record in place, parameter or not.
        let rec tryPrefix (k: int) =
            if k < 1 then None
            else
                let prefix = parts |> List.take k |> String.concat "."
                match tryLookupBinding prefix env with
                | Some binding when binding.NativeLiteral.IsNone -> Some (binding, prefix, parts |> List.skip k)
                | _ -> tryPrefix (k - 1)
        match (if parts.Length >= 2 then tryPrefix (parts.Length - 1) else None) with
        | Some (binding, prefix, fieldPath) ->
            let baseNode = builder.Create(
                SemanticKind.VarRef(prefix, binding.NodeId),
                binding.Type,
                range,
                arena = env.CurrentArena)
            // Walk the intermediate fields with FieldGet; the last one is the FieldSet target.
            let middle = fieldPath |> List.take (fieldPath.Length - 1)
            let lastField = List.last fieldPath
            let (objNode, objType) =
                middle |> List.fold (fun (node: SemanticNode, ty: NativeType) fieldName ->
                    let fieldTy = Types.resolveFieldType (applySubst ty) fieldName env range
                    let fieldNode = builder.Create(
                        SemanticKind.FieldGet(node.Id, fieldName),
                        fieldTy,
                        range,
                        children = [node.Id])
                    builder.SetParent(node.Id, fieldNode.Id)
                    (fieldNode, fieldTy)
                ) (baseNode, applySubst binding.Type)
            let lastFieldTy = Types.resolveFieldType (applySubst objType) lastField env range
            addConstraint (Constraint.Equals(lastFieldTy, valueNode.Type, range)) env
            let setNode = builder.Create(
                SemanticKind.FieldSet(objNode.Id, lastField, valueNode.Id),
                Types.unitType,
                range,
                children = [objNode.Id; valueNode.Id])
            builder.SetParent(objNode.Id, setNode.Id)
            builder.SetParent(valueNode.Id, setNode.Id)
            setNode
        | None ->
            builder.Create(
                SemanticKind.Error $"Cannot assign to '{targetName}' (not found or not mutable)",
                NativeType.TError "assignment error",
                range)

/// Check DotNamedIndexedPropertySet: obj.Prop[idx] <- value
let checkDotNamedIndexedPropertySet
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (objExpr: SynExpr)
    (longId: Ident list)
    (indexExpr: SynExpr)
    (valueExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let objNode = checkExpr env builder objExpr
    let indexNode = checkExpr env builder indexExpr
    let valueNode = checkExpr env builder valueExpr
    let propName = longId |> List.map (fun id -> id.idText) |> String.concat "."

    addConstraint (Constraint.HasMember(objNode.Type, propName, freshTypeVar range, range)) env

    builder.Create(
        SemanticKind.NamedIndexedPropertySet(objNode.Id, propName, indexNode.Id, valueNode.Id),
        Types.unitType,
        range,
        children = [objNode.Id; indexNode.Id; valueNode.Id])
