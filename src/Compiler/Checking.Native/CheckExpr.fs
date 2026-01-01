// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Expression type checking for the native type checker.
/// Produces SemanticNode with types ATTACHED during construction.
module FSharp.Native.Compiler.Checking.Native.CheckExpr

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Text
open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.NativeGlobals
open FSharp.Native.Compiler.Checking.Native.UnionFind
open FSharp.Native.Compiler.Checking.Native.Unify
open FSharp.Native.Compiler.Checking.Native.SemanticGraph

//-------------------------------------------------------------------------
// Type Environment
//-------------------------------------------------------------------------

/// A binding in the type environment
type Binding = {
    Name: string
    Type: NativeType
    IsMutable: bool
    NodeId: NodeId option  // Reference to definition node
}

/// The type checking environment
[<NoComparison; NoEquality>]
type TypeEnv = {
    /// Global type information
    Globals: NativeGlobals
    /// Local variable bindings (name -> type)
    Bindings: Map<string, Binding>
    /// Type definitions (name -> TypeConRef)
    TypeDefs: Map<string, TypeConRef>
    /// Current constraints being collected
    mutable Constraints: Constraint list
    /// Current arena affinity
    CurrentArena: ArenaAffinity
    /// Enclosing function return type (for return checking)
    ExpectedReturnType: NativeType option
}

/// Create an empty type environment with globals
let createTypeEnv (globals: NativeGlobals) : TypeEnv = {
    Globals = globals
    Bindings = Map.empty
    TypeDefs = Map.empty
    Constraints = []
    CurrentArena = ArenaAffinity.CurrentActor
    ExpectedReturnType = None
}

/// Add a binding to the environment
let addBinding (name: string) (ty: NativeType) (isMutable: bool) (nodeId: NodeId option) (env: TypeEnv) : TypeEnv =
    let binding = { Name = name; Type = ty; IsMutable = isMutable; NodeId = nodeId }
    { env with Bindings = Map.add name binding env.Bindings }

/// Look up a binding
let tryLookupBinding (name: string) (env: TypeEnv) : Binding option =
    Map.tryFind name env.Bindings

/// Add a constraint to the environment
let addConstraint (c: Constraint) (env: TypeEnv) : unit =
    env.Constraints <- c :: env.Constraints

//-------------------------------------------------------------------------
// Range Conversion
//-------------------------------------------------------------------------

/// Convert FCS range to our SourceRange
let rangeToSourceRange (r: range) : SourceRange = {
    File = r.FileName
    Start = { Line = r.StartLine; Column = r.StartColumn }
    End = { Line = r.EndLine; Column = r.EndColumn }
}

//-------------------------------------------------------------------------
// Constant Type Inference
//-------------------------------------------------------------------------

/// Get the type of a constant
let rec typeOfConst (globals: NativeGlobals) (c: SynConst) : NativeType =
    match c with
    | SynConst.Unit -> globals.UnitType
    | SynConst.Bool _ -> globals.BoolType
    | SynConst.SByte _ -> Types.int8Type
    | SynConst.Byte _ -> Types.uint8Type
    | SynConst.Int16 _ -> Types.int16Type
    | SynConst.UInt16 _ -> Types.uint16Type
    | SynConst.Int32 _ -> globals.IntType
    | SynConst.UInt32 _ -> Types.uintType
    | SynConst.Int64 _ -> globals.Int64Type
    | SynConst.UInt64 _ -> Types.uint64Type
    | SynConst.IntPtr _ -> Types.nintType
    | SynConst.UIntPtr _ -> Types.unintType
    | SynConst.Single _ -> Types.float32Type
    | SynConst.Double _ -> globals.FloatType
    | SynConst.Char _ -> globals.CharType
    | SynConst.Decimal _ -> Types.decimalType
    | SynConst.String _ -> globals.StringType
    | SynConst.Bytes _ -> mkArrayType Types.uint8Type
    | SynConst.UInt16s _ -> mkArrayType Types.uint16Type
    | SynConst.Measure(innerConst, _, synMeasure, _) ->
        // For now, just use the base type; measure annotation is tracked separately
        // Full measure type would be: TMeasure applied to base type
        let baseType = typeOfConst globals innerConst
        // In future: wrap with measure type based on synMeasure
        let _ = synMeasure  // Suppress warning
        baseType
    | SynConst.UserNum(_, suffix) ->
        // UserNum with suffix - "I" is bigint, others are user-defined
        match suffix with
        | "I" -> globals.IntType  // Treat bigint as int for now (full bigint support later)
        | _ -> globals.IntType  // Fallback
    | SynConst.SourceIdentifier _ -> globals.StringType

/// Convert SynConst to LiteralValue
let rec constToLiteral (c: SynConst) : LiteralValue =
    match c with
    | SynConst.Unit -> LiteralValue.Unit
    | SynConst.Bool b -> LiteralValue.Bool b
    | SynConst.SByte v -> LiteralValue.Int8 v
    | SynConst.Byte v -> LiteralValue.UInt8 v
    | SynConst.Int16 v -> LiteralValue.Int16 v
    | SynConst.UInt16 v -> LiteralValue.UInt16 v
    | SynConst.Int32 v -> LiteralValue.Int32 v
    | SynConst.UInt32 v -> LiteralValue.UInt32 v
    | SynConst.Int64 v -> LiteralValue.Int64 v
    | SynConst.UInt64 v -> LiteralValue.UInt64 v
    | SynConst.IntPtr v -> LiteralValue.NativeInt(nativeint v)
    | SynConst.UIntPtr v -> LiteralValue.UNativeInt(unativeint v)
    | SynConst.Single v -> LiteralValue.Float32 v
    | SynConst.Double v -> LiteralValue.Float64 v
    | SynConst.Char v -> LiteralValue.Char v
    | SynConst.Decimal v -> LiteralValue.Decimal v
    | SynConst.String(s, _, _) -> LiteralValue.String s
    | SynConst.Measure(innerConst, _, _, _) -> constToLiteral innerConst
    | SynConst.UserNum(value, suffix) ->
        // UserNum is for bigint (I suffix) or user-defined numeric types
        match suffix with
        | "I" -> LiteralValue.BigInt value
        | _ -> LiteralValue.String value  // Fallback for other user-defined types
    | SynConst.SourceIdentifier(_, value, _) -> LiteralValue.String value
    | SynConst.Bytes(bytes, _, _) -> LiteralValue.ByteArray bytes
    | SynConst.UInt16s values -> LiteralValue.UInt16Array values

//-------------------------------------------------------------------------
// Expression Checking
//-------------------------------------------------------------------------

/// Check an expression and produce a SemanticNode with type attached.
/// This is the core of the native type checker.
let rec checkExpr (env: TypeEnv) (builder: NodeBuilder) (syn: SynExpr) : SemanticNode =
    let range = rangeToSourceRange syn.Range

    match syn with
    //---------------------------------------------------------------------
    // Literals
    //---------------------------------------------------------------------
    | SynExpr.Const(constant, _) ->
        let ty = typeOfConst env.Globals constant
        let lit = constToLiteral constant
        builder.Create(
            SemanticKind.Literal lit,
            ty,
            range,
            arena = env.CurrentArena,
            layout = layoutOf ty)

    //---------------------------------------------------------------------
    // Parenthesized expressions (transparent)
    //---------------------------------------------------------------------
    | SynExpr.Paren(innerExpr, _, _, _) ->
        checkExpr env builder innerExpr

    //---------------------------------------------------------------------
    // Variable references
    //---------------------------------------------------------------------
    | SynExpr.Ident(ident) ->
        let name = ident.idText
        match tryLookupBinding name env with
        | Some binding ->
            builder.Create(
                SemanticKind.VarRef(name, binding.NodeId),
                binding.Type,
                range,
                arena = env.CurrentArena)
        | None ->
            // Unknown identifier - create error node
            builder.Create(
                SemanticKind.Error $"Unknown identifier: {name}",
                NativeType.TError $"Unknown: {name}",
                range)

    | SynExpr.LongIdent(_, longDotId, _, _) ->
        let name = longDotId.LongIdent |> List.map (fun id -> id.idText) |> String.concat "."
        // TODO: Handle qualified names properly
        match tryLookupBinding name env with
        | Some binding ->
            builder.Create(
                SemanticKind.VarRef(name, binding.NodeId),
                binding.Type,
                range,
                arena = env.CurrentArena)
        | None ->
            // Could be a module-qualified name - for now, create a placeholder
            let resultTy = freshTypeVar range
            builder.Create(
                SemanticKind.VarRef(name, None),
                resultTy,
                range,
                arena = env.CurrentArena)

    //---------------------------------------------------------------------
    // Type annotations
    //---------------------------------------------------------------------
    | SynExpr.Typed(innerExpr, synType, _) ->
        let innerNode = checkExpr env builder innerExpr
        let annotatedTy = checkSynType env synType
        // Add equality constraint
        addConstraint (Constraint.Equals(innerNode.Type, annotatedTy, range)) env
        builder.Create(
            SemanticKind.TypeAnnotation(innerNode.Id, annotatedTy),
            annotatedTy,
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // Tuples
    //---------------------------------------------------------------------
    | SynExpr.Tuple(isStruct, exprs, _, _) ->
        let elementNodes = exprs |> List.map (checkExpr env builder)
        let elementTypes = elementNodes |> List.map (fun n -> n.Type)
        let tupleType = NativeType.TTuple(elementTypes, isStruct)
        let childIds = elementNodes |> List.map (fun n -> n.Id)
        builder.Create(
            SemanticKind.TupleExpr childIds,
            tupleType,
            range,
            children = childIds)

    //---------------------------------------------------------------------
    // Function application
    //---------------------------------------------------------------------
    | SynExpr.App(_, _isInfix, funcExpr, argExpr, _) ->
        let funcNode = checkExpr env builder funcExpr
        let argNode = checkExpr env builder argExpr

        // Generate constraint: funcType = argType -> ?result
        let resultTy = freshTypeVar range
        addConstraint (Constraint.Equals(
            funcNode.Type,
            NativeType.TFun(argNode.Type, resultTy),
            range)) env

        // TODO: Check for SRTP (will be done in SRTPResolution.fs)

        builder.Create(
            SemanticKind.Application(funcNode.Id, [argNode.Id]),
            resultTy,
            range,
            children = [funcNode.Id; argNode.Id])

    //---------------------------------------------------------------------
    // Lambda expressions
    //---------------------------------------------------------------------
    | SynExpr.Lambda(_, _, args, bodyExpr, _, _, _) ->
        // Extract parameter names and create fresh type variables
        let paramBindings = extractLambdaParams env args range

        // Create new environment with parameters
        let bodyEnv =
            paramBindings
            |> List.fold (fun env (name, ty) -> addBinding name ty false None env) env

        // Check body
        let bodyNode = checkExpr bodyEnv builder bodyExpr

        // Build function type
        let paramTypes = paramBindings |> List.map snd
        let funcType = mkFunctionType paramTypes bodyNode.Type

        builder.Create(
            SemanticKind.Lambda(paramBindings, bodyNode.Id),
            funcType,
            range,
            children = [bodyNode.Id])

    //---------------------------------------------------------------------
    // Let bindings
    //---------------------------------------------------------------------
    | SynExpr.LetOrUse(letOrUse) ->
        checkLetOrUse env builder letOrUse range

    //---------------------------------------------------------------------
    // Sequential expressions
    //---------------------------------------------------------------------
    | SynExpr.Sequential(_, _, expr1, expr2, _, _) ->
        let node1 = checkExpr env builder expr1
        let node2 = checkExpr env builder expr2
        builder.Create(
            SemanticKind.Sequential [node1.Id; node2.Id],
            node2.Type,  // Result type is the last expression
            range,
            children = [node1.Id; node2.Id])

    //---------------------------------------------------------------------
    // If-then-else
    //---------------------------------------------------------------------
    | SynExpr.IfThenElse(condExpr, thenExpr, elseExprOpt, _, _, _, _) ->
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

    //---------------------------------------------------------------------
    // While loops
    //---------------------------------------------------------------------
    | SynExpr.While(_, guardExpr, bodyExpr, _) ->
        let guardNode = checkExpr env builder guardExpr
        let bodyNode = checkExpr env builder bodyExpr

        // Guard must be bool
        addConstraint (Constraint.Equals(guardNode.Type, env.Globals.BoolType, range)) env

        builder.Create(
            SemanticKind.WhileLoop(guardNode.Id, bodyNode.Id),
            env.Globals.UnitType,  // While always returns unit
            range,
            children = [guardNode.Id; bodyNode.Id])

    //---------------------------------------------------------------------
    // For loops
    //---------------------------------------------------------------------
    | SynExpr.For(_, _, ident, _, startExpr, direction, endExpr, bodyExpr, _) ->
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

    //---------------------------------------------------------------------
    // Match expressions
    //---------------------------------------------------------------------
    | SynExpr.Match(_, scrutinee, clauses, _, _) ->
        let scrutineeNode = checkExpr env builder scrutinee
        let resultTy = freshTypeVar range

        let matchCases = clauses |> List.map (fun clause ->
            checkMatchClause env builder scrutineeNode.Type resultTy clause)

        builder.Create(
            SemanticKind.Match(scrutineeNode.Id, matchCases),
            resultTy,
            range,
            children = scrutineeNode.Id :: (matchCases |> List.map (fun c -> c.Body)))

    //---------------------------------------------------------------------
    // Record expressions
    //---------------------------------------------------------------------
    | SynExpr.Record(_, copyInfo, fields, _) ->
        let copyNode = copyInfo |> Option.map (fun (expr, _) -> checkExpr env builder expr)
        let fieldNodes = fields |> List.choose (fun field ->
            match field with
            | SynExprRecordField((fieldId, _), _, Some expr, _, _) ->
                let fieldName = fieldId.LongIdent |> List.map (fun id -> id.idText) |> String.concat "."
                let exprNode = checkExpr env builder expr
                Some (fieldName, exprNode.Id)
            | _ -> None)

        // TODO: Infer record type from fields
        let recordTy = freshTypeVar range

        builder.Create(
            SemanticKind.RecordExpr(fieldNodes, copyNode |> Option.map (fun n -> n.Id)),
            recordTy,
            range,
            children = (copyNode |> Option.map (fun n -> [n.Id]) |> Option.defaultValue []) @ (fieldNodes |> List.map snd))

    //---------------------------------------------------------------------
    // Array/list expressions
    //---------------------------------------------------------------------
    | SynExpr.ArrayOrList(isArray, exprs, _) ->
        let elementNodes = exprs |> List.map (checkExpr env builder)
        let elementTy =
            match elementNodes with
            | [] -> freshTypeVar range
            | first :: rest ->
                // All elements must have same type
                for node in rest do
                    addConstraint (Constraint.Equals(first.Type, node.Type, range)) env
                first.Type

        let collectionTy =
            if isArray then mkArrayType elementTy
            else mkListType elementTy

        let childIds = elementNodes |> List.map (fun n -> n.Id)
        let kind = if isArray then SemanticKind.ArrayExpr childIds else SemanticKind.ListExpr childIds

        builder.Create(kind, collectionTy, range, children = childIds)

    //---------------------------------------------------------------------
    // Try-with expressions
    //---------------------------------------------------------------------
    | SynExpr.TryWith(tryExpr, withCases, _, _, _, _) ->
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

    //---------------------------------------------------------------------
    // Try-finally expressions
    //---------------------------------------------------------------------
    | SynExpr.TryFinally(tryExpr, finallyExpr, _, _, _, _) ->
        let tryNode = checkExpr env builder tryExpr
        let finallyNode = checkExpr env builder finallyExpr
        builder.Create(
            SemanticKind.TryFinally(tryNode.Id, finallyNode.Id),
            tryNode.Type,
            range,
            children = [tryNode.Id; finallyNode.Id])

    //---------------------------------------------------------------------
    // Field access
    //---------------------------------------------------------------------
    | SynExpr.DotGet(expr, _, longDotId, _) ->
        let exprNode = checkExpr env builder expr
        let fieldName = longDotId.LongIdent |> List.map (fun id -> id.idText) |> String.concat "."
        let resultTy = freshTypeVar range

        // Add HasMember constraint for SRTP
        addConstraint (Constraint.HasMember(exprNode.Type, fieldName, resultTy, range)) env

        builder.Create(
            SemanticKind.FieldGet(exprNode.Id, fieldName),
            resultTy,
            range,
            children = [exprNode.Id])

    //---------------------------------------------------------------------
    // Assignment
    //---------------------------------------------------------------------
    | SynExpr.Set(targetExpr, valueExpr, _) ->
        let targetNode = checkExpr env builder targetExpr
        let valueNode = checkExpr env builder valueExpr
        addConstraint (Constraint.Equals(targetNode.Type, valueNode.Type, range)) env
        builder.Create(
            SemanticKind.Set(targetNode.Id, valueNode.Id),
            env.Globals.UnitType,
            range,
            children = [targetNode.Id; valueNode.Id])

    //---------------------------------------------------------------------
    // Do expressions
    //---------------------------------------------------------------------
    | SynExpr.Do(expr, _) ->
        checkExpr env builder expr

    //---------------------------------------------------------------------
    // Null (should be avoided in native F#)
    //---------------------------------------------------------------------
    | SynExpr.Null _ ->
        builder.Create(
            SemanticKind.Error "null is not supported in native F#",
            NativeType.TError "null not supported",
            range)

    //---------------------------------------------------------------------
    // Quote expressions
    //---------------------------------------------------------------------
    | SynExpr.Quote(_, isRaw, quotedExpr, _, _) ->
        let innerNode = checkExpr env builder quotedExpr
        // Typed quotation (<@ @>) has type Expr<'T>
        // Raw quotation (<@@ @@>) has type Expr<obj> (erased)
        let quotedType =
            if isRaw then mkExprType (freshTypeVar range)  // Raw: Expr<_>
            else mkExprType innerNode.Type  // Typed: Expr<'T>
        builder.Create(
            SemanticKind.Quote(innerNode.Id, not isRaw),
            quotedType,
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // Interpolated strings
    //---------------------------------------------------------------------
    | SynExpr.InterpolatedString(contents, _synStringKind, _) ->
        // Process each part of the interpolated string
        let mutable exprNodeIds = []
        let parts =
            contents |> List.map (fun part ->
                match part with
                | SynInterpolatedStringPart.String(value, _) ->
                    InterpolatedPart.StringPart value
                | SynInterpolatedStringPart.FillExpr(fillExpr, _qualifiers) ->
                    // Type check the expression in the hole
                    let exprNode = checkExpr env builder fillExpr
                    exprNodeIds <- exprNode.Id :: exprNodeIds
                    InterpolatedPart.ExprPart exprNode.Id
            )

        builder.Create(
            SemanticKind.InterpolatedString parts,
            env.Globals.StringType,
            range,
            children = List.rev exprNodeIds)

    //---------------------------------------------------------------------
    // Fallback for unhandled expressions
    //---------------------------------------------------------------------
    | _ ->
        builder.Create(
            SemanticKind.Error $"Unhandled expression: {syn.GetType().Name}",
            NativeType.TError "unhandled",
            range)

//-------------------------------------------------------------------------
// Helper Functions
//-------------------------------------------------------------------------

/// Extract parameter names from lambda arguments
and extractLambdaParams (env: TypeEnv) (args: SynSimplePats) (range: SourceRange) : (string * NativeType) list =
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

/// Check a let-or-use binding
and checkLetOrUse (env: TypeEnv) (builder: NodeBuilder) (letOrUse: SynLetOrUse) (range: SourceRange) : SemanticNode =
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

    // Check each binding
    let bindingNodes = bindings |> List.map (fun binding ->
        checkBinding bindingEnv builder binding)

    // Add bindings to environment for body
    let bodyEnv =
        List.zip bindings bindingNodes
        |> List.fold (fun env (binding, node) ->
            let name = getBindingName binding
            let isMutable = isBindingMutable binding
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

/// Get the name from a binding
and getBindingName (binding: SynBinding) : string =
    let (SynBinding(_, _, _, _, _, _, _, headPat, _, _, _, _, _)) = binding
    match headPat with
    | SynPat.Named(SynIdent(ident, _), _, _, _) -> ident.idText
    | SynPat.LongIdent(longDotId, _, _, _, _, _) ->
        longDotId.LongIdent |> List.last |> fun id -> id.idText
    | _ -> "_"

/// Check if a binding is mutable
and isBindingMutable (binding: SynBinding) : bool =
    let (SynBinding(_, _, _, isMutable, _, _, _, _, _, _, _, _, _)) = binding
    isMutable

/// Extract function parameters from a LongIdent pattern
/// For `let f x y = body`, returns Some [(x, ty); (y, ty)]
/// For `let x = body`, returns None
and tryGetFunctionParams (headPat: SynPat) (_env: TypeEnv) (range: SourceRange) : (string * NativeType) list option =
    match headPat with
    | SynPat.LongIdent(_, _, _, argPats, _, _) ->
        match argPats with
        | SynArgPats.Pats pats when not (List.isEmpty pats) ->
            // Has parameters - this is a function definition
            let params = pats |> List.collect (fun pat ->
                match pat with
                | SynPat.Paren(innerPat, _) ->
                    // Parenthesized pattern like (x, y) or ()
                    match innerPat with
                    | SynPat.Const(SynConst.Unit, _) ->
                        // () parameter - unit type, no binding name
                        []  // Don't create a parameter for unit
                    | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                        [(ident.idText, freshTypeVar range)]
                    | SynPat.Tuple(_, pats, _, _) ->
                        pats |> List.map (fun p ->
                            match p with
                            | SynPat.Named(SynIdent(id, _), _, _, _) -> (id.idText, freshTypeVar range)
                            | _ -> ("_", freshTypeVar range))
                    | _ -> [("_", freshTypeVar range)]
                | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                    [(ident.idText, freshTypeVar range)]
                | SynPat.Const(SynConst.Unit, _) ->
                    []  // Unit literal - no parameter binding
                | _ -> [("_", freshTypeVar range)]
            )
            Some params
        | _ -> None
    | _ -> None

/// Check a single binding
and checkBinding (env: TypeEnv) (builder: NodeBuilder) (binding: SynBinding) : SemanticNode =
    let (SynBinding(_, _, _, isMutable, _, _, _, headPat, _, expr, bindingRange, _, _)) = binding
    let range = rangeToSourceRange bindingRange
    let name = getBindingName binding

    // Check if this is a function definition (has parameters)
    match tryGetFunctionParams headPat env range with
    | Some paramBindings ->
        // This is a function definition like `let f x = body` or `let f() = body`
        // Create a Lambda node wrapping the body

        // Add parameters to environment for checking body
        let bodyEnv =
            paramBindings
            |> List.fold (fun env (paramName, paramTy) -> addBinding paramName paramTy false None env) env

        // Check body with extended environment
        let bodyNode = checkExpr bodyEnv builder expr

        // Build function type
        let paramTypes = paramBindings |> List.map snd
        // For unit-parameterized functions like f(), the paramTypes might be empty
        // but it's still a function: unit -> returnType
        let funcType =
            if List.isEmpty paramTypes then
                mkFunctionType [env.Globals.UnitType] bodyNode.Type
            else
                mkFunctionType paramTypes bodyNode.Type

        // Create Lambda node
        let lambdaNode = builder.Create(
            SemanticKind.Lambda(paramBindings, bodyNode.Id),
            funcType,
            range,
            children = [bodyNode.Id])

        // Create Binding node wrapping the Lambda
        builder.Create(
            SemanticKind.Binding(name, isMutable, false),
            funcType,
            range,
            children = [lambdaNode.Id])

    | None ->
        // Regular value binding
        let exprNode = checkExpr env builder expr
        builder.Create(
            SemanticKind.Binding(name, isMutable, false),
            exprNode.Type,
            range,
            children = [exprNode.Id])

/// Check a match clause
and checkMatchClause (env: TypeEnv) (builder: NodeBuilder) (scrutineeTy: NativeType) (resultTy: NativeType) (clause: SynMatchClause) : MatchCase =
    let (SynMatchClause(pat, guardOpt, bodyExpr, _, _, _)) = clause
    let range = rangeToSourceRange bodyExpr.Range

    // Check pattern and extract bindings
    let (pattern, patBindings) = checkPattern env pat scrutineeTy range

    // Add pattern bindings to environment
    let bodyEnv =
        patBindings
        |> List.fold (fun env (name, ty) -> addBinding name ty false None env) env

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

/// Check a pattern and return bindings
and checkPattern (env: TypeEnv) (pat: SynPat) (expectedTy: NativeType) (range: SourceRange) : Pattern * (string * NativeType) list =
    match pat with
    | SynPat.Const(constant, _) ->
        (Pattern.Const(constToLiteral constant), [])

    | SynPat.Wild _ ->
        (Pattern.Wildcard, [])

    | SynPat.Named(SynIdent(ident, _), _, _, _) ->
        let name = ident.idText
        (Pattern.Var(name, expectedTy), [(name, expectedTy)])

    | SynPat.Typed(innerPat, synType, _) ->
        let annotatedTy = checkSynType env synType
        addConstraint (Constraint.Equals(expectedTy, annotatedTy, range)) env
        checkPattern env innerPat annotatedTy range

    | SynPat.Tuple(_, pats, _, _) ->
        let elementTypes = pats |> List.map (fun _ -> freshTypeVar range)
        let tupleTy = NativeType.TTuple(elementTypes, false)
        addConstraint (Constraint.Equals(expectedTy, tupleTy, range)) env

        let (patterns, bindings) =
            List.zip pats elementTypes
            |> List.map (fun (p, ty) -> checkPattern env p ty range)
            |> List.unzip

        (Pattern.Tuple patterns, List.concat bindings)

    | SynPat.Paren(innerPat, _) ->
        checkPattern env innerPat expectedTy range

    | SynPat.Null _ ->
        (Pattern.Null, [])

    | _ ->
        // Fallback for unhandled patterns
        (Pattern.Wildcard, [])

/// Check a SynType and convert to NativeType
and checkSynType (env: TypeEnv) (synType: SynType) : NativeType =
    match synType with
    | SynType.LongIdent(longIdent) ->
        let name = longIdent.LongIdent |> List.map (fun id -> id.idText) |> String.concat "."
        match tryFindBuiltinTyCon name with
        | Some tyCon -> mkSimpleType tyCon
        | None ->
            // Try to find in type definitions
            match Map.tryFind name env.TypeDefs with
            | Some tyCon -> mkSimpleType tyCon
            | None -> NativeType.TError $"Unknown type: {name}"

    | SynType.App(typeName, _, typeArgs, _, _, _, _) ->
        let baseTy = checkSynType env typeName
        let argTys = typeArgs |> List.map (checkSynType env)
        match baseTy with
        | NativeType.TApp(tyCon, []) -> NativeType.TApp(tyCon, argTys)
        | _ -> baseTy  // Already an error or complex type

    | SynType.Tuple(isStruct, elementTypes, _) ->
        // SynTupleTypeSegment is a union: Type of SynType | Star of range | Slash of range
        // Filter for Type segments only
        let elemTys =
            elementTypes
            |> List.choose (function
                | SynTupleTypeSegment.Type ty -> Some (checkSynType env ty)
                | SynTupleTypeSegment.Star _ -> None
                | SynTupleTypeSegment.Slash _ -> None)
        NativeType.TTuple(elemTys, isStruct)

    | SynType.Fun(argType, returnType, _, _) ->
        let argTy = checkSynType env argType
        let retTy = checkSynType env returnType
        NativeType.TFun(argTy, retTy)

    | SynType.Var(_typar, _) ->
        // Type variable - create a fresh type variable
        freshTypeVar dummyRange

    | SynType.Paren(innerType, _) ->
        checkSynType env innerType

    | _ ->
        NativeType.TError "Unsupported type syntax"

//-------------------------------------------------------------------------
// Entry Point
//-------------------------------------------------------------------------

/// Check an expression and solve constraints
let checkAndSolve (env: TypeEnv) (builder: NodeBuilder) (expr: SynExpr) : SemanticNode * Constraint list =
    // Reset constraint list
    env.Constraints <- []

    // Check expression
    let node = checkExpr env builder expr

    // Collect constraints
    let constraints = env.Constraints

    (node, constraints)
