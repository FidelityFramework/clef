// Copyright (c) 2025 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Collection expression handlers for F# Native.
/// Handles: Tuple, Array, List, Record, AnonRecd
module FSharp.Native.Compiler.Checking.Native.Expressions.Collections

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Text
open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.NativeGlobals
open FSharp.Native.Compiler.Checking.Native.UnionFind
open FSharp.Native.Compiler.Checking.Native.SemanticGraph
open FSharp.Native.Compiler.Checking.Native.Expressions.Types

//-------------------------------------------------------------------------
// Callback Types
//-------------------------------------------------------------------------

/// Callback for checking expressions
type CheckExprFn = TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode

/// Callback for checking match clauses
type CheckMatchClauseFn = TypeEnv -> NodeBuilder -> NativeType -> NativeType -> SynMatchClause -> MatchCase

//-------------------------------------------------------------------------
// Tuple Expressions
//-------------------------------------------------------------------------

let checkTuple
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (isStruct: bool)
    (exprs: SynExpr list)
    (range: SourceRange)
    : SemanticNode =

    let elementNodes = exprs |> List.map (checkExpr env builder)
    let elementTypes = elementNodes |> List.map (fun n -> n.Type)
    let tupleType = NativeType.TTuple(elementTypes, isStruct)
    let childIds = elementNodes |> List.map (fun n -> n.Id)
    builder.Create(
        SemanticKind.TupleExpr childIds,
        tupleType,
        range,
        children = childIds)

//-------------------------------------------------------------------------
// Array/List Expressions
//-------------------------------------------------------------------------

let checkArrayOrList
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (isArray: bool)
    (exprs: SynExpr list)
    (range: SourceRange)
    : SemanticNode =

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

//-------------------------------------------------------------------------
// ArrayOrListComputed: [| for x in xs -> f x |] or [ for x in xs -> f x ]
//-------------------------------------------------------------------------

let checkArrayOrListComputed
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (isArray: bool)
    (compExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =

    let compNode = checkExpr env builder compExpr
    let elemType = freshTypeVar range
    let resultType = if isArray then mkArrayType elemType else mkListType elemType
    builder.Create(
        SemanticKind.ArrayExpr [compNode.Id],
        resultType,
        range,
        children = [compNode.Id])

//-------------------------------------------------------------------------
// Record Expressions
//-------------------------------------------------------------------------

let checkRecord
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (copyInfo: (SynExpr * BlockSeparator) option)
    (fields: SynExprRecordField list)
    (recordRange: range)
    (range: SourceRange)
    : SemanticNode =

    let copyNode = copyInfo |> Option.map (fun (expr, _) -> checkExpr env builder expr)

    // Extract field names and check expressions
    let fieldNodes = fields |> List.choose (fun field ->
        match field with
        | SynExprRecordField((fieldId, _), _, Some expr, _, _) ->
            let fieldName = fieldId.LongIdent |> List.map (fun id -> id.idText) |> String.concat "."
            let exprNode = checkExpr env builder expr
            Some (fieldName, exprNode)
        | _ -> None)

    // Extract just the field names for type resolution
    let fieldNames = fieldNodes |> List.map fst

    // Resolve record type using Field Label Resolution Algorithm
    // Per fsnative-spec: intersection of candidate sets for each field label
    let recordTy =
        match copyNode with
        | Some copyExpr ->
            // Copy-update expression: { existingRecord with Field = value }
            // The type comes from the copied record
            copyExpr.Type
        | None ->
            // Fresh record expression: { Field1 = v1; Field2 = v2 }
            // Resolve type from field labels
            match resolveRecordTypeFromFields fieldNames range env with
            | Result.Ok resolvedTy ->
                // Verify field types match (add constraints)
                // Each NativeType case must be handled explicitly - no catch-all patterns
                match resolvedTy with
                | NativeType.TApp(tyCon, _) ->
                    // Expected case: nominal record type like `Person` or `Record<'a>`
                    match Map.tryFind tyCon.Name env.RecordDefs with
                    | Some recordInfo ->
                        // Add constraints: each field expression must match field type
                        for (fieldName, exprNode) in fieldNodes do
                            match recordInfo.Fields |> List.tryFind (fun (n, _) -> n = fieldName) with
                            | Some (_, expectedTy) ->
                                addConstraint (Constraint.Equals(exprNode.Type, expectedTy, range)) env
                            | None ->
                                // Field not found in record definition - this is an error
                                addNativeError DiagnosticCodes.FS8702_UndefinedField recordRange
                                    (sprintf "Field '%s' is not defined in record type '%s'" fieldName tyCon.Name) env
                    | None ->
                        // Record type not in RecordDefs - internal error in resolution
                        addNativeError DiagnosticCodes.FS0001_GenericError recordRange
                            (sprintf "Internal error: record type '%s' not found in RecordDefs" tyCon.Name) env
                // Named records use TApp with field lookup via RecordDefs
                | NativeType.TError _ ->
                    // Already an error - don't add more diagnostics
                    ()
                // All other NativeType cases are invalid for record expressions
                | NativeType.TForall _ ->
                    addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                        "Record expression cannot have polymorphic type" env
                | NativeType.TTuple _ ->
                    addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                        "Expected record type, got tuple. Use record syntax { Field = value } not tuple syntax (a, b)" env
                | NativeType.TFun _ ->
                    addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                        "Expected record type, got function type" env
                | NativeType.TVar typar ->
                    addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                        (sprintf "Could not resolve record type - type variable '%s' is still unbound" typar.Name) env
                | NativeType.TMeasure _ ->
                    addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                        "Expected record type, got unit of measure" env
                | NativeType.TAnon _ ->
                    addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                        "Expected nominal record type. For anonymous records, use {| Field = value |} syntax" env
                | NativeType.TUnion _ ->
                    addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                        "Expected record type, got discriminated union. Use union case constructors instead" env
                | NativeType.TByref _ ->
                    addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                        "Expected record type, got byref type" env
                | NativeType.TNativePtr _ ->
                    addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                        "Expected record type, got native pointer type" env
                resolvedTy
            | Result.Error((code, message)) ->
                addNativeError code recordRange message env
                NativeType.TError message

    let fieldNodePairs = fieldNodes |> List.map (fun (name, node) -> (name, node.Id))

    builder.Create(
        SemanticKind.RecordExpr(fieldNodePairs, copyNode |> Option.map (fun n -> n.Id)),
        recordTy,
        range,
        children = (copyNode |> Option.map (fun n -> [n.Id]) |> Option.defaultValue []) @ (fieldNodes |> List.map (fun (_, n) -> n.Id)))

//-------------------------------------------------------------------------
// Anonymous Record Expressions
//-------------------------------------------------------------------------

let checkAnonRecd
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (isStruct: bool)
    (copyInfo: (SynExpr * BlockSeparator) option)
    (recordFields: (SynLongIdent * range option * SynExpr) list)
    (range: SourceRange)
    : SemanticNode =

    // Handle copy-and-update source if present: {| source with field = value |}
    let copyFromNode, inheritedFields =
        match copyInfo with
        | Some (sourceExpr, _blockSep) ->
            let sourceNode = checkExpr env builder sourceExpr
            // The source expression provides fields to inherit
            // Type must be extracted from the source for field inheritance
            let srcFields =
                match sourceNode.Type with
                | NativeType.TAnon(fields, _) -> fields
                | _ -> []  // Source type will be resolved during unification
            Some sourceNode, srcFields
        | None -> None, []

    // Process new field assignments
    let newFieldNodes = recordFields |> List.map (fun (SynLongIdent(longId, _, _), _rangeOption, fieldExpr) ->
        let fieldName = longId |> List.map (fun id -> id.idText) |> String.concat "."
        (fieldName, checkExpr env builder fieldExpr))

    // Merge inherited and new fields (new fields override inherited ones)
    let newFieldNames = newFieldNodes |> List.map fst |> Set.ofList
    let keptInheritedFields =
        inheritedFields
        |> List.filter (fun (name, _) -> not (Set.contains name newFieldNames))
    let allFieldTypes =
        keptInheritedFields @
        (newFieldNodes |> List.map (fun (name, node) -> (name, node.Type)))

    let childNodeIds =
        (copyFromNode |> Option.map (fun n -> [n.Id]) |> Option.defaultValue []) @
        (newFieldNodes |> List.map (fun (_, node) -> node.Id))

    builder.Create(
        SemanticKind.RecordExpr(
            newFieldNodes |> List.map (fun (name, node) -> (name, node.Id)),
            copyFromNode |> Option.map (fun n -> n.Id)),
        NativeType.TAnon(allFieldTypes, isStruct),
        range,
        children = childNodeIds)

//-------------------------------------------------------------------------
// MatchLambda: function | pat -> expr
// Desugars to: fun arg -> match arg with | pat1 -> expr1 | ...
//-------------------------------------------------------------------------

let checkMatchLambda
    (_checkExpr: CheckExprFn)
    (checkMatchClause: CheckMatchClauseFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (clauses: SynMatchClause list)
    (range: SourceRange)
    : SemanticNode =

    // Create fresh types for domain and result
    let domainType = freshTypeVar range
    let resultType = freshTypeVar range

    // Process each match clause
    let matchCases = clauses |> List.map (fun clause ->
        checkMatchClause env builder domainType resultType clause)

    // Create synthetic argument for the lambda
    let syntheticArgName = "_arg"
    // Create PatternBinding for the synthetic argument
    let syntheticParamNode = builder.Create(
        SemanticKind.PatternBinding(syntheticArgName),
        domainType,
        range)
    // Create VarRef that references the PatternBinding
    let syntheticArgNodeId =
        let argNode = builder.Create(
            SemanticKind.VarRef(syntheticArgName, Some syntheticParamNode.Id),
            domainType,
            range)
        argNode.Id

    // Create match expression over the synthetic argument
    let matchNodeChildIds = syntheticArgNodeId :: (matchCases |> List.collect (fun mc ->
        let guardAndBody = match mc.Guard with Some g -> [g; mc.Body] | None -> [mc.Body]
        mc.PatternBindings @ guardAndBody))
    let matchNode = builder.Create(
        SemanticKind.Match(syntheticArgNodeId, matchCases),
        resultType,
        range,
        children = matchNodeChildIds)

    // Wrap in lambda with PatternBinding NodeId for SSA assignment
    // This is a synthetic lambda for the function keyword - no outer captures
    // Children includes parameter PatternBinding + body for proper traversal
    // Inherit enclosing function context for nested function qualification
    builder.Create(
        SemanticKind.Lambda([(syntheticArgName, domainType, syntheticParamNode.Id)], matchNode.Id, [], env.EnclosingFunction),
        NativeType.TFun(domainType, resultType),
        range,
        children = [syntheticParamNode.Id; matchNode.Id])
