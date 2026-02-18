// Copyright (c) 2025 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Collection expression handlers for F# Native.
/// Handles: Tuple, Array, List, Record, AnonRecd, Indexing, Field access, Lazy, Seq
module Clef.Compiler.NativeTypedTree.Expressions.Collections

open Clef.Compiler.Syntax
open Clef.Compiler.Text
open Clef.Compiler.NativeTypedTree.NativeTypes

open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Builder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.NativeTypedTree.Expressions.Types

// Module aliases for qualified access
module Types = Clef.Compiler.NativeTypedTree.Expressions.Types
module NativeTypes = Clef.Compiler.NativeTypedTree.NativeTypes

//-------------------------------------------------------------------------
// Callback Types
//-------------------------------------------------------------------------

/// Callback for checking expressions
type CheckExprFn = TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode

/// Callback for checking match clauses
/// Now includes scrutinee NodeId to enable field extraction for record patterns
type CheckMatchClauseFn = TypeEnv -> NodeBuilder -> NodeId -> NativeType -> NativeType -> SynMatchClause -> MatchCase

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
        if isArray then NativeType.TApp(Types.arrayTyCon, [elementTy])
        else NativeType.TList elementTy

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
    let resultType = if isArray then NativeType.TApp(Types.arrayTyCon, [elemType]) else NativeType.TList elemType
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
                | NativeType.TLazy _ ->
                    addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                        "Expected record type, got Lazy<'T> type" env  // PRD-14
                | NativeType.TSeq _ ->
                    addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                        "Expected record type, got seq<'T> type" env  // PRD-15
                | NativeType.TSeqEnumerator _ ->
                    addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                        "Expected record type, got SeqEnumerator<'T> type" env  // PRD-15/16
                // PRD-13a: Collection types
                | NativeType.TList _ ->
                    addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                        "Expected record type, got list<'T> type. Use list syntax [a; b; c]" env
                | NativeType.TMap _ ->
                    addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                        "Expected record type, got Map<'K,'V> type. Use Map.ofList or Map.add" env
                | NativeType.TSet _ ->
                    addNativeError DiagnosticCodes.FS8000_TypeMismatch recordRange
                        "Expected record type, got Set<'T> type. Use Set.ofList or Set.add" env
                // Note: option<'T> is handled via TUnion - it's a discriminated union
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

    // Create synthetic argument for the lambda FIRST (so we have its NodeId for pattern extraction)
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

    // Process each match clause with scrutinee ID for pattern binding extraction
    let matchCases = clauses |> List.map (fun clause ->
        checkMatchClause env builder syntheticArgNodeId domainType resultType clause)

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
    let lambdaNode = builder.Create(
        SemanticKind.Lambda([(syntheticArgName, domainType, syntheticParamNode.Id)], matchNode.Id, [], env.EnclosingFunction, LambdaContext.RegularClosure),
        NativeType.TFun(domainType, resultType),
        range,
        children = [syntheticParamNode.Id; matchNode.Id])
    
    // Architectural fix (January 2026): Mark Lambda body as SeparateFunction
    // Function keyword lambdas have no outer captures (synthetic)
    builder.SetEmissionStrategy(matchNode.Id, EmissionStrategy.SeparateFunction 0)

    lambdaNode


//-------------------------------------------------------------------------
// Indexing Operations
//-------------------------------------------------------------------------

/// Check dotless indexer get: expr[index]
let checkDotlessIndexGet
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (objExpr: SynExpr)
    (indexExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let objNode = checkExpr env builder objExpr
    let indexNodes =
        match indexExpr with
        | SynExpr.Tuple(_, exprs, _, _) -> exprs |> List.map (checkExpr env builder)
        | _ -> [checkExpr env builder indexExpr]

    match indexNodes with
    | [single] ->
        addConstraint (Constraint.Equals(single.Type, Types.intType, range)) env
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

    let elementType = resolveIndexElementType (applySubst objNode.Type) env range

    let allChildNodeIds = objNode.Id :: (indexNodes |> List.map (fun n -> n.Id))
    builder.Create(
        SemanticKind.IndexGet(objNode.Id, indexNodeId),
        elementType,
        range,
        children = allChildNodeIds)

/// Check dotless indexer set: expr[index] <- value
let checkDotlessIndexSet
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (objExpr: SynExpr)
    (indexExpr: SynExpr)
    (valueExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let objNode = checkExpr env builder objExpr
    let valueNode = checkExpr env builder valueExpr
    let indexNodes =
        match indexExpr with
        | SynExpr.Tuple(_, exprs, _, _) -> exprs |> List.map (checkExpr env builder)
        | _ -> [checkExpr env builder indexExpr]

    match indexNodes with
    | [single] ->
        addConstraint (Constraint.Equals(single.Type, Types.intType, range)) env
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

    let elementType = resolveIndexElementType (applySubst objNode.Type) env range
    addConstraint (Constraint.Equals(valueNode.Type, elementType, range)) env

    let allChildNodeIds = objNode.Id :: (indexNodes |> List.map (fun n -> n.Id)) @ [valueNode.Id]
    builder.Create(
        SemanticKind.IndexSet(objNode.Id, indexNodeId, valueNode.Id),
        Types.unitType,
        range,
        children = allChildNodeIds)

/// Check DotIndexedGet: expr.[index]
let checkDotIndexedGet
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (objExpr: SynExpr)
    (indexArgs: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let objNode = checkExpr env builder objExpr
    let indexNodes =
        match indexArgs with
        | SynExpr.Tuple(_, exprs, _, _) -> exprs |> List.map (checkExpr env builder)
        | indexExpr -> [checkExpr env builder indexExpr]

    match indexNodes with
    | [single] ->
        addConstraint (Constraint.Equals(single.Type, Types.intType, range)) env
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

    let elementType = resolveIndexElementType (applySubst objNode.Type) env range

    let allChildNodeIds = objNode.Id :: (indexNodes |> List.map (fun n -> n.Id))
    builder.Create(
        SemanticKind.IndexGet(objNode.Id, indexNodeId),
        elementType,
        range,
        children = allChildNodeIds)

/// Check DotIndexedSet: expr.[index] <- value
let checkDotIndexedSet
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (objExpr: SynExpr)
    (indexArgs: SynExpr)
    (valueExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
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
        Types.unitType,
        range,
        children = allChildNodeIds)

//-------------------------------------------------------------------------
// Field Access
//-------------------------------------------------------------------------

/// Check DotGet: expr.field or expr.field1.field2...
/// Multi-part paths (e.g., c.Person.Name) create nested FieldGet nodes
let checkDotGet
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (expr: SynExpr)
    (longDotId: SynLongIdent)
    (range: SourceRange)
    : SemanticNode =
    let exprNode = checkExpr env builder expr
    let fieldParts = longDotId.LongIdent |> List.map (fun id -> id.idText)

    /// Create a single FieldGet node for one field access
    /// Uses Types.resolveFieldType for canonical field type resolution
    let createFieldGet (baseNode: SemanticNode) (fieldName: string) : SemanticNode =
        let resultTy = Types.resolveFieldType baseNode.Type fieldName env range
        builder.Create(
            SemanticKind.FieldGet(baseNode.Id, fieldName),
            resultTy,
            range,
            children = [baseNode.Id])

    // Fold over field parts, creating nested FieldGet nodes
    // e.g., c.Person.Name becomes FieldGet(FieldGet(c, "Person"), "Name")
    fieldParts |> List.fold createFieldGet exprNode

//-------------------------------------------------------------------------
// Lazy Expressions (PRD-14)
//-------------------------------------------------------------------------

/// Check Lazy: lazy expr
/// PRD-14: Creates LazyExpr node with a thunk (unit -> 'T) wrapping the body
/// Thunk calling convention (Option B): thunk receives lazy struct pointer and extracts its own captures
/// Captures are computed using the same analysis as Lambda (MLKit-style flat closures)
let checkLazy
    (checkExpr: CheckExprFn)
    (computeCaptures: NodeBuilder -> TypeEnv -> NodeId -> Set<string> -> CaptureInfo list)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (innerExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let innerNode = checkExpr env builder innerExpr
    let lazyType = NativeTypes.Types.mkLazyType innerNode.Type

    // Capture analysis: find VarRefs in body that are NOT the unit parameter
    // These are variables captured from the enclosing scope
    // PRD-14: Lazy values are "extended flat closures" with inlined captures
    let unitParamName = "_unit"
    let captures = computeCaptures builder env innerNode.Id (Set.singleton unitParamName)

    // Create a thunk Lambda: unit -> 'T
    // The thunk takes a unit parameter and returns the lazy body
    // Thunk captures the same variables as the lazy expression
    let thunkType = NativeType.TFun(Types.unitType, innerNode.Type)
    let thunkLambda = builder.Create(
        SemanticKind.Lambda([("_unit", Types.unitType, NodeId -1)], innerNode.Id, captures, env.EnclosingFunction, LambdaContext.LazyThunk),
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

//-------------------------------------------------------------------------
// Sequence Expressions (PRD-15)
//-------------------------------------------------------------------------

/// Check seq expression: seq { ... }
/// PRD-15: Creates a SeqExpr with a MoveNext thunk (LambdaContext.SeqGenerator)
let checkSeq
    (checkExpr: CheckExprFn)
    (computeCaptures: NodeBuilder -> TypeEnv -> NodeId -> Set<string> -> CaptureInfo list)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (bodyExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
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
    let seqType = NativeTypes.Types.mkSeqType elementType

    // Capture analysis: find VarRefs in body that are NOT local to the seq
    // PRD-15: Seq values are "extended flat closures" with inlined captures
    let captures = computeCaptures builder env bodyNode.Id Set.empty

    // Create MoveNext thunk: (seq_ptr: nativeptr<Seq<T>>) -> bool
    // The thunk receives pointer to the seq struct, extracts its captures
    // Returns true if a value was yielded, false if exhausted
    let seqPtrType = NativeType.TNativePtr seqType
    let moveNextType = NativeType.TFun(seqPtrType, Types.boolType)
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
let checkYield
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (valueExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    // Validate that yield appears inside a seq expression
    match env.EnclosingSeqExpr with
    | None ->
        // Return error node - yield outside seq context
        builder.Create(
            SemanticKind.Error "yield may only appear directly in a seq expression",
            Types.unitType,
            range)
    | Some _ ->
        let valueNode = checkExpr env builder valueExpr
        // yield is an effectful operation - it stores the value but returns unit
        // The value's type is captured in the Yield node for codegen, but the
        // expression type is unit (yield doesn't return a value to the caller)
        builder.Create(
            SemanticKind.Yield valueNode.Id,
            Types.unitType,
            range,
            children = [valueNode.Id])

/// Check yield!: yield! seq
/// PRD-15: Flattens another sequence into this one
let checkYieldBang
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (seqExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    // Validate that yield! appears inside a seq expression
    match env.EnclosingSeqExpr with
    | None ->
        // Return error node - yield! outside seq context
        builder.Create(
            SemanticKind.Error "yield! may only appear directly in a seq expression",
            Types.unitType,
            range)
    | Some _ ->
        let seqNode = checkExpr env builder seqExpr
        // yield! is an effectful operation - it flattens a seq but returns unit
        // The element type is inferred from the seqNode for codegen purposes
        builder.Create(
            SemanticKind.YieldBang seqNode.Id,
            Types.unitType,
            range,
            children = [seqNode.Id])
