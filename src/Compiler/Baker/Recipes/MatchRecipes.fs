// SPDX-License-Identifier: MIT

/// Baker Match Recipes - Decomposition of Match expressions to decision trees.
///
/// Pattern matching compilation reduces Match expressions to IfThenElse chains:
/// - Union patterns: Extract tag, compare against expected, extract payload
/// - Constant patterns: Direct equality comparison
/// - Variable patterns: Let binding for the matched value
/// - Wildcard patterns: Always match (default case)
///
/// This follows the F# spec: "Patterns are elaborated to expressions through
/// pattern match compilation. This reduces pattern matching to decision trees."
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
/// See: fsnative-spec/spec/patterns.md
module Clef.Compiler.Baker.Recipes.MatchRecipes

open XParsec.Parsers
open XParsec.Combinators
open Clef.Compiler.NativeTypedTree.NativeTypes

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives

//=============================================================================
// BRIDGE: Convert SaturationParser results to Decomposition.Result
//=============================================================================

/// Convert a Decomposition.Context to a SaturationState
let private toSaturationState (ctx: Context) : SaturationState =
    { EmittedNodes = []
      Bindings = Map.empty
      ExpansionId = ctx.ExpansionId
      OriginalHOF = ctx.OriginalHOF
      SourceRange = ctx.SourceRange
      InspiringNode = ctx.InspiringNode
      Platform = ctx.Platform }

/// Run a saturation parser and convert to Decomposition.Result
let private runSaturation (ctx: Context) (parser: SaturationParser<NodeId>) : Result =
    let initialState = toSaturationState ctx
    let result, nodes = run initialState parser
    match result with
    | Matched resultNodeId ->
        mkResultNoShadow nodes resultNodeId []
    | NoMatch reason ->
        failwithf "Saturation failed: %s" reason

//=============================================================================
// PATTERN BINDING HELPERS
//=============================================================================

/// Create let bindings for pattern-bound variables
/// Returns the bound value node ID for use in the body
let private bindPatternVar (name: string) (valueId: NodeId) (ty: NativeType) : SaturationParser<NodeId> =
    saturation {
        let! bindingId = letBind name valueId ty
        return bindingId
    }

//=============================================================================
// PATTERN COMPILATION
//=============================================================================

/// Extract bindings from a pattern WITHOUT creating guard condition.
/// Used for the last case in exhaustive matching where we know it will match.
/// Returns just the new binding NodeIds.
let rec private extractPatternBindings
    (scrutineeId: NodeId)
    (pattern: Pattern)
    (patternBindings: NodeId list)
    : SaturationParser<NodeId list> =

    match pattern with
    | Pattern.Wildcard | Pattern.Var _ | Pattern.Null ->
        // No bindings to extract
        saturation { return patternBindings }

    | Pattern.Union (caseName, tagIndex, payload, _unionType) ->
        // Extract payload bindings, reusing original PatternBinding NodeIds
        match payload with
        | Some (Pattern.Var (name, ty)) ->
            saturation {
                let! payloadId = duEliminate scrutineeId caseName tagIndex ty
                let originalBindingId = List.head patternBindings
                let! bindingId = letBindAt originalBindingId name payloadId ty
                return [bindingId]
            }
        | Some (Pattern.Tuple [Pattern.Var (name, ty)]) ->
            // Single-element tuple - treat as direct value
            saturation {
                let! payloadId = duEliminate scrutineeId caseName tagIndex ty
                let originalBindingId = List.head patternBindings
                let! bindingId = letBindAt originalBindingId name payloadId ty
                return [bindingId]
            }
        | Some (Pattern.Tuple elements) ->
            saturation {
                let elementTypes =
                    elements
                    |> List.map (fun elem ->
                        match elem with
                        | Pattern.Var (_, ty) -> ty
                        | _ -> failwithf "Unsupported tuple element pattern in DU payload")
                let tuplePayloadType = NativeType.TTuple (elementTypes, false)
                let! tuplePayloadId = duEliminate scrutineeId caseName tagIndex tuplePayloadType

                let! bindings =
                    elements
                    |> List.mapi (fun index elem ->
                        match elem with
                        | Pattern.Var (name, ty) ->
                            saturation {
                                let! elementId = createWithChildren (SemanticKind.TupleGet (tuplePayloadId, index)) ty [tuplePayloadId]
                                let originalBindingId = patternBindings.[index]
                                let! bindingId = letBindAt originalBindingId name elementId ty
                                return bindingId
                            }
                        | other ->
                            failwithf "Unsupported tuple element pattern: %A" other)
                    |> sequence
                return bindings
            }
        | None ->
            saturation { return [] }
        | Some other ->
            failwithf "extractPatternBindings: Unsupported union payload pattern: %A" other

    | Pattern.Tuple elements ->
        // Top-level tuple pattern: extract each element and recursively extract bindings
        let extractElement index elemPattern =
            saturation {
                // Extract this element from the scrutinee tuple
                let elemType = getPatternType elemPattern
                let! elemId = createWithChildren (SemanticKind.TupleGet (scrutineeId, index)) elemType [scrutineeId]
                // Get pattern bindings for this element
                let elemBindings = getElementPatternBindings index patternBindings elements
                // Recursively extract bindings
                return! extractPatternBindings elemId elemPattern elemBindings
            }
        saturation {
            let! allBindings =
                elements
                |> List.mapi extractElement
                |> sequence
            return List.concat allBindings
        }

    | Pattern.Const _ ->
        // Constant patterns don't create bindings
        saturation { return patternBindings }

    | Pattern.Record (fields, recordType) ->
        // Record pattern: extract each field and create bindings.
        // For each field: create FieldGet, then Binding (or recurse for nested patterns).
        // Wildcards skip FieldGet creation to avoid orphaned nodes.
        let expectedFieldCount =
            match recordType with
            | NativeType.TApp(tycon, _) -> tycon.FieldCount
            | _ -> 0
        if expectedFieldCount > 0 && List.length fields > expectedFieldCount then
            failwithf "Record pattern has %d fields but record type %A only has %d fields"
                (List.length fields) recordType expectedFieldCount
        saturation {
            let! bindings =
                fields
                |> List.mapi (fun index (fieldName, fieldPattern) ->
                    saturation {
                        match fieldPattern with
                        | Pattern.Wildcard ->
                            // Wildcard - no binding needed, don't create FieldGet (would be orphaned)
                            return []

                        | Pattern.Var (name, ty) ->
                            // Direct variable binding - create FieldGet then bind it
                            let! fieldId = createWithChildren (SemanticKind.FieldGet (scrutineeId, fieldName)) ty [scrutineeId]
                            if index < List.length patternBindings then
                                let originalBindingId = patternBindings.[index]
                                let! bindingId = letBindAt originalBindingId name fieldId ty
                                return [bindingId]
                            else
                                // No original PatternBinding - create new binding
                                let! bindingId = letBind name fieldId ty
                                return [bindingId]

                        | nestedPattern ->
                            // Nested pattern (Record, Tuple, etc.) - create FieldGet and recurse
                            let fieldType = getPatternType nestedPattern
                            let! fieldId = createWithChildren (SemanticKind.FieldGet (scrutineeId, fieldName)) fieldType [scrutineeId]
                            let nestedBindings =
                                if index < List.length patternBindings then
                                    let nestedCount = countPatternBindings nestedPattern
                                    patternBindings |> List.skip index |> List.truncate nestedCount
                                else []
                            return! extractPatternBindings fieldId nestedPattern nestedBindings
                    })
                |> sequence
            return List.concat bindings
        }

    | unsupported ->
        // HARD ERROR: Unsupported pattern type - do not silently fall through
        failwithf "extractPatternBindings: Unsupported pattern type: %A. This is a compiler bug - please report." unsupported

/// Compile a single pattern case to a conditional expression.
/// Returns (guard expression, body, new binding NodeIds).
/// The new binding NodeIds replace the old PatternBinding NodeIds - they have
/// proper value sources (e.g., FieldGet for DU payload extraction).
and private compilePattern
    (scrutineeId: NodeId)
    (pattern: Pattern)
    (patternBindings: NodeId list)
    (guard: NodeId option)
    (body: NodeId)
    (_resultType: NativeType)
    : SaturationParser<NodeId * NodeId * NodeId list> =

    match pattern with
    | Pattern.Wildcard ->
        // Wildcard always matches - guard is "true", body is unchanged
        // No new bindings - use original PatternBindings
        // CRITICAL: Only create boolLit when no guard, to avoid orphaned nodes
        saturation {
            match guard with
            | Some guardId -> return (guardId, body, patternBindings)
            | None ->
                let! trueId = boolLit true
                return (trueId, body, patternBindings)
        }

    | Pattern.Var (_name, _ty) ->
        // Variable pattern: bind scrutinee to name, always matches
        // No new bindings - use original PatternBindings
        // CRITICAL: Only create boolLit when no guard, to avoid orphaned nodes
        saturation {
            match guard with
            | Some guardId -> return (guardId, body, patternBindings)
            | None ->
                let! trueId = boolLit true
                return (trueId, body, patternBindings)
        }

    | Pattern.Const literal ->
        // Constant pattern: compare scrutinee to literal
        // No new bindings - use original PatternBindings
        saturation {
            let literalType = literalToType literal
            let! literalId = createAndEmit (SemanticKind.Literal literal) literalType
            let! compareId = compareEq scrutineeId literalId literalType
            match guard with
            | Some guardId ->
                let! combinedGuard = andAlso compareId guardId
                return (combinedGuard, body, patternBindings)
            | None ->
                return (compareId, body, patternBindings)
        }

    | Pattern.Union (caseName, tagIndex, payload, unionType) ->
        // Union pattern: compare tag, then extract and bind payload
        // Use letBindAt to create Bindings AT THE SAME NodeIds as PatternBindings
        // This way VarRefs in the body continue to resolve correctly
        saturation {
            // Use DUGetTag for type-safe tag extraction
            let! tagId = duGetTag scrutineeId unionType
            let! tagLitId = int8Lit tagIndex
            let! tagMatches = compareEq tagId tagLitId Types.int8Type

            // Extract and bind payload, reusing original PatternBinding NodeIds
            let! newBindings =
                match payload with
                | Some (Pattern.Var (name, ty)) ->
                    // Single variable binding - reuse the PatternBinding's NodeId
                    saturation {
                        let! payloadId = duEliminate scrutineeId caseName tagIndex ty
                        // Use letBindAt to create Binding at the original PatternBinding's NodeId
                        let originalBindingId = List.head patternBindings
                        let! bindingId = letBindAt originalBindingId name payloadId ty
                        return [bindingId]
                    }
                | Some (Pattern.Tuple [Pattern.Var (name, ty)]) ->
                    // Single-element tuple - F# represents `Case of T` as a 1-tuple
                    // Treat this as a direct value, not a tuple
                    saturation {
                        let! payloadId = duEliminate scrutineeId caseName tagIndex ty
                        let originalBindingId = List.head patternBindings
                        let! bindingId = letBindAt originalBindingId name payloadId ty
                        return [bindingId]
                    }
                | Some (Pattern.Tuple elements) ->
                    // Multi-field tuple payload like `SomeCase of int * float`:
                    // Each element reuses its corresponding PatternBinding NodeId
                    saturation {
                        // Build the tuple type from element types
                        let elementTypes =
                            elements
                            |> List.map (fun elem ->
                                match elem with
                                | Pattern.Var (_, ty) -> ty
                                | _ -> failwithf "Unsupported tuple element pattern in DU payload")
                        let tuplePayloadType = NativeType.TTuple (elementTypes, false)

                        // Extract the whole tuple payload
                        let! tuplePayloadId = duEliminate scrutineeId caseName tagIndex tuplePayloadType

                        // Extract and bind each element, reusing original PatternBinding NodeIds
                        let! bindings =
                            elements
                            |> List.mapi (fun index elem ->
                                match elem with
                                | Pattern.Var (name, ty) ->
                                    saturation {
                                        // TupleGet extracts element at index from the tuple
                                        let! elementId = createWithChildren (SemanticKind.TupleGet (tuplePayloadId, index)) ty [tuplePayloadId]
                                        // Reuse the original PatternBinding's NodeId
                                        let originalBindingId = patternBindings.[index]
                                        let! bindingId = letBindAt originalBindingId name elementId ty
                                        return bindingId
                                    }
                                | other ->
                                    failwithf "Unsupported tuple element pattern: %A" other)
                            |> sequence
                        return bindings
                    }
                | None ->
                    // No payload - no bindings needed (nullary case like None)
                    saturation { return [] }
                | Some other ->
                    failwithf "Unsupported union payload pattern: %A" other

            match guard with
            | Some guardId ->
                let! combinedGuard = andAlso tagMatches guardId
                return (combinedGuard, body, newBindings)
            | None ->
                return (tagMatches, body, newBindings)
        }

    | Pattern.Tuple elements ->
        // Tuple pattern: extract all elements and wrap in Sequential to ensure
        // TupleGets are emitted BEFORE any control flow from guard combination.
        // Structure: Sequential([TupleGet0; TupleGet1; ...; actualGuard])
        saturation {
            // Phase 1: Extract ALL tuple elements
            let! extractedElems =
                elements
                |> List.mapi (fun index elemPattern ->
                    saturation {
                        let elemType = getPatternType elemPattern
                        let! elemId = createWithChildren (SemanticKind.TupleGet (scrutineeId, index)) elemType [scrutineeId]
                        return (elemId, elemPattern)
                    })
                |> sequence

            let tupleGetIds = extractedElems |> List.map fst

            // Phase 2: Compile each element pattern using pre-extracted values
            let! results =
                extractedElems
                |> List.mapi (fun index (elemId, elemPattern) ->
                    saturation {
                        let elemBindings = getElementPatternBindings index patternBindings elements
                        return! compilePattern elemId elemPattern elemBindings None body _resultType
                    })
                |> sequence

            // Combine all guards with AND
            let guards = results |> List.map (fun (g, _, _) -> g)
            let combineGuards accParser g =
                saturation {
                    let! acc = accParser
                    return! andAlso acc g
                }
            let! combinedGuard =
                match guards with
                | [] -> boolLit true
                | [g] -> saturation { return g }
                | g :: rest -> rest |> List.fold combineGuards (saturation { return g })

            // Wrap TupleGets + guard in Sequential to hoist TupleGets before control flow
            // Sequential visits children in order, so TupleGets emit before guard's scf.if
            let! hoistedGuard =
                createWithChildren
                    (SemanticKind.Sequential (tupleGetIds @ [combinedGuard]))
                    Types.boolType
                    (tupleGetIds @ [combinedGuard])

            // Collect all bindings
            let allBindings = results |> List.collect (fun (_, _, bindings) -> bindings)

            // Apply optional outer guard
            match guard with
            | Some guardId ->
                let! finalGuard = andAlso hoistedGuard guardId
                return (finalGuard, body, allBindings)
            | None ->
                return (hoistedGuard, body, allBindings)
        }

    | Pattern.Null ->
        // Null pattern: check if value is null (for reference types)
        // In native F#, this is rare - most types are non-nullable
        // CRITICAL: Only create boolLit when no guard, to avoid orphaned nodes
        saturation {
            match guard with
            | Some guardId -> return (guardId, body, patternBindings)
            | None ->
                let! trueId = boolLit true  // Simplified - treat as always match for now
                return (trueId, body, patternBindings)
        }

    | Pattern.Record (fields, recordType) ->
        // Record patterns always match structurally (no runtime tag check).
        // Extract each field and create bindings inline, like Union.
        saturation {
            // Validate field count
            let expectedFieldCount =
                match recordType with
                | NativeType.TApp(tycon, _) -> tycon.FieldCount
                | _ -> 0
            if expectedFieldCount > 0 && List.length fields > expectedFieldCount then
                failwithf "Record pattern has %d fields but record type %A only has %d fields"
                    (List.length fields) recordType expectedFieldCount

            // Extract and bind each field
            let! newBindings =
                fields
                |> List.mapi (fun index (fieldName, fieldPattern) ->
                    saturation {
                        match fieldPattern with
                        | Pattern.Wildcard ->
                            // Wildcard - no binding needed, skip FieldGet to avoid orphaned nodes
                            return []

                        | Pattern.Var (name, ty) ->
                            // Direct variable binding - create FieldGet then bind it
                            let! fieldId = createWithChildren (SemanticKind.FieldGet (scrutineeId, fieldName)) ty [scrutineeId]
                            if index < List.length patternBindings then
                                let originalBindingId = patternBindings.[index]
                                let! bindingId = letBindAt originalBindingId name fieldId ty
                                return [bindingId]
                            else
                                let! bindingId = letBind name fieldId ty
                                return [bindingId]

                        | nestedPattern ->
                            // Nested pattern - create FieldGet and recurse
                            let fieldType = getPatternType nestedPattern
                            let! fieldId = createWithChildren (SemanticKind.FieldGet (scrutineeId, fieldName)) fieldType [scrutineeId]
                            let nestedBindings =
                                if index < List.length patternBindings then
                                    let nestedCount = countPatternBindings nestedPattern
                                    patternBindings |> List.skip index |> List.truncate nestedCount
                                else []
                            return! extractPatternBindings fieldId nestedPattern nestedBindings
                    })
                |> sequence

            let allBindings = List.concat newBindings

            match guard with
            | Some guardId -> return (guardId, body, allBindings)
            | None ->
                let! trueId = boolLit true
                return (trueId, body, allBindings)
        }

    | unsupported ->
        // HARD ERROR: Unsupported pattern type - do not silently fall through
        // This surfaces missing pattern support immediately rather than causing
        // cryptic "unbound type variable" errors downstream
        failwithf "compilePattern: Unsupported pattern type: %A. This is a compiler bug - please report." unsupported

/// Map NTUKind to NativeType
and private ntuKindToType (kind: NTUKind) : NativeType =
    match kind with
    // Signed integers
    | NTUKind.NTUint (NTUWidth.Fixed 8) -> Types.int8Type
    | NTUKind.NTUint (NTUWidth.Fixed 16) -> Types.int16Type
    | NTUKind.NTUint (NTUWidth.Fixed 32) -> Types.int32Type
    | NTUKind.NTUint (NTUWidth.Fixed 64) -> Types.int64Type
    | NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register) -> Types.intType
    | NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Pointer) -> Types.nintType
    // Unsigned integers
    | NTUKind.NTUuint (NTUWidth.Fixed 8) -> Types.uint8Type
    | NTUKind.NTUuint (NTUWidth.Fixed 16) -> Types.uint16Type
    | NTUKind.NTUuint (NTUWidth.Fixed 32) -> Types.uint32Type
    | NTUKind.NTUuint (NTUWidth.Fixed 64) -> Types.uint64Type
    | NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Register) -> Types.uintType
    | NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Pointer) -> Types.unintType
    // Floats
    | NTUKind.NTUfloat (NTUWidth.Fixed 32) -> Types.float32Type
    | NTUKind.NTUfloat (NTUWidth.Fixed 64) -> Types.floatType
    // Posits
    | NTUKind.NTUposit (NTUWidth.Fixed 8, _) -> Types.posit8Type
    | NTUKind.NTUposit (NTUWidth.Fixed 16, _) -> Types.posit16Type
    | NTUKind.NTUposit (NTUWidth.Fixed 32, _) -> Types.posit32Type
    | NTUKind.NTUposit (NTUWidth.Fixed 64, _) -> Types.posit64Type
    | _ -> failwithf "ntuKindToType: unexpected kind %A" kind

/// Helper to get type from literal
and private literalToType (lit: NativeLiteral) : NativeType =
    match lit with
    | NativeLiteral.Int (_, kind) -> ntuKindToType kind
    | NativeLiteral.UInt (_, kind) -> ntuKindToType kind
    | NativeLiteral.Float (_, kind) -> ntuKindToType kind
    | NativeLiteral.Bool _ -> Types.boolType
    | NativeLiteral.Char _ -> Types.charType
    | NativeLiteral.String _ -> Types.stringType
    | NativeLiteral.Unit -> Types.unitType
    | NativeLiteral.Decimal _ -> Types.decimalType
    | NativeLiteral.ByteArray _ -> NativeType.TApp(Types.arrayTyCon, [Types.uint8Type])
    | NativeLiteral.UInt16Array _ -> NativeType.TApp(Types.arrayTyCon, [Types.uint16Type])
    | NativeLiteral.BigInt _ -> Types.int64Type  // BigInt maps to int64 for now

/// Get the type from a pattern (uses literalToType for Const patterns)
and private getPatternType (pattern: Pattern) : NativeType =
    match pattern with
    | Pattern.Var (_, ty) -> ty
    | Pattern.Union (_, _, _, ty) -> ty
    | Pattern.Tuple elements ->
        NativeType.TTuple (elements |> List.map getPatternType, false)
    | Pattern.Const lit -> literalToType lit
    | Pattern.Wildcard -> Types.unitType
    | Pattern.Null -> Types.unitType
    | Pattern.Record (_, recordType) -> recordType
    | Pattern.Array elements ->
        match elements with
        | [] -> NativeType.TApp(Types.arrayTyCon, [Types.unitType])
        | first :: _ -> NativeType.TApp(Types.arrayTyCon, [getPatternType first])
    | Pattern.And (left, _) -> getPatternType left
    | Pattern.Or (left, _) -> getPatternType left
    | Pattern.As (inner, _) -> getPatternType inner
    | Pattern.IsType ty -> ty
    | Pattern.Exception (exnType, _) -> exnType

/// Count bindings in a pattern (recursive for nested patterns)
and private countPatternBindings (pattern: Pattern) : int =
    match pattern with
    | Pattern.Var _ -> 1
    | Pattern.Union (_, _, Some payload, _) -> countPatternBindings payload
    | Pattern.Union (_, _, None, _) -> 0
    | Pattern.Tuple elements -> elements |> List.sumBy countPatternBindings
    | Pattern.Record (fields, _) ->
        fields |> List.sumBy (fun (_, fieldPattern) -> countPatternBindings fieldPattern)
    | Pattern.Array elements -> elements |> List.sumBy countPatternBindings
    | Pattern.And (left, right) -> countPatternBindings left + countPatternBindings right
    | Pattern.Or (left, _) -> countPatternBindings left  // Or patterns must bind same names
    | Pattern.As (inner, _) -> 1 + countPatternBindings inner  // 1 for the 'as' binding + inner
    | Pattern.Exception (_, bindName) -> if Option.isSome bindName then 1 else 0
    | Pattern.Wildcard | Pattern.Null | Pattern.Const _ | Pattern.IsType _ -> 0

/// Get pattern bindings for a specific tuple element.
/// Partitions the flat patternBindings list based on each element's binding count.
and private getElementPatternBindings
    (index: int)
    (patternBindings: NodeId list)
    (elements: Pattern list)
    : NodeId list =
    let bindingsPerElement = elements |> List.map countPatternBindings
    let offset = bindingsPerElement |> List.take index |> List.sum
    let count = bindingsPerElement.[index]
    patternBindings |> List.skip offset |> List.take count

//=============================================================================
// MATCH DECOMPOSITION
//=============================================================================

/// Wrap a body with pattern bindings in a Sequential if there are bindings.
/// PatternBinding nodes already exist in the graph; we just need to include
/// them in the control flow so they're walked during SSA traversal.
let private wrapWithPatternBindings
    (patternBindings: NodeId list)
    (bodyId: NodeId)
    (resultType: NativeType)
    : SaturationParser<NodeId> =
    
    match patternBindings with
    | [] -> 
        // No bindings - just return the body
        saturation { return bodyId }
    | bindings ->
        // Wrap: Sequential([binding1; binding2; ...; body])
        // The PatternBinding nodes already exist; we create a Sequential that references them
        let elements = bindings @ [bodyId]
        let seqKind = SemanticKind.Sequential elements
        createWithChildren seqKind resultType elements

/// Decompose a Match expression into nested IfThenElse chains.
///
/// match scrutinee with
/// | Pattern1 -> body1
/// | Pattern2 when guard2 -> body2
/// | _ -> defaultBody
///
/// Becomes:
/// if (pattern1Matches) then Sequential([patternBindings...; body1])
/// elif (pattern2Matches && guard2) then Sequential([patternBindings...; body2])
/// else defaultBody
///
/// CRITICAL: PatternBindings MUST be included in the then-branch structure.
/// After Match saturation, the IfThenElse replaces the Match node. The original
/// PatternBinding nodes exist in the graph but are orphaned if not referenced
/// by the IfThenElse structure. Wrapping them in a Sequential with the body
/// ensures they're walked during SSA traversal.
let matchDecomposeParser
    (scrutineeId: NodeId)
    (cases: MatchCase list)
    (resultType: NativeType)
    : SaturationParser<NodeId> =

    let rec buildDecisionTree (remainingCases: MatchCase list) : SaturationParser<NodeId> =
        match remainingCases with
        | [] ->
            // No more cases - this shouldn't happen with exhaustive patterns
            // Return unit or error value
            createAndEmit (SemanticKind.Literal NativeLiteral.Unit) Types.unitType

        | [lastCase] ->
            // Last case - assuming exhaustive matching, this case WILL match.
            // Only extract bindings, don't create guard nodes (they'd be orphaned).
            // CRITICAL: Use extractPatternBindings, NOT compilePattern, to avoid
            // creating unused tag-check nodes that become orphans after fold-in.
            saturation {
                let! newBindings = extractPatternBindings scrutineeId lastCase.Pattern lastCase.PatternBindings
                return! wrapWithPatternBindings newBindings lastCase.Body resultType
            }

        | case :: rest ->
            saturation {
                // Compile this case's pattern to a guard condition
                // compilePattern returns (guard, body, newBindings)
                // newBindings replaces case.PatternBindings with properly-sourced Binding nodes
                let! (guardExpr, _body, newBindings) =
                    compilePattern scrutineeId case.Pattern case.PatternBindings case.Guard case.Body resultType

                // Build the else branch (rest of the cases)
                let! elseResult = buildDecisionTree rest

                // CRITICAL (January 2026): Guard expressions may reference pattern bindings.
                // When there's a guard, pattern bindings must be hoisted BEFORE the IfThenElse
                // so VarRefs in the guard can resolve. Without a guard, bindings stay inside
                // the then-branch (only evaluated if pattern matches).
                //
                // With guard:    Sequential([bindings..., IfThenElse(guard, body, else)])
                // Without guard: IfThenElse(patternCheck, Sequential([bindings..., body]), else)
                match case.Guard with
                | Some _ ->
                    // Guard may reference pattern bindings - hoist them BEFORE IfThenElse
                    let! ifResult = ifThenElse guardExpr case.Body elseResult resultType
                    return! wrapWithPatternBindings newBindings ifResult resultType
                | None ->
                    // No guard - bindings can stay inside the then-branch
                    let! bodyWithBindings = wrapWithPatternBindings newBindings case.Body resultType
                    return! ifThenElse guardExpr bodyWithBindings elseResult resultType
            }

    buildDecisionTree cases

//=============================================================================
// PUBLIC API: Match Decomposition Entry Point
//=============================================================================

/// Decompose a Match node to IfThenElse decision tree.
/// This is called from HOFDecomposition when encountering SemanticKind.Match.
let decomposeMatch
    (ctx: Context)
    (scrutineeId: NodeId)
    (cases: MatchCase list)
    (resultType: NativeType)
    : Result =
    
    let parser = matchDecomposeParser scrutineeId cases resultType
    runSaturation ctx parser
