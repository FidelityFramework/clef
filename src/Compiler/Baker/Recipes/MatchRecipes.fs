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
module FSharp.Native.Compiler.Baker.Recipes.MatchRecipes

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.NativeTypedTree.NativeGlobals
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.Baker.Recipes.Decomposition
open FSharp.Native.Compiler.Baker.ShadowAST
open FSharp.Native.Compiler.Baker.Ingredients.RecipeBuilder
open FSharp.Native.Compiler.Baker.Ingredients.Primitives

//=============================================================================
// BRIDGE: Convert Recipe results to Decomposition.Result
//=============================================================================

/// Convert a Decomposition.Context to a RecipeBuilder.RecipeContext
let private toRecipeContext (ctx: Context) : RecipeContext =
    { SourceRange = ctx.SourceRange
      OriginalHOF = ctx.OriginalHOF
      ExpansionId = ctx.ExpansionId
      InspiringNode = ctx.InspiringNode
      Platform = ctx.Platform }

/// Run a recipe and convert to Decomposition.Result
let private runRecipe (ctx: Context) (recipe: Recipe<NodeId>) : Result =
    let recipeCtx = toRecipeContext ctx
    let resultNodeId, nodes = run recipeCtx recipe
    mkResultNoShadow nodes resultNodeId []

//=============================================================================
// PATTERN BINDING HELPERS
//=============================================================================

/// Create let bindings for pattern-bound variables
/// Returns the bound value node ID for use in the body
let private bindPatternVar (name: string) (valueId: NodeId) (ty: NativeType) : Recipe<NodeId> =
    recipe {
        let! bindingId = letBind name valueId ty
        return bindingId
    }

//=============================================================================
// PATTERN COMPILATION
//=============================================================================

/// Compile a single pattern case to a conditional expression.
/// Returns (guard expression, body with bindings).
let rec private compilePattern
    (scrutineeId: NodeId)
    (pattern: Pattern)
    (_patternBindings: NodeId list)
    (guard: NodeId option)
    (body: NodeId)
    (_resultType: NativeType)
    : Recipe<NodeId * NodeId> =
    
    match pattern with
    | Pattern.Wildcard ->
        // Wildcard always matches - guard is "true", body is unchanged
        recipe {
            let! trueId = boolLit true
            // Apply guard if present
            match guard with
            | Some guardId -> return (guardId, body)
            | None -> return (trueId, body)
        }
    
    | Pattern.Var (_name, _ty) ->
        // Variable pattern: bind scrutinee to name, always matches
        recipe {
            let! trueId = boolLit true
            // The pattern binding node should already exist, body uses it
            match guard with
            | Some guardId -> return (guardId, body)
            | None -> return (trueId, body)
        }
    
    | Pattern.Const literal ->
        // Constant pattern: compare scrutinee to literal
        recipe {
            let literalType = literalToType literal
            let! literalId = createAndEmit (SemanticKind.Literal literal) literalType
            let! compareId = compareEq scrutineeId literalId literalType
            match guard with
            | Some guardId ->
                let! combinedGuard = andAlso compareId guardId
                return (combinedGuard, body)
            | None ->
                return (compareId, body)
        }
    
    | Pattern.Union (_caseName, tagIndex, _payload, _unionType) ->
        // Union pattern: compare tag, then extract and bind payload
        recipe {
            let! tagMatches = compareTagEq scrutineeId tagIndex
            
            // If there's a payload pattern, we need to extract and bind it
            // For now, payload bindings are handled via PatternBinding nodes
            // that are already in the PSG (created during type checking)
            
            match guard with
            | Some guardId ->
                let! combinedGuard = andAlso tagMatches guardId
                return (combinedGuard, body)
            | None ->
                return (tagMatches, body)
        }
    
    | Pattern.Tuple _elements ->
        // Tuple pattern: extract each element and match recursively
        // For now, treat as always-match (bindings handled by PatternBinding nodes)
        recipe {
            let! trueId = boolLit true
            match guard with
            | Some guardId -> return (guardId, body)
            | None -> return (trueId, body)
        }
    
    | Pattern.Null ->
        // Null pattern: check if value is null (for reference types)
        // In native F#, this is rare - most types are non-nullable
        recipe {
            let! trueId = boolLit true  // Simplified - treat as always match for now
            match guard with
            | Some guardId -> return (guardId, body)
            | None -> return (trueId, body)
        }
    
    | _ ->
        // Other patterns (Record, Array, Or, And, As, IsType, Exception)
        // Treat as always-match for now, expand as needed
        recipe {
            let! trueId = boolLit true
            match guard with
            | Some guardId -> return (guardId, body)
            | None -> return (trueId, body)
        }

/// Map NTUKind to NativeType
and private ntuKindToType (kind: NTUKind) : NativeType =
    match kind with
    | NTUKind.NTUint8 -> Types.int8Type
    | NTUKind.NTUuint8 -> Types.uint8Type
    | NTUKind.NTUint16 -> Types.int16Type
    | NTUKind.NTUuint16 -> Types.uint16Type
    | NTUKind.NTUint32 -> Types.int32Type
    | NTUKind.NTUuint32 -> Types.uint32Type
    | NTUKind.NTUint64 -> Types.int64Type
    | NTUKind.NTUuint64 -> Types.uint64Type
    | NTUKind.NTUint -> Types.intType
    | NTUKind.NTUuint -> Types.uintType
    | NTUKind.NTUnint -> Types.nintType
    | NTUKind.NTUunint -> Types.unintType
    | NTUKind.NTUfloat32 -> Types.float32Type
    | NTUKind.NTUfloat64 -> Types.floatType
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
    | NativeLiteral.ByteArray _ -> mkArrayType Types.uint8Type
    | NativeLiteral.UInt16Array _ -> mkArrayType Types.uint16Type
    | NativeLiteral.BigInt _ -> Types.int64Type  // BigInt maps to int64 for now

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
    : Recipe<NodeId> =
    
    match patternBindings with
    | [] -> 
        // No bindings - just return the body
        recipe { return bodyId }
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
let matchDecomposeRecipe
    (scrutineeId: NodeId)
    (cases: MatchCase list)
    (resultType: NativeType)
    : Recipe<NodeId> =
    
    let rec buildDecisionTree (remainingCases: MatchCase list) : Recipe<NodeId> =
        match remainingCases with
        | [] ->
            // No more cases - this shouldn't happen with exhaustive patterns
            // Return unit or error value
            createAndEmit (SemanticKind.Literal NativeLiteral.Unit) Types.unitType
        
        | [lastCase] ->
            // Last case - could be wildcard, just return body
            // CRITICAL: Include PatternBindings in the body structure
            match lastCase.Pattern with
            | Pattern.Wildcard ->
                // Wildcard with no guard - wrap body with any bindings
                wrapWithPatternBindings lastCase.PatternBindings lastCase.Body resultType
            | _ ->
                // Non-wildcard last case - still need conditional
                recipe {
                    let! (_guardExpr, _bodyWithBindings) = 
                        compilePattern scrutineeId lastCase.Pattern lastCase.PatternBindings lastCase.Guard lastCase.Body resultType
                    // For last case, wrap body with bindings (assuming exhaustive matching)
                    return! wrapWithPatternBindings lastCase.PatternBindings lastCase.Body resultType
                }
        
        | case :: rest ->
            recipe {
                // Compile this case's pattern to a guard condition
                let! (guardExpr, _bodyWithBindings) = 
                    compilePattern scrutineeId case.Pattern case.PatternBindings case.Guard case.Body resultType
                
                // Wrap case body with its PatternBindings
                let! bodyWithBindings = wrapWithPatternBindings case.PatternBindings case.Body resultType
                
                // Build the else branch (rest of the cases)
                let! elseResult = buildDecisionTree rest
                
                // Build: if guardExpr then bodyWithBindings else elseResult
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
    
    let recipe = matchDecomposeRecipe scrutineeId cases resultType
    runRecipe ctx recipe
