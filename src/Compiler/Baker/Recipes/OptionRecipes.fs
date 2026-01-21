// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Baker Option Recipes - Decomposition of Option HOFs to primitives.
///
/// Option operations are simpler than List/Map/Set since Option is a discriminated union
/// with just two cases (None, Some). Most operations decompose to conditionals.
///
/// COMBINATOR MODEL:
/// Each recipe is 5-10 lines composing patterns from Ingredients/.
/// The verbose 100+ line manual node construction is eliminated.
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
/// See: Serena memory "baker_saturation_architecture"
module FSharp.Native.Compiler.Baker.Recipes.OptionRecipes

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
// OPTION.MAP: map f opt → if isSome then Some (f (get opt)) else None
//=============================================================================

let private optionMapRecipe
    (mapperNodeId: NodeId)
    (optionNodeId: NodeId)
    (inputType: NativeType)
    (outputType: NativeType)
    : Recipe<NodeId> =
    
    let outputOptionType = NativeType.TApp (Parameterized.optionTyCon, [outputType])
    
    recipe {
        // Check if option has value
        let! isSomeResult = isSome optionNodeId inputType
        
        // Then branch: Some (f (get opt))
        let! value = optionGet optionNodeId inputType
        let! mapped = app1 mapperNodeId value outputType
        let! someResult = some mapped outputType
        
        // Else branch: None
        let! noneResult = none outputType
        
        // Conditional: if isSome then Some(f(get)) else None
        return! ifThenElse isSomeResult someResult noneResult outputOptionType
    }

//=============================================================================
// OPTION.BIND: bind f opt → if isSome then f (get opt) else None
//=============================================================================

let private optionBindRecipe
    (binderNodeId: NodeId)
    (optionNodeId: NodeId)
    (inputType: NativeType)
    (outputType: NativeType)
    : Recipe<NodeId> =
    
    let outputOptionType = NativeType.TApp (Parameterized.optionTyCon, [outputType])
    
    recipe {
        // Check if option has value
        let! isSomeResult = isSome optionNodeId inputType
        
        // Then branch: f (get opt) - binder returns Option<'U>
        let! value = optionGet optionNodeId inputType
        let! boundResult = app1 binderNodeId value outputOptionType
        
        // Else branch: None
        let! noneResult = none outputType
        
        // Conditional: if isSome then f(get) else None
        return! ifThenElse isSomeResult boundResult noneResult outputOptionType
    }

//=============================================================================
// OPTION.FILTER: filter p opt → if isSome && p (get opt) then opt else None
//=============================================================================

let private optionFilterRecipe
    (predicateNodeId: NodeId)
    (optionNodeId: NodeId)
    (valueType: NativeType)
    : Recipe<NodeId> =
    
    let optionType = NativeType.TApp (Parameterized.optionTyCon, [valueType])
    
    recipe {
        // Check if option has value
        let! isSomeResult = isSome optionNodeId valueType
        
        // Get the value
        let! value = optionGet optionNodeId valueType
        
        // Apply predicate
        let! predicateResult = app1 predicateNodeId value Types.boolType
        
        // None for else branches
        let! noneResult = none valueType
        
        // Inner if: if p(value) then opt else None
        // We need a varRef to the original option
        let! optRef = varRef "opt_filter" (Some optionNodeId) optionType
        let! innerIf = ifThenElse predicateResult optRef noneResult optionType
        
        // Outer if: if isSome then innerIf else None
        let! noneOuter = none valueType
        return! ifThenElse isSomeResult innerIf noneOuter optionType
    }

//=============================================================================
// PUBLIC API: tryDecompose
//=============================================================================

/// Try to decompose an Option HOF operation
let tryDecompose
    (ctx: Context)
    (operation: string)
    (args: NodeId list)
    (inputType: NativeType)
    (outputType: NativeType option)
    : Result option =
    
    match operation, args with
    | "map", [mapper; opt] ->
        let outType = outputType |> Option.defaultValue inputType
        Some (runRecipe ctx (optionMapRecipe mapper opt inputType outType))
    
    | "bind", [binder; opt] ->
        let outType = outputType |> Option.defaultValue inputType
        Some (runRecipe ctx (optionBindRecipe binder opt inputType outType))
    
    | "filter", [predicate; opt] ->
        Some (runRecipe ctx (optionFilterRecipe predicate opt inputType))
    
    // Primitive operations - Alex witnesses directly
    | "isSome", _
    | "isNone", _
    | "get", _
    | "defaultValue", _
    | "some", _
    | "none", _ -> None
    
    | _ -> None
