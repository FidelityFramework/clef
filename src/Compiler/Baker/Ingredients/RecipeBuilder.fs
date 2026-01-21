// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Baker Recipe Builder - Opaque type and monadic composition for recipes.
///
/// ARCHITECTURAL ENFORCEMENT:
/// The Recipe type is OPAQUE. Code outside Baker/Ingredients/ cannot:
/// - Construct Recipe values directly
/// - Access the internal representation
/// - Call low-level PSG node constructors
///
/// This ensures recipes are ONLY composed from combinators, preventing
/// the verbose boilerplate anti-pattern.
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
/// See: Serena memory "baker_saturation_architecture"
module FSharp.Native.Compiler.Baker.Ingredients.RecipeBuilder

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types

//=============================================================================
// BUILD STATE
//=============================================================================

/// Accumulated state during recipe execution
type BuildState = {
    /// Nodes created so far (in creation order)
    Nodes: SemanticNode list
    /// Variable bindings in scope: name -> (nodeId, type)
    Bindings: Map<string, NodeId * NativeType>
}

module BuildState =
    let empty = { Nodes = []; Bindings = Map.empty }
    
    let addNode (node: SemanticNode) (state: BuildState) =
        { state with Nodes = node :: state.Nodes }
    
    let addNodes (nodes: SemanticNode list) (state: BuildState) =
        { state with Nodes = List.rev nodes @ state.Nodes }
    
    let bindVar (name: string) (nodeId: NodeId) (ty: NativeType) (state: BuildState) =
        { state with Bindings = Map.add name (nodeId, ty) state.Bindings }
    
    let lookupVar (name: string) (state: BuildState) =
        Map.tryFind name state.Bindings

//=============================================================================
// RECIPE CONTEXT (passed to all recipe operations)
//=============================================================================

/// Context for recipe execution - carries source info and metadata
type RecipeContext = {
    /// Source range for generated nodes (inherited from original HOF)
    SourceRange: SourceRange
    /// Original HOF name for metadata (e.g., "List.map")
    OriginalHOF: string
    /// Unique expansion ID for this decomposition
    ExpansionId: int
    /// The inspiring node that triggered this expansion
    InspiringNode: NodeId
    /// Platform context
    Platform: PlatformContext option
}

//=============================================================================
// RECIPE TYPE (OPAQUE)
//=============================================================================

/// A recipe that builds PSG nodes.
/// 
/// OPAQUE: The internal representation is hidden from code outside Ingredients/.
/// Recipes can only be created via combinators in Primitives.fs and Patterns.fs.
///
/// The recipe is a function: Context -> State -> (Result, NewState)
/// This enables monadic composition.
type Recipe<'a> = private Recipe of (RecipeContext -> BuildState -> 'a * BuildState)

//=============================================================================
// RECIPE EXECUTION
//=============================================================================

/// Run a recipe, returning the result and all created nodes
let run (ctx: RecipeContext) (Recipe f: Recipe<'a>) : 'a * SemanticNode list =
    let result, state = f ctx BuildState.empty
    // Nodes are accumulated in reverse order, so reverse them
    result, List.rev state.Nodes

/// Run a recipe starting from existing state (for composition)
let runWithState (ctx: RecipeContext) (state: BuildState) (Recipe f: Recipe<'a>) : 'a * BuildState =
    f ctx state

//=============================================================================
// MONADIC OPERATIONS
//=============================================================================

/// Return a value without creating any nodes
let ret (x: 'a) : Recipe<'a> =
    Recipe (fun _ctx state -> (x, state))

/// Bind: sequence two recipes, threading state
let bind (Recipe f: Recipe<'a>) (g: 'a -> Recipe<'b>) : Recipe<'b> =
    Recipe (fun ctx state ->
        let a, state' = f ctx state
        let (Recipe h) = g a
        h ctx state')

/// Map: transform the result of a recipe
let map (f: 'a -> 'b) (recipe: Recipe<'a>) : Recipe<'b> =
    bind recipe (f >> ret)

/// Combine two recipes, keeping the second result
let combine (Recipe f: Recipe<unit>) (Recipe g: Recipe<'a>) : Recipe<'a> =
    Recipe (fun ctx state ->
        let (), state' = f ctx state
        g ctx state')

/// Sequence a list of recipes, collecting results
let sequence (recipes: Recipe<'a> list) : Recipe<'a list> =
    let folder recipe acc =
        bind acc (fun results ->
            bind recipe (fun result ->
                ret (result :: results)))
    List.foldBack folder recipes (ret [])

//=============================================================================
// COMPUTATION EXPRESSION BUILDER
//=============================================================================

type RecipeBuilder() =
    member _.Return(x) = ret x
    member _.ReturnFrom(r: Recipe<'a>) = r
    member _.Bind(r, f) = bind r f
    member _.Zero() = ret ()
    member _.Combine(r1, r2) = combine r1 r2
    member _.Delay(f: unit -> Recipe<'a>) = f ()

/// Computation expression for recipe building
let recipe = RecipeBuilder()

//=============================================================================
// INTERNAL: STATE ACCESS (only for Primitives.fs and Patterns.fs)
//=============================================================================

/// INTERNAL: Get the current context
let internal getContext : Recipe<RecipeContext> =
    Recipe (fun ctx state -> (ctx, state))

/// INTERNAL: Get current build state
let internal getState : Recipe<BuildState> =
    Recipe (fun _ctx state -> (state, state))

/// INTERNAL: Modify build state
let internal modifyState (f: BuildState -> BuildState) : Recipe<unit> =
    Recipe (fun _ctx state -> ((), f state))

/// INTERNAL: Add a node to the accumulated nodes
let internal emitNode (node: SemanticNode) : Recipe<unit> =
    modifyState (BuildState.addNode node)

/// INTERNAL: Add multiple nodes
let internal emitNodes (nodes: SemanticNode list) : Recipe<unit> =
    modifyState (BuildState.addNodes nodes)

/// INTERNAL: Bind a variable in scope
let internal bindVariable (name: string) (nodeId: NodeId) (ty: NativeType) : Recipe<unit> =
    modifyState (BuildState.bindVar name nodeId ty)

/// INTERNAL: Look up a variable
let internal lookupVariable (name: string) : Recipe<(NodeId * NativeType) option> =
    recipe {
        let! state = getState
        return BuildState.lookupVar name state
    }
