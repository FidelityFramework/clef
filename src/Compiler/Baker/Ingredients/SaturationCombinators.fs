// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// XParsec-Based Saturation Combinators
///
/// Baker generates PSG sub-trees using XParsec parser combinator library.
/// This module provides saturation-specific wrappers around XParsec primitives.
///
/// ARCHITECTURE: Compose from standing art - uses XParsec 0.3.0 library instead
/// of reimplementing combinators (Phase 4.0: Baker XParsec Migration).
///
/// See: Serena memory "compose_from_standing_art_principle"
/// See: Serena memory "baker_saturation_architecture"
module FSharp.Native.Compiler.Baker.Ingredients.SaturationCombinators

open XParsec
open XParsec.Parsers
open XParsec.Combinators
open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types

//=============================================================================
// STATE TYPE - Domain-specific state threaded through saturation
//=============================================================================

/// State threaded through saturation combinators
type SaturationState = {
    /// Nodes emitted so far (in creation order, most recent first)
    EmittedNodes: SemanticNode list
    /// Variable bindings in scope: name -> (nodeId, type)
    Bindings: Map<string, NodeId * NativeType>
    /// Unique expansion ID for this decomposition
    ExpansionId: int
    /// Original HOF name for metadata (e.g., "List.map")
    OriginalHOF: string
    /// Source range for generated nodes (inherited from original HOF)
    SourceRange: SourceRange
    /// The inspiring node that triggered this expansion
    InspiringNode: NodeId
    /// Platform context (for platform-aware saturation)
    Platform: PlatformContext option
}

module SaturationState =
    /// Create initial state for a saturation operation
    let create (sourceRange: SourceRange) (originalHOF: string) (expansionId: int) (inspiringNode: NodeId) (platform: PlatformContext option) =
        { EmittedNodes = []
          Bindings = Map.empty
          ExpansionId = expansionId
          OriginalHOF = originalHOF
          SourceRange = sourceRange
          InspiringNode = inspiringNode
          Platform = platform }

    /// Add an emitted node to state
    let addNode (node: SemanticNode) (state: SaturationState) =
        { state with EmittedNodes = node :: state.EmittedNodes }

    /// Add multiple nodes (maintains order)
    let addNodes (nodes: SemanticNode list) (state: SaturationState) =
        { state with EmittedNodes = List.rev nodes @ state.EmittedNodes }

    /// Bind a variable in scope
    let bindVar (name: string) (nodeId: NodeId) (ty: NativeType) (state: SaturationState) =
        { state with Bindings = Map.add name (nodeId, ty) state.Bindings }

    /// Look up a variable binding
    let lookupVar (name: string) (state: SaturationState) =
        Map.tryFind name state.Bindings

    /// Get all emitted nodes in creation order
    let getNodes (state: SaturationState) =
        List.rev state.EmittedNodes

//=============================================================================
// TYPE ALIASES - Map Baker concepts to XParsec types
//=============================================================================

/// Baker's saturation parser - XParsec Parser with SaturationState
/// Uses ReadableString as dummy input (saturation doesn't consume input, just threads state)
type SaturationParser<'T> =
    Parser<'T, char, SaturationState, ReadableString, ReadableStringSlice>

/// Baker's saturation result - wrapper for backward compatibility
[<Struct>]
type SaturationResult<'T> =
    | Matched of value: 'T
    | NoMatch of reason: string

//=============================================================================
// DOMAIN-SPECIFIC COMBINATORS - Built on XParsec primitives
//=============================================================================

/// Emit a node to the state (uses XParsec's updateUserState)
let emit (node: SemanticNode) : SaturationParser<unit> =
    updateUserState (SaturationState.addNode node)

/// Emit multiple nodes to the state
let emitNodes (nodes: SemanticNode list) : SaturationParser<unit> =
    updateUserState (SaturationState.addNodes nodes)

/// Bind a variable in scope
let withBinding (name: string) (nodeId: NodeId) (ty: NativeType) : SaturationParser<unit> =
    updateUserState (fun s -> SaturationState.bindVar name nodeId ty s)

/// Look up a bound variable (uses XParsec's getUserState)
let lookupBinding (name: string) : SaturationParser<(NodeId * NativeType) option> =
    getUserState |>> fun state -> SaturationState.lookupVar name state

/// Get the source range from state
let getSourceRange : SaturationParser<SourceRange> =
    getUserState |>> fun s -> s.SourceRange

/// Get the expansion ID from state
let getExpansionId : SaturationParser<int> =
    getUserState |>> fun s -> s.ExpansionId

/// Get the original HOF name from state
let getOriginalHOF : SaturationParser<string> =
    getUserState |>> fun s -> s.OriginalHOF

/// Get the inspiring node from state
let getInspiringNode : SaturationParser<NodeId> =
    getUserState |>> fun s -> s.InspiringNode

/// Get the platform context from state
let getPlatform : SaturationParser<PlatformContext option> =
    getUserState |>> fun s -> s.Platform

//=============================================================================
// COMPUTATION EXPRESSION - Use XParsec's parser { } builder
//=============================================================================

/// Computation expression for saturation combinators
/// Delegates to XParsec's parser builder
let saturation = parser

/// Sequence a list of parsers - run each parser and collect results
let rec sequence (parsers: SaturationParser<'a> list) : SaturationParser<'a list> =
    match parsers with
    | [] -> preturn []
    | p :: ps ->
        saturation {
            let! x = p
            let! xs = sequence ps
            return x :: xs
        }

//=============================================================================
// EXECUTION - Adapt XParsec's run to Baker's API
//=============================================================================

/// Run a saturation parser with initial state, return result and emitted nodes
let run (state: SaturationState) (p: SaturationParser<'a>) : SaturationResult<'a> * SemanticNode list =
    // Create dummy reader with Baker's state (empty input, saturation doesn't consume)
    let reader = Reader.ofString "" state

    // Run XParsec parser
    let result = p reader

    // Extract final state and nodes
    let finalState = reader.State
    let nodes = SaturationState.getNodes finalState

    // Convert XParsec result to Baker result for compatibility
    let bakerResult =
        match result with
        | Ok success -> Matched success.Parsed
        | Error err -> NoMatch (sprintf "%A" err.Errors)

    bakerResult, nodes

/// Run a saturation parser, returning only the result
let runValue (state: SaturationState) (p: SaturationParser<'a>) : SaturationResult<'a> =
    let reader = Reader.ofString "" state
    let result = p reader
    match result with
    | Ok success -> Matched success.Parsed
    | Error err -> NoMatch (sprintf "%A" err.Errors)

/// Run a saturation parser, returning result and full final state
let runWithState (state: SaturationState) (p: SaturationParser<'a>) : SaturationResult<'a> * SaturationState =
    let reader = Reader.ofString "" state
    let result = p reader
    let finalState = reader.State
    let bakerResult =
        match result with
        | Ok success -> Matched success.Parsed
        | Error err -> NoMatch (sprintf "%A" err.Errors)
    bakerResult, finalState
