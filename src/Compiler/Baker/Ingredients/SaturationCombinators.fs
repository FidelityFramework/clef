// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// XParsec-Centric Saturation Combinators
///
/// This module defines the core types and combinators for Baker saturation
/// using an XParsec-inspired design. The key insight is that saturation
/// (generating PSG sub-trees) can use the same combinator patterns as parsing.
///
/// Design Philosophy:
/// - SaturationParser<'T> is a function: State -> Result * State
/// - Combinators compose these parsers in a type-safe manner
/// - Failure is explicit via SaturationResult.NoMatch
/// - State threading is automatic through monadic composition
///
/// Uses standard XParsec patterns for saturation combinators.
///
/// See: Serena memory "baker_saturation_architecture"
/// See: Serena memory "compose_from_standing_art_principle"
module FSharp.Native.Compiler.Baker.Ingredients.SaturationCombinators

open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types

//=============================================================================
// RESULT TYPE - Explicit success/failure
//=============================================================================

/// Result of a saturation combinator application
[<Struct>]
type SaturationResult<'T> =
    /// Combinator succeeded with value
    | Matched of value: 'T
    /// Combinator failed with reason (for diagnostics)
    | NoMatch of reason: string

module SaturationResult =
    /// Map over a successful result
    let map (f: 'a -> 'b) (result: SaturationResult<'a>) : SaturationResult<'b> =
        match result with
        | Matched v -> Matched (f v)
        | NoMatch r -> NoMatch r

    /// Bind over a result
    let bind (f: 'a -> SaturationResult<'b>) (result: SaturationResult<'a>) : SaturationResult<'b> =
        match result with
        | Matched v -> f v
        | NoMatch r -> NoMatch r

    /// True if result is Matched
    let isMatched = function Matched _ -> true | NoMatch _ -> false

    /// Get value or raise
    let getValue = function 
        | Matched v -> v 
        | NoMatch r -> failwithf "SaturationResult.getValue on NoMatch: %s" r

//=============================================================================
// STATE TYPE - Threading context through saturation
//=============================================================================

/// State threaded through saturation combinators.
///
/// This unified state carries everything needed for saturation in one place.
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
// PARSER TYPE - The core saturation combinator
//=============================================================================

/// A saturation parser/combinator.
///
/// This is the fundamental building block of XParsec-centric Baker.
/// A parser takes state and produces a result plus new state.
///
/// The type mirrors XParsec's parser type, enabling the same compositional
/// patterns (sequence, choice, mapping) that work for parsing.
type SaturationParser<'T> = SaturationState -> SaturationResult<'T> * SaturationState

//=============================================================================
// PRIMITIVE COMBINATORS
//=============================================================================

/// Return a value without modifying state (XParsec: preturn)
let preturn (x: 'T) : SaturationParser<'T> =
    fun state -> (Matched x, state)

/// Alias for preturn (common in monadic code)
let ret = preturn

/// Fail with a reason (XParsec: pfail)
let pfail (reason: string) : SaturationParser<'T> =
    fun state -> (NoMatch reason, state)

/// Get the current state
let getState : SaturationParser<SaturationState> =
    fun state -> (Matched state, state)

/// Modify the state
let modifyState (f: SaturationState -> SaturationState) : SaturationParser<unit> =
    fun state -> (Matched (), f state)

/// Set the state
let setState (newState: SaturationState) : SaturationParser<unit> =
    fun _ -> (Matched (), newState)

//=============================================================================
// MONADIC COMBINATORS
//=============================================================================

/// Bind: sequence two parsers, threading state (XParsec: >>= / bind)
let bind (f: 'a -> SaturationParser<'b>) (p: SaturationParser<'a>) : SaturationParser<'b> =
    fun state ->
        match p state with
        | Matched a, state' -> f a state'
        | NoMatch r, state' -> (NoMatch r, state')

/// Operator for bind
let (>>=) p f = bind f p

/// Map: transform the result (XParsec: |>>)
let map (f: 'a -> 'b) (p: SaturationParser<'a>) : SaturationParser<'b> =
    fun state ->
        match p state with
        | Matched a, state' -> (Matched (f a), state')
        | NoMatch r, state' -> (NoMatch r, state')

/// Operator for map
let (|>>) p f = map f p

/// Sequence: run first parser, ignore result, run second (XParsec: >>.)
let andThen_ (p1: SaturationParser<'a>) (p2: SaturationParser<'b>) : SaturationParser<'b> =
    fun state ->
        match p1 state with
        | Matched _, state' -> p2 state'
        | NoMatch r, state' -> (NoMatch r, state')

/// Operator for andThen_
let (>>.) p1 p2 = andThen_ p1 p2

/// Sequence: run first parser, keep result, run second (XParsec: .>>)
let thenAnd_ (p1: SaturationParser<'a>) (p2: SaturationParser<'b>) : SaturationParser<'a> =
    fun state ->
        match p1 state with
        | Matched a, state' ->
            match p2 state' with
            | Matched _, state'' -> (Matched a, state'')
            | NoMatch r, state'' -> (NoMatch r, state'')
        | NoMatch r, state' -> (NoMatch r, state')

/// Operator for thenAnd_
let (.>>) p1 p2 = thenAnd_ p1 p2

/// Sequence: run both parsers, combine results (XParsec: .>>.)
let andThen (p1: SaturationParser<'a>) (p2: SaturationParser<'b>) : SaturationParser<'a * 'b> =
    fun state ->
        match p1 state with
        | Matched a, state' ->
            match p2 state' with
            | Matched b, state'' -> (Matched (a, b), state'')
            | NoMatch r, state'' -> (NoMatch r, state'')
        | NoMatch r, state' -> (NoMatch r, state')

/// Operator for andThen
let (.>>.) p1 p2 = andThen p1 p2

//=============================================================================
// CHOICE COMBINATORS
//=============================================================================

/// Choice: try first parser, if it fails try second (XParsec: <|>)
///
/// Note: This is a simple choice that doesn't backtrack state.
/// If p1 fails, p2 runs with the state AFTER p1's failure.
/// For backtracking behavior, use `attempt`.
let choice (p1: SaturationParser<'a>) (p2: SaturationParser<'a>) : SaturationParser<'a> =
    fun state ->
        match p1 state with
        | Matched a, state' -> (Matched a, state')
        | NoMatch _, _ -> p2 state  // Backtrack to original state

/// Operator for choice
let (<|>) p1 p2 = choice p1 p2

/// Try parser, backtracking state on failure
let attempt (p: SaturationParser<'a>) : SaturationParser<'a> =
    fun state ->
        match p state with
        | Matched a, state' -> (Matched a, state')
        | NoMatch r, _ -> (NoMatch r, state)  // Restore original state

/// Optional: try parser, return Some on success, None on failure
let opt (p: SaturationParser<'a>) : SaturationParser<'a option> =
    fun state ->
        match p state with
        | Matched a, state' -> (Matched (Some a), state')
        | NoMatch _, _ -> (Matched None, state)

//=============================================================================
// COLLECTION COMBINATORS
//=============================================================================

/// Sequence a list of parsers, collecting results
let sequence (parsers: SaturationParser<'a> list) : SaturationParser<'a list> =
    let rec loop acc remaining state =
        match remaining with
        | [] -> (Matched (List.rev acc), state)
        | p :: rest ->
            match p state with
            | Matched a, state' -> loop (a :: acc) rest state'
            | NoMatch r, state' -> (NoMatch r, state')
    fun state -> loop [] parsers state

/// Run parser zero or more times until it fails
let many (p: SaturationParser<'a>) : SaturationParser<'a list> =
    let rec loop acc state =
        match p state with
        | Matched a, state' -> loop (a :: acc) state'
        | NoMatch _, _ -> (Matched (List.rev acc), state)
    fun state -> loop [] state

/// Run parser one or more times
let many1 (p: SaturationParser<'a>) : SaturationParser<'a list> =
    p >>= fun first ->
    many p |>> fun rest ->
    first :: rest

//=============================================================================
// STATE ACCESS COMBINATORS
//=============================================================================

/// Emit a node to the state
let emit (node: SemanticNode) : SaturationParser<unit> =
    modifyState (SaturationState.addNode node)

/// Emit multiple nodes
let emitNodes (nodes: SemanticNode list) : SaturationParser<unit> =
    modifyState (SaturationState.addNodes nodes)

/// Bind a variable in scope
let withBinding (name: string) (nodeId: NodeId) (ty: NativeType) : SaturationParser<unit> =
    modifyState (SaturationState.bindVar name nodeId ty)

/// Look up a bound variable
let lookupBinding (name: string) : SaturationParser<(NodeId * NativeType) option> =
    getState |>> fun state -> SaturationState.lookupVar name state

/// Get the source range from state
let getSourceRange : SaturationParser<SourceRange> =
    getState |>> fun s -> s.SourceRange

/// Get the expansion ID from state
let getExpansionId : SaturationParser<int> =
    getState |>> fun s -> s.ExpansionId

/// Get the original HOF name from state
let getOriginalHOF : SaturationParser<string> =
    getState |>> fun s -> s.OriginalHOF

/// Get the inspiring node from state
let getInspiringNode : SaturationParser<NodeId> =
    getState |>> fun s -> s.InspiringNode

/// Get the platform context from state
let getPlatform : SaturationParser<PlatformContext option> =
    getState |>> fun s -> s.Platform

//=============================================================================
// COMPUTATION EXPRESSION BUILDER
//=============================================================================

/// Computation expression builder for saturation parsers.
/// Enables `saturation { ... }` syntax for composing combinators.
type SaturationBuilder() =
    member _.Return(x) = preturn x
    member _.ReturnFrom(p: SaturationParser<'a>) = p
    member _.Bind(p, f) = bind f p
    member _.Zero() = preturn ()
    member _.Combine(p1: SaturationParser<unit>, p2: SaturationParser<'a>) = p1 >>. p2
    member _.Delay(f: unit -> SaturationParser<'a>) : SaturationParser<'a> = fun state -> f () state
    member _.For(items: 'a seq, body: 'a -> SaturationParser<unit>) : SaturationParser<unit> =
        items |> Seq.map body |> Seq.toList |> sequence |>> ignore

/// Computation expression for saturation combinators
let saturation = SaturationBuilder()

//=============================================================================
// EXECUTION
//=============================================================================

/// Run a saturation parser with initial state
let run (state: SaturationState) (p: SaturationParser<'a>) : SaturationResult<'a> * SemanticNode list =
    let result, finalState = p state
    result, SaturationState.getNodes finalState

/// Run a saturation parser, extracting just the result
let runValue (state: SaturationState) (p: SaturationParser<'a>) : SaturationResult<'a> =
    fst (p state)

/// Run a saturation parser, returning result and full final state
let runWithState (state: SaturationState) (p: SaturationParser<'a>) : SaturationResult<'a> * SaturationState =
    p state


