// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Shadow AST - Lightweight representation of synthesized code structure.
///
/// When Baker decomposes HOFs into primitive operations, the resulting PSG nodes
/// have no corresponding source syntax. The Shadow AST provides:
///
/// 1. **Editing Transparency**: Developers can see "code I wrote" vs "compiler-saturated"
/// 2. **Tooling Integration**: IDEs can show expansion views with source links
/// 3. **Provenance Tracking**: Every synthesized element links to its inspiring source
///
/// ARCHITECTURAL PRINCIPLES:
/// - Shadow is SEMANTIC, not 1:1 with PSG nodes
/// - Built alongside PSG in single pass (no separate construction)
/// - Two levels: semantic shadow (developer-facing) + PSG nodes (compiler-facing)
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md (INTERIM: the collections decision in
/// docs/fidelity/phg/Design_Supersession_Register.md replaces HOF decomposition with the sentinel form)
/// See: Serena memory "baker_shadow_ast_architecture"
module Clef.Compiler.Baker.ShadowAST

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

// ═══════════════════════════════════════════════════════════════════════════
// IDENTIFIERS
// ═══════════════════════════════════════════════════════════════════════════

/// Unique identifier for shadow nodes
[<Struct>]
type ShadowId = ShadowId of int

module ShadowId =
    let value (ShadowId id) = id
    
    /// Counter for generating unique IDs within a tree
    let mutable private counter = 0
    
    let fresh () =
        let id = counter
        counter <- counter + 1
        ShadowId id
    
    let reset () =
        counter <- 0

// ═══════════════════════════════════════════════════════════════════════════
// PROVENANCE - Where did this synthesized code come from?
// ═══════════════════════════════════════════════════════════════════════════

/// Provenance tracks the origin of synthesized code
type Provenance = {
    /// The source PSG node that "inspired" this expansion
    InspiringNode: NodeId
    /// Original source range (for IDE navigation)
    SourceRange: SourceRange
    /// What HOF was expanded (e.g., "List.map", "Seq.collect")
    ExpandedOperation: string
    /// Nesting depth (for nested expansions like map inside collect)
    Depth: int
}

module Provenance =
    let create (inspiringNode: NodeId) (range: SourceRange) (operation: string) : Provenance =
        { InspiringNode = inspiringNode
          SourceRange = range
          ExpandedOperation = operation
          Depth = 0 }
    
    let nested (parent: Provenance) (operation: string) : Provenance =
        { parent with
            ExpandedOperation = operation
            Depth = parent.Depth + 1 }

// ═══════════════════════════════════════════════════════════════════════════
// SHADOW REFERENCES - Points to real source or synthesized shadow
// ═══════════════════════════════════════════════════════════════════════════

/// A reference can point to either a shadow node (synthesized) or a real PSG node (source)
[<RequireQualifiedAccess>]
type ShadowRef =
    /// Points to another shadow node (synthesized by Baker)
    | Synthetic of ShadowId
    /// Points to a real PSG node (from developer's source code)
    | Real of NodeId

module ShadowRef =
    let isSynthetic = function ShadowRef.Synthetic _ -> true | _ -> false
    let isReal = function ShadowRef.Real _ -> true | _ -> false

// ═══════════════════════════════════════════════════════════════════════════
// SHADOW EXPRESSIONS - AST-shaped but lightweight
// ═══════════════════════════════════════════════════════════════════════════

/// Shadow expression - captures structure without full SynExpr complexity.
/// This is the "shape" of synthesized code for tooling display.
[<RequireQualifiedAccess>]
type ShadowExpr =
    /// Function application: func(args)
    | App of func: ShadowRef * args: ShadowRef list
    
    /// Conditional: if guard then thenBranch else elseBranch
    | IfThenElse of guard: ShadowRef * thenBranch: ShadowRef * elseBranch: ShadowRef
    
    /// Let binding: let name = value in body
    | Let of name: string * value: ShadowRef * body: ShadowRef * isRecursive: bool
    
    /// Variable reference (bound by Let or Lambda)
    | Var of name: string
    
    /// Primitive/intrinsic reference (List.isEmpty, List.head, etc.)
    | Primitive of moduleName: string * opName: string
    
    /// Lambda: fun params -> body
    | Lambda of parameters: string list * body: ShadowRef
    
    /// Literal value description (for things like empty list, none, etc.)
    | Literal of description: string
    
    /// Match expression (for pattern matching in expansions)
    | Match of scrutinee: ShadowRef * cases: ShadowMatchCase list
    
    /// Sequential expressions
    | Sequential of exprs: ShadowRef list
    
    /// Field access
    | FieldGet of expr: ShadowRef * fieldName: string
    
    /// Field assignment
    | FieldSet of expr: ShadowRef * fieldName: string * value: ShadowRef
    
    /// While loop (for imperative state machine bodies)
    | While of guard: ShadowRef * body: ShadowRef

/// Match case for pattern matching shadows
and ShadowMatchCase = {
    /// Human-readable pattern description (e.g., "IntVal x", "[] (empty)")
    Pattern: string
    /// Optional guard expression
    Guard: ShadowRef option
    /// Body to execute if matched
    Body: ShadowRef
}

// ═══════════════════════════════════════════════════════════════════════════
// SEMANTIC SHADOW KINDS - High-level patterns for different HOF types
// ═══════════════════════════════════════════════════════════════════════════

/// Yield point in a state machine
type YieldPoint = {
    /// Which state yields
    State: string
    /// Description of yielded value
    Value: string
}

/// State transition in a state machine
type StateTransition = {
    /// Starting state
    From: string
    /// Target state
    To: string
    /// Condition for transition (human-readable)
    Condition: string option
    /// Action description
    Action: string option
}

/// Semantic shadow for simple recursive patterns (List.map, List.fold, etc.)
type RecursivePatternShadow = {
    /// The HOF operation (e.g., "List.map")
    Operation: string
    /// Base case description (e.g., "empty list → empty list")
    BaseCase: string
    /// Recursive case description (e.g., "cons(f(head), recurse(tail))")
    RecursiveCase: string
    /// References to source nodes by role
    SourceRefs: Map<string, NodeId>
}

/// Semantic shadow for state machines (Seq operations)
type StateMachineShadow = {
    /// The HOF operation (e.g., "Seq.collect")
    Operation: string
    /// All states in the machine
    States: string list
    /// Initial state name
    InitialState: string
    /// Reference to outer source (the input sequence)
    OuterSource: ShadowRef
    /// Reference to inner mapper function (if applicable)
    InnerMapper: ShadowRef option
    /// Points where the machine yields values
    YieldPoints: YieldPoint list
    /// State transition table
    Transitions: StateTransition list
}

/// Semantic shadow for simple transformations (Option.map, etc.)
type TransformShadow = {
    /// The HOF operation
    Operation: string
    /// Input reference
    Input: ShadowRef
    /// Transformation function reference
    Mapper: ShadowRef
    /// Brief description
    Description: string
}

/// Top-level semantic shadow kind
[<RequireQualifiedAccess>]
type SemanticShadow =
    /// Simple recursive pattern (List.map, List.fold, List.filter, etc.)
    | RecursivePattern of RecursivePatternShadow
    /// State machine (Seq.collect, Seq.unfold, etc.)
    | StateMachine of StateMachineShadow
    /// Simple transformation (Option.map, Option.bind, etc.)
    | Transform of TransformShadow
    /// Tree traversal (Map.add, Set.add, etc.)
    | TreeTraversal of operation: string * description: string * sourceRefs: Map<string, NodeId>

// ═══════════════════════════════════════════════════════════════════════════
// SHADOW NODE - The unit of the shadow AST
// ═══════════════════════════════════════════════════════════════════════════

/// A shadow node - lightweight AST-like node for tooling
type ShadowNode = {
    /// Unique identifier within this shadow tree
    Id: ShadowId
    /// The expression structure
    Expr: ShadowExpr
    /// Which PSG node this shadow corresponds to (for linking)
    PSGNodeId: NodeId
    /// Provenance - where this came from
    Provenance: Provenance
    /// Type of this expression (for rendering)
    Type: NativeType
}

// ═══════════════════════════════════════════════════════════════════════════
// SHADOW TREE - Complete expansion tree
// ═══════════════════════════════════════════════════════════════════════════

/// A shadow tree representing one HOF expansion
type ShadowTree = {
    /// All shadow nodes in this tree, keyed by ID
    Nodes: Map<ShadowId, ShadowNode>
    /// The root of this expansion
    Root: ShadowId
    /// High-level semantic description
    Semantic: SemanticShadow
    /// Provenance for the whole tree
    Provenance: Provenance
}

/// Registry of all shadow trees in a compilation unit
type ShadowRegistry = {
    /// Shadow trees keyed by the inspiring PSG node
    Trees: Map<NodeId, ShadowTree>
}

module ShadowRegistry =
    let empty : ShadowRegistry = { Trees = Map.empty }
    
    let add (inspiringNode: NodeId) (tree: ShadowTree) (registry: ShadowRegistry) : ShadowRegistry =
        { registry with Trees = Map.add inspiringNode tree registry.Trees }
    
    let tryFind (inspiringNode: NodeId) (registry: ShadowRegistry) : ShadowTree option =
        Map.tryFind inspiringNode registry.Trees
    
    let merge (a: ShadowRegistry) (b: ShadowRegistry) : ShadowRegistry =
        { Trees = Map.fold (fun acc k v -> Map.add k v acc) a.Trees b.Trees }

// ═══════════════════════════════════════════════════════════════════════════
// SHADOW BUILDER - Mutable builder for constructing shadow trees
// ═══════════════════════════════════════════════════════════════════════════

/// Builder for constructing shadow trees during expansion
type ShadowBuilder(provenance: Provenance) =
    let mutable nodes = Map.empty<ShadowId, ShadowNode>
    
    member _.Provenance = provenance
    
    /// Create a new shadow node
    member _.Create(expr: ShadowExpr, psgNodeId: NodeId, ty: NativeType) : ShadowId =
        let id = ShadowId.fresh()
        let node = {
            Id = id
            Expr = expr
            PSGNodeId = psgNodeId
            Provenance = provenance
            Type = ty
        }
        nodes <- Map.add id node nodes
        id
    
    /// Create a reference to a real source PSG node
    member _.Real(nodeId: NodeId) : ShadowRef = 
        ShadowRef.Real nodeId
    
    /// Create a reference to a shadow node
    member _.Synthetic(shadowId: ShadowId) : ShadowRef = 
        ShadowRef.Synthetic shadowId
    
    /// Shorthand: create App shadow
    member this.App(func: ShadowRef, args: ShadowRef list, psgNodeId: NodeId, ty: NativeType) : ShadowId =
        this.Create(ShadowExpr.App(func, args), psgNodeId, ty)
    
    /// Shorthand: create Primitive shadow
    member this.Primitive(moduleName: string, opName: string, psgNodeId: NodeId, ty: NativeType) : ShadowId =
        this.Create(ShadowExpr.Primitive(moduleName, opName), psgNodeId, ty)
    
    /// Shorthand: create IfThenElse shadow
    member this.IfThenElse(guard: ShadowRef, thenBr: ShadowRef, elseBr: ShadowRef, psgNodeId: NodeId, ty: NativeType) : ShadowId =
        this.Create(ShadowExpr.IfThenElse(guard, thenBr, elseBr), psgNodeId, ty)
    
    /// Shorthand: create Let shadow
    member this.Let(name: string, value: ShadowRef, body: ShadowRef, isRec: bool, psgNodeId: NodeId, ty: NativeType) : ShadowId =
        this.Create(ShadowExpr.Let(name, value, body, isRec), psgNodeId, ty)
    
    /// Shorthand: create Lambda shadow
    member this.Lambda(parameters: string list, body: ShadowRef, psgNodeId: NodeId, ty: NativeType) : ShadowId =
        this.Create(ShadowExpr.Lambda(parameters, body), psgNodeId, ty)
    
    /// Shorthand: create Var shadow
    member this.Var(name: string, psgNodeId: NodeId, ty: NativeType) : ShadowId =
        this.Create(ShadowExpr.Var name, psgNodeId, ty)
    
    /// Shorthand: create Literal shadow
    member this.Literal(desc: string, psgNodeId: NodeId, ty: NativeType) : ShadowId =
        this.Create(ShadowExpr.Literal desc, psgNodeId, ty)
    
    /// Build the final tree with a semantic summary
    member _.Build(root: ShadowId, semantic: SemanticShadow) : ShadowTree =
        { Nodes = nodes
          Root = root
          Semantic = semantic
          Provenance = provenance }

// ═══════════════════════════════════════════════════════════════════════════
// RENDERING - Produce human-readable views for tooling
// ═══════════════════════════════════════════════════════════════════════════

module Render =
    
    /// Render a shadow reference
    let rec renderRef (tree: ShadowTree) (ref: ShadowRef) : string =
        match ref with
        | ShadowRef.Real nodeId ->
            let (NodeId n) = nodeId
            sprintf "«source:%d»" n
        | ShadowRef.Synthetic shadowId ->
            match Map.tryFind shadowId tree.Nodes with
            | None -> "«unknown»"
            | Some node -> renderExpr tree node.Expr
    
    /// Render a shadow expression as pseudo-F# source
    and renderExpr (tree: ShadowTree) (expr: ShadowExpr) : string =
        match expr with
        | ShadowExpr.App (func, args) ->
            let funcStr = renderRef tree func
            let argsStr = args |> List.map (renderRef tree) |> String.concat " "
            if List.isEmpty args then funcStr
            else sprintf "(%s %s)" funcStr argsStr
        
        | ShadowExpr.IfThenElse (guard, thenBr, elseBr) ->
            sprintf "if %s then %s else %s"
                (renderRef tree guard)
                (renderRef tree thenBr)
                (renderRef tree elseBr)
        
        | ShadowExpr.Let (name, value, body, isRec) ->
            let recKw = if isRec then "rec " else ""
            sprintf "let %s%s = %s in %s"
                recKw name
                (renderRef tree value)
                (renderRef tree body)
        
        | ShadowExpr.Var name -> name
        
        | ShadowExpr.Primitive (modName, opName) ->
            sprintf "%s.%s" modName opName
        
        | ShadowExpr.Lambda (parameters, body) ->
            let paramsStr = parameters |> String.concat " "
            sprintf "(fun %s -> %s)" paramsStr (renderRef tree body)
        
        | ShadowExpr.Literal desc -> desc
        
        | ShadowExpr.Match (scrutinee, cases) ->
            let casesStr =
                cases
                |> List.map (fun c ->
                    let guardStr = c.Guard |> Option.map (fun g -> sprintf " when %s" (renderRef tree g)) |> Option.defaultValue ""
                    sprintf "| %s%s -> %s" c.Pattern guardStr (renderRef tree c.Body))
                |> String.concat " "
            sprintf "match %s with %s" (renderRef tree scrutinee) casesStr
        
        | ShadowExpr.Sequential exprs ->
            exprs |> List.map (renderRef tree) |> String.concat "; "
        
        | ShadowExpr.FieldGet (expr, field) ->
            sprintf "%s.%s" (renderRef tree expr) field
        
        | ShadowExpr.FieldSet (expr, field, value) ->
            sprintf "%s.%s <- %s" (renderRef tree expr) field (renderRef tree value)
        
        | ShadowExpr.While (guard, body) ->
            sprintf "while %s do %s" (renderRef tree guard) (renderRef tree body)
    
    /// Render semantic shadow summary
    let renderSemantic (semantic: SemanticShadow) : string =
        match semantic with
        | SemanticShadow.RecursivePattern rp ->
            sprintf "// Pattern: Recursive (%s)\n//   Base case: %s\n//   Recursive: %s"
                rp.Operation rp.BaseCase rp.RecursiveCase
        
        | SemanticShadow.StateMachine sm ->
            let statesStr = sm.States |> String.concat " → "
            let yieldsStr = 
                sm.YieldPoints 
                |> List.map (fun y -> sprintf "%s: %s" y.State y.Value) 
                |> String.concat ", "
            sprintf "// Pattern: State Machine (%s)\n//   States: %s\n//   Yields: %s"
                sm.Operation statesStr yieldsStr
        
        | SemanticShadow.Transform t ->
            sprintf "// Pattern: Transform (%s)\n//   %s" t.Operation t.Description
        
        | SemanticShadow.TreeTraversal (op, desc, _) ->
            sprintf "// Pattern: Tree Traversal (%s)\n//   %s" op desc
    
    /// Render full expansion with provenance header
    let renderTree (tree: ShadowTree) : string =
        let header = sprintf "// Expanded from %s at %s:%d:%d"
                        tree.Provenance.ExpandedOperation
                        tree.Provenance.SourceRange.File
                        tree.Provenance.SourceRange.Start.Line
                        tree.Provenance.SourceRange.Start.Column
        let semantic = renderSemantic tree.Semantic
        let body = renderRef tree (ShadowRef.Synthetic tree.Root)
        sprintf "%s\n%s\n\n%s" header semantic body
    
    /// Render a brief summary (for inline tooltips)
    let renderBrief (tree: ShadowTree) : string =
        sprintf "Expanded from %s (line %d)"
            tree.Provenance.ExpandedOperation
            tree.Provenance.SourceRange.Start.Line


