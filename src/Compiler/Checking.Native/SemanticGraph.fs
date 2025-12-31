// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// The semantic graph output structure for Firefly consumption.
/// Types are attached during construction (unified representation).
module FSharp.Native.Compiler.Checking.Native.SemanticGraph

open System.Collections.Generic
open FSharp.Native.Compiler.Checking.Native.NativeTypes

//-------------------------------------------------------------------------
// Node Identity
//-------------------------------------------------------------------------

/// Unique identifier for semantic nodes
[<Struct>]
type NodeId = NodeId of int

module NodeId =
    let mutable private counter = 0
    
    let fresh () =
        let id = counter
        counter <- counter + 1
        NodeId id
    
    let reset () = counter <- 0
    
    let value (NodeId id) = id

//-------------------------------------------------------------------------
// SRTP Resolution
//-------------------------------------------------------------------------

/// Resolved SRTP witness - captures the resolution of a statically resolved type parameter
type WitnessResolution = {
    /// The operator being resolved (e.g., "$", "+")
    Operator: string
    /// The type on which the operator is resolved
    ArgType: NativeType
    /// The resolved member (fully qualified)
    ResolvedMember: string
    /// Implementation details for code generation
    Implementation: WitnessImplementation
}

/// How a witness is implemented
and WitnessImplementation =
    /// Direct function call
    | Direct of modulePath: ModulePath * functionName: string
    /// Instance method
    | InstanceMethod of methodName: string
    /// Static method
    | StaticMethod of modulePath: ModulePath * methodName: string
    /// Built-in operation (generated inline)
    | Builtin of operationKind: string

//-------------------------------------------------------------------------
// Literal Values
//-------------------------------------------------------------------------

/// Literal values in the semantic graph
[<RequireQualifiedAccess>]
type LiteralValue =
    | Unit
    | Bool of bool
    | Int8 of int8
    | UInt8 of uint8
    | Int16 of int16
    | UInt16 of uint16
    | Int32 of int32
    | UInt32 of uint32
    | Int64 of int64
    | UInt64 of uint64
    | NativeInt of nativeint
    | UNativeInt of unativeint
    | Float32 of float32
    | Float64 of float
    | Char of char
    | String of string
    | Decimal of decimal
    | ByteArray of byte[]
    | UInt16Array of uint16[]
    | BigInt of string  // For UserNum with bigint suffix

//-------------------------------------------------------------------------
// Pattern Matching
//-------------------------------------------------------------------------

/// A case in a match expression
type MatchCase = {
    /// The pattern to match
    Pattern: Pattern
    /// Optional guard expression
    Guard: NodeId option
    /// The body to execute if matched
    Body: NodeId
}

/// Patterns in match expressions
and [<RequireQualifiedAccess>] Pattern =
    | Const of LiteralValue
    | Var of name: string * ty: NativeType
    | Wildcard
    | Tuple of elements: Pattern list
    | Union of caseName: string * payload: Pattern option * unionType: NativeType
    | Record of fields: (string * Pattern) list * recordType: NativeType
    | Array of elements: Pattern list
    | Or of Pattern * Pattern
    | And of Pattern * Pattern
    | As of Pattern * name: string
    | Null
    | IsType of ty: NativeType
    | Exception of exnType: NativeType * bindName: string option

//-------------------------------------------------------------------------
// Semantic Node Kind
//-------------------------------------------------------------------------

/// The kind of semantic node - what syntactic/semantic construct it represents
[<RequireQualifiedAccess>]
type SemanticKind =
    /// Let binding: let name = value
    | Binding of name: string * isMutable: bool * isRecursive: bool
    
    /// Function application: f arg1 arg2
    | Application of func: NodeId * args: NodeId list
    
    /// Lambda expression: fun x -> body
    | Lambda of parameters: (string * NativeType) list * body: NodeId
    
    /// Literal value
    | Literal of value: LiteralValue
    
    /// Variable reference
    | VarRef of name: string * definition: NodeId option
    
    /// Match expression: match scrutinee with cases
    | Match of scrutinee: NodeId * cases: MatchCase list
    
    /// Sequential expression: expr1; expr2
    | Sequential of nodes: NodeId list
    
    /// While loop: while guard do body
    | WhileLoop of guard: NodeId * body: NodeId
    
    /// For loop: for var = start to/downto finish do body
    | ForLoop of var: string * start: NodeId * finish: NodeId * isUp: bool * body: NodeId
    
    /// For-each loop: for x in collection do body
    | ForEach of var: string * collection: NodeId * body: NodeId
    
    /// If-then-else: if guard then thenBranch else elseBranch
    | IfThenElse of guard: NodeId * thenBranch: NodeId * elseBranch: NodeId option
    
    /// Try-with: try body with handler
    | TryWith of body: NodeId * handler: NodeId
    
    /// Try-finally: try body finally cleanup
    | TryFinally of body: NodeId * cleanup: NodeId
    
    /// Record expression: { field1 = v1; field2 = v2 }
    | RecordExpr of fields: (string * NodeId) list * copyFrom: NodeId option
    
    /// Union case construction: Case payload
    | UnionCase of caseName: string * payload: NodeId option
    
    /// Tuple expression: (e1, e2, ...)
    | TupleExpr of elements: NodeId list
    
    /// Array expression: [| e1; e2; ... |]
    | ArrayExpr of elements: NodeId list
    
    /// List expression: [ e1; e2; ... ]
    | ListExpr of elements: NodeId list
    
    /// Field access: expr.field
    | FieldGet of expr: NodeId * fieldName: string
    
    /// Field set: expr.field <- value
    | FieldSet of expr: NodeId * fieldName: string * value: NodeId
    
    /// Index access: expr.[index]
    | IndexGet of expr: NodeId * index: NodeId
    
    /// Index set: expr.[index] <- value
    | IndexSet of expr: NodeId * index: NodeId * value: NodeId
    
    /// Type annotation: (expr : type)
    | TypeAnnotation of expr: NodeId * annotatedType: NativeType
    
    /// Upcast: expr :> type
    | Upcast of expr: NodeId * targetType: NativeType
    
    /// Downcast: expr :?> type
    | Downcast of expr: NodeId * targetType: NativeType
    
    /// Type test: expr :? type
    | TypeTest of expr: NodeId * testType: NativeType
    
    /// Address-of: &expr or &&expr
    | AddressOf of expr: NodeId * isByref: bool
    
    /// Dereference: !expr
    | Deref of expr: NodeId
    
    /// Assignment: expr <- value
    | Set of target: NodeId * value: NodeId
    
    /// Platform binding marker (for Alex)
    | PlatformBinding of name: string
    
    /// Quote expression: <@ expr @> or <@@ expr @@>
    | Quote of expr: NodeId * isTyped: bool
    
    /// Object expression: { new Interface with member ... }
    | ObjectExpr of interfaceType: NativeType * members: NodeId list
    
    /// Module definition
    | ModuleDef of name: string * members: NodeId list
    
    /// Type definition
    | TypeDef of name: string * kind: TypeDefKind * members: NodeId list
    
    /// Member definition (method, property, etc.)
    | MemberDef of name: string * kind: MemberKind * body: NodeId option
    
    /// Error node (for recovery)
    | Error of message: string

/// Kind of type definition
and TypeDefKind =
    | RecordDef of fields: (string * NativeType) list
    | UnionDef of cases: (string * (string option * NativeType) list) list
    | ClassDef
    | InterfaceDef
    | StructDef
    | EnumDef of cases: (string * LiteralValue) list
    | AbbreviationDef of target: NativeType

/// Kind of member
and MemberKind =
    | Method
    | Property
    | Field
    | Constructor
    | Event

//-------------------------------------------------------------------------
// Semantic Node
//-------------------------------------------------------------------------

/// A node in the semantic graph - the unified representation with types attached
[<NoComparison; NoEquality>]
type SemanticNode = {
    /// Unique identifier for this node
    Id: NodeId
    
    /// What kind of construct this is
    Kind: SemanticKind
    
    /// Source location
    Range: SourceRange
    
    /// Type attached during construction (not post-hoc!)
    Type: NativeType
    
    /// SRTP resolution (if this is an SRTP application)
    SRTPResolution: WitnessResolution option
    
    /// Memory affinity (for allocation decisions)
    ArenaAffinity: ArenaAffinity
    
    /// Layout hint (may be refined during lowering)
    LayoutHint: TypeLayout option
    
    /// Child nodes (structural children)
    Children: NodeId list
    
    /// Parent node (for navigation)
    Parent: NodeId option
    
    /// Additional metadata
    Metadata: Map<string, obj>
}

//-------------------------------------------------------------------------
// Semantic Graph
//-------------------------------------------------------------------------

/// The complete semantic graph output
[<NoComparison; NoEquality>]
type SemanticGraph = {
    /// All nodes in the graph (by ID)
    Nodes: Map<NodeId, SemanticNode>
    
    /// Entry points (e.g., main function, module initializers)
    EntryPoints: NodeId list
    
    /// Module structure
    Modules: Map<ModulePath, NodeId list>
    
    /// Type definitions
    Types: Map<string, NodeId>
}

module SemanticGraph =
    /// Create an empty semantic graph
    let empty : SemanticGraph = {
        Nodes = Map.empty
        EntryPoints = []
        Modules = Map.empty
        Types = Map.empty
    }
    
    /// Add a node to the graph
    let addNode (node: SemanticNode) (graph: SemanticGraph) : SemanticGraph =
        { graph with Nodes = Map.add node.Id node graph.Nodes }
    
    /// Get a node by ID
    let tryGetNode (id: NodeId) (graph: SemanticGraph) : SemanticNode option =
        Map.tryFind id graph.Nodes
    
    /// Get a node by ID (throws if not found)
    let getNode (id: NodeId) (graph: SemanticGraph) : SemanticNode =
        match Map.tryFind id graph.Nodes with
        | Some node -> node
        | None -> failwith $"Node not found: {NodeId.value id}"
    
    /// Add an entry point
    let addEntryPoint (id: NodeId) (graph: SemanticGraph) : SemanticGraph =
        { graph with EntryPoints = id :: graph.EntryPoints }
    
    /// Get all nodes of a given kind
    let nodesOfKind (predicate: SemanticKind -> bool) (graph: SemanticGraph) : SemanticNode list =
        graph.Nodes
        |> Map.values
        |> Seq.filter (fun n -> predicate n.Kind)
        |> List.ofSeq
    
    /// Get all bindings in the graph
    let bindings (graph: SemanticGraph) : SemanticNode list =
        nodesOfKind (function SemanticKind.Binding _ -> true | _ -> false) graph

//-------------------------------------------------------------------------
// Node Builder
//-------------------------------------------------------------------------

/// Builder for creating semantic nodes with type attached
type NodeBuilder() =
    let mutable nodes = Map.empty<NodeId, SemanticNode>
    
    /// Create a new node and add it to the builder
    member _.Create(kind: SemanticKind, ty: NativeType, range: SourceRange, 
                    ?srtp: WitnessResolution, ?arena: ArenaAffinity, 
                    ?layout: TypeLayout, ?children: NodeId list, 
                    ?parent: NodeId) : SemanticNode =
        let id = NodeId.fresh()
        let node = {
            Id = id
            Kind = kind
            Range = range
            Type = ty
            SRTPResolution = srtp
            ArenaAffinity = defaultArg arena ArenaAffinity.CurrentActor
            LayoutHint = layout
            Children = defaultArg children []
            Parent = parent
            Metadata = Map.empty
        }
        nodes <- Map.add id node nodes
        node
    
    /// Get all nodes created by this builder
    member _.Nodes = nodes
    
    /// Build the semantic graph
    member _.Build(entryPoints: NodeId list) : SemanticGraph =
        { Nodes = nodes
          EntryPoints = entryPoints
          Modules = Map.empty
          Types = Map.empty }
    
    /// Reset the builder
    member _.Reset() =
        nodes <- Map.empty
        NodeId.reset()

//-------------------------------------------------------------------------
// Reachability Analysis
//-------------------------------------------------------------------------

module Reachability =
    /// Compute the set of reachable nodes from given entry points
    let computeReachable (graph: SemanticGraph) (entries: NodeId list) : Set<NodeId> =
        let rec walk (visited: Set<NodeId>) (nodeId: NodeId) =
            if Set.contains nodeId visited then
                visited
            else
                match SemanticGraph.tryGetNode nodeId graph with
                | None -> visited
                | Some node ->
                    let visited = Set.add nodeId visited
                    node.Children |> List.fold walk visited
        
        entries |> List.fold walk Set.empty
    
    /// Hard prune unreachable nodes (not soft-delete!)
    let pruneUnreachable (graph: SemanticGraph) : SemanticGraph =
        let reachable = computeReachable graph graph.EntryPoints
        { graph with
            Nodes = graph.Nodes |> Map.filter (fun id _ -> Set.contains id reachable) }

//-------------------------------------------------------------------------
// Graph Traversal
//-------------------------------------------------------------------------

module Traversal =
    /// Fold over all nodes in depth-first pre-order
    let foldPreOrder (folder: 'State -> SemanticNode -> 'State) 
                     (state: 'State) 
                     (graph: SemanticGraph) : 'State =
        let rec walk state nodeId =
            match SemanticGraph.tryGetNode nodeId graph with
            | None -> state
            | Some node ->
                let state = folder state node
                node.Children |> List.fold walk state
        
        graph.EntryPoints |> List.fold walk state
    
    /// Fold over all nodes in depth-first post-order
    let foldPostOrder (folder: 'State -> SemanticNode -> 'State)
                      (state: 'State)
                      (graph: SemanticGraph) : 'State =
        let rec walk state nodeId =
            match SemanticGraph.tryGetNode nodeId graph with
            | None -> state
            | Some node ->
                let state = node.Children |> List.fold walk state
                folder state node
        
        graph.EntryPoints |> List.fold walk state
    
    /// Map over all nodes
    let map (f: SemanticNode -> SemanticNode) (graph: SemanticGraph) : SemanticGraph =
        { graph with
            Nodes = graph.Nodes |> Map.map (fun _ node -> f node) }
    
    /// Filter nodes
    let filter (predicate: SemanticNode -> bool) (graph: SemanticGraph) : SemanticGraph =
        { graph with
            Nodes = graph.Nodes |> Map.filter (fun _ node -> predicate node) }

//-------------------------------------------------------------------------
// Diagnostics
//-------------------------------------------------------------------------

/// Diagnostic severity
type DiagnosticSeverity =
    | Error
    | Warning
    | Info

/// A diagnostic message
type Diagnostic = {
    Severity: DiagnosticSeverity
    Code: string
    Message: string
    Range: SourceRange
    RelatedNodes: NodeId list
}

/// Result of type checking a project
type CheckResult = {
    Graph: SemanticGraph
    Diagnostics: Diagnostic list
}

module CheckResult =
    let hasErrors (result: CheckResult) =
        result.Diagnostics |> List.exists (fun d -> d.Severity = DiagnosticSeverity.Error)
    
    let errors (result: CheckResult) =
        result.Diagnostics |> List.filter (fun d -> d.Severity = DiagnosticSeverity.Error)
    
    let warnings (result: CheckResult) =
        result.Diagnostics |> List.filter (fun d -> d.Severity = DiagnosticSeverity.Warning)
