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
// Platform Context (NTU Resolution)
//-------------------------------------------------------------------------

/// Platform context for NTU type resolution.
/// Carries quotation-resolved platform information that Alex uses to
/// resolve platform-dependent types (NTUint, NTUptr, etc.) to concrete widths.
[<NoComparison; NoEquality>]
type PlatformContext = {
    /// Platform identifier (e.g., "Linux_x86_64", "Windows_ARM64")
    PlatformId: string
    
    /// Word size in bits (32 or 64)
    WordSize: int
    
    /// Pointer size in bytes (4 or 8)
    PointerSize: int
    
    /// Pointer alignment in bytes
    PointerAlign: int
    
    /// Path to the Fidelity.Platform library
    PlatformLibraryPath: string option
    
    /// Evaluated platform predicates (from quotations)
    Predicates: Map<PlatformPredicate, bool>
}

/// Default platform context for x86_64 Linux (most common development target)
module PlatformContext =
    let defaultLinux_x86_64 = {
        PlatformId = "Linux_x86_64"
        WordSize = 64
        PointerSize = 8
        PointerAlign = 8
        PlatformLibraryPath = None
        Predicates = Map.ofList [
            (PlatformPredicate.FitsU32, true)
            (PlatformPredicate.FitsU64, true)
            (PlatformPredicate.HasAtomics64, true)
            (PlatformPredicate.HasUnalignedAccess, true)
            (PlatformPredicate.HasHardwareFloat, true)
        ]
    }
    
    /// Create a platform context from a platform library path
    let fromPlatformPath (path: string) : PlatformContext =
        // Extract platform ID from path (e.g., "Linux_x86_64" from ".../Fidelity.Platform/Linux_x86_64")
        let platformId =
            let parts = path.Replace("\\", "/").Split('/')
            parts |> Array.tryLast |> Option.defaultValue "Unknown"
        
        // Default to x86_64 assumptions, will be refined by quotation evaluation
        { defaultLinux_x86_64 with
            PlatformId = platformId
            PlatformLibraryPath = Some path }
    
    /// Resolve the byte size for an NTU kind on this platform
    let resolveSize (ctx: PlatformContext) (kind: NTUKind) : int =
        match kind with
        // Platform-dependent
        | NTUKind.NTUint | NTUKind.NTUuint -> ctx.WordSize / 8
        | NTUKind.NTUnint | NTUKind.NTUunint -> ctx.PointerSize
        | NTUKind.NTUptr -> ctx.PointerSize
        | NTUKind.NTUsize | NTUKind.NTUdiff -> ctx.PointerSize
        // Fixed width
        | NTUKind.NTUint8 | NTUKind.NTUuint8 -> 1
        | NTUKind.NTUint16 | NTUKind.NTUuint16 -> 2
        | NTUKind.NTUint32 | NTUKind.NTUuint32 -> 4
        | NTUKind.NTUint64 | NTUKind.NTUuint64 -> 8
        | NTUKind.NTUfloat32 -> 4
        | NTUKind.NTUfloat64 -> 8
        // Special types
        | NTUKind.NTUstring -> 16  // Fat pointer: ptr + length
        | NTUKind.NTUbool -> 1
        | NTUKind.NTUchar -> 4  // UTF-32
        | NTUKind.NTUunit -> 0
        | NTUKind.NTUdecimal -> 16
        // Temporal and identity types
        | NTUKind.NTUuuid -> 16  // 128-bit UUID
        | NTUKind.NTUdatetime -> 8  // 64-bit ticks
        | NTUKind.NTUtimespan -> 8  // 64-bit duration
        | NTUKind.NTUother -> -1  // Unknown
    
    /// Resolve the alignment for an NTU kind on this platform
    let resolveAlign (ctx: PlatformContext) (kind: NTUKind) : int =
        match kind with
        // Platform-dependent - align to word size
        | NTUKind.NTUint | NTUKind.NTUuint -> ctx.WordSize / 8
        | NTUKind.NTUnint | NTUKind.NTUunint -> ctx.PointerAlign
        | NTUKind.NTUptr -> ctx.PointerAlign
        | NTUKind.NTUsize | NTUKind.NTUdiff -> ctx.PointerAlign
        // Fixed width - natural alignment
        | NTUKind.NTUint8 | NTUKind.NTUuint8 -> 1
        | NTUKind.NTUint16 | NTUKind.NTUuint16 -> 2
        | NTUKind.NTUint32 | NTUKind.NTUuint32 -> 4
        | NTUKind.NTUint64 | NTUKind.NTUuint64 -> 8
        | NTUKind.NTUfloat32 -> 4
        | NTUKind.NTUfloat64 -> 8
        // Special types
        | NTUKind.NTUstring -> 8  // Pointer alignment for fat pointer
        | NTUKind.NTUbool -> 1
        | NTUKind.NTUchar -> 4
        | NTUKind.NTUunit -> 1
        | NTUKind.NTUdecimal -> 8
        // Temporal and identity types
        | NTUKind.NTUuuid -> 8  // 64-bit aligned (two i64s)
        | NTUKind.NTUdatetime -> 8  // 64-bit aligned
        | NTUKind.NTUtimespan -> 8  // 64-bit aligned
        | NTUKind.NTUother -> -1

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
// Interpolated Strings
//-------------------------------------------------------------------------

/// A part of an interpolated string
[<RequireQualifiedAccess>]
type InterpolatedPart =
    /// A literal string segment
    | StringPart of string
    /// An expression hole (the {expr} parts)
    | ExprPart of NodeId

//-------------------------------------------------------------------------
// Intrinsic Metadata
//-------------------------------------------------------------------------

/// Module that provides the intrinsic function
/// Used by Alex to dispatch to appropriate emission logic without string matching
[<RequireQualifiedAccess>]
type IntrinsicModule =
    | Sys           // System calls (write, read, exit, nanosleep, etc.)
    | NativePtr     // Pointer operations (get, set, add, stackalloc, etc.)
    | NativeStr     // Native string construction (fromPointer)
    | NativeDefault // Default value generation (zeroed)
    | String        // String operations (concat2, contains, etc.)
    | Console       // Console I/O (writeln, write, readln)
    | Array         // Array operations (zeroCreate, length, get, set)
    | Math          // Math functions
    | Unchecked     // Unchecked arithmetic
    | Operators     // Built-in operators (op_Addition, op_LessThan, etc.)
    | Parse         // String parsing (int, float - NTU string→numeric conversion)
    | Format        // Value formatting (string - NTU numeric→string conversion)
    | Convert       // Type conversions (float, int, int64, byte, etc. - numeric↔numeric)

/// Category of intrinsic - guides how Alex should emit it
[<RequireQualifiedAccess>]
type IntrinsicCategory =
    | Platform      // Emits as platform-specific syscall (Sys.*, Console.*)
    | Memory        // Emits as memory operation (NativePtr.get, set, stackalloc)
    | Arithmetic    // Emits as arith dialect ops (op_Addition, etc.)
    | Comparison    // Emits as comparison ops (op_LessThan, etc.)
    | Bitwise       // Emits as bitwise ops (op_BitwiseAnd, etc.)
    | Conversion    // Emits as type conversion (int, float, etc.)
    | StringOp      // Emits as string manipulation (concat2, etc.)
    | Pure          // Emits as pure MLIR (no side effects, NativeDefault.zeroed)

/// Rich metadata for compiler intrinsics
/// Replaces string-based dispatch with structured information
type IntrinsicInfo = {
    /// The module providing this intrinsic
    Module: IntrinsicModule
    /// The operation name within the module (e.g., "write", "get", "concat2")
    Operation: string
    /// Category guiding emission strategy
    Category: IntrinsicCategory
    /// Original full name for error messages/debugging (e.g., "Sys.write")
    FullName: string
}

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
    /// isEntryPoint: true if [<EntryPoint>] attribute is present
    | Binding of name: string * isMutable: bool * isRecursive: bool * isEntryPoint: bool
    
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
    
    /// Union case construction: Case payload with tag index for emission
    | UnionCase of caseName: string * caseIndex: int * payload: NodeId option
    
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

    /// Named indexed property set: expr.Property[index] <- value
    /// Distinguished from IndexSet because it accesses a named property
    | NamedIndexedPropertySet of expr: NodeId * propName: string * index: NodeId * value: NodeId

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

    /// Compiler intrinsic function (e.g., NativePtr.toNativeInt)
    | Intrinsic of info: IntrinsicInfo

    /// SRTP trait call: (^T : (member Name : unit -> unit) t)
    /// In native compilation, SRTP is resolved at compile time (no runtime dispatch).
    /// The constrainedTypes are the type parameters that must have the member.
    | TraitCall of memberName: string * constrainedTypes: NativeType list * arg: NodeId

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

    /// Interpolated string: $"prefix{expr1}middle{expr2}suffix"
    | InterpolatedString of parts: InterpolatedPart list

    /// Pattern binding: a variable introduced by a match pattern
    /// Following ML/FStar convention where the pattern binding IS the definition.
    /// The type is carried in SemanticNode.Type, name identifies the binding.
    | PatternBinding of name: string

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
// Typed Metadata (no obj!)
//-------------------------------------------------------------------------

/// Typed metadata values for semantic nodes.
/// F# Native does not have 'obj' - all values must be typed.
[<RequireQualifiedAccess>]
type MetadataValue =
    | String of string
    | Int of int
    | Int64 of int64
    | Bool of bool
    | Float of float
    | Type of NativeType
    | NodeId of NodeId
    | SourceRange of SourceRange
    | StringList of string list
    | NodeIdList of NodeId list

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
    
    /// Additional typed metadata (no obj - all values are statically typed)
    Metadata: Map<string, MetadataValue>
    
    /// Soft-delete marker for reachability analysis
    /// When false, node is unreachable but preserved for debugging/analysis
    IsReachable: bool
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
    
    /// Type definitions - lazy extraction from witnessed TypeDef nodes (codata pattern)
    /// Computed on first observation, cached thereafter
    Types: Lazy<Map<string, NodeId>>
    
    /// Platform context for NTU type resolution.
    /// Carries quotation-resolved platform information for Alex to use when
    /// lowering platform-dependent types to concrete MLIR types.
    Platform: PlatformContext option
}

module SemanticGraph =
    /// Extract types index from witnessed TypeDef nodes (lazy computation)
    let private extractTypesIndex (nodes: Map<NodeId, SemanticNode>) : Map<string, NodeId> =
        nodes
        |> Map.values
        |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.TypeDef(name, _, _) -> Some (name, node.Id)
            | _ -> None)
        |> Map.ofSeq
    
    /// Create a lazy types index from nodes
    let mkTypesIndex (nodes: Map<NodeId, SemanticNode>) : Lazy<Map<string, NodeId>> =
        lazy (extractTypesIndex nodes)
    
    /// Recall a type definition by name (codata observation)
    let recallType (name: string) (graph: SemanticGraph) : NodeId option =
        graph.Types.Value |> Map.tryFind name

    /// Create an empty semantic graph
    let empty : SemanticGraph = {
        Nodes = Map.empty
        EntryPoints = []
        Modules = Map.empty
        Types = lazy Map.empty
        Platform = None
    }
    
    /// Create an empty semantic graph with platform context
    let emptyWithPlatform (platform: PlatformContext) : SemanticGraph = {
        Nodes = Map.empty
        EntryPoints = []
        Modules = Map.empty
        Types = lazy Map.empty
        Platform = Some platform
    }
    
    /// Set the platform context on a graph
    let withPlatform (platform: PlatformContext) (graph: SemanticGraph) : SemanticGraph =
        { graph with Platform = Some platform }
    
    /// Add a node to the graph
    let addNode (node: SemanticNode) (graph: SemanticGraph) : SemanticGraph =
        { graph with Nodes = Map.add node.Id node graph.Nodes }
    
    /// Get a node by ID
    let tryGetNode (id: NodeId) (graph: SemanticGraph) : SemanticNode option =
        Map.tryFind id graph.Nodes

    /// Get record field definitions by type name (FCS TyconRef.Deref pattern)
    /// Returns None if type is not found or is not a record type
    let tryGetRecordFields (typeName: string) (graph: SemanticGraph) : (string * NativeType) list option =
        match recallType typeName graph with
        | Some nodeId ->
            match tryGetNode nodeId graph with
            | Some node ->
                match node.Kind with
                | SemanticKind.TypeDef(_, TypeDefKind.RecordDef fields, _) -> Some fields
                | _ -> None  // Not a record type
            | None -> None  // Node not found (shouldn't happen)
        | None -> None  // Type not in index

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
            IsReachable = true  // Default to reachable; soft-delete marks false
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
          Types = SemanticGraph.mkTypesIndex nodes
          Platform = None }
    
    /// Build the semantic graph with platform context
    member _.BuildWithPlatform(entryPoints: NodeId list, platform: PlatformContext) : SemanticGraph =
        { Nodes = nodes
          EntryPoints = entryPoints
          Modules = Map.empty
          Types = SemanticGraph.mkTypesIndex nodes
          Platform = Some platform }
    
    /// Reset the builder
    member _.Reset() =
        nodes <- Map.empty
        NodeId.reset()

//-------------------------------------------------------------------------
// Reachability Analysis
//-------------------------------------------------------------------------

module Reachability =
    /// Extract semantic references from a node's Kind (call targets, definition refs, etc.)
    /// Used by traversal to ensure all semantic children are visited
    let getSemanticReferences (node: SemanticNode) : NodeId list =
        match node.Kind with
        // Application: follow function and arguments
        | SemanticKind.Application (funcId, argIds) ->
            funcId :: argIds
        // VarRef with definition: follow to definition
        | SemanticKind.VarRef (_, Some defId) ->
            [defId]
        // Match: follow scrutinee and case bodies
        | SemanticKind.Match (scrutinee, cases) ->
            scrutinee :: (cases |> List.collect (fun c ->
                match c.Guard with
                | Some g -> [c.Body; g]
                | None -> [c.Body]))
        // Sequential: follow all nodes
        | SemanticKind.Sequential nodes ->
            nodes
        // Binding: follow value node (first child usually)
        | SemanticKind.Binding _ ->
            node.Children
        // Lambda: follow body
        | SemanticKind.Lambda (_, bodyId) ->
            [bodyId]
        // Control flow: follow branches
        | SemanticKind.IfThenElse (guard, thenB, elseB) ->
            guard :: thenB :: (Option.toList elseB)
        | SemanticKind.WhileLoop (guard, body) ->
            [guard; body]
        | SemanticKind.ForLoop (_, start, finish, _, body) ->
            [start; finish; body]
        | SemanticKind.ForEach (_, collection, body) ->
            [collection; body]
        | SemanticKind.TryWith (body, handler) ->
            [body; handler]
        | SemanticKind.TryFinally (body, cleanup) ->
            [body; cleanup]
        // Expressions with sub-expressions
        | SemanticKind.TupleExpr elements ->
            elements
        | SemanticKind.ArrayExpr elements ->
            elements
        | SemanticKind.ListExpr elements ->
            elements
        | SemanticKind.RecordExpr (fields, copyFrom) ->
            (fields |> List.map snd) @ (Option.toList copyFrom)
        | SemanticKind.UnionCase (_, _, payload) ->
            Option.toList payload
        | SemanticKind.FieldGet (expr, _) ->
            [expr]
        | SemanticKind.FieldSet (expr, _, value) ->
            [expr; value]
        | SemanticKind.IndexGet (expr, index) ->
            [expr; index]
        | SemanticKind.IndexSet (expr, index, value) ->
            [expr; index; value]
        | SemanticKind.TypeAnnotation (expr, _) ->
            [expr]
        | SemanticKind.Upcast (expr, _) ->
            [expr]
        | SemanticKind.Downcast (expr, _) ->
            [expr]
        | SemanticKind.Set (target, value) ->
            [target; value]
        | SemanticKind.AddressOf (expr, _) ->
            [expr]
        // ModuleDef: follow member bindings
        | SemanticKind.ModuleDef (_, memberIds) ->
            memberIds
        // Others: use children
        | _ ->
            node.Children

    /// Compute the set of reachable nodes from given entry points
    /// Follows both structural children and semantic references (call edges, etc.)
    let computeReachable (graph: SemanticGraph) (entries: NodeId list) : Set<NodeId> =
        let rec walk (visited: Set<NodeId>) (nodeId: NodeId) =
            if Set.contains nodeId visited then
                visited
            else
                match SemanticGraph.tryGetNode nodeId graph with
                | None -> visited
                | Some node ->
                    let visited = Set.add nodeId visited
                    // Follow both structural children and semantic references
                    let refs = getSemanticReferences node
                    let allRefs = List.append node.Children refs |> List.distinct
                    allRefs |> List.fold walk visited

        entries |> List.fold walk Set.empty

    /// Soft-delete: mark unreachable nodes but preserve structure
    /// Use this for debugging - allows inspection of full graph with reachability info
    let markUnreachable (graph: SemanticGraph) : SemanticGraph =
        let reachable = computeReachable graph graph.EntryPoints
        let updatedNodes =
            graph.Nodes
            |> Map.map (fun id node ->
                { node with IsReachable = Set.contains id reachable })
        { graph with Nodes = updatedNodes }
    
    /// Get counts of reachable and unreachable nodes
    let getReachabilityStats (graph: SemanticGraph) : int * int =
        let reachableCount = 
            graph.Nodes 
            |> Map.filter (fun _ n -> n.IsReachable) 
            |> Map.count
        let unreachableCount = 
            graph.Nodes 
            |> Map.filter (fun _ n -> not n.IsReachable) 
            |> Map.count
        (reachableCount, unreachableCount)

    /// Hard prune unreachable nodes (not soft-delete!)
    /// Use for production - removes unreachable nodes entirely
    let pruneUnreachable (graph: SemanticGraph) : SemanticGraph =
        let reachable = computeReachable graph graph.EntryPoints
        { graph with
            Nodes = graph.Nodes |> Map.filter (fun id _ -> Set.contains id reachable) }

//-------------------------------------------------------------------------
// SCF Region Types (for structured control flow witnessing)
//-------------------------------------------------------------------------

/// Kind of SCF region for control flow operations
type RegionKind =
    /// Guard/condition region (while condition, if condition)
    | GuardRegion
    /// Body region (while body, for body)
    | BodyRegion
    /// Then branch region (if-then)
    | ThenRegion
    /// Else branch region (if-then-else)
    | ElseRegion
    /// Start expression region (for loop start bound)
    | StartExprRegion
    /// End expression region (for loop end bound)
    | EndExprRegion
    /// Match case body region (match case index, 0-based)
    | MatchCaseRegion of index: int

/// Hook for SCF region boundary tracking during traversal
/// Called before/after processing each child region of control flow nodes
type SCFRegionHook<'State> = {
    /// Called before entering a region (e.g., before processing guard subtree)
    BeforeRegion: 'State -> NodeId -> RegionKind -> 'State
    /// Called after exiting a region (e.g., after processing guard subtree)
    AfterRegion: 'State -> NodeId -> RegionKind -> 'State
}

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

    /// Fold with pre-order action for Lambda parameters
    /// The preBind function is called BEFORE children, specifically for binding Lambda params
    /// The folder function is called AFTER children (post-order style for SSA)
    ///
    /// CRITICAL: This traversal follows SEMANTIC dependencies (VarRef.defId), not just
    /// structural containment (Children). When a VarRef references a definition, that
    /// definition is visited first. This ensures correct-by-construction ordering where
    /// definitions are always witnessed before uses.
    let foldWithLambdaPreBind
            (preBind: 'State -> SemanticNode -> 'State)  // Called before children (for Lambda params)
            (folder: 'State -> SemanticNode -> 'State)   // Called after children (for code gen)
            (state: 'State)
            (graph: SemanticGraph) : 'State =
        // Track visited nodes to prevent infinite loops on cyclic references
        let visited = System.Collections.Generic.HashSet<int>()

        let rec walk state nodeId =
            let nodeIdVal = NodeId.value nodeId
            // Skip if already visited (handles cycles and shared references)
            if visited.Contains(nodeIdVal) then
                state
            else
                visited.Add(nodeIdVal) |> ignore
                match SemanticGraph.tryGetNode nodeId graph with
                | None -> state
                | Some node ->
                    // FIRST: Follow semantic dependencies (VarRef definitions)
                    // This ensures definitions are visited before uses
                    let state =
                        match node.Kind with
                        | SemanticKind.VarRef (_, Some defId) ->
                            // Visit the definition first if not already visited
                            walk state defId
                        | _ -> state

                    // Pre-bind Lambda parameters before processing children
                    let state =
                        match node.Kind with
                        | SemanticKind.Lambda _ -> preBind state node
                        | _ -> state

                    // Process semantic references from the Kind
                    // This handles TypeAnnotation.expr, Application.args, Sequential.nodes, etc.
                    let semanticRefs = Reachability.getSemanticReferences node
                    let state = semanticRefs |> List.fold walk state

                    // Also process structural children if any
                    let state = node.Children |> List.fold walk state

                    // Apply main folder (post-order)
                    folder state node

        graph.EntryPoints |> List.fold walk state

    /// Fold with pre-order action for Lambda parameters AND SCF region hooks
    /// Extends foldWithLambdaPreBind with region boundary hooks for control flow nodes.
    /// The scfHook is called before/after each child region of WhileLoop, ForLoop, IfThenElse.
    let foldWithSCFRegions
            (preBind: 'State -> SemanticNode -> 'State)
            (scfHook: SCFRegionHook<'State> option)
            (folder: 'State -> SemanticNode -> 'State)
            (state: 'State)
            (graph: SemanticGraph) : 'State =

        let visited = System.Collections.Generic.HashSet<int>()

        let rec walk state nodeId =
            let nodeIdVal = NodeId.value nodeId
            if visited.Contains(nodeIdVal) then
                state
            else
                visited.Add(nodeIdVal) |> ignore
                match SemanticGraph.tryGetNode nodeId graph with
                | None -> state
                | Some node ->
                    // FIRST: Follow semantic dependencies (VarRef definitions)
                    let state =
                        match node.Kind with
                        | SemanticKind.VarRef (_, Some defId) ->
                            walk state defId
                        | _ -> state

                    // Pre-bind Lambda parameters before processing children
                    let state =
                        match node.Kind with
                        | SemanticKind.Lambda _ -> preBind state node
                        | _ -> state

                    // Process children with SCF region hooks for control flow nodes
                    let state =
                        match node.Kind, scfHook with
                        // WhileLoop: guard region, then body region
                        // NOTE: Both BeforeRegion and AfterRegion receive parentId (the WhileLoop's Id)
                        // so the hook can look up the parent to extract guardId/bodyId as needed
                        | SemanticKind.WhileLoop (guardId, bodyId), Some hook ->
                            let parentId = node.Id
                            // Guard region
                            let state = hook.BeforeRegion state parentId GuardRegion
                            let state = walk state guardId
                            let state = hook.AfterRegion state parentId GuardRegion
                            // Body region
                            let state = hook.BeforeRegion state parentId BodyRegion
                            let state = walk state bodyId
                            let state = hook.AfterRegion state parentId BodyRegion
                            state

                        // ForLoop: start, end, body regions
                        // NOTE: BeforeRegion receives parentId consistently
                        | SemanticKind.ForLoop (_, startId, endId, _, bodyId), Some hook ->
                            let parentId = node.Id
                            // Start expression region
                            let state = hook.BeforeRegion state parentId StartExprRegion
                            let state = walk state startId
                            let state = hook.AfterRegion state parentId StartExprRegion
                            // End expression region
                            let state = hook.BeforeRegion state parentId EndExprRegion
                            let state = walk state endId
                            let state = hook.AfterRegion state parentId EndExprRegion
                            // Body region
                            let state = hook.BeforeRegion state parentId BodyRegion
                            let state = walk state bodyId
                            let state = hook.AfterRegion state parentId BodyRegion
                            state

                        // IfThenElse: only then/else are regions, guard is just a boolean SSA value
                        // NOTE: BeforeRegion receives parentId consistently
                        | SemanticKind.IfThenElse (guardId, thenId, elseIdOpt), Some hook ->
                            let parentId = node.Id
                            // Guard - walk normally (not a region for scf.if)
                            let state = walk state guardId
                            // Then region
                            let state = hook.BeforeRegion state parentId ThenRegion
                            let state = walk state thenId
                            let state = hook.AfterRegion state parentId ThenRegion
                            // Else region (optional)
                            match elseIdOpt with
                            | Some elseId ->
                                let state = hook.BeforeRegion state parentId ElseRegion
                                let state = walk state elseId
                                hook.AfterRegion state parentId ElseRegion
                            | None -> state

                        // Match: scrutinee is evaluated first, then each case body is a region
                        // NOTE: Pattern bindings are children of Match, processed as part of case body traversal
                        | SemanticKind.Match (scrutineeId, cases), Some hook ->
                            let parentId = node.Id
                            // Scrutinee - walk normally (value to match against)
                            let state = walk state scrutineeId
                            // Each case body is a separate region
                            cases
                            |> List.fold (fun (state, idx) case ->
                                let state = hook.BeforeRegion state parentId (MatchCaseRegion idx)
                                // Walk optional guard
                                let state = 
                                    match case.Guard with
                                    | Some guardId -> walk state guardId
                                    | None -> state
                                // Walk case body
                                let state = walk state case.Body
                                let state = hook.AfterRegion state parentId (MatchCaseRegion idx)
                                (state, idx + 1)
                            ) (state, 0)
                            |> fst

                        // No SCF hook or non-control-flow node: process normally
                        | _ ->
                            let semanticRefs = Reachability.getSemanticReferences node
                            let state = semanticRefs |> List.fold walk state
                            node.Children |> List.fold walk state

                    // Apply main folder (post-order)
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
type NativeDiagnosticSeverity =
    | Error
    | Warning
    | Info

/// A diagnostic message
type Diagnostic = {
    Severity: NativeDiagnosticSeverity
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
        result.Diagnostics |> List.exists (fun d -> d.Severity = NativeDiagnosticSeverity.Error)
    
    let errors (result: CheckResult) =
        result.Diagnostics |> List.filter (fun d -> d.Severity = NativeDiagnosticSeverity.Error)
    
    let warnings (result: CheckResult) =
        result.Diagnostics |> List.filter (fun d -> d.Severity = NativeDiagnosticSeverity.Warning)
