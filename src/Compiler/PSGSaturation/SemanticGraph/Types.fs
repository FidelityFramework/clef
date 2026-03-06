// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Core type definitions for the Program Semantic Graph (PSG).
/// These types form the unified representation for Firefly.
module Clef.Compiler.PSGSaturation.SemanticGraph.Types

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.SeqSaturation

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
    | NativePtr     // Pointer operations (get, set, add, stackalloc, etc.) - F# semantics
    | MemRef        // MLIR memref operations (alloca, load, store, storeIndexed) - MLIR semantics
    | NativeStr     // Native string construction (fromPointer)
    | NativeDefault // Default value generation (zeroed)
    | String        // String operations (concat2, contains, etc.)
    | Array         // Array operations (zeroCreate, length, get, set)
    | Math          // Math functions
    | Unchecked     // Unchecked arithmetic
    | Operators     // Built-in operators (op_Addition, op_LessThan, etc.)
    | Parse         // String parsing (int, float - NTU string→numeric conversion)
    | Format        // Value formatting (string - NTU numeric→string conversion)
    | Convert       // Type conversions (float, int, int64, byte, etc. - numeric↔numeric)
    | Crypto        // Cryptographic operations (sha1, base64Encode, base64Decode)
    | Bits          // Bit manipulation and byte order (htons, ntohs, float↔int bits)
    | DateTime      // DateTime operations (now, utcNow, today, toString, components)
    | TimeSpan      // TimeSpan operations (fromMilliseconds, fromSeconds, components)
    | FnPtr         // Function pointer operations (fromSymbol, invoke, ofFunction)
    | Lazy          // Lazy values (create, force, isValueCreated)
    | Seq           // Sequence generation (seq { }, toArray, toList, etc.)
    | SeqEnumerator // Sequence enumerator operations (moveNext, current) - PRD-15/16
    | Arena         // Arena allocation (fromPointer, alloc, allocAligned, remaining, reset)
    | Platform      // Platform info (wordSize, sizeof)
    // PRD-13a: Core Collections
    | Map           // Immutable map operations (empty, add, tryFind, containsKey, values, keys, etc.)
    | Set           // Immutable set operations (empty, add, contains, remove, union, intersect)
    | List          // Immutable list operations (head, tail, length, map, filter, fold, etc.)
    | Option        // Option operations (map, bind, defaultValue, isSome, isNone)
    | Result        // Result operations (map, bind, mapError, isOk, isError, defaultValue)

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
    | Reactive      // Emits as reactive signal operations (Signal.*, Effect.*, Memo.*)

/// Rich metadata for compiler intrinsics
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
// Lambda and Emission Context
//-------------------------------------------------------------------------

/// Context in which a Lambda operates, affecting how captures are extracted at runtime.
[<RequireQualifiedAccess>]
type LambdaContext =
    /// Standard closure: extract captures from {code_ptr, cap0, cap1, ...} at indices 1, 2, ...
    | RegularClosure
    /// Lazy thunk: extract captures from {computed, value, code_ptr, cap0, cap1, ...} at indices 3, 4, ...
    | LazyThunk
    /// Sequence generator context
    | SeqGenerator

/// How a node should be emitted during code generation.
[<RequireQualifiedAccess>]
type EmissionStrategy =
    /// Standard inline emission: emit this node as encountered during traversal.
    | Inline
    /// Separate function: this node's parent handles its emission specially.
    /// captureCount: Number of captures in the enclosing Lambda/SeqExpr.
    | SeparateFunction of captureCount: int
    /// Module-level value binding: emit at start of main function.
    | MainPrologue

//-------------------------------------------------------------------------
// Declaration Roots
//-------------------------------------------------------------------------

/// Declaration root flavor — what makes a binding the "top" of a design.
/// Platform-agnostic: the pipeline routes based on DeclRoot kind.
[<RequireQualifiedAccess>]
type DeclRoot =
    | EntryPoint        // CPU: [<EntryPoint>] or name="main" — OS calls this
    | HardwareModule    // FPGA: [<HardwareModule>] — this IS the circuit

//-------------------------------------------------------------------------
// Module Classification
//-------------------------------------------------------------------------

/// Classification of module members for code generation.
type ModuleClassification = {
    Name: string
    ModuleInit: NodeId list
    Definitions: NodeId list
    DeclarationRoot: (NodeId * DeclRoot) option
}

//-------------------------------------------------------------------------
// Pattern Matching
//-------------------------------------------------------------------------

/// A case in a match expression
type MatchCase = {
    /// The pattern to match
    Pattern: Pattern
    /// PatternBinding NodeIds for variables bound by this pattern.
    PatternBindings: NodeId list
    /// Optional guard expression
    Guard: NodeId option
    /// The body to execute if matched
    Body: NodeId
}

/// An arm in a case elimination — enriched by Baker with concrete bindings.
/// Pattern carries the structural info (Union tag index, payload type).
/// Bindings are fully resolved (DUEliminate + Binding via letBindAt).
and CaseArm = {
    /// The pattern (carries Union tag index and payload type info)
    Pattern: Pattern
    /// NodeIds of binding nodes created by extractPatternBindings
    Bindings: NodeId list
    /// Optional guard expression
    Guard: NodeId option
    /// The body expression
    Body: NodeId
}

/// Patterns in match expressions
and [<RequireQualifiedAccess>] Pattern =
    | Const of NativeLiteral
    | Var of name: string * ty: NativeType
    | Wildcard
    | Tuple of elements: Pattern list
    | Union of caseName: string * tagIndex: int * payload: Pattern option * unionType: NativeType
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
    | Binding of name: string * isMutable: bool * isRecursive: bool * declRoot: DeclRoot option
    | Application of func: NodeId * args: NodeId list
    | Lambda of parameters: (string * NativeType * NodeId) list * body: NodeId * captures: CaptureInfo list * enclosingFunction: string option * context: LambdaContext
    | Literal of value: NativeLiteral
    | VarRef of name: string * definition: NodeId option
    | Match of scrutinee: NodeId * cases: MatchCase list
    /// Structural elimination (catamorphism) — Baker-enriched form of Match.
    /// Preserves the fold structure: constructor index → (bindings, body).
    /// No DUGetTag, comparison, or IfThenElse nodes — those are elision concerns.
    | CaseElimination of scrutinee: NodeId * arms: CaseArm list
    | Sequential of nodes: NodeId list
    | WhileLoop of guard: NodeId * body: NodeId
    | ForLoop of var: string * start: NodeId * finish: NodeId * isUp: bool * body: NodeId
    | ForEach of var: string * collection: NodeId * body: NodeId
    | IfThenElse of guard: NodeId * thenBranch: NodeId * elseBranch: NodeId option
    | TryWith of body: NodeId * handler: NodeId
    | TryFinally of body: NodeId * cleanup: NodeId
    | RecordExpr of fields: (string * NodeId) list * copyFrom: NodeId option
    | UnionCase of caseName: string * caseIndex: int * payload: NodeId option
    /// Extract tag from a DU value (returns i8 or i16 depending on case count)
    | DUGetTag of duValue: NodeId * duType: NativeType
    /// Type-safe payload extraction via case eliminator (pointer bitcast + typed extraction)
    | DUEliminate of duValue: NodeId * caseIndex: int * caseName: string * payloadType: NativeType
    /// Construct a DU value in the specified arena (or implicit arena if None)
    | DUConstruct of caseName: string * caseIndex: int * payload: NodeId option * arenaHint: NodeId option
    | TupleExpr of elements: NodeId list
    | ArrayExpr of elements: NodeId list
    | ListExpr of elements: NodeId list
    | FieldGet of expr: NodeId * fieldName: string
    | FieldSet of expr: NodeId * fieldName: string * value: NodeId
    | IndexGet of expr: NodeId * index: NodeId
    | IndexSet of expr: NodeId * index: NodeId * value: NodeId
    | NamedIndexedPropertySet of expr: NodeId * propName: string * index: NodeId * value: NodeId
    | TypeAnnotation of expr: NodeId * annotatedType: NativeType
    | Upcast of expr: NodeId * targetType: NativeType
    | Downcast of expr: NodeId * targetType: NativeType
    | TypeTest of expr: NodeId * testType: NativeType
    | AddressOf of expr: NodeId * isByref: bool
    | Deref of expr: NodeId
    | Set of target: NodeId * value: NodeId
    | PlatformBinding of name: string
    | Intrinsic of info: IntrinsicInfo
    | TraitCall of memberName: string * constrainedTypes: NativeType list * arg: NodeId
    | Quote of expr: NodeId * isTyped: bool
    | ObjectExpr of interfaceType: NativeType * members: NodeId list
    | ModuleDef of name: string * members: NodeId list
    | TypeDef of name: string * kind: TypeDefKind * members: NodeId list
    | MemberDef of name: string * kind: MemberKind * body: NodeId option
    | InterpolatedString of parts: InterpolatedPart list
    | PatternBinding of name: string
    | LazyExpr of body: NodeId * captures: CaptureInfo list
    | LazyForce of lazyValue: NodeId
    | SeqExpr of body: NodeId * captures: CaptureInfo list
    | Yield of value: NodeId
    | YieldBang of seq: NodeId
    | TupleGet of tuple: NodeId * index: int
    | Error of message: string

/// Kind of type definition
and TypeDefKind =
    | RecordDef of fields: (string * NativeType) list
    | UnionDef of cases: (string * (string option * NativeType) list) list
    | ClassDef
    | InterfaceDef
    | StructDef
    | EnumDef of cases: (string * NativeLiteral) list  // Uses NativeLiteral, not NativeLiteral
    | AbbreviationDef of target: NativeType

/// Kind of member
and MemberKind =
    | Method
    | Property
    | Field
    | Constructor
    | Event

//-------------------------------------------------------------------------
// Typed Metadata
//-------------------------------------------------------------------------

/// Typed metadata values for semantic nodes.
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
// Elaboration Metadata Keys
//-------------------------------------------------------------------------

/// Metadata keys for tracking compiler-elaborated nodes.
///
/// PSG nodes fall into categories:
///   - Source-based: Direct from user's AST (no elaboration metadata)
///   - Elaborated: Synthesized by compiler (has elaboration metadata)
///
/// A for-loop is structurally identical whether from source or elaboration.
/// The ONLY distinction is the presence of these metadata keys.
[<RequireQualifiedAccess>]
module ElaborationMetadata =
    /// What kind of elaboration created this node.
    /// Values: "Intrinsic" | "Baker" | "Coeffect"
    ///   - Intrinsic: Elaborated to implement an intrinsic's semantics
    ///   - Baker: Added during HOF decomposition (List.map → recursion)
    ///   - Coeffect: Added during PSGElaboration nanopasses
    [<Literal>]
    let Kind = "Elaboration.Kind"

    /// What construct triggered the elaboration.
    /// Examples: "List.map", "Console.write", "lazy", "seq"
    [<Literal>]
    let For = "Elaboration.For"

    /// Links related nodes from the same elaboration expansion (int).
    /// All nodes created for a single elaboration share the same ID.
    [<Literal>]
    let Id = "Elaboration.Id"

/// Metadata keys for closure pair construction decisions.
/// Baker marks zero-capture lambdas in value position with these keys,
/// signaling to SSAAssignment that a closure pair must be constructed
/// even when the captures list is empty.
[<RequireQualifiedAccess>]
module ClosureMetadata =
    /// When true, indicates this Lambda requires closure pair construction
    /// ({code_ptr, env_ptr}) even with zero captures. The env_ptr will be null.
    /// Set by Baker when a Lambda is discovered in value position (e.g., as
    /// an argument to an Application).
    [<Literal>]
    let RequiresClosurePair = "Closure.RequiresClosurePair"

//-------------------------------------------------------------------------
// Semantic Node
//-------------------------------------------------------------------------

/// A node in the semantic graph - the unified representation with types attached
[<NoComparison; NoEquality>]
type SemanticNode = {
    Id: NodeId
    Kind: SemanticKind
    Range: SourceRange
    Type: NativeType
    SRTPResolution: WitnessResolution option
    ArenaAffinity: ArenaAffinity
    LayoutHint: TypeLayout option
    Children: NodeId list
    Parent: NodeId option
    Metadata: Map<string, MetadataValue>
    IsReachable: bool
    EmissionStrategy: EmissionStrategy
}

//-------------------------------------------------------------------------
// Semantic Graph
//-------------------------------------------------------------------------

/// The complete semantic graph output
[<NoComparison; NoEquality>]
type SemanticGraph = {
    Nodes: Map<NodeId, SemanticNode>
    DeclarationRoots: (NodeId * DeclRoot) list
    Modules: Map<ModulePath, NodeId list>
    Types: Lazy<Map<string, NodeId>>
    Platform: PlatformContext option
    ModuleClassifications: Lazy<Map<NodeId, ModuleClassification>>
    SeqSaturation: Lazy<Map<NodeId, SeqStateMachineInfo>>
}
