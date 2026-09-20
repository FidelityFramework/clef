// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Core type definitions for the Program Semantic Graph (PSG).
/// These types form the unified representation for Composer.
module Clef.Compiler.PSGSaturation.SemanticGraph.Types

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.DimensionAlgebra

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
    | Mmio          // Opaque exact-width volatile register access
    | BorrowedView  // Declared mapped-storage access; no address constructors
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
    | Memory        // Emits as memory operation (MemRef.load, store, alloca)
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
    | KernelModule      // NPU: [<KernelModule>] — compute kernel dispatched to AIE tiles

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
// Proof Obligations: graph citizens (C-01 14.5; Obligation_Residency 3)
//-------------------------------------------------------------------------
//
// An obligation is a node in V (its identity, provenance and source position;
// the thing Lattice shows) and a hyperedge in F whose source set is the
// structure it constrains. Both readings in the corpus -- "obligation node with
// dependency edges" (C-01) and "obligations as hyperedges" (PHG paper 6.4) --
// are this one structure seen from V and from F.
//
// Obligations are minted at saturation by Baker, over the saturated graph, and
// discharged twice against the same anchor name: design-time from the graph
// (SMT-LIB to cvc5) and build-time from the witnessed MLIR (smt dialect).
// Nothing below the graph authors an obligation.
//
// INVARIANT I1: every body is a proposition over literals with an enumerated
// source set. All fragments are quantifier-free.

/// The exponent relation required by a numeric operation. These laws concern
/// dimensions; they do not assert numeric range, precision or nonzero divisors.
[<RequireQualifiedAccess>]
type DimensionalRule =
    | Product
    | Quotient
    | SameDimension
    | Comparison

/// What an obligation asserts. Every constant is a literal fixed at saturation;
/// the two dispatches transcribe, never compute.
type MappedSpanModel = {
    PointerBits: int
    MaximumExtent: bigint
    ElementBytes: int
    BaseAlignment: int
    ElementAlignment: int
}

/// Numeric premises of an admitted monotone loop, normalized to increasing
/// coordinates. Original source identities and direction stay in F.
type FiniteLoopTripModel = {
    InitialLower: bigint
    LimitUpper: bigint
    MinimumStep: bigint
    Inclusive: bool
    MaximumIterations: bigint
}

/// An additive enclosure across all iteration prefixes, including the initial
/// state and the final write. This is independent of any physical carrier.
type AdditiveLoopInvariantModel = {
    MaximumIterations: bigint
    InitialLower: bigint
    InitialUpper: bigint
    DeltaLower: bigint
    DeltaUpper: bigint
    Lower: bigint
    Upper: bigint
}

[<RequireQualifiedAccess>]
type ObligationBody =
    | FiniteLoopTrip of FiniteLoopTripModel
    | AdditiveLoopInvariant of AdditiveLoopInvariantModel
    /// The additive/index step after successful native mapping guards establish
    /// a finite byte extent. Native allocation provenance and stride*rows
    /// arithmetic are explicit premises, not conclusions of this QF_LIA slice.
    | MappedElementSpan of model: MappedSpanModel
    /// Exact integer literal enclosed by the range already analysed on its node.
    | IntegerLiteralRange of value: bigint * lower: bigint * upper: bigint
    /// The analysed integer range fits the representation actually selected
    /// from the platform declaration; this does not assert physical placement.
    | IntegerRepresentationCoverage of lower: bigint * upper: bigint * minimum: bigint * maximum: bigint
    /// Dimensional positions in an ordinary call: instantiated signature versus
    /// actual arguments/result. A missing side is an incompatible type shape,
    /// never an invented dimensionless value. Paths include partial results.
    | ApplicationDimensions of comparisons: (string * Dimension option * Dimension option) list
    /// Exact source-real literal and the singleton enclosure it seeds.
    | RealLiteralRange of value: ExactRational * lower: ExactRational * upper: ExactRational
    /// Finite-bound coverage against the actual representation declaration.
    /// This is a range obligation, not a rounding or optimal-selection claim.
    | RealRepresentationCoverage of lower: ExactRational * upper: ExactRational * minimum: ExactRational * maximum: ExactRational
    /// Actual operand/result dimensions from the saturated graph. Free measure
    /// variables retain their identities as formal generators; the solver
    /// checks each coefficient, including axes absent from another operand.
    /// Comparisons have no numeric result dimension (None).
    | DimensionalRelation of rule: DimensionalRule * left: Dimension * right: Dimension * result: Dimension option
    /// storage = len + 1 (the NUL byte is reserved at allocation)
    | StorageReservation of len: int * storage: int
    /// view = len AND view < storage (the terminator is never written)
    | ViewContainment of view: int * len: int * storage: int
    /// final storage byte is 0x00
    | NulSentinel of lastByte: int
    /// consecutive layout of the given storages is pairwise disjoint, spans
    /// exactly `span` bytes, and -- where a declared space bounds it -- the
    /// span fits the space's capacity. `capacity` is None when no declaration
    /// was found to cite.
    | ConsecutiveLayout of storages: int list * span: int * capacity: int64 option
    /// Concrete BAREWire placements in the exact byte pool emitted by Composer.
    /// Every alignment, extent and capacity is checked, never assumed.
    | StaticStorageLayout of slots: (int * int * int) list * usedSize: int * allocationSize: int * poolAlignment: int * capacity: int64 * spaceAlignment: int * granularity: int
    /// Exact ordered continuation slots, including alignment padding. This
    /// establishes layout only, not allocation lifetime or a memory budget.
    /// The empty transient activation layout has extent zero and alignment one.
    | ContinuationLayout of slots: (int * int * int) list * extent: int * alignment: int
    /// String.concat2 copy discipline: for ANY operand lengths a, b >= 0
    /// (pinned where the operand is a literal), the two copy windows [0,a) and
    /// [a,a+b) lie within the (a+b)-byte allocation.
    | ConcatCopyBound of leftLen: int option * rightLen: int option
    /// A declared buffer's capacity is positive.
    | CapacityPositive of capacity: int64
    /// A declared buffer's capacity is at most its declared space's capacity.
    | CapacityFits of capacity: int64 * spaceCapacity: int64
    /// The count handed to a reader is the declared capacity, which sizes the
    /// allocation the same declaration governs (count <= allocation).
    | InputBufferBound of count: int64 * allocation: int64
    /// For any successful read of r bytes, 1 <= r <= capacity, the trimmed copy
    /// of r - 1 bytes is within bound.
    | InputCopyBound of capacity: int64 * bound: int64

/// The obligation record carried by an Obligation node.
type ObligationInfo = {
    /// Stable anchor name: the identity that travels through both dispatches
    Id: string
    /// The family (callsheet vocabulary): "storage-reservation", "buffer-capacity", ...
    Kind: string
    /// SMT-LIB logic fragment: "QF_LIA" or "QF_BV"
    Logic: string
    /// Human-readable statement (ledger and demo surface)
    Statement: string
    /// Origin. A program site is file:line:col; a declaration is
    /// `<description id>:<declaration name>` (BAREWire Platform/Obligations.fs).
    Source: string
    /// External rule cross-references (CWE ids)
    Refs: string list
    Body: ObligationBody
}

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
    /// Baker-settled finite continuation selection. Each child is a complete
    /// region; the witness pulls those regions without discovering successors.
    | ContinuationDispatch of selector: NodeId * cases: (int * NodeId) list * otherwise: NodeId
    /// Typed access to a slot whose identity and layout belong to a settled
    /// continuation frame. The slot reference is not an initializer demand.
    | FrameRead of frame: NodeId * slot: NodeId
    /// Borrow the typed cell view, retaining its frame's lifetime obligation.
    | FrameBorrow of frame: NodeId * slot: NodeId
    | FrameWrite of frame: NodeId * slot: NodeId * value: NodeId
    /// Transient activation storage, separate from the persistent suspension
    /// frame. Its exact slots and extent are settled on the owning continuation.
    | ContinuationStorage of owner: NodeId
    /// Internal caller-owned destination for one sequence factory result.
    /// Allocation does not initialize the frame; the factory constructor does.
    | ContinuationAllocate of owner: NodeId
    /// Uninitialized owned aggregate backing at a proven activation occurrence.
    | AggregateStorage of source: NodeId
    /// Initialize a case in an explicit typed destination; returns unit.
    | DUInitialize of destination: NodeId * caseName: string * caseIndex: int * payload: NodeId option
    /// A logical callable retains its implementation separately from its
    /// actual environment value. The implementation body remains deferred.
    | ClosureValue of implementation: NodeId * environment: NodeId
    /// Formation snapshots already evaluated captures at this occurrence.
    /// Slot identities are provenance, never demands to reevaluate declarations.
    | EnvironmentCreate of owner: NodeId * initializers: (NodeId * NodeId) list
    | EnvironmentReference of callable: NodeId
    | EnvironmentRead of environment: NodeId * slot: NodeId
    | EnvironmentBorrow of environment: NodeId * slot: NodeId
    | EnvironmentWrite of environment: NodeId * slot: NodeId * value: NodeId
    | ForLoop of var: string * start: NodeId * finish: NodeId * isUp: bool * body: NodeId
    | ForEach of var: string * formal: NodeId * collection: NodeId * body: NodeId
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
    /// A proof obligation as a graph citizen. Its constraining structure is
    /// the source set of its hyperedge in F; it is never on the emission spine.
    | Obligation of ObligationInfo

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
// Program Hypergraph: the edge set (F) and its annotation (beta)
//-------------------------------------------------------------------------
//
// PHG = (V, F, alpha, beta) -- arxiv-papers/program-hypergraph-paper.md 2.1.
//   V      the node set                     (SemanticGraph.Nodes)
//   F      the hyperedge set                (SemanticGraph.Edges)
//   alpha  per-node annotation              (Type, ArenaAffinity, LayoutHint, Metadata)
//   beta   per-edge annotation              (Class, Role, Ordinal)
//
// A hyperedge is f = (S_f, t_f, lambda_f): a SOURCE SET that produces or
// constrains a TARGET. The PSG is the degenerate case in which every
// |S_f| = 1, so this embedding preserves behaviour by construction (2.4).
//
// DIRECTION. Sources produce or constrain the target. An Application's callee
// and arguments are the sources of the Application node; a VarRef's definition
// is the source of the VarRef. Reachability therefore walks target -> sources,
// which is the direction the existing parent -> children walk already takes.
//
// INVARIANT I1 (enumerated source sets). S_f is finite and fixed at
// elaboration. Nothing may construct an edge whose source set is open; that is
// what keeps the obligations these edges will carry quantifier-free.

/// Ports of a local evaluation contract. Operand indices identify incidences
/// within the target node, not runtime states or new semantic node identities.
[<RequireQualifiedAccess>]
type EvaluationPort =
    | Entry
    | OperandEntry of int
    | OperandExit of int
    | Ready
    | Exit

[<RequireQualifiedAccess>]
type EvaluationTransfer =
    | Continue
    | WhenTrue
    | WhenFalse
    | Resume

/// A value demand does not re-execute a referenced declaration's initializer.
[<RequireQualifiedAccess>]
type EvaluationAccess =
    | Value
    | Storage

/// Explicitly unsettled local contracts; these are not source diagnostics or
/// permission for a witness to reconstruct missing control semantics.
[<RequireQualifiedAccess>]
type EvaluationResidual =
    | MissingOperand
    | InvalidShape
    | MatchSelection
    | ExceptionFlow
    | CollectionIteration
    | CountedIteration
    | Delegation

/// How an edge participates in the graph's projections.
[<RequireQualifiedAccess>]
type LoopRangeResidual =
    | Guard
    | Step
    | OtherWrites
    | ConditionalUpdate
    | CapturedCell
    | UnknownEffect
    | Reentry
    | NonAdditive
    | MissingBound

[<RequireQualifiedAccess>]
type EdgeClass =
    /// Containment: the source is structurally part of the target.
    /// These are the edges that materialise as SemanticNode.Children.
    | Structural
    /// A non-containment relation the reachability walk must still follow:
    /// VarRef -> its binding, a node's type -> its TypeDef, an intrinsic ->
    /// its implementation, a string literal -> the symbol it names.
    | Reference
    /// Provenance: groups the nodes minted by one enrichment firing.
    | Provenance
    /// An obligation's constraining structure -> the obligation node.
    | Obligation
    /// Suspension, iterator and continuation evidence settled by Baker.
    /// Roles distinguish ownership, enumerated cuts and resume/live identities;
    /// these are neither containment nor executable transfer edges.
    | Suspension
    /// Baker's local evaluation contracts. Composition, dominance and frame
    /// liveness require further saturation; this is not a flattened CFG.
    | Evaluation
    /// Joint numeric premises and their recurrence dependency, distinct from
    /// the local interval annotation resulting from range saturation.
    | Range

/// The role the source plays relative to the target -- the edge label.
/// Generalises Traversal.RegionKind, which named the same thing but was
/// handed to a callback and discarded instead of being stored.
[<RequireQualifiedAccess>]
type EdgeRole =
    /// [conversion; input; allocation; complete alias/write/value premises]
    /// -> exact array occurrence. Byte units, not UTF-8 sequence validity.
    | StringByteStorage of lower: bigint * upper: bigint * representation: string
    /// [allocation; array occurrence; complete write/value premises] -> element read.
    | StringByteRead
    /// The exact read enclosure derived from complete encoding storage premises.
    | StringByteRange of lower: bigint * upper: bigint
    /// [original input; fresh copy] -> conversion; copy preserves string immutability.
    | StringByteSnapshot
    /// [immutable string; internal byte view; fresh copy] -> public array conversion.
    | StringToBytesSnapshot
    /// Complete storage range establishes ASCII text.
    | StringAscii
    /// The exact immutable byte sequence passed strict UTF-8 decoding.
    | StringUtf8Constant of bytes: byte list
    /// [owner; guard; induction cell; initial value; limit; step; update; store]
    /// -> loop. Direction and strictness describe the actual comparison.
    | LoopInduction of ascending: bool * inclusive: bool
    /// [loop; induction cell; accumulator initial; store; update; delta]
    /// -> accumulator cell. Both cell and exact update acquire its enclosure.
    | LoopAccumulation
    /// [owner; loop] -> cell whose recurrence remains outside admission.
    | LoopRangePending of LoopRangeResidual
    // structural
    | Callee
    | Argument
    | Parameter
    | Body
    | Scrutinee
    | CaseBinding
    | CaseGuard
    | CaseBody
    | Guard
    | ThenBranch
    | ElseBranch
    | LoopStart
    | LoopFinish
    | Collection
    | Handler
    | Cleanup
    | Element
    | FieldValue
    | CopyFrom
    | Payload
    | ArenaHint
    | AssignTarget
    | AssignValue
    | Subject
    | Index
    | Member
    | Operand
    | InterpolationPart
    /// A child attached by the builder rather than derived from the kind
    /// payload -- a Binding's value, an Intrinsic's arguments.
    | Attached
    // reference
    | Definition
    | TypeDefinition
    | IntrinsicImplementation
    | Symbol
    // provenance
    | EnrichedWith
    /// Ordered startup, its preserved source entry, and the actual execution spine.
    | ProgramInitialization
    /// Source entry and its declaration constrain an unsettled initializer.
    | ProgramInitializationPending of reason: string
    /// [module; source binding; initializer; startup lambda] -> ordered spine.
    | ProgramInitializer
    /// Startup, source entry and exact owned-unit or demanded-value premises
    /// activate this module's implementation unit before the source call.
    | ProgramUnitActivation
    /// [startup binding; source binding; source lambda; startup lambda] -> call.
    | ProgramEntryCall
    /// [startup lambda; spine; initializer] -> runtime value binding.
    | ProgramValueIntent
    /// Runtime value intent joined with the exact writable program designation.
    | ProgramValue
    /// [startup; caller activation; callee occurrence; implementation] -> call.
    | ProgramActivationCall
    /// Startup and complete finite callable uses cover the implementation.
    | ProgramActivationCoverage
    /// An elaborated expression's distinct mutually exclusive branch occurrence.
    /// Sources retain the original expression and its original branch body.
    | BranchOccurrence
    /// Direct capture origin: ordered sources [lambda; captured declaration]
    /// produce the hidden formal target. The declaration may itself be a
    /// hidden formal; source tooling follows this specific relation by identity.
    | CaptureOrigin
    /// Exact environment formation inputs; the flag retains shared-cell mode.
    /// [owner; source declaration; initializer] -> environment creation.
    | EnvironmentCapture of isMutable: bool
    | EnvironmentInitializer
    | EnvironmentFormal
    /// Complete-use covering activation and retained source cells.
    | EnvironmentResidence
    /// Exact source closure, implementation and formal supplying a child constructor.
    | SequenceCaptureFormation
    /// Original child slot and its eager value/cell initializer; never a new slot identity.
    | SequenceCaptureInitializer of isMutable: bool
    /// Joint environment coverage, actual call and caller-owned child destination.
    | SequenceEnvironmentBorrow
    /// Ordered sources [sequence owner; its generator] constrain the target
    /// Yield/YieldBang site. Ordinal is zero, not a resumption state number.
    | Delimiter
    /// Ordered sources [delegation expression; supplied sequence operand]
    /// produce the target owner-local yield after Baker expands yield!.
    | DelegationOrigin
    /// [immutable enumerator binding; successful pull guard; iteration loop]
    /// admits the target current read at that loop's first body action.
    | IteratorCurrentAdmitted
    /// [enumerator binding; successful pull guard; iteration loop] retains the
    /// current-admission dependency of the target current call's element facts.
    | SequenceElementAdmission
    /// [iterator operand; sequence owner] contributes a finite known origin.
    | SequenceElementOwner
    /// [sequence owner; exact yielded payload] contributes to the target
    /// admitted current call's range fixed point, through its delimiter.
    | SequenceElementPayload
    /// [iterator operand; unknown origin site] prevents finite narrowing.
    | SequenceElementUnknown
    /// [iterator operand; source sequence owner; generator; deferred body]
    /// supplies one possible body's source-cell writes to the target pull.
    | SequencePullBody
    /// [sequence operand; source owner; generator] establishes fresh iterator
    /// formation without invoking that deferred body at the target acquisition.
    | SequenceInitialize
    /// [operand; unresolved origin site] prevents a closed effect summary for
    /// the target iterator operation, even alongside other known origins.
    | SequenceEffectUnknown
    /// [owner; generator; payload] enumerates the target source cut's state.
    | SuspensionCut of int
    /// [owner; generator; source cut] retains an exact live-across value.
    | SuspensionLiveAcross
    /// [owner; generator; source cut] selects the generated resume entry;
    /// state zero has only owner/generator because it precedes every cut.
    | SuspensionResume of int
    /// [owner; generator; generated entry; source cut when positive] selects
    /// the actual first dispatch action after pass-through control is skipped.
    | SuspensionResumeAction of int
    /// [owner; generator; state slot] selects the completed-entry body.
    | SuspensionCompleted
    /// [owner; operand] constrains a container's indexed operand demand.
    | EvaluationOperand of EvaluationAccess
    /// Port transfer within the target container. Sources retain the owner
    /// and the operands named by the two ports; identities never hide in beta.
    | EvaluationFlow of EvaluationPort * EvaluationPort * EvaluationTransfer
    /// [owner; captured declaration] constrains deferred value formation.
    | EvaluationCapture
    /// [owner; generator] selects that generator's own body as a local root.
    | EvaluationRoot
    /// [owner; resident related sites] constrains an unsettled local contract.
    | EvaluationPending of EvaluationResidual
    | ContinuationCase of int
    | ContinuationDefault
    | FrameSlot
    /// Exact source-value identity retained by continuation realization.
    | ContinuationValue
    | ContinuationRegion
    | ContinuationBorrow
    /// Source value, destination, discriminant and selected case initialization.
    | AggregateCopy
    /// Successful current read, owned snapshot and its finite activation uses.
    | AggregateSnapshot
    /// [source allocation; covering activation; captured declaration;
    /// capturing generator] proves the target sequence template's complete
    /// bounded use is covered by its captured source allocation's residence.
    | SequenceTemplateBorrow
    // declared platform (BAREWire docs/11: cross-applied with the code it governs)
    /// A declared memory space or buffer schema constrains the value that
    /// resides in it: source = the declaration node, target = the value.
    | Resides
    /// The structure an obligation constrains -> the obligation node.
    | Constrains

/// One hyperedge. In this phase every edge is degenerate (|Sources| = 1);
/// the list is the shape arity > 1 requires and costs nothing now.
[<NoComparison; NoEquality>]
type Hyperedge = {
    /// S_f -- the nodes that produce or constrain the target.
    Sources: NodeId list
    /// t_f -- what they produce or constrain.
    Target: NodeId
    /// beta: which projections this edge belongs to.
    Class: EdgeClass
    /// beta: the role the sources play.
    Role: EdgeRole
    /// beta: position among same-role siblings (argument 0, 1, ...); 0 if unique.
    Ordinal: int
}

/// Canonical edge construction and projection.
[<RequireQualifiedAccess>]
module Hyperedge =

    /// A degenerate edge: `source` produces or constrains `target`.
    let edge1 (cls: EdgeClass) (role: EdgeRole) (ordinal: int) (source: NodeId) (target: NodeId) : Hyperedge =
        { Sources = [source]; Target = target; Class = cls; Role = role; Ordinal = ordinal }

    /// The single source of a degenerate edge.
    let soleSource (e: Hyperedge) : NodeId = List.head e.Sources

    let isStructural (e: Hyperedge) = (e.Class = EdgeClass.Structural)
    let isReference (e: Hyperedge) = (e.Class = EdgeClass.Reference)

/// Every edge implied by a node's SemanticKind payload.
///
/// THIS IS THE SINGLE DEFINITION OF THE KIND-DERIVED RELATION. It replaces the
/// three hand-maintained case-per-kind matches that each re-derived it:
///   Builder.extractImpliedChildren      -- the structural projection
///   Reachability.getSemanticReferences  -- structural + reference projection
///   FoldIn.updateKindRefs               -- the rewriting direction
///
/// Those three had drifted. Lambda parameters appeared in the first and not the
/// second; Binding and Intrinsic fell back to node.Children in the second and
/// were leaves in the first; and InterpolatedString's ExprParts were missing
/// from the structural projection entirely, so interpolation sub-expressions
/// never became children and survived only because the other projection caught
/// them. One table cannot drift against itself.
///
/// `target` is the node whose kind this is; every returned edge points at it.
let kindEdges (target: NodeId) (kind: SemanticKind) : Hyperedge list =
    // one structural edge
    let st role src = Hyperedge.edge1 EdgeClass.Structural role 0 src target
    // an ordered run of same-role structural edges
    let sts role srcs = srcs |> List.mapi (fun i src -> Hyperedge.edge1 EdgeClass.Structural role i src target)
    // one reference edge
    let rf role src = Hyperedge.edge1 EdgeClass.Reference role 0 src target

    match kind with
    | SemanticKind.Application (func, args) ->
        st EdgeRole.Callee func :: sts EdgeRole.Argument args

    | SemanticKind.Lambda (parameters, body, _, _, _) ->
        sts EdgeRole.Parameter (parameters |> List.map (fun (_, _, nodeId) -> nodeId))
        @ [ st EdgeRole.Body body ]

    | SemanticKind.Match (scrutinee, cases) ->
        st EdgeRole.Scrutinee scrutinee
        :: (cases |> List.mapi (fun ordinal c ->
                sts EdgeRole.CaseBinding c.PatternBindings
                @ (c.Guard |> Option.toList |> List.map (fun source -> Hyperedge.edge1 EdgeClass.Structural EdgeRole.CaseGuard ordinal source target))
                @ [ Hyperedge.edge1 EdgeClass.Structural EdgeRole.CaseBody ordinal c.Body target ]) |> List.concat)

    | SemanticKind.CaseElimination (scrutinee, arms) ->
        st EdgeRole.Scrutinee scrutinee
        :: (arms |> List.mapi (fun ordinal arm ->
                sts EdgeRole.CaseBinding arm.Bindings
                @ (arm.Guard |> Option.toList |> List.map (fun source -> Hyperedge.edge1 EdgeClass.Structural EdgeRole.CaseGuard ordinal source target))
                @ [ Hyperedge.edge1 EdgeClass.Structural EdgeRole.CaseBody ordinal arm.Body target ]) |> List.concat)

    | SemanticKind.Sequential nodes -> sts EdgeRole.Element nodes
    | SemanticKind.WhileLoop (guard, body) -> [ st EdgeRole.Guard guard; st EdgeRole.Body body ]
    | SemanticKind.ContinuationDispatch (selector, cases, otherwise) ->
        st EdgeRole.Scrutinee selector :: st EdgeRole.ContinuationDefault otherwise
        :: (cases |> List.map (fun (state, body) -> st (EdgeRole.ContinuationCase state) body))
    | SemanticKind.FrameRead (frame, slot) -> [ st EdgeRole.Subject frame; Hyperedge.edge1 EdgeClass.Provenance EdgeRole.FrameSlot 0 slot target ]
    | SemanticKind.FrameBorrow (frame, slot) -> [ st EdgeRole.Subject frame; Hyperedge.edge1 EdgeClass.Provenance EdgeRole.FrameSlot 0 slot target ]
    | SemanticKind.FrameWrite (frame, slot, value) ->
        [ st EdgeRole.Subject frame; Hyperedge.edge1 EdgeClass.Provenance EdgeRole.FrameSlot 0 slot target; st EdgeRole.AssignValue value ]
    | SemanticKind.ContinuationStorage owner
    | SemanticKind.ContinuationAllocate owner
    | SemanticKind.AggregateStorage owner ->
        [ Hyperedge.edge1 EdgeClass.Provenance EdgeRole.Definition 0 owner target ]
    | SemanticKind.ClosureValue (implementation, environment) ->
        [ st EdgeRole.Body implementation; st EdgeRole.Subject environment ]
    | SemanticKind.EnvironmentCreate (owner, initializers) ->
        Hyperedge.edge1 EdgeClass.Provenance EdgeRole.Definition 0 owner target
        :: (initializers |> List.mapi (fun ordinal (_, value) ->
            Hyperedge.edge1 EdgeClass.Reference EdgeRole.EnvironmentInitializer ordinal value target))
    | SemanticKind.EnvironmentReference value -> [st EdgeRole.Subject value]
    | SemanticKind.EnvironmentRead (environment, slot)
    | SemanticKind.EnvironmentBorrow (environment, slot) ->
        [st EdgeRole.Subject environment; Hyperedge.edge1 EdgeClass.Provenance EdgeRole.FrameSlot 0 slot target]
    | SemanticKind.EnvironmentWrite (environment, slot, value) ->
        [st EdgeRole.Subject environment; st EdgeRole.AssignValue value
         Hyperedge.edge1 EdgeClass.Provenance EdgeRole.FrameSlot 0 slot target]
    | SemanticKind.ForLoop (_, start, finish, _, body) ->
        [ st EdgeRole.LoopStart start; st EdgeRole.LoopFinish finish; st EdgeRole.Body body ]
    | SemanticKind.ForEach (_, formal, collection, body) ->
        [ st EdgeRole.Collection collection; st EdgeRole.Parameter formal; st EdgeRole.Body body ]
    | SemanticKind.IfThenElse (guard, thenB, elseB) ->
        [ st EdgeRole.Guard guard; st EdgeRole.ThenBranch thenB ]
        @ (elseB |> Option.toList |> List.map (st EdgeRole.ElseBranch))
    | SemanticKind.TryWith (body, handler) -> [ st EdgeRole.Body body; st EdgeRole.Handler handler ]
    | SemanticKind.TryFinally (body, cleanup) -> [ st EdgeRole.Body body; st EdgeRole.Cleanup cleanup ]

    | SemanticKind.RecordExpr (fields, copyFrom) ->
        (copyFrom |> Option.toList |> List.map (st EdgeRole.CopyFrom))
        @ sts EdgeRole.FieldValue (fields |> List.map snd)
    | SemanticKind.UnionCase (_, _, payload) ->
        payload |> Option.toList |> List.map (st EdgeRole.Payload)
    | SemanticKind.DUGetTag (duValue, _) -> [ st EdgeRole.Subject duValue ]
    | SemanticKind.DUEliminate (duValue, _, _, _) -> [ st EdgeRole.Subject duValue ]
    | SemanticKind.DUInitialize (destination, _, _, payload) ->
        st EdgeRole.Subject destination :: (payload |> Option.toList |> List.map (st EdgeRole.Payload))
    | SemanticKind.DUConstruct (_, _, payload, arenaHint) ->
        (payload |> Option.toList |> List.map (st EdgeRole.Payload))
        @ (arenaHint |> Option.toList |> List.map (st EdgeRole.ArenaHint))

    | SemanticKind.TupleExpr elements -> sts EdgeRole.Element elements
    | SemanticKind.ArrayExpr elements -> sts EdgeRole.Element elements
    | SemanticKind.ListExpr elements -> sts EdgeRole.Element elements
    | SemanticKind.TupleGet (tuple, _) -> [ st EdgeRole.Subject tuple ]

    | SemanticKind.FieldGet (expr, _) -> [ st EdgeRole.Subject expr ]
    | SemanticKind.FieldSet (expr, _, value) ->
        [ st EdgeRole.Subject expr; st EdgeRole.AssignValue value ]
    | SemanticKind.IndexGet (expr, index) ->
        [ st EdgeRole.Subject expr; st EdgeRole.Index index ]
    | SemanticKind.IndexSet (expr, index, value) ->
        [ st EdgeRole.Subject expr; st EdgeRole.Index index; st EdgeRole.AssignValue value ]
    | SemanticKind.NamedIndexedPropertySet (expr, _, index, value) ->
        [ st EdgeRole.Subject expr; st EdgeRole.Index index; st EdgeRole.AssignValue value ]

    | SemanticKind.TypeAnnotation (expr, _) -> [ st EdgeRole.Operand expr ]
    | SemanticKind.Upcast (expr, _) -> [ st EdgeRole.Operand expr ]
    | SemanticKind.Downcast (expr, _) -> [ st EdgeRole.Operand expr ]
    | SemanticKind.TypeTest (expr, _) -> [ st EdgeRole.Operand expr ]
    | SemanticKind.AddressOf (expr, _) -> [ st EdgeRole.Operand expr ]
    | SemanticKind.Deref expr -> [ st EdgeRole.Operand expr ]
    | SemanticKind.Set (target', value) ->
        [ st EdgeRole.AssignTarget target'; st EdgeRole.AssignValue value ]
    | SemanticKind.TraitCall (_, _, arg) -> [ st EdgeRole.Argument arg ]
    | SemanticKind.Quote (expr, _) -> [ st EdgeRole.Operand expr ]

    | SemanticKind.ObjectExpr (_, members) -> sts EdgeRole.Member members
    | SemanticKind.ModuleDef (_, members) ->
        members |> List.mapi (fun ordinal memberId -> Hyperedge.edge1 EdgeClass.Reference EdgeRole.Member ordinal memberId target)
    | SemanticKind.TypeDef (_, _, members) -> sts EdgeRole.Member members
    | SemanticKind.MemberDef (_, _, body) ->
        body |> Option.toList |> List.map (st EdgeRole.Body)

    | SemanticKind.LazyExpr (body, _) -> [ st EdgeRole.Body body ]
    | SemanticKind.LazyForce lazyValue -> [ st EdgeRole.Subject lazyValue ]
    | SemanticKind.SeqExpr (body, _) -> [ st EdgeRole.Body body ]
    | SemanticKind.Yield value -> [ st EdgeRole.Operand value ]
    | SemanticKind.YieldBang seq -> [ st EdgeRole.Operand seq ]

    // Interpolation parts ARE structural. The previous structural projection
    // treated this kind as a leaf, so these never became children.
    | SemanticKind.InterpolatedString parts ->
        sts EdgeRole.InterpolationPart
            (parts |> List.choose (function
                | InterpolatedPart.ExprPart id -> Some id
                | InterpolatedPart.StringPart _ -> None))

    // A resolved VarRef names the binding that produces its value. This is a
    // relation, not containment: the definition is not part of the reference.
    | SemanticKind.VarRef (_, Some defId) -> [ rf EdgeRole.Definition defId ]
    | SemanticKind.VarRef (_, None) -> []

    // Kinds whose children are attached by the builder rather than carried in
    // the payload: a Binding's value, an Intrinsic's arguments. Their edges
    // come from `attachedEdges` below, which reads node.Children.
    | SemanticKind.Binding _
    | SemanticKind.Intrinsic _ -> []

    // Obligation nodes: their edges are minted by the obligation pass, in F,
    // with an enumerated source set. Nothing is derived from the payload.
    | SemanticKind.Obligation _ -> []

    // Genuine leaves.
    | SemanticKind.Literal _
    | SemanticKind.PlatformBinding _
    | SemanticKind.PatternBinding _
    | SemanticKind.Error _ -> []

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
    | RealLiteral of sourceText: string * value: ExactRational
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

/// Metadata keys for a declared buffer's facts, projected onto the program
/// site that reads into it. This is the hyperedge's consequence on alpha
/// (PHG paper 2.4): the site carries the capacity as a saturated annotation,
/// and the lowering reads it. Nothing below the graph authors the number.
[<RequireQualifiedAccess>]
module BufferMetadata =
    /// Declared capacity in bytes (MetadataValue.Int64)
    [<Literal>]
    let Capacity = "Buffer.Capacity"
    /// The declaration cited, `<platform id>:<buffer name>` (MetadataValue.String)
    [<Literal>]
    let Declaration = "Buffer.Declaration"
    /// Whether the framing delimiter is trimmed from the value (MetadataValue.Bool)
    [<Literal>]
    let TrimDelimiter = "Buffer.TrimDelimiter"

/// Metadata keys for the obligations a node is constrained by: the anchor
/// names of every obligation hyperedge this node is a source of, projected
/// onto the node at saturation. This is the transport rule's first carrier
/// (PHG paper 2.4a) -- a saturated annotation the witness reads as codata --
/// and the witness reifies it as the second (2.4b): an attribute on the op it
/// emits, so the artifact carries the correspondence explicitly.
[<RequireQualifiedAccess>]
module ObligationMetadata =
    /// Anchor names, in obligation-node order (MetadataValue.StringList)
    [<Literal>]
    let Anchors = "Obligation.Anchors"

/// Metadata keys for the generalisation of let-bound schemes (design b.4 step 4).
[<RequireQualifiedAccess>]
module SchemeMetadata =
    /// On an Application node whose function is a use of a generalised binding: the instance
    /// of the scheme at this use (MetadataValue.Type), so hover shows the instance while the
    /// binding keeps its scheme.
    [<Literal>]
    let Instantiation = "Scheme.Instantiation"

/// Metadata keys for closure pair construction decisions.
/// Baker marks zero-capture lambdas in value position with these keys,
/// signaling to SSAAssignment that a closure pair must be constructed
/// even when the captures list is empty.
[<RequireQualifiedAccess>]
module ClosureMetadata =
    /// The source-visible callable type before hidden capture parameters are
    /// made explicit. Semantic Type remains the fully saturated signature.
    [<Literal>]
    let SourceSignature = "Closure.SourceSignature"

    /// An anonymous function expression (`fun` or `function`), distinguished from
    /// the Lambda used to represent a named function declaration. Synthetic subsequent
    /// parameter groups of one `fun` are not separate expression boundaries.
    [<Literal>]
    let LambdaExpression = "Closure.LambdaExpression"

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
    /// The analysed range of an integer value (Dimensional_Range_Design.md §1; Horizon C3): a
    /// coeffect beside the type, written once by RangeAnalysis at saturation and read by every
    /// later pass. `None`: not a numeric node, or not analysed (unreachable). `Some r`: analysed;
    /// `r` is the range, and the width is derived from it on read (`ValueRange.width`), never
    /// stored beside it. An unobservable `r` (no width) is CCS8011 at the node.
    ValueRange: ValueRange option
}

//-------------------------------------------------------------------------
// Settled layouts (Dimensional_Range_Design.md §3.3, ruling 2; Layout_As_Joint_Constraint.md §3)
//-------------------------------------------------------------------------

/// How one field of a settled layout is held on the graph's platform. A record's layout is the
/// consequence of its fields' selections, settled at saturation once the range pass has run and
/// the platform has filled the context (CS-11 slice 0); `TypeConRef.Layout` keeps the identity of
/// a type's layout family and never a byte count.
[<RequireQualifiedAccess>]
type SettledSlot =
    /// Owned bytes at an already settled aggregate extent and alignment.
    | InlineBytes of bytes: int * alignment: int
    /// An integer at the representation its range selects: the bits, and the declared
    /// representation's name on a core (`None` on fabric, where the width is exactly the range's).
    | Integer of bits: int * representation: string option
    /// A boolean: one byte on a core, one bit on fabric.
    | Bool
    /// A char at its code-point representation (32 bits).
    | Char
    /// A real at its declared bits.
    | Real of bits: int
    /// A pointer-sized field: `words` declared Pointer widths. One word is an address (a handle,
    /// a byref, a list or map node); five words a view of a buffer (a string, an array, a nested
    /// record, a tuple, an option, a union, a lazy, a seq or a function's closure pair), which the
    /// CPU leg holds as its memref descriptor: two addresses, an offset, a
    /// size and a stride. The word count is the leg's realisation, read here and never summed
    /// below the graph; a declaration of it belongs to the platform description (CS-12, owed).
    | Pointer of words: int
    /// The unit value, held as the leg's zero of 32 bits.
    | Unit
    /// A type the pass cannot place (an unresolved variable, an unmapped kind): a stop for any
    /// reader that needs its size, naming the type.
    | Opaque of what: string

/// One field of a settled layout: its slot, and on a core its byte offset, size and alignment,
/// tiled in declaration order with the alignment the selected representation declares
/// (native-type-universe.md §2.3). `None` on a context declaring no representations (fabric).
type SettledField = {
    Name: string
    Slot: SettledSlot
    Offset: int option
    Size: int option
    Align: int option
}

/// The settled layout of an aggregate type.
[<RequireQualifiedAccess>]
type SettledLayout =
    /// A record (or a tuple, `Item1`..): its fields, its size and its alignment (`None` on fabric,
    /// or where a field is opaque).
    | Record of fields: SettledField list * size: int option * align: int option
    /// A union (a user union, an option, a Result): one byte of tag at offset zero, then the
    /// payload slot of the widest case at `payloadOffset`; each case names its payload slot
    /// (`None` for a case without one). The tag-then-payload form is the leg's realisation of a
    /// union as a byte buffer read through typed views; its alignment is one.
    | Union of cases: (string * SettledSlot option) list * payloadOffset: int option * size: int option * align: int option

//-------------------------------------------------------------------------
// Semantic Graph
//-------------------------------------------------------------------------

//-------------------------------------------------------------------------
// Codata read by emission (CCS_Architecture.md, "Coeffects Computed During Elaboration")
//-------------------------------------------------------------------------
//
// Facts about the saturated graph that Composer's witnesses read and never compute. Each row
// below was once computed in Composer's PSGElaboration layer; that layer is gone, and the graph
// is the one authority (Alex observes, it does not compute, infer or decide). The values these
// facts give rise to at emission are emission's own to name.

/// How a constructed value escapes its defining scope: the four-point lifetime lattice
/// (closure-representation.md §3.3). Read by the allocation site's witness to place the value on
/// the stack, in static storage, or in the arena.
[<RequireQualifiedAccess>]
type EscapeKind =
    | StackScoped
    | EscapesViaClosure of target: NodeId
    | EscapesViaReturn
    | EscapesViaByRef
    | StaticLifetime

/// How a meet adapts its operand (Dimensional_Range_Design.md §3.1, §8.3; rulings 1 and 3).
[<RequireQualifiedAccess>]
type MeetKind =
    | ExtendUnsigned
    | ExtendSigned
    | Truncate
    | ExtendFloat
    | TruncateFloat

/// One meet: the consumer node, the operand node (the consumer itself for a read of a slot), and
/// the bit widths it adapts between.
type Meet = { Consumer: NodeId; Operand: NodeId; From: int; To: int; Adapt: MeetKind }

/// A partial application of a flattened curried function.
type PartialApplication = { TargetBindingId: NodeId; SuppliedArgNodes: NodeId list; TotalParams: int }

/// A call that saturates a partial application: the target and every argument in order.
type SaturatedCall = { TargetBindingId: NodeId; AllArgNodes: NodeId list }

/// The curried structure of the graph once nested lambdas are flattened (Curry.fs).
type CurryInfo = {
    PartialApplications: Map<NodeId, PartialApplication>
    SaturatedCalls: Map<NodeId, SaturatedCall>
    /// Bindings that hold a partial application (their witnesses emit nothing).
    PartialAppBindings: Set<NodeId>
    /// Lambdas absorbed by flattening (unreachable now).
    AbsorbedLambdas: Set<NodeId>
    /// Arguments of partial applications whose emission is deferred to the saturating call.
    DeferredArgNodes: Set<NodeId>
}

/// What a closure environment slot holds.
[<RequireQualifiedAccess>]
type CaptureSlotKind =
    /// The actual environment of a separately known callable implementation.
    /// No function address, runtime type tag or legacy closure pair is stored.
    | EnvironmentView of owner: NodeId
    /// A complete rank-one memref descriptor for a captured mutable cell.
    /// Its payload type is retained; no address-to-view reconstruction occurs.
    | CellView of NativeType
    /// A complete rank-one descriptor for a buffer-backed value. Bounds and
    /// stride travel with the value rather than being reconstructed from an address.
    | ValueView of NativeType
    /// Owned aggregate bytes, never a descriptor to separately lived storage.
    | InlineValue of NativeType
    /// One word: the base address of a buffer-backed value (a record, tuple, union, lazy, seq,
    /// function value's pair) or of a mutable cell; construction extracts the base pointer first.
    | Address
    /// One word held as it arrives, such as an opaque handle.
    | Handle
    /// A string or array, decomposed into its base address and its extent: two words.
    | Decomposed
    /// A scalar at its settled slot.
    | Scalar of SettledSlot

/// One settled slot of a closure environment.
type CaptureSlot = {
    Capture: string
    Index: int
    Holds: CaptureSlotKind
    /// The byte offset after the environment's prefix.
    ByteOffset: int
    Bytes: int
    Mutable: bool
    SourceNode: NodeId option
}

/// The prefix an environment carries before its capture slots.
[<RequireQualifiedAccess>]
type ClosurePrefix =
    /// The code pointer.
    | RegularClosure
    /// A lazy thunk: the computed flag, the value at its slot, the code pointer.
    | LazyThunk of value: SettledSlot * valueBytes: int
    /// A seq generator: the state, the current value's address, the code pointer.
    | SeqGenerator

/// The settled placement of a closure's environment (Layout_As_Joint_Constraint.md §2.1, the
/// closure aggregate). Composer reads offsets and sizes here and computes none.
type ClosurePlacement = {
    Lambda: NodeId
    Prefix: ClosurePrefix
    PrefixBytes: int
    Captures: CaptureSlot list
    /// The captures alone.
    CapturesBytes: int
    /// One word for the code pointer, then the captures.
    WithCodePointerBytes: int
    /// The prefix, then the captures.
    WithPrefixBytes: int
}

/// A continuation slot retains the declaration/value identity used by Baker's
/// liveness relation and the exact representation chosen by placement.
type ContinuationSlot = {
    Source: NodeId
    ValueType: NativeType
    Field: SettledField
    Holds: CaptureSlotKind
    IsCapture: bool
}

/// Shared typed slot placement for one materialized closure environment.
/// Empty captures have a real zero-byte, alignment-one environment.
type EnvironmentLayout = {
    Owner: NodeId
    Implementation: NodeId
    Formal: NodeId
    Slots: ContinuationSlot list
    Bytes: int
    Alignment: int
    Obligations: NodeId list
}

/// This proves only the function half and layout. The environment itself is
/// always the value at the queried occurrence, including aliases/frame reads.
type KnownCallable = { Implementation: NodeId; EnvironmentOwner: NodeId }

/// Source construction, fresh enumeration and generator access share this
/// single settled frame contract. The callable identity is separate from its
/// storage; no slot carries a function address.
type ContinuationRegion = {
    ParentOwner: NodeId
    ParentFormal: NodeId
    ChildOwner: NodeId
    Offset: int
    Bytes: int
    Alignment: int
}

type ContinuationFrame = {
    Owner: NodeId
    Generator: NodeId
    Formal: NodeId
    State: NodeId
    Current: NodeId
    Slots: ContinuationSlot list
    Bytes: int
    Alignment: int
    ScratchSlots: ContinuationSlot list
    ScratchBytes: int
    ScratchAlignment: int
    Initializers: (NodeId * NodeId) list
    ResumeStates: int list
    Obligations: NodeId list
}

/// Where a union's values live on a core: a heterogeneous union in the arena, a homogeneous one
/// inline.
[<RequireQualifiedAccess>]
type UnionResidence = Arena | Inline

/// The runtime a program is compiled against.
[<RequireQualifiedAccess>]
type RuntimeMode = Freestanding | Console

/// How a platform operation is resolved. A syscall names the operation; its number is the
/// description's (`Syscalls`), read by the freestanding leg.
[<RequireQualifiedAccess>]
type ResolvedBinding =
    | Syscall of operation: string
    | LibcCall of name: string
    | ExternCall of library: string * symbol: string

type BindingResolution = { Node: NodeId; EntryPoint: string; Resolved: ResolvedBinding }

type PlatformBindings = {
    RuntimeMode: RuntimeMode
    /// Keyed by the call site (the Application node).
    Bindings: Map<NodeId, BindingResolution>
    /// Statically linked libraries; a dynamic extern is resolved at run time and is not here.
    ExternLibraries: Set<string>
}

type PinConstraint = { PortName: string; PackagePin: string; IOStandard: string; Direction: string }
type ClockConstraint = { PortName: string; PackagePin: string; IOStandard: string; FrequencyHz: int64 }
type ResetConstraint = { PortName: string; IsExternal: bool; PackagePin: string; IOStandard: string; ActiveHigh: bool }

/// The pin facts of a hardware design: the description's endpoints joined with the design's
/// `[<Pin>]` attributes. Read by the hardware module witness and the XDC writer.
type PinMapping = {
    Pins: PinConstraint list
    Clock: ClockConstraint
    Reset: ResetConstraint option
    DevicePart: string
    FieldPinAttrs: Map<string, string list>
}

/// A native callback keeps a resolved declaration edge, without a closure environment.
type FunctionPointerPlan =
    | Address of symbol: string * lambda: NodeId
    | Invoke of pointer: NodeId * arguments: NodeId list * parameters: NativeType list * result: NativeType

/// A quoted source condition's standing at its declaration dependencies.
type PredicateStatus = Established | Contradicted | Pending

type PredicateEvidence = {
    Name: string
    Declaration: NodeId
    Expression: NodeId
    Dependencies: NodeId list
    Status: PredicateStatus
    Message: string
    Source: string
}

type MmioBindingEvidence = {
    Plan: string
    Grant: string
    Register: string
    Region: string
    Mapping: string
    AddressSpace: string
    DeclarationNodes: NodeId list
    Predicates: PredicateEvidence list
    /// Platform/loader assertions. Arithmetic checks do not prove hardware.
    Premises: string list
}

type MmioAccessEvidence = {
    Operation: string
    Address: bigint
    Bits: int
    Binding: MmioBindingEvidence option
}

/// The codata the graph carries for emission, settled once at the end of saturation.
type Codata = {
    Escapes: Map<NodeId, EscapeKind>
    Curry: CurryInfo
    /// Per consumer node, its meets in operand order.
    Meets: Map<NodeId, Meet list>
    /// Per lambda, the meet of its body's last value to the body's width.
    ReturnMeets: Map<NodeId, Meet>
    Closures: Map<NodeId, ClosurePlacement>
    EnvironmentLayouts: Map<NodeId, EnvironmentLayout>
    EnvironmentOrigins: Map<NodeId, NodeId>
    KnownCallables: Map<NodeId, KnownCallable>
    ContinuationFrames: Map<NodeId, ContinuationFrame>
    /// A unique sequence constructor at a use, established in Baker. This
    /// evidence permits elision of the known function half of (fn, env).
    SequenceOrigins: Map<NodeId, NodeId>
    /// Transient activation allocation/reference -> owning continuation.
    ContinuationStorage: Map<NodeId, NodeId>
    /// Exact allocation occurrence -> owned byte region within a parent frame.
    ContinuationRegions: Map<NodeId, ContinuationRegion>
    SequenceInitializers: Map<NodeId, (NodeId * NodeId) list>
    /// Caller-owned destination for a known sequence factory constructor.
    SequenceDestinations: Map<NodeId, NodeId>
    SequenceCurrentReads: Set<NodeId>
    Bindings: PlatformBindings
    Pins: PinMapping option
    /// The lambda of each declaration root, with the root's flavour.
    DeclarationRootLambdas: Map<NodeId, DeclRoot>
    FunctionPointers: Map<NodeId, FunctionPointerPlan>
    Mmio: Map<NodeId, MmioAccessEvidence>
}

module Codata =
    let empty : Codata = {
        Escapes = Map.empty
        Curry = { PartialApplications = Map.empty; SaturatedCalls = Map.empty; PartialAppBindings = Set.empty; AbsorbedLambdas = Set.empty; DeferredArgNodes = Set.empty }
        Meets = Map.empty
        ReturnMeets = Map.empty
        Closures = Map.empty
        EnvironmentLayouts = Map.empty
        EnvironmentOrigins = Map.empty
        KnownCallables = Map.empty
        ContinuationFrames = Map.empty
        SequenceOrigins = Map.empty
        ContinuationStorage = Map.empty
        ContinuationRegions = Map.empty
        SequenceInitializers = Map.empty
        SequenceDestinations = Map.empty
        SequenceCurrentReads = Set.empty
        Bindings = { RuntimeMode = RuntimeMode.Console; Bindings = Map.empty; ExternLibraries = Set.empty }
        Pins = None
        DeclarationRootLambdas = Map.empty
        FunctionPointers = Map.empty
        Mmio = Map.empty
    }

/// A source string's view into the BAREWire-owned static byte pool.
type StaticStringEntry = {
    NodeIds: NodeId list
    Content: string
    Offset: int
    Length: int
    StorageLength: int
}

/// One immutable allocation plan shared by obligations and native emission.
/// Offsets are pool-relative; the linker assigns its aligned absolute origin.
type StaticStringPool = {
    Symbol: string
    Bytes: byte list
    Alignment: int
    Size: int
    UsedSize: int
    Entries: StaticStringEntry list
    SpaceName: string
    Capacity: int64
    SpaceAlignment: int
    Granularity: int
    DeclarationNode: NodeId
}

/// The complete semantic graph output
[<NoComparison; NoEquality>]
type SemanticGraph = {
    Nodes: Map<NodeId, SemanticNode>
    DeclarationRoots: (NodeId * DeclRoot) list
    Modules: Map<ModulePath, NodeId list>
    Types: Lazy<Map<string, NodeId>>
    Platform: PlatformContext option
    ModuleClassifications: Lazy<Map<NodeId, ModuleClassification>>
    /// Per record type, per field: the join of the field's range over every reachable
    /// construction of that type (Dimensional_Range_Design.md §3.3: a record's field widths are
    /// one settled fact on the graph, the `hw.struct` of a module signature). Keyed by the type
    /// constructor's name; every integer field of every record type definition has an entry, the
    /// empty range where nothing reachable constructs it. Filled by RangeAnalysis.
    FieldRanges: Lazy<Map<string, Map<string, ValueRange>>>
    /// Per array element type, the join of every value the program stores into an array of that
    /// element type (an array literal's elements, an indexer or `Array.set` assignment, the seed of
    /// `Array.create`, the zero of `Array.zeroCreate`, the result of `Array.init`'s function; a
    /// width-named element carrier met with its declared range): the range an element read has
    /// (Dimensional_Range_Design.md §3.3, CS-11). Type-level and sound: one range per element type
    /// over the whole program, coarse where two arrays of one type hold different ranges. Keyed by
    /// the element type's rendered form; a type nothing reachable stores into has no entry, and a
    /// read of it is unobservable. Filled by RangeAnalysis.
    ElementRanges: Lazy<Map<string, ValueRange>>
    /// Per aggregate type, its settled layout (Dimensional_Range_Design.md §3.3, ruling 2): every
    /// reachable non-generic record and union keyed by the type constructor's name (as
    /// `FieldRanges`), each generic record instance by RecordInstances.layoutKey,
    /// every reachable tuple, option and Result type keyed by its rendered form (as
    /// `ElementRanges`). Filled by Placement after RangeAnalysis; defaulted empty at every graph
    /// construction. The CPU leg reads a field's representation, offset and size here and computes
    /// none of them.
    Layouts: Lazy<Map<string, SettledLayout>>
    /// BAREWire static storage placement, settled after range/aggregate placement.
    StaticStringPool: StaticStringPool option
    /// Per escaping lambda (Dimensional_Range_Design.md ruling 1; CS-11 slice 1): the reason it
    /// escapes as a value, keyed by the Lambda node. A lambda here has its parameters and its
    /// result at the declared Register width, the value-call boundary (§4.1's second row);
    /// `RangeAnalysis.escapes` reads it. Filled by RangeAnalysis.run; defaulted empty.
    Escaping: Lazy<Map<NodeId, string>>
    /// The codata emission reads (Codata): settled at the end of saturation, after the range
    /// pass and placement; defaulted empty at every construction.
    Codata: Lazy<Codata>
    /// F -- the hyperedge set. Phase 0 carries only what enrichment mints
    /// explicitly (obligations, residence); the kind-derived structural and
    /// reference edges are projected on demand by `kindEdges` and are not
    /// materialised here until the fixpoint driver needs them as data.
    /// The emission traversal never queries this set (PHG paper 2.4).
    Edges: Hyperedge list
}
