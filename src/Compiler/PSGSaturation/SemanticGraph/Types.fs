// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Core type definitions for the Program Semantic Graph (PSG).
/// These types form the unified representation for Composer.
module Clef.Compiler.PSGSaturation.SemanticGraph.Types

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
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

[<RequireQualifiedAccess>]
type ObligationBody =
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

/// How an edge participates in the graph's projections.
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

/// The role the source plays relative to the target -- the edge label.
/// Generalises Traversal.RegionKind, which named the same thing but was
/// handed to a callback and discarded instead of being stored.
[<RequireQualifiedAccess>]
type EdgeRole =
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

/// Edge construction and projection helpers.
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
        :: (cases |> List.collect (fun c ->
                sts EdgeRole.CaseBinding c.PatternBindings
                @ (c.Guard |> Option.toList |> List.map (st EdgeRole.CaseGuard))
                @ [ st EdgeRole.CaseBody c.Body ]))

    | SemanticKind.CaseElimination (scrutinee, arms) ->
        st EdgeRole.Scrutinee scrutinee
        :: (arms |> List.collect (fun arm ->
                sts EdgeRole.CaseBinding arm.Bindings
                @ (arm.Guard |> Option.toList |> List.map (st EdgeRole.CaseGuard))
                @ [ st EdgeRole.CaseBody arm.Body ]))

    | SemanticKind.Sequential nodes -> sts EdgeRole.Element nodes
    | SemanticKind.WhileLoop (guard, body) -> [ st EdgeRole.Guard guard; st EdgeRole.Body body ]
    | SemanticKind.ForLoop (_, start, finish, _, body) ->
        [ st EdgeRole.LoopStart start; st EdgeRole.LoopFinish finish; st EdgeRole.Body body ]
    | SemanticKind.ForEach (_, collection, body) ->
        [ st EdgeRole.Collection collection; st EdgeRole.Body body ]
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
    | SemanticKind.ModuleDef (_, members) -> sts EdgeRole.Member members
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
    /// An anonymous function expression (`fun` or `function`), distinguished from
    /// the Lambda used to represent a named function declaration.
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

/// The codata the graph carries for emission, settled once at the end of saturation.
type Codata = {
    Escapes: Map<NodeId, EscapeKind>
    Curry: CurryInfo
    /// Per consumer node, its meets in operand order.
    Meets: Map<NodeId, Meet list>
    /// Per lambda, the meet of its body's last value to the body's width.
    ReturnMeets: Map<NodeId, Meet>
    Closures: Map<NodeId, ClosurePlacement>
    Bindings: PlatformBindings
    Pins: PinMapping option
    /// The lambda of each declaration root, with the root's flavour.
    DeclarationRootLambdas: Map<NodeId, DeclRoot>
    FunctionPointers: Map<NodeId, FunctionPointerPlan>
}

module Codata =
    let empty : Codata = {
        Escapes = Map.empty
        Curry = { PartialApplications = Map.empty; SaturatedCalls = Map.empty; PartialAppBindings = Set.empty; AbsorbedLambdas = Set.empty; DeferredArgNodes = Set.empty }
        Meets = Map.empty
        ReturnMeets = Map.empty
        Closures = Map.empty
        Bindings = { RuntimeMode = RuntimeMode.Console; Bindings = Map.empty; ExternLibraries = Set.empty }
        Pins = None
        DeclarationRootLambdas = Map.empty
        FunctionPointers = Map.empty
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
    SeqSaturation: Lazy<Map<NodeId, SeqStateMachineInfo>>
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
    /// reachable record and union type keyed by the type constructor's name (as `FieldRanges`),
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
