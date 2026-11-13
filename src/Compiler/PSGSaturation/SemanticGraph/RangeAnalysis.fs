// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// The range pass (Dimensional_Range_Design.md §1, §3.1, §3.3; width-inference.md §2, §3, §6, §8;
/// CS-10, CS-11).
///
/// Every reachable integer value carries its analysed range as a coeffect beside its type
/// (`SemanticNode.ValueRange`), every record type carries the join of each field's range over its
/// reachable constructions (`SemanticGraph.FieldRanges`), and every array element type the join of
/// every value stored into an array of it (`SemanticGraph.ElementRanges`). The width is derived
/// from the range wherever it is read (`ValueRange.width` on fabric; on a core the selected declared
/// representation, `selectedWidth`, derived on read from the range and the platform's declaration)
/// and is never stored beside it (Horizon C3).
///
/// The pass is a least fixed point over immutable shared and invocation-context cells: a transfer
/// function per node kind (§1.1 seeding, §1.2 propagation), iterated to a post-fixpoint with a
/// widening operator whose thresholds are the declared integer representations' boundaries
/// (numeric-selection.md §9.1; on fabric, which declares none, an endpoint that keeps growing goes
/// to its infinity), then a bounded narrowing that recovers the precision the widening gave up
/// (§1.2a). A comparison bounds the branch it guards: a reference to the compared binding inside
/// the then-subtree carries the binding's range met with the bound, and inside the else-subtree the
/// complement (§1.1, "a comparison bounds the branch it guards"); the per-node range is what makes
/// that representable, since a reference under a guard is its own node.
///
/// The declared sources (§1.1 last bullet, CS-11) are read from one table beside the intrinsic
/// definitions (`Intrinsics.RangeSources`): an intrinsic result's fact, the interim declared
/// boundary of a width-named carrier, and what a higher-order intrinsic supplies to the function
/// it is handed. A call through a function value (a parameter, a closure, a partial application)
/// reaches every lambda that escapes as a value and whose parameters may unify with the call's
/// arguments, and its arguments join into those lambdas' parameters; a parameter no seen call
/// supplies is unobservable and its CCS8011 names the escape.
///
/// A reachable integer whose final range has no width is CCS8011 (§1.3, §7), an error on every
/// substrate: no width has another source. A bounded range of the bare
/// kind that no declared integer representation covers is CCS8012, a warning promoted by
/// `--warnaserror` (§4.2). Runs on every substrate, over reachable nodes only, after the declared
/// platform has filled the context and before it is checked (NativeService.buildResult).
module Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.TypeIdentities
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.NativeTypedTree.Expressions.Types
open Clef.Compiler.NativeTypedTree.Expressions.Intrinsics
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module PlatformResolution = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
module LoopRecipes = Clef.Compiler.Baker.Recipes.LoopRangeRecipes
module LoopRanges = Clef.Compiler.Nanopass.LoopRanges
module SequenceAccumulation = Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes
module SequenceAccumulations = Clef.Compiler.Nanopass.SequenceAccumulations

//-------------------------------------------------------------------------
// The program as the pass reads it
//-------------------------------------------------------------------------

/// The relation a comparison guard establishes between a reference and a bound: `x < K`, ...
[<RequireQualifiedAccess>]
type private Relation =
    | Lt
    | Le
    | Gt
    | Ge
    | Eq
    | Ne

/// What a bound is read from: one node's range, or the difference or sum of two nodes' ranges,
/// the one-level backward refinement through `-` and `+` of §1.2a (ruling 3: `count <= length -
/// offset` bounds `offset` by `length - count`).
[<RequireQualifiedAccess>]
type private Bound =
    | Of of NodeId
    | Diff of NodeId * NodeId
    | Sum of NodeId * NodeId

/// A bound in force on a read: the value read stands in `Relation` to `Bound`'s range.
type private Refinement = { Bound: Bound; Relation: Relation }

/// What a guard compares: a binding (through any reference to it) or one particular node (an
/// expression Baker's recipes share between the guard and a branch, `min hi (max lo x)`).
[<RequireQualifiedAccess>]
type private Compared =
    | Definition of NodeId
    | Node of NodeId

/// A lambda a call through a function value may reach, with the parameters still open: a partial
/// application supplies the first `Offset` directly and hands the rest on as a value.
type private Candidate = {
    LambdaId: NodeId
    Parameters: (string * NativeType * NodeId) list
    Body: NodeId
    Offset: int
    /// How the lambda escapes, for the diagnostic that names it.
    Escape: string
}

/// What an application calls.
[<RequireQualifiedAccess>]
type private Callee =
    /// One lambda, named directly (or applied in place), with the arguments from its first parameter.
    | Direct of parameters: (string * NativeType * NodeId) list * body: NodeId
    /// Every candidate a function value may be, each with the parameters open from its offset;
    /// `poisoned` when a non-lambda function value (an intrinsic, an extern or platform binding,
    /// a partial application of one) in value position may be the value called, so the result
    /// and the open parameters are unobservable
    | Value of candidates: Candidate list * poisoned: bool
    | Intrinsic of IntrinsicInfo

/// May-writes while evaluating a node, rather than while merely constructing a
/// delayed body. Unknown calls may write any mutable cell visible to the program.
type private WriteEffect = { Definitions: Set<NodeId>; Unknown: bool }

let private noWrites = { Definitions = Set.empty; Unknown = false }
let private unknownWrites = { noWrites with Unknown = true }
let private joinWrites left right =
    { Definitions = Set.union left.Definitions right.Definitions
      Unknown = left.Unknown || right.Unknown }

/// What the pass reads of the graph, computed once: the reachable nodes, the parent index, the
/// callee of every application, what supplies every parameter, the assignments to every mutable
/// binding, the refinement at every reference, the reachable constructions of every record type
/// and the integer fields its definition declares, the values stored into arrays by element type,
/// and the widening thresholds the platform declares.
type private AggregateProjection =
    | TupleSlot of int
    | UnionPayload of int * string
    | RecordField of TypeIdentity * string

type private Program = {
    Graph: SemanticGraph
    Context: PlatformContext option
    Reachable: Map<NodeId, SemanticNode>
    /// Reachable nodes in node order.
    Ordered: SemanticNode list
    /// Values that require runtime representation under current source demand.
    /// Domain/type facts for deferred source expressions remain in the graph.
    CommitmentSites: Set<NodeId>
    Parents: Map<NodeId, NodeId>
    /// An application node -> what it calls and its whole argument list (curried calls flattened).
    Callees: Map<NodeId, Callee * NodeId list>
    /// Complete ordinary applications keep each alternative's actual correspondence.
    Applications: Map<NodeId, CallableOrigins.CallTarget list>
    /// Exact foreign declaration rows are incidence, never behavior inferred from a stub.
    ForeignDeclarations: Map<NodeId, BoundaryDeclaration list>
    ForeignEntryCalls: Map<NodeId, BoundaryDeclaration * NodeId list * Set<NodeId>>
    ForeignBodies: Set<NodeId>
    ForeignEffectBodies: Set<NodeId>
    ForeignDeclarationFailure: (NodeId * string) option
    ForeignResultRanges: Map<NodeId, PlatformResolution.DeclaredResultRange list>
    ForeignAbi: Map<NodeId, PlatformResolution.DeclaredFunction list>
    Effects: Map<NodeId, WriteEffect>
    LoopRecognition: LoopRecipes.Recognition
    LoopAccumulations: Map<NodeId, LoopRecipes.Accumulation>
    LoopLinear: Map<NodeId, LoopRecipes.LinearRecurrence * int>
    TailRecurrences: Map<NodeId, LoopRecipes.TailRecurrence>
    SequenceAccumulations: SequenceAccumulation.Accumulation list
    SequenceAccumulationTargets: Map<NodeId, SequenceAccumulation.Accumulation>
    LazyEffects: Map<NodeId, LazyEffectRanges.Bound>
    FiniteCells: Map<NodeId, FiniteCellRanges.Bound>
    /// Complete owner-local payload incidence for a certified current read.
    /// Missing/unknown origin alternatives deliberately have no entry.
    SequenceElements: Map<NodeId, NodeId * (NodeId * NodeId) list>
    /// Graph-carried deferred body effects, validated against complete origins.
    SequencePullBodies: Map<NodeId, NodeId * NodeId list>
    SequenceInitializations: Set<NodeId>
    SequenceCurrentReads: Set<NodeId>
    /// Original captured declaration -> mode and exact formation initializer reads.
    /// Shared cells retain source storage identity; immutable slots retain snapshots.
    EnvironmentCaptures: Map<NodeId, bool * (NodeId * NodeId) list>
    /// Current writes (or an immutable formation initializer) for a frame read.
    /// Entries exist only after complete source/storage correspondence validation.
    ContinuationInputs: Map<NodeId, ValueRange * (NodeId * NodeId) list>
    /// Checked shared captures read the logical mutable cell, across all owners.
    ContinuationCells: Map<NodeId, NodeId>
    /// Actual frame writers admitted by the same complete storage census.
    /// Mutable source slots retain their logical cell effect across the rewrite.
    ContinuationWrites: Map<NodeId, NodeId>
    /// Exact cache declaration/read -> the validated instance's thunk result.
    /// This is an enclosure across dynamic instances, never instance equality.
    LazyResults: Map<NodeId, NodeId>
    /// Exact lazy capture access -> original slot, mode, formation and initializer.
    LazyCaptures: Map<NodeId, NodeId * bool * NodeId * NodeId>
    /// Guarded internal cache/publication writes do not mutate source cells.
    LazyPrivateWrites: Set<NodeId>
    /// A Lambda parameter node -> (the call node, the argument node) at every reachable call that
    /// supplies it, directly or through a function value; the parameter reads the argument as the
    /// call does.
    CallArguments: Map<NodeId, (NodeId * NodeId) list>
    /// A Lambda parameter node -> (the intrinsic call node, its count argument) where an
    /// intrinsic calls the lambda at every index below the count (`Array.init n f`).
    IndexSeeds: Map<NodeId, (NodeId * NodeId) list>
    /// A Lambda parameter node -> the reason its lambda escapes, for every parameter of an
    /// escaping candidate; the diagnostic names it when nothing supplies the parameter.
    Escaping: Map<NodeId, string>
    /// An escaping Lambda node -> the reason it escapes (ruling 1: the whole lambda sits at the
    /// value-call boundary, its parameters and its result at the declared Register width).
    EscapingLambdas: Map<NodeId, string>
    /// Every Lambda parameter node.
    Parameters: Set<NodeId>
    /// Empty execution joins certified by the current ordinary-demand census.
    /// These formals keep their source type and signature position.
    InactiveFormals: Set<NodeId>
    /// Body occurrences excluded from execution by that same demand proof.
    InactiveOccurrences: Set<NodeId>
    /// A Lambda parameter node -> its lambda's declaration root, for a root's parameters.
    RootParameters: Map<NodeId, DeclRoot>
    /// A mutable binding -> every value assigned to it.
    Assignments: Map<NodeId, NodeId list>
    /// The bounds in force on a read, by use edge: consumer node -> operand node -> bounds. A
    /// read under a comparison guard is a use edge inside the guarded branch (or the branch edge
    /// of the `if` itself), which is what makes a refinement representable when a node is shared
    /// between the guard and a branch.
    Refinements: Map<NodeId, Map<NodeId, Refinement list>>
    /// Necessary guard atoms at each source occurrence, issued by the same
    /// effect-aware walk as the operand refinements.
    GuardRefinements: Map<NodeId, (Compared * Refinement) list>
    /// Exact reads reached with a guard through the checked continuation machine.
    ContinuationRefinements: Map<NodeId, Refinement list>
    /// A record type name -> its reachable constructions: the construction node and its (field, value) list.
    Constructions: Map<NominalTypeIdentity, (NodeId * (string * NodeId) list) list>
    /// A record type name -> the fields its definition declares at an integer type.
    IntegerFields: Map<NominalTypeIdentity, string list>
    /// The declared inputs of a hardware design (§1.1: an input arrives through a declaration):
    /// the record type of a `[<HardwareModule>]` design's Step inputs parameter, each pin field at
    /// its declared range, a boolean pin `[0, 1]`. No program constructs this record; the pins do.
    InputSeeds: Map<NominalTypeIdentity, Map<string, ValueRange>>
    /// A node whose value a binding descriptor declares (§4.1, the C ABI row; ruling 1 of
    /// CS-12): an extern's parameter node at its declared range, the extern's body at the
    /// declared return. The declaration binds (§4.4); the arguments are checked against it.
    BoundarySeeds: Map<NodeId, ValueRange>
    ArrayLengths: Map<NodeId, Clef.Compiler.Baker.Ingredients.ArrayShapes.Extent>
    /// The declared wire fields seeded into `InputSeeds`, for the boundary check (§4.2): the
    /// record type and the field's declaration.
    DeclaredFields: (NominalTypeIdentity * PlatformResolution.DeclaredField) list
    /// The declared extern parameters seeded into `BoundarySeeds`: the parameter node and its
    /// declaration.
    DeclaredParameters: (NodeId * PlatformResolution.DeclaredParameter) list
    /// An array element type (rendered) -> every value stored into an array of that type, as
    /// (the storing node, the value node): an array literal's elements, an indexer or `Array.set`
    /// assignment, `Array.create`'s seed, `Array.init`'s function result.
    ElementStores: Map<TypeIdentity, (NodeId * NodeId) list>
    /// An array element type (rendered) -> the constant seeds stored into it: `Array.zeroCreate`'s
    /// zero, and the unbounded store of an array handed to a boundary call.
    ElementSeeds: Map<TypeIdentity, ValueRange>
    Thresholds: ValueRange.Threshold list
    Fabric: bool
    AtomsCache: System.Collections.Generic.Dictionary<NodeId * bool * int, (Compared * Refinement) list>
    SourceEdgesByTarget: Lazy<Map<NodeId, Hyperedge list>>
    RecordIncidenceCache: System.Collections.Generic.Dictionary<NodeId, bool>
    ImmutableRecordFieldCache: System.Collections.Generic.Dictionary<NodeId * string, (TypeIdentity * TypeIdentity) option>
    AggregateElementCache: System.Collections.Generic.Dictionary<NodeId * AggregateProjection list, bool * Set<NodeId>>
}

/// The parent of every node, read from the children lists (as NativeService.parentIndex).
let private parentIndex (nodes: Map<NodeId, SemanticNode>) : Map<NodeId, NodeId> =
    nodes
    |> Map.fold (fun index _ node ->
        node.Children |> List.fold (fun index child -> Map.add child node.Id index) index) Map.empty

let private isIntegerNode (node: SemanticNode) : bool =
    Types.tryGetNTUKind node.Type |> Option.exists NTUKind.isInteger

let private isBoolNode (node: SemanticNode) : bool =
    Types.tryGetNTUKind node.Type = Some NTUKind.NTUbool

let private isCharNode (node: SemanticNode) : bool =
    Types.tryGetNTUKind node.Type = Some NTUKind.NTUchar

/// A node the pass ranges: an integer, a boolean or a char (the last two by their type).
let private isRanged (node: SemanticNode) : bool =
    isIntegerNode node || isBoolNode node || isCharNode node

/// The element type of an array type, if the type is one, with its variables resolved.
let private arrayElementType (ty: NativeType) : NativeType option =
    match applySubst ty with
    | NativeType.TApp (tycon, [ elem ]) when tycon.Name = Types.arrayTyCon.Name -> Some (applySubst elem)
    | _ -> None

/// The key of `ElementRanges`: the element type's rendered form.
let private elementKey (elem: NativeType) : TypeIdentity = ofType elem

/// Whether two types may be the same type: a conservative reading (a type variable unifies with
/// anything; a shape the reader does not know is not excluded), so that no lambda a call could
/// reach is left out.
let rec private mayUnify (a: NativeType) (b: NativeType) : bool =
    match applySubst a, applySubst b with
    | NativeType.TVar _, _ | _, NativeType.TVar _ -> true
    | NativeType.TNum _, NativeType.TNum _ ->
        // an integer never unifies with a real; carrier variables unify with either
        match Types.isIntegerType a, Types.isFloatType a, Types.isIntegerType b, Types.isFloatType b with
        | true, _, _, true | _, true, true, _ -> false
        | _ -> true
    | NativeType.TNum _, _ | _, NativeType.TNum _ -> false
    | NativeType.TFun (a1, a2), NativeType.TFun (b1, b2) -> mayUnify a1 b1 && mayUnify a2 b2
    | NativeType.TFun _, _ | _, NativeType.TFun _ -> false
    | NativeType.TApp (ta, aargs), NativeType.TApp (tb, bargs) ->
        ta.Name = tb.Name && aargs.Length = bargs.Length && List.forall2 mayUnify aargs bargs
    | NativeType.TApp _, _ | _, NativeType.TApp _ -> false
    | NativeType.TTuple (aes, _), NativeType.TTuple (bes, _) -> aes.Length = bes.Length && List.forall2 mayUnify aes bes
    | NativeType.TTuple _, _ | _, NativeType.TTuple _ -> false
    | _ -> true

/// The direct lambda chain that Curry.normalize will flatten after range analysis.
/// Read its complete parameter list here too: `fun lo hi -> ...` is still two
/// nested one-parameter nodes at this phase, while a saturated call already has
/// both arguments. Comparing only the outer parameter loses the actual call's
/// range evidence and can leave callback-to-callback argument cycles at Empty.
/// Explicit returned function values stop the chain, as they do in Curry: their
/// parameters and result belong to a different callable and range boundary.
let rec private lambdaShape (nodes: Map<NodeId, SemanticNode>) (id: NodeId) : ((string * NativeType * NodeId) list * NodeId) option =
    match Map.tryFind id nodes with
    | Some { Kind = SemanticKind.Lambda (parameters, body, _, _, _) } ->
        let returnedFunction =
            Map.tryFind body nodes |> Option.exists (fun node ->
                [ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
                |> List.exists (fun key -> Map.tryFind key node.Metadata = Some (MetadataValue.Bool true)))
        match (if returnedFunction then None else lambdaShape nodes body) with
        | Some (innerParameters, innerBody) -> Some (parameters @ innerParameters, innerBody)
        | None -> Some (parameters, body)
    | _ -> None

/// The Lambda an immutable function binding holds, if any. Mutable callable
/// storage is resolved through the complete current origin family instead.
let private lambdaOf (reachable: Map<NodeId, SemanticNode>) (bindingId: NodeId) : (NodeId * (string * NativeType * NodeId) list * NodeId) option =
    let rec ofValue (id: NodeId) (depth: int) =
        if depth > 4 then None
        else
            match Map.tryFind id reachable with
            | Some { Kind = SemanticKind.Lambda _ } -> lambdaShape reachable id |> Option.map (fun (parameters, body) -> id, parameters, body)
            | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> ofValue inner (depth + 1)
            | _ -> None
    match Map.tryFind bindingId reachable with
    | Some ({ Kind = SemanticKind.Binding (_, false, _, _) } as binding) ->
        binding.Children |> List.tryPick (fun childId -> ofValue childId 0)
    | _ -> None

/// The root of a possibly curried application with every argument along the chain in order.
let rec private flattenApplication (reachable: Map<NodeId, SemanticNode>) (funcId: NodeId) (args: NodeId list) : NodeId * NodeId list =
    match Map.tryFind funcId reachable with
    | Some { Kind = SemanticKind.Application (innerFunc, innerArgs) } -> flattenApplication reachable innerFunc (innerArgs @ args)
    | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> flattenApplication reachable inner args
    | _ -> (funcId, args)

/// The nodes along an application's callee chain: the root and every inner application and
/// annotation, which are callee positions and not values.
let rec private calleeChain (reachable: Map<NodeId, SemanticNode>) (funcId: NodeId) : NodeId list =
    match Map.tryFind funcId reachable with
    | Some { Kind = SemanticKind.Application (innerFunc, _) } -> funcId :: calleeChain reachable innerFunc
    | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> funcId :: calleeChain reachable inner
    | _ -> [ funcId ]

/// The candidates among `candidates` a call through a value of `args` may reach: those with at
/// least as many open parameters as arguments, each parameter unifiable with its argument.
let private reachable (reachable: Map<NodeId, SemanticNode>) (candidates: Candidate list) (args: NodeId list) : Candidate list =
    let argTypes = args |> List.map (fun a -> Map.tryFind a reachable |> Option.map (fun n -> n.Type))
    candidates
    |> List.filter (fun c ->
        let openParams = c.Parameters |> List.skip (min c.Offset c.Parameters.Length)
        openParams.Length >= args.Length
        && List.forall2 (fun (_, pty, _) aty -> match aty with Some t -> mayUnify pty t | None -> true)
                        (List.truncate args.Length openParams) argTypes)

/// What a callee expression calls, with the whole argument list: a lambda named by a reference
/// or applied in place, an intrinsic, or a function value, which reaches every escaping candidate
/// its arguments may unify with. A named lambda applied to more arguments than it has parameters
/// hands the surplus to the value its body returns, a call through a value.
/// The domains of a function type, outermost first, through bound variables.
let rec private domainsOf (ty: NativeType) : NativeType list =
    match applySubst ty with
    | NativeType.TFun (d, r) -> d :: domainsOf r
    | _ -> []

/// Whether a poisoning value of type `ty` may be the value a call with `args` calls: it takes at
/// least as many arguments and each argument's type may unify with the domain's.
let private poisonReaches (nodes: Map<NodeId, SemanticNode>) (poisons: (NodeId * NativeType) list) (args: NodeId list) : bool =
    let argTypes = args |> List.map (fun a -> Map.tryFind a nodes |> Option.map (fun n -> n.Type))
    poisons |> List.exists (fun (_, ty) ->
        let domains = domainsOf ty
        domains.Length >= args.Length
        && List.forall2 (fun d aty -> match aty with Some t -> mayUnify d t | None -> true) (List.truncate args.Length domains) argTypes)

let private resolveCallee (nodes: Map<NodeId, SemanticNode>) (candidates: Candidate list) (poisons: (NodeId * NativeType) list) (funcId: NodeId) (args: NodeId list) : (Callee * NodeId list) option =
    let (rootId, allArgs) = flattenApplication nodes funcId args
    let value () = Callee.Value (reachable nodes candidates allArgs, poisonReaches nodes poisons allArgs)
    match Map.tryFind rootId nodes with
    | Some { Kind = SemanticKind.Intrinsic info } -> Some (Callee.Intrinsic info, allArgs)
    | Some { Kind = SemanticKind.Lambda _ } -> lambdaShape nodes rootId |> Option.map (fun (parameters, body) -> Callee.Direct (parameters, body), allArgs)
    | Some { Kind = SemanticKind.VarRef (_, Some defId) } ->
        match lambdaOf nodes defId with
        | Some (_, parameters, body) -> Some (Callee.Direct (parameters, body), allArgs)
        | None -> Some (value (), allArgs)
    | Some { Kind = SemanticKind.VarRef (_, None) } -> None
    | Some _ -> Some (value (), allArgs)
    | None -> None

/// How a lambda in value position escapes, named by what holds it.
let private escapeOf (nodes: Map<NodeId, SemanticNode>) (parents: Map<NodeId, NodeId>) (id: NodeId) : string =
    match Map.tryFind id parents |> Option.bind (fun p -> Map.tryFind p nodes) with
    | Some { Kind = SemanticKind.Application _ } -> "passed as a value"
    | Some { Kind = SemanticKind.RecordExpr _ } | Some { Kind = SemanticKind.TupleExpr _ }
    | Some { Kind = SemanticKind.ArrayExpr _ } | Some { Kind = SemanticKind.ListExpr _ }
    | Some { Kind = SemanticKind.UnionCase _ } | Some { Kind = SemanticKind.DUConstruct _ }
    | Some { Kind = SemanticKind.Set _ } | Some { Kind = SemanticKind.IndexSet _ }
    | Some { Kind = SemanticKind.FieldSet _ } -> "stored as a value"
    | Some { Kind = SemanticKind.Binding _ } -> "bound as a value"
    | Some { Kind = SemanticKind.Lambda _ } | Some { Kind = SemanticKind.Sequential _ }
    | Some { Kind = SemanticKind.IfThenElse _ } | Some { Kind = SemanticKind.Match _ } -> "returned as a value"
    | _ -> "used as a value"

/// The lambdas that escape as values (§1.2, CS-11): an anonymous lambda anywhere but the value
/// of a binding (Baker's eta-expanded lambda for a named function in value position among them);
/// a function binding referenced anywhere but a callee position; a named lambda applied to fewer
/// arguments than it has parameters (the open parameters escape). Each is a candidate for every
/// call through a function value its arguments may unify with.
let private escapingOf (nodes: Map<NodeId, SemanticNode>) (ordered: SemanticNode list) (parents: Map<NodeId, NodeId>) : Candidate list =
    let calleePositions =
        ordered
        |> List.collect (fun node ->
            match node.Kind with
            | SemanticKind.Application (funcId, _) -> calleeChain nodes funcId
            | _ -> [])
        |> Set.ofList
    let anonymous =
        ordered
        |> List.choose (fun node ->
            match node.Kind with
            | SemanticKind.Lambda _ ->
                // A mutable binding stores a function value, including its
                // initializer. Only immutable bindings denote a direct function.
                let ownedByDirectBinding =
                    match Map.tryFind node.Id parents |> Option.bind (fun p -> Map.tryFind p nodes) with
                    | Some { Kind = SemanticKind.Binding (_, false, _, _) } -> true
                    | Some { Kind = SemanticKind.TypeAnnotation _ } ->
                        // `let f : t = fun ...`: the annotation's parent is the binding
                        Map.tryFind node.Id parents
                        |> Option.bind (fun a -> Map.tryFind a parents)
                        |> Option.bind (fun p -> Map.tryFind p nodes)
                        |> Option.exists (fun p -> match p.Kind with SemanticKind.Binding (_, false, _, _) -> true | _ -> false)
                    | _ -> false
                if ownedByDirectBinding || Set.contains node.Id calleePositions then None
                else
                    lambdaShape nodes node.Id |> Option.map (fun (parameters, body) ->
                        { LambdaId = node.Id; Parameters = parameters; Body = body; Offset = 0; Escape = escapeOf nodes parents node.Id })
            | _ -> None)
    let referenced =
        ordered
        |> List.choose (fun node ->
            match node.Kind with
            | SemanticKind.VarRef (_, Some defId) when not (Set.contains node.Id calleePositions) ->
                lambdaOf nodes defId
                |> Option.map (fun (lambdaId, parameters, body) ->
                    { LambdaId = lambdaId; Parameters = parameters; Body = body; Offset = 0; Escape = escapeOf nodes parents node.Id })
            | _ -> None)
    let partial =
        ordered
        |> List.choose (fun node ->
            match node.Kind with
            | SemanticKind.Application (funcId, args) when not (Set.contains node.Id calleePositions) ->
                let (rootId, allArgs) = flattenApplication nodes funcId args
                match Map.tryFind rootId nodes with
                | Some { Kind = SemanticKind.VarRef (_, Some defId) } ->
                    match lambdaOf nodes defId with
                    | Some (lambdaId, parameters, body) when allArgs.Length < parameters.Length ->
                        Some { LambdaId = lambdaId; Parameters = parameters; Body = body; Offset = allArgs.Length; Escape = "partially applied" }
                    | _ -> None
                | _ -> None
            | _ -> None)
    (anonymous @ referenced @ partial)
    |> List.distinctBy (fun c -> (c.LambdaId, c.Offset))

/// The function values that are no lambda, in value position (the reviewer's valcall probes,
/// CS-11): an intrinsic named as a value, a partial application whose root is an intrinsic or a
/// non-lambda binding, a reference to an extern or platform binding of function type. A call
/// through a value such a value may reach is unobservable: its body is no graph the pass reads.
let private poisoningOf (nodes: Map<NodeId, SemanticNode>) (ordered: SemanticNode list) : (NodeId * NativeType) list =
    let calleePositions =
        ordered
        |> List.collect (fun node ->
            match node.Kind with
            | SemanticKind.Application (funcId, _) -> calleeChain nodes funcId
            | _ -> [])
        |> Set.ofList
    let isFunctionTyped (node: SemanticNode) = not (List.isEmpty (domainsOf node.Type))
    let nonLambdaDefinition (defId: NodeId) =
        match Map.tryFind defId nodes with
        | Some { Kind = SemanticKind.PlatformBinding _ } -> true
        | Some ({ Kind = SemanticKind.Binding _ } as d) -> (lambdaOf nodes defId).IsNone && Map.containsKey "FidelityExtern.Library" d.Metadata
        | _ -> false
    ordered
    |> List.choose (fun node ->
        if Set.contains node.Id calleePositions || not (isFunctionTyped node) then None
        else
            match node.Kind with
            | SemanticKind.Intrinsic _ -> Some (node.Id, node.Type)
            | SemanticKind.Application (funcId, args) ->
                let (rootId, _) = flattenApplication nodes funcId args
                match Map.tryFind rootId nodes with
                | Some { Kind = SemanticKind.Intrinsic _ } -> Some (node.Id, node.Type)
                | Some { Kind = SemanticKind.VarRef (_, Some defId) } when nonLambdaDefinition defId -> Some (node.Id, node.Type)
                | _ -> None
            | SemanticKind.VarRef (_, Some defId) when nonLambdaDefinition defId -> Some (node.Id, node.Type)
            | _ -> None)

let private intrinsicOf (program: Program) (funcId: NodeId) : IntrinsicInfo option =
    match Map.tryFind funcId program.Reachable with
    | Some { Kind = SemanticKind.Intrinsic info } -> Some info
    | _ -> None

/// A binding whose value is fixed at its definition: an immutable `let` or a parameter. Only such
/// a binding's references are refined by a guard; a mutable one is refined only up to its first
/// assignment in the guarded subtree (see `refinementsOf`).
let private isImmutableDefinition (program: Program) (defId: NodeId) : bool =
    match program.EnvironmentCaptures.TryFind defId, Map.tryFind defId program.Graph.Nodes with
    | Some (mutableSlot, _), _ -> not mutableSlot
    | _, Some { Kind = SemanticKind.Binding (_, false, _, _) } -> true
    | _, Some { Kind = SemanticKind.PatternBinding _ } -> true
    | _ -> false

let private isMutableDefinition (program: Program) (defId: NodeId) : bool =
    match program.EnvironmentCaptures.TryFind defId, Map.tryFind defId program.Graph.Nodes with
    | Some (mutableSlot, _), _ -> mutableSlot
    | _, Some { Kind = SemanticKind.Binding (_, true, _, _) } -> true
    | _ -> false

/// Capture reads keep the source storage identity after closure elaboration.
/// Only a complete, typed formation relation licenses that projection.
let private readDefinition (program: Program) (id: NodeId) =
    match program.Reachable.TryFind id with
    | Some { Kind = SemanticKind.VarRef(_, Some source) } -> Some source
    | Some { Kind = SemanticKind.EnvironmentRead(_, slot) } when program.EnvironmentCaptures.ContainsKey slot -> Some slot
    | Some { Kind = SemanticKind.LazyRead _ } ->
        program.LazyCaptures.TryFind id |> Option.map (fun (slot, _, _, _) -> slot)
    | Some { Kind = SemanticKind.FrameRead _ } -> program.ContinuationCells.TryFind id
    | _ -> None

let private isLiteralBool (program: Program) (id: NodeId) (value: bool) : bool =
    match Map.tryFind id program.Reachable with
    | Some { Kind = SemanticKind.Literal (NativeLiteral.Bool b) } -> b = value
    | _ -> false

/// Finite least fixed point: each node accumulates only reachable definition IDs
/// and one unknown-effect bit. Recursive and transitive calls use the same body
/// summaries; a partial application and a closure construction do not run a body.
let private effectsOf (program: Program) : Map<NodeId, WriteEffect> =
    let candidates = escapingOf program.Reachable program.Ordered program.Parents
    let poisons = poisoningOf program.Reachable program.Ordered
    let rec invocationSpec callee (args: NodeId list) : WriteEffect * NodeId list =
        match callee with
        | Callee.Direct (parameters, body) ->
            if args.Length < parameters.Length then noWrites, []
            elif program.ForeignEffectBodies.Contains body then unknownWrites, []
            elif args.Length = parameters.Length then noWrites, [body]
            else
                let surplus = List.skip parameters.Length args
                let returned = Callee.Value (reachable program.Reachable candidates surplus, poisonReaches program.Reachable poisons surplus)
                let subEffect, subDeps = invocationSpec returned surplus
                subEffect, body :: subDeps
        | Callee.Value (possible, poisoned) ->
            let initial = if poisoned || List.isEmpty possible then unknownWrites else noWrites
            possible |> List.fold (fun (accEffect, accDeps) candidate ->
                if args.Length < candidate.Parameters.Length - candidate.Offset then accEffect, accDeps
                elif program.ForeignEffectBodies.Contains candidate.Body then joinWrites accEffect unknownWrites, accDeps
                else accEffect, candidate.Body :: accDeps) (initial, [])
        | Callee.Intrinsic info ->
            // The emission category is not a callback-effect declaration. Read
            // the existing callback table, and keep delayed/foreign operations
            // conservative even when their emission category says Pure.
            let callbacks = RangeSources.calls info
            let delayed =
                match info.Module with
                | IntrinsicModule.Lazy | IntrinsicModule.Seq | IntrinsicModule.SeqEnumerator -> true
                | _ -> false
            let unmodelledCallback =
                List.isEmpty callbacks && (args |> List.exists (fun id ->
                    Map.tryFind id program.Reachable |> Option.exists (fun n ->
                        match applySubst n.Type with NativeType.TFun _ -> true | _ -> false)))
            let initial =
                match info.Category with
                | _ when info.Module = IntrinsicModule.Mmio -> noWrites
                | IntrinsicCategory.Platform | IntrinsicCategory.Reactive -> unknownWrites
                | IntrinsicCategory.Memory when List.isEmpty callbacks -> unknownWrites
                | _ when delayed || unmodelledCallback -> unknownWrites
                | _ -> noWrites
            callbacks |> List.fold (fun (accEffect, accDeps) (position, supplies) ->
                match List.tryItem position args with
                | None -> accEffect, accDeps
                | Some callback ->
                    let mutableCallback =
                        match Map.tryFind callback program.Reachable with
                        | Some { Kind = SemanticKind.VarRef (_, Some definition) } -> isMutableDefinition program definition
                        | _ -> false
                    let possible =
                        match Map.tryFind callback program.Reachable with
                        | Some { Kind = SemanticKind.Lambda _ } ->
                            lambdaShape program.Reachable callback |> Option.map (fun (_, body) -> [body])
                        | Some { Kind = SemanticKind.VarRef (_, Some definition) } ->
                            lambdaOf program.Reachable definition |> Option.map (fun (_, _, body) -> [body])
                        | _ -> None
                    match possible with
                    | _ when mutableCallback -> joinWrites accEffect unknownWrites, accDeps
                    | Some bodies -> accEffect, bodies @ accDeps
                    | None ->
                        // The callback argument supplies no concrete values
                        // here; every escaped callable of this arity may run.
                        let bodies = candidates |> List.filter (fun c -> c.Parameters.Length - c.Offset = supplies.Length) |> List.map (fun c -> c.Body)
                        let seed = if List.isEmpty bodies || not (List.isEmpty poisons) then unknownWrites else noWrites
                        joinWrites accEffect seed, bodies @ accDeps) (initial, [])
    let nodeSpec (node: SemanticNode) : NodeId * WriteEffect * NodeId list =
        let staticEffect, rawDeps =
            match node.Kind with
            | _ when program.InactiveOccurrences.Contains node.Id -> noWrites, []
            | SemanticKind.Lambda _ | SemanticKind.LazyExpr _ | SemanticKind.LazyValue _ | SemanticKind.SeqExpr _
            | SemanticKind.VarRef _ | SemanticKind.Quote _ -> noWrites, []
            | SemanticKind.EnvironmentRead _ | SemanticKind.EnvironmentBorrow _ -> noWrites, node.Children
            | SemanticKind.EnvironmentWrite(_, slot, value) ->
                let store =
                    match program.EnvironmentCaptures.TryFind slot with
                    | Some (true, _) -> { noWrites with Definitions = Set.singleton slot }
                    | _ -> unknownWrites
                store, value :: node.Children
            | SemanticKind.LazyWrite(_, _, value) ->
                let store =
                    match program.LazyCaptures.TryFind node.Id with
                    | Some(slot, true, _, _) -> { noWrites with Definitions = Set.singleton slot }
                    | _ when program.LazyPrivateWrites.Contains node.Id -> noWrites
                    | _ -> unknownWrites
                store, value :: node.Children
            | SemanticKind.FrameWrite(_, _, value) ->
                let store =
                    match program.ContinuationWrites.TryFind node.Id with
                    | Some slot ->
                        match program.Graph.Nodes.TryFind slot with
                        | Some { Kind = SemanticKind.Binding(_, true, _, _) } -> { noWrites with Definitions = Set.singleton slot }
                        | Some _ -> noWrites
                        | None -> unknownWrites
                    | None -> unknownWrites
                store, value :: node.Children
            | SemanticKind.Set (target, value) ->
                let store =
                    match Map.tryFind target program.Reachable with
                    | Some { Kind = SemanticKind.VarRef (_, Some definition) } -> { noWrites with Definitions = Set.singleton definition }
                    | _ -> unknownWrites
                store, [value]
            | SemanticKind.Application (calleeId, arguments) ->
                let root, _ = flattenApplication program.Reachable calleeId arguments
                let mutableCallee =
                    match Map.tryFind root program.Reachable with
                    | Some { Kind = SemanticKind.VarRef (_, Some definition) } -> isMutableDefinition program definition
                    | _ -> false
                let callEffect, callDeps =
                    match Map.tryFind node.Id program.Callees with
                    | _ when mutableCallee -> unknownWrites, []
                    | Some (Callee.Intrinsic { Module = IntrinsicModule.SeqEnumerator; Operation = "moveNext" }, [iterator]) ->
                        match program.SequencePullBodies.TryFind node.Id with
                        | Some (actual, bodies) when actual = iterator -> noWrites, bodies
                        | _ -> unknownWrites, []
                    | Some (Callee.Intrinsic { Module = IntrinsicModule.Seq; Operation = "getEnumerator" }, [_])
                        when program.SequenceInitializations.Contains node.Id -> noWrites, []
                    | Some (Callee.Intrinsic { Module = IntrinsicModule.SeqEnumerator; Operation = "current" }, [_])
                        when program.SequenceCurrentReads.Contains node.Id -> noWrites, []
                    | Some (callee, args) -> invocationSpec callee args
                    | None -> unknownWrites, []
                callEffect, node.Children @ callDeps
            | SemanticKind.LazyForce _ | SemanticKind.YieldBang _ | SemanticKind.TraitCall _ | SemanticKind.PlatformBinding _ ->
                unknownWrites, node.Children
            | _ -> noWrites, node.Children
        node.Id, staticEffect, List.distinct rawDeps
    let specs = program.Ordered |> List.map nodeSpec |> List.toArray
    let effectsDict = System.Collections.Generic.Dictionary<NodeId, WriteEffect>(specs.Length)
    for i = 0 to specs.Length - 1 do
        let (nodeId, staticEffect, _) = specs.[i]
        effectsDict[nodeId] <- staticEffect
    let mutable changed = true
    while changed do
        changed <- false
        for i = specs.Length - 1 downto 0 do
            let (nodeId, _, deps) = specs.[i]
            if not deps.IsEmpty then
                let prevVal = effectsDict[nodeId]
                if not prevVal.Unknown then
                    let mutable nextVal = prevVal
                    let mutable d = deps
                    while not d.IsEmpty && not nextVal.Unknown do
                        let depId = d.Head
                        d <- d.Tail
                        match effectsDict.TryGetValue(depId) with
                        | true, depEffect ->
                            if depEffect.Unknown then
                                nextVal <- unknownWrites
                            elif not depEffect.Definitions.IsEmpty && not (Set.isSubset depEffect.Definitions nextVal.Definitions) then
                                nextVal <- { nextVal with Definitions = Set.union nextVal.Definitions depEffect.Definitions }
                        | false, _ -> ()
                    if nextVal.Unknown <> prevVal.Unknown || not (obj.ReferenceEquals(nextVal.Definitions, prevVal.Definitions)) then
                        effectsDict[nodeId] <- nextVal
                        changed <- true
    effectsDict |> Seq.map (fun kvp -> kvp.Key, kvp.Value) |> Map.ofSeq

let private effectAt (program: Program) id = Map.tryFind id program.Effects |> Option.defaultValue noWrites

let private afterEffect (program: Program) effect bounds =
    bounds |> List.filter (fun (compared, _) ->
        match compared with
        | Compared.Definition definition when isMutableDefinition program definition ->
            not effect.Unknown && not (Set.contains definition effect.Definitions)
        | _ -> true)

//-------------------------------------------------------------------------
// Comparison refinement (width-inference.md §2, "Comparisons seed ranges")
//-------------------------------------------------------------------------

let private relationOf (operation: string) : Relation option =
    match operation with
    | "op_LessThan" -> Some Relation.Lt
    | "op_LessThanOrEqual" -> Some Relation.Le
    | "op_GreaterThan" -> Some Relation.Gt
    | "op_GreaterThanOrEqual" -> Some Relation.Ge
    | "op_Equality" -> Some Relation.Eq
    | "op_Inequality" -> Some Relation.Ne
    | _ -> None

/// The relation that holds when this one does not.
let private complement (r: Relation) : Relation =
    match r with
    | Relation.Lt -> Relation.Ge
    | Relation.Le -> Relation.Gt
    | Relation.Gt -> Relation.Le
    | Relation.Ge -> Relation.Lt
    | Relation.Eq -> Relation.Ne
    | Relation.Ne -> Relation.Eq

/// `x r y` read as `y r' x`.
let private flip (r: Relation) : Relation =
    match r with
    | Relation.Lt -> Relation.Gt
    | Relation.Le -> Relation.Ge
    | Relation.Gt -> Relation.Lt
    | Relation.Ge -> Relation.Le
    | Relation.Eq -> Relation.Eq
    | Relation.Ne -> Relation.Ne

/// The bounds a guard establishes on bindings when it holds (`polarity` true) or fails (false):
/// a comparison of a reference against any expression, through `not`, `&&`, `||` (and Baker's
/// conditional forms of them), a boolean binding's definition and a type annotation.
let rec private atoms (program: Program) (depth: int) (guardId: NodeId) (polarity: bool) : (Compared * Refinement) list =
    if depth > 8 then []
    else
        let key = guardId, polarity, depth
        match program.AtomsCache.TryGetValue key with
        | true, cached -> cached
        | false, _ ->
            let computed = atomsUncached program depth guardId polarity
            program.AtomsCache[key] <- computed
            computed

and private atomsUncached (program: Program) (depth: int) (guardId: NodeId) (polarity: bool) : (Compared * Refinement) list =
    if depth > 8 then []
    else
        match Map.tryFind guardId program.Reachable with
        | Some { Kind = SemanticKind.Application (funcId, args) } ->
            match intrinsicOf program funcId, args with
            | Some { Module = IntrinsicModule.Operators; Operation = "not" }, [ x ] ->
                atoms program (depth + 1) x (not polarity)
            | Some { Module = IntrinsicModule.Operators; Operation = "op_BooleanAnd" }, [ x; y ] ->
                if polarity then afterEffect program (effectAt program y) (atoms program (depth + 1) x true) @ atoms program (depth + 1) y true else []
            | Some { Module = IntrinsicModule.Operators; Operation = "op_BooleanOr" }, [ x; y ] ->
                if polarity then [] else afterEffect program (effectAt program y) (atoms program (depth + 1) x false) @ atoms program (depth + 1) y false
            | Some { Module = IntrinsicModule.Operators; Operation = op }, [ x; y ] ->
                match relationOf op, Map.tryFind x program.Reachable, Map.tryFind y program.Reachable with
                | Some relation, Some nx, Some ny when isRanged nx && isRanged ny ->
                    let relation = if polarity then relation else complement relation
                    let ofDefinition (side: NodeId) (bound: Bound) (r: Relation) =
                        match readDefinition program side with
                        | Some defId when isImmutableDefinition program defId || isMutableDefinition program defId ->
                            [ (Compared.Definition defId, { Bound = bound; Relation = r }) ]
                        | _ -> []
                    let ofSide (side: NodeId) (other: NodeId) (r: Relation) =
                        match Map.tryFind side program.Reachable with
                        | Some _ when readDefinition program side |> Option.exists (fun d -> isImmutableDefinition program d || isMutableDefinition program d) ->
                            let defId = readDefinition program side |> Option.get
                            [ (Compared.Definition defId, { Bound = Bound.Of other; Relation = r }) ]
                        | Some { Kind = SemanticKind.Literal _ } -> []
                        | Some { Kind = SemanticKind.Application (f, [ a; b ]) } ->
                            // one level back through `-` and `+` (§1.2a): `a - b r K` gives `a r K + b`
                            // and `b (flip r) a - K`; `a + b r K` gives `a r K - b` and `b r K - a`
                            let pushed =
                                match intrinsicOf program f with
                                | Some { Module = IntrinsicModule.Operators; Operation = "op_Subtraction" } ->
                                    ofDefinition a (Bound.Sum (other, b)) r @ ofDefinition b (Bound.Diff (a, other)) (flip r)
                                | Some { Module = IntrinsicModule.Operators; Operation = "op_Addition" } ->
                                    ofDefinition a (Bound.Diff (other, b)) r @ ofDefinition b (Bound.Diff (other, a)) r
                                | _ -> []
                            (Compared.Node side, { Bound = Bound.Of other; Relation = r }) :: pushed
                        | Some _ -> [ (Compared.Node side, { Bound = Bound.Of other; Relation = r }) ]
                        | None -> []
                    afterEffect program (joinWrites (effectAt program x) (effectAt program y)) (ofSide x y relation)
                    @ afterEffect program (effectAt program y) (ofSide y x (flip relation))
                | _ -> []
            | None, _ ->
                // A call of a boolean function whose body is comparison atoms over its parameters
                // (`Cursor.fits data offset count`, ruling 3): the body's atoms, with each parameter
                // read as the argument the call supplies. A bound stays the callee's own node, whose
                // range is the join over every call and so contains this call's, which is sound; a
                // literal argument learns nothing; the callee's own interior nodes are not at the
                // call site and are dropped, as is a bound on a mutable the callee reads but does not
                // own.
                match Map.tryFind guardId program.Callees with
                | Some (Callee.Direct (parameters, body), allArgs) when not (program.ForeignEffectBodies.Contains body) ->
                    let argOf = parameters |> List.mapi (fun i (_, _, id) -> id, List.tryItem i allArgs) |> Map.ofList
                    // a bound that reads a parameter reads this call's argument instead: the
                    // argument's range is exactly the parameter's value here, where the parameter
                    // node's is the join over every call
                    let substitute (id: NodeId) =
                        match Map.tryFind id program.Reachable with
                        | Some { Kind = SemanticKind.VarRef (_, Some p) } when Map.containsKey p argOf -> Map.find p argOf |> Option.defaultValue id
                        | _ -> id
                    let substituteBound (bound: Bound) =
                        match bound with
                        | Bound.Of a -> Bound.Of (substitute a)
                        | Bound.Diff (a, c) -> Bound.Diff (substitute a, substitute c)
                        | Bound.Sum (a, c) -> Bound.Sum (substitute a, substitute c)
                    atoms program (depth + 1) body polarity
                    |> List.map (fun (compared, refinement) -> compared, { refinement with Bound = substituteBound refinement.Bound })
                    |> List.choose (fun (compared, refinement) ->
                        match compared with
                        | Compared.Definition d when Map.containsKey d argOf ->
                            match Map.find d argOf |> Option.bind (fun argId -> Map.tryFind argId program.Reachable) with
                            | Some { Kind = SemanticKind.VarRef (_, Some defId) } when isImmutableDefinition program defId || isMutableDefinition program defId ->
                                Some (Compared.Definition defId, refinement)
                            | Some { Kind = SemanticKind.Literal _ } | None -> None
                            | Some arg -> Some (Compared.Node arg.Id, refinement)
                        | Compared.Definition d when isImmutableDefinition program d -> Some (compared, refinement)
                        | _ -> None)
                    |> afterEffect program (effectAt program guardId)
                | _ -> []
            | _ -> []
        | Some { Kind = SemanticKind.IfThenElse (g, t, Some e) } ->
            // `g && t` is `if g then t else false`; `g || e` is `if g then true else e`
            if isLiteralBool program e false then
                (if polarity then afterEffect program (effectAt program t) (atoms program (depth + 1) g true) @ atoms program (depth + 1) t true else [])
            elif isLiteralBool program t true then
                (if polarity then [] else afterEffect program (effectAt program e) (atoms program (depth + 1) g false) @ atoms program (depth + 1) e false)
            else []
        | Some { Kind = SemanticKind.VarRef (_, Some defId) } ->
            match Map.tryFind defId program.Reachable with
            | Some ({ Kind = SemanticKind.Binding (_, false, _, _) } as binding) ->
                match List.tryLast binding.Children with
                | Some valueId ->
                    // An immutable bool preserves an earlier observation. It is
                    // not a fresh comparison of mutable storage at this use.
                    atoms program (depth + 1) valueId polarity |> afterEffect program unknownWrites
                | None -> []
            | _ -> []
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) }
        | Some { Kind = SemanticKind.EagerExpr inner } -> atoms program (depth + 1) inner polarity
        | Some { Kind = SemanticKind.Sequential ids } ->
            // a block's value is its last expression; its bounds hold once the block has run
            match List.tryLast ids with
            | Some last -> atoms program (depth + 1) last polarity
            | None -> []
        | _ -> []

let private boundsOn (program: Program) (bounds: (Compared * Refinement) list) (operand: NodeId) : Refinement list =
    match bounds with
    | [] -> []
    | _ ->
        let k1, k2Opt =
            match Map.tryFind operand program.Reachable with
            | Some { Kind = SemanticKind.VarRef (_, Some defId) } -> Compared.Definition defId, ValueNone
            | Some { Kind = SemanticKind.EnvironmentRead(_, slot) } when program.EnvironmentCaptures.ContainsKey slot -> Compared.Definition slot, ValueNone
            | Some { Kind = SemanticKind.LazyRead _ } ->
                match program.LazyCaptures.TryFind operand with
                | Some(slot, _, _, _) -> Compared.Definition slot, ValueNone
                | None -> Compared.Node operand, ValueNone
            | Some { Kind = SemanticKind.Binding _ } | Some { Kind = SemanticKind.PatternBinding _ } ->
                Compared.Definition operand, ValueSome (Compared.Node operand)
            | _ -> Compared.Node operand, ValueNone
        match k2Opt with
        | ValueNone ->
            bounds |> List.choose (fun (k, r) -> if k = k1 then Some r else None)
        | ValueSome k2 ->
            bounds |> List.choose (fun (k, r) -> if k = k1 || k = k2 then Some r else None)

/// The refinements of the whole program: for every reachable `if`, the guard's bounds on the
/// then-branch's reads and their complements on the else-branch's, the `if`'s own read of each
/// branch included; for every `while`, the guard's bounds on the body's reads.
let private refinementsOf (program: Program) =
    let emptyHashSet = System.Collections.Generic.HashSet<NodeId>()
    let subtreeCache = System.Collections.Generic.Dictionary<NodeId, System.Collections.Generic.HashSet<NodeId>>()
    let cachedSubtree (id: NodeId) : System.Collections.Generic.HashSet<NodeId> =
        match subtreeCache.TryGetValue(id) with
        | true, cached -> cached
        | false, _ ->
            let seen = System.Collections.Generic.HashSet<NodeId>()
            let pending = System.Collections.Generic.Stack<NodeId>()
            pending.Push id
            while pending.Count > 0 do
                let current = pending.Pop()
                match Map.tryFind current program.Reachable with
                | Some node when seen.Add current ->
                    for child in node.Children do pending.Push child
                | _ -> ()
            subtreeCache[id] <- seen
            seen
    let readsAcc = System.Collections.Generic.Dictionary<NodeId, System.Collections.Generic.Dictionary<NodeId, ResizeArray<Refinement>>>()
    let guardsAcc = System.Collections.Generic.Dictionary<NodeId, ResizeArray<Compared * Refinement>>()
    let addEdgeMut (consumer: NodeId) (operand: NodeId) (refs: Refinement list) =
        match refs with
        | [] -> ()
        | _ ->
            let inner =
                match readsAcc.TryGetValue(consumer) with
                | true, d -> d
                | false, _ ->
                    let d = System.Collections.Generic.Dictionary<NodeId, ResizeArray<Refinement>>(2)
                    readsAcc[consumer] <- d
                    d
            let list =
                match inner.TryGetValue(operand) with
                | true, l -> l
                | false, _ ->
                    let l = ResizeArray<Refinement>(4)
                    inner[operand] <- l
                    l
            for r in refs do
                list.Add(r)
    let addGuardMut (id: NodeId) (own: (Compared * Refinement) list) =
        match own with
        | [] -> ()
        | _ ->
            let list =
                match guardsAcc.TryGetValue(id) with
                | true, l -> l
                | false, _ ->
                    let l = ResizeArray<Compared * Refinement>(4)
                    guardsAcc[id] <- l
                    l
            for item in own do
                if not (list.Contains(item)) then
                    list.Add(item)
    let refineEdgesMut (rootId: NodeId) (excl1: System.Collections.Generic.HashSet<NodeId>) (excl2: System.Collections.Generic.HashSet<NodeId>) (bounds: (Compared * Refinement) list) =
        if not (List.isEmpty bounds) then
            let mutableDefs =
                bounds |> List.choose (fun (k, _) -> match k with Compared.Definition d when isMutableDefinition program d -> Some d | _ -> None) |> Set.ofList
            let hasMutables = not mutableDefs.IsEmpty
            let invalidate assigned effect =
                if not hasMutables then Set.empty
                else Set.union assigned (if effect.Unknown then mutableDefs else effect.Definitions)
            let live (assigned: Set<NodeId>) inLambda =
                if not hasMutables then bounds
                elif not inLambda && assigned.IsEmpty then bounds
                else
                    bounds |> List.filter (fun (key, _) ->
                        match key with
                        | Compared.Definition definition when Set.contains definition mutableDefs ->
                            not inLambda && not (Set.contains definition assigned)
                        | _ -> true)
            let inline isExcluded (id: NodeId) = excl1.Contains(id) || excl2.Contains(id)
            let rec walk inLambda (assigned: Set<NodeId>) (id: NodeId) : Set<NodeId> =
                match Map.tryFind id program.Reachable with
                | None -> assigned
                | Some node ->
                    let excluded = isExcluded id
                    if not excluded then
                        let own = live assigned inLambda
                        addGuardMut id own
                    let record (curAssigned: Set<NodeId>) (operand: NodeId) =
                        if not excluded then
                            addEdgeMut id operand (boundsOn program (live curAssigned inLambda) operand)
                    let operand (curAssigned: Set<NodeId>) (child: NodeId) : Set<NodeId> =
                        let nextAssigned = walk inLambda curAssigned child
                        record nextAssigned child
                        nextAssigned
                    match node.Kind with
                    | SemanticKind.VarRef (_, Some definition) ->
                        record assigned definition
                        assigned
                    | SemanticKind.EnvironmentRead(environment, slot) ->
                        let nextAssigned = operand assigned environment
                        record nextAssigned slot
                        nextAssigned
                    | SemanticKind.LazyRead(environment, _) ->
                        let nextAssigned = operand assigned environment
                        match program.LazyCaptures.TryFind id with
                        | Some(slot, _, _, _) -> record nextAssigned slot
                        | None -> ()
                        nextAssigned
                    | SemanticKind.Set (_, value) ->
                        let nextAssigned = operand assigned value
                        invalidate nextAssigned (effectAt program id)
                    | SemanticKind.Lambda _ | SemanticKind.LazyExpr _ | SemanticKind.LazyValue _ | SemanticKind.SeqExpr _ ->
                        for child in node.Children do
                            walk true assigned child |> ignore
                        assigned
                    | SemanticKind.IfThenElse (guard, yes, no) ->
                        let afterGuard = operand assigned guard
                        let afterYes = operand afterGuard yes
                        let afterNo =
                            match no with
                            | Some branch -> operand afterGuard branch
                            | None -> afterGuard
                        Set.union afterYes afterNo
                    | SemanticKind.WhileLoop _ | SemanticKind.ForLoop _ | SemanticKind.ForEach _ ->
                        let nextAssigned = invalidate assigned (effectAt program id)
                        node.Children |> List.fold operand nextAssigned
                    | _ ->
                        let nextAssigned = node.Children |> List.fold operand assigned
                        invalidate nextAssigned (effectAt program id)
            walk false Set.empty rootId |> ignore
    for node in program.Ordered do
        match node.Kind with
        | SemanticKind.IfThenElse (guardId, thenId, elseId) ->
            let positive = atoms program 0 guardId true
            let negative = atoms program 0 guardId false
            if not (List.isEmpty positive && List.isEmpty negative) then
                let guardSet = cachedSubtree guardId
                let thenSet = cachedSubtree thenId
                let elseSet = elseId |> Option.map cachedSubtree |> Option.defaultValue emptyHashSet
                refineEdgesMut thenId guardSet elseSet positive
                addEdgeMut node.Id thenId (boundsOn program positive thenId)
                match elseId with
                | Some e ->
                    refineEdgesMut e guardSet thenSet negative
                    addEdgeMut node.Id e (boundsOn program negative e)
                | None -> ()
        | SemanticKind.WhileLoop (guardId, bodyId) ->
            let positive = atoms program 0 guardId true
            if not (List.isEmpty positive) then
                refineEdgesMut bodyId (cachedSubtree guardId) emptyHashSet positive
        | _ -> ()
    let readsMap =
        readsAcc
        |> Seq.map (fun kvp ->
            let innerMap =
                kvp.Value
                |> Seq.map (fun innerKvp -> innerKvp.Key, Seq.toList innerKvp.Value)
                |> Map.ofSeq
            kvp.Key, innerMap)
        |> Map.ofSeq
    let guardsMap =
        guardsAcc
        |> Seq.map (fun kvp -> kvp.Key, Seq.toList kvp.Value)
        |> Map.ofSeq
    readsMap, guardsMap

/// The range `r` met with the bound `r Relation k`.
let private refine (r: ValueRange) (relation: Relation) (k: ValueRange) : ValueRange =
    match ValueRange.endpoints k with
    | None -> r   // a bound with no values: the branch is not taken; nothing is learnt
    | Some (klo, khi) ->
        match relation with
        | Relation.Lt ->
            match khi with
            | ValueRange.Endpoint.Finite h -> ValueRange.meet r (ValueRange.Below (h - bigint.One))
            | _ -> r
        | Relation.Le ->
            match khi with
            | ValueRange.Endpoint.Finite h -> ValueRange.meet r (ValueRange.Below h)
            | _ -> r
        | Relation.Gt ->
            match klo with
            | ValueRange.Endpoint.Finite l -> ValueRange.meet r (ValueRange.Above (l + bigint.One))
            | _ -> r
        | Relation.Ge ->
            match klo with
            | ValueRange.Endpoint.Finite l -> ValueRange.meet r (ValueRange.Above l)
            | _ -> r
        | Relation.Eq -> ValueRange.meet r (ValueRange.ofEndpoints klo khi)
        | Relation.Ne ->
            // An interval can exclude a singleton only at an established
            // endpoint. An arbitrary inequality proves neither sign nor a
            // finite bound, and a non-singleton comparison excludes no value.
            match klo, khi, ValueRange.endpoints r with
            | ValueRange.Endpoint.Finite value, ValueRange.Endpoint.Finite same,
              Some(ValueRange.Endpoint.Finite lower, _) when value = same && value = lower ->
                ValueRange.meet r (ValueRange.Above(value + bigint.One))
            | ValueRange.Endpoint.Finite value, ValueRange.Endpoint.Finite same,
              Some(_, ValueRange.Endpoint.Finite upper) when value = same && value = upper ->
                ValueRange.meet r (ValueRange.Below(value - bigint.One))
            | _ -> r

//-------------------------------------------------------------------------
// Reading the program
//-------------------------------------------------------------------------

/// The declared integer representations as widening thresholds (numeric-selection.md §9.1).
let private thresholdsOf (context: PlatformContext option) : ValueRange.Threshold list =
    match context with
    | None -> []
    | Some ctx ->
        ctx.Representations
        |> Map.toList
        |> List.choose (fun (_, r) ->
            if (r.Family = "int" || r.Family = "uint") && NumericRepresentation.isOffered r then
                match RangeSources.declaredRange r with
                | Some (ValueRange.Bounded (lo, hi)) -> Some { ValueRange.Threshold.Family = r.Family; Lo = lo; Hi = hi }
                | _ -> None   // a declaration whose range is not integer text is CCS8207's, not a threshold
            else None)

/// Every `Yield` value in a subtree (a comprehension's elements), the nested lambdas and
/// sequence expressions included, since a comprehension's body is one.
let private yieldsWithin (nodes: Map<NodeId, SemanticNode>) (rootId: NodeId) : NodeId list =
    let rec walk (acc: NodeId list) (id: NodeId) =
        match Map.tryFind id nodes with
        | None -> acc
        | Some node ->
            let acc = match node.Kind with SemanticKind.Yield v -> v :: acc | _ -> acc
            node.Children |> List.fold walk acc
    walk [] rootId |> List.rev

/// Consume finite Baker evidence, retaining its exact successful-pull dependency.
/// Completeness against owner delimiters prevents a missing payload edge from
/// silently narrowing the join. Unknown alternatives have no finite entry.
let private sequenceElements (ingress: Lazy<CallableIngress.Reading>)
                             (currentCorrespondence: Lazy<Clef.Compiler.Baker.Ingredients.SequenceCurrentCorrespondence.Evidence list>)
                             (graph: SemanticGraph) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let lifted = currentCorrespondence.Value |> List.groupBy _.Source |> Map.ofList
    let consumers = lazy (Clef.Compiler.Baker.Recipes.SequenceCurrentRecipes.structuralConsumers graph)
    let protocols = System.Collections.Generic.Dictionary<NodeId, ContinuationCurrentInputs.Protocol option>()
    let protocol owner =
        match protocols.TryGetValue owner with
        | true, value -> value
        | _ ->
            let value = ContinuationCurrentInputs.forOwner graph owner
            protocols.Add(owner, value)
            value
    let edges = graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Suspension)
    let byTarget = edges |> List.groupBy _.Target
    byTarget |> List.choose (fun (target, facts) ->
        let sources role = facts |> List.filter (fun edge -> edge.Role = role) |> List.map _.Sources
        let owners = sources EdgeRole.SequenceElementOwner
        let payloads = sources EdgeRole.SequenceElementPayload
        let admissions = sources EdgeRole.SequenceElementAdmission
        let certified = sources EdgeRole.IteratorCurrentAdmitted
        let directAdmission =
            match admissions with
            | [[enumerator; _; loop] as dependency] ->
                certified = [dependency] && (dependency |> List.forall nodes.ContainsKey)
                && (nodes.TryFind loop
                    |> Option.bind (Clef.Compiler.Baker.Recipes.SequenceCurrentRecipes.forLoop graph consumers.Value)
                    |> Option.exists (fun actual -> actual.Target = target && actual.Sources = dependency))
                && (match nodes.TryFind target with
                    | Some { Kind = SemanticKind.Application (_, [iterator]) } ->
                        match nodes.TryFind iterator with
                        | Some { Kind = SemanticKind.VarRef (_, Some actual) } -> actual = enumerator
                        | _ -> false
                    | _ -> false)
            | _ -> false
        let representations = lifted.TryFind target |> Option.defaultValue []
        let ownerPairs = owners |> List.choose (function [iterator; owner] -> Some (iterator, owner) | _ -> None)
        let supplied = payloads |> List.choose (function [owner; payload] -> Some (owner, payload) | _ -> None) |> Set.ofList
        let expected = ownerPairs |> List.map (fun (_, owner) ->
            match nodes.TryFind owner with
            | Some { Kind = SemanticKind.SeqExpr (generator, _) } ->
                match protocol owner with
                | Some protocol ->
                    // The source cuts delimit the complete element set. Their
                    // actual machine writers provide its current scalar facts.
                    protocol.CurrentSlot |> Option.bind (CallableIngress.trySlotAccess ingress.Value owner)
                    |> Option.bind (fun storage ->
                        let inputs = protocol.Cuts |> List.map (fun cut -> cut.Writer, cut.Value)
                        if storage.InitialState.IsSome || Set.ofList inputs <> Set.ofList storage.Inputs then None
                        else Some(protocol.Cuts |> List.map (fun cut -> (owner, cut.Payload), (cut.Writer, cut.Value))))
                | None ->
                    let delimiters = edges |> List.filter (fun edge -> edge.Role = EdgeRole.Delimiter && edge.Sources = [owner; generator])
                    let livePayloads =
                        nodes.TryFind generator |> Option.map (fun node -> yieldsWithin nodes node.Id |> Set.ofList)
                        |> Option.defaultValue Set.empty
                    let values = delimiters |> List.choose (fun edge ->
                        match nodes.TryFind edge.Target with
                        | Some { Kind = SemanticKind.Yield value } when nodes.ContainsKey value && livePayloads.Contains value ->
                            Some ((owner, value), (edge.Target, value))
                        | _ -> None)
                    if values.Length = delimiters.Length then Some values else None
            | _ -> None)
        let iterators = ownerPairs |> List.map fst |> List.distinct
        if (not directAdmission && representations.IsEmpty) || not (List.isEmpty (sources EdgeRole.SequenceElementUnknown))
           || List.isEmpty owners || ownerPairs.Length <> owners.Length
           || (Set.ofList ownerPairs).Count <> ownerPairs.Length
           || supplied.Count <> payloads.Length || (expected |> List.exists Option.isNone) then None
        else
            let expected = expected |> List.collect Option.get
            match iterators with
            | [iterator] when Set.ofList (List.map fst expected) = supplied ->
                let inputs = expected |> List.map snd |> List.distinct
                let direct = if directAdmission then [target, (iterator, inputs)] else []
                Some (direct @ (representations |> List.map (fun value -> value.Current, (value.Iterator, inputs))))
            | _ -> None)
    |> List.concat
    |> List.groupBy fst
    |> List.choose (fun (_, values) -> match values with [value] -> Some value | _ -> None)
    |> Map.ofList

/// Read only complete effect incidence. Origin validation prevents a deleted
/// alternative from turning a partial body list into a closed write summary.
/// The solver reads the currently realized bodies named by that incidence.
let private sequenceEffectSources (currentCorrespondence: Lazy<Clef.Compiler.Baker.Ingredients.SequenceCurrentCorrespondence.Evidence list>)
                                  (graph: SemanticGraph) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let _, origins = SequenceOrigins.resolve graph
    let edges = graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Suspension)
    let byTarget = edges |> List.groupBy _.Target |> Map.ofList
    let pullBodies, initializations =
        nodes |> Map.fold (fun (pulls, initializers) id node ->
            match node.Kind with
            | SemanticKind.Application(_, [operand]) ->
                let facts = byTarget.TryFind id |> Option.defaultValue []
                let sources role = facts |> List.filter (fun edge -> edge.Role = role) |> List.map _.Sources
                let pullRows, initRows = sources EdgeRole.SequencePullBody, sources EdgeRole.SequenceInitialize
                let owners =
                    origins.TryFind operand |> Option.bind (fun alternatives ->
                        let known = alternatives |> Set.toList |> List.choose (function SequenceOrigins.Origin.Known owner -> Some owner | _ -> None)
                        if not alternatives.IsEmpty && known.Length = alternatives.Count then Some known else None)
                let definitions =
                    owners |> Option.bind (fun owners ->
                        let definitions =
                            owners |> List.choose (fun owner ->
                                match nodes.TryFind owner with
                                | Some { Kind = SemanticKind.SeqExpr(generator, _) } ->
                                    match nodes.TryFind generator with
                                    | Some { Kind = SemanticKind.Lambda(_, body, _, _, LambdaContext.SeqGenerator) } when nodes.ContainsKey body -> Some(owner, generator, body)
                                    | _ -> None
                                | _ -> None)
                        if definitions.Length = owners.Length then Some definitions else None)
                match definitions with
                | Some definitions when List.isEmpty (sources EdgeRole.SequenceEffectUnknown) ->
                    let expectedPulls = definitions |> List.map (fun (owner, generator, body) -> [operand; owner; generator; body]) |> Set.ofList
                    let expectedInitializers = definitions |> List.map (fun (owner, generator, _) -> [operand; owner; generator]) |> Set.ofList
                    if List.isEmpty initRows && Set.ofList pullRows = expectedPulls then
                        Map.add id (operand, definitions |> List.map (fun (_, _, body) -> body)) pulls, initializers
                    elif List.isEmpty pullRows && Set.ofList initRows = expectedInitializers then
                        pulls, Set.add id initializers
                    else pulls, initializers
                | _ -> pulls, initializers
            | _ -> pulls, initializers) (Map.empty, Set.empty)
    let currentReads =
        let certificates = edges |> List.filter (fun edge -> edge.Role = EdgeRole.IteratorCurrentAdmitted)
        if certificates.IsEmpty then Set.empty
        else
            let consumers = Clef.Compiler.Baker.Recipes.SequenceCurrentRecipes.structuralConsumers graph
            certificates |> List.choose (fun certificate ->
                match certificate.Sources with
                | [_; _; loop] ->
                    nodes.TryFind loop
                    |> Option.bind (Clef.Compiler.Baker.Recipes.SequenceCurrentRecipes.forLoop graph consumers)
                    |> Option.bind (fun actual ->
                        if actual.Target = certificate.Target && actual.Sources = certificate.Sources then Some actual.Target else None)
                | _ -> None) |> Set.ofList
    let currentReads = currentCorrespondence.Value |> List.fold (fun sites proof -> Set.add proof.Current sites) currentReads
    pullBodies, initializations, currentReads

/// Formation incidence retains capture mode independently of subsequent source
/// rewrites. Join every formation of the same declaration, but never complete a
/// missing or contradictory row from the read's slot name alone.
let private environmentCaptureSources (graph: SemanticGraph) =
    let captures =
        graph.Edges |> List.choose (fun edge ->
            match edge.Class, edge.Role, edge.Sources with
            | EdgeClass.Provenance, EdgeRole.EnvironmentCapture isMutable, [owner; slot; value] ->
                Some ((edge.Target, edge.Ordinal, slot), (owner, value, isMutable))
            | _ -> None)
        |> List.groupBy fst
        |> Map.ofList
    graph.Nodes.Values
    |> Seq.filter _.IsReachable
    |> Seq.collect (fun node ->
        match node.Kind with
        | SemanticKind.EnvironmentCreate(owner, initializers) ->
            initializers |> List.mapi (fun ordinal (slot, value) ->
                let admitted =
                    match Map.tryFind (node.Id, ordinal, slot) captures with
                    | Some [(_, (actualOwner, actualValue, isMutable))]
                        when actualOwner = owner && actualValue = value && graph.Nodes.ContainsKey slot && graph.Nodes.ContainsKey value ->
                        Some (isMutable, (node.Id, value))
                    | _ -> None
                slot, admitted)
        | _ -> [])
    |> Seq.groupBy fst
    |> Seq.choose (fun (slot, rows) ->
        let rows = rows |> Seq.map snd |> Seq.toList
        if rows |> List.exists Option.isNone then None else
        let values = rows |> List.choose id
        match values |> List.map fst |> List.distinct with
        | [isMutable] -> Some (slot, (isMutable, values |> List.map snd))
        | _ -> None)
    |> Map.ofSeq

/// A cache is not an uninitialized integer source and not a fresh read of its
/// captures. Only Baker's complete formation/guard/store protocol establishes
/// that every readable cached value came from this exact thunk result. A
/// malformed lazy access leaves the projection unavailable, never guessed.
let private lazyRangeSources (graph: SemanticGraph) =
    if not (graph.Edges |> List.exists (fun edge -> edge.Role = EdgeRole.LazyInstance)) then
        Map.empty, Map.empty, Set.empty
    else
        let settled = LazyValues.settle graph
        if not settled.Residuals.IsEmpty then Map.empty, Map.empty, Set.empty
        else
            let ownerOf = LazyValues.tryOwner graph
            let results =
                settled.Instances.Values
                |> Seq.map (fun instance -> instance.Cached, instance.ThunkBody)
                |> Map.ofSeq
            let results =
                settled.Forces.Values |> Seq.fold (fun sources force ->
                    sources |> Map.add force.CachedRead settled.Instances[force.Formation].ThunkBody) results
            let captures =
                graph.Nodes.Values |> Seq.choose (fun node ->
                    let environmentAndSlot =
                        match node.Kind with
                        | SemanticKind.LazyRead(environment, slot) | SemanticKind.LazyBorrow(environment, slot)
                        | SemanticKind.LazyWrite(environment, slot, _) when node.IsReachable -> Some(environment, slot)
                        | _ -> None
                    environmentAndSlot |> Option.bind (fun (environment, slot) ->
                        ownerOf environment |> Option.bind settled.Instances.TryFind |> Option.bind (fun instance ->
                            instance.Captured |> List.tryFind (fun (source, _, _) -> source = slot)
                            |> Option.map (fun (_, value, mutableCell) ->
                                node.Id, (slot, mutableCell, instance.Environment, value)))))
                |> Map.ofSeq
            let privateWrites =
                settled.Forces.Values |> Seq.collect (fun force -> [force.ResultStore; force.Publication]) |> Set.ofSeq
            results, captures, privateWrites

let private continuationSources (ingress: Lazy<CallableIngress.Reading>) (unaccountedCells: Set<NodeId>) (graph: SemanticGraph) =
    let reads = graph.Nodes.Values |> Seq.filter (fun node ->
        node.IsReachable &&
        match node.Kind with SemanticKind.FrameRead _ -> true | _ -> false) |> Seq.toList
    let accesses = reads |> List.choose (fun node ->
        match CallableIngress.tryStorageAccess ingress.Value node.Id with
        | Some access ->
            // The shared storage protocol validates the exact writer census,
            // types and every raw storage use. Scalar ranges join the current
            // values; callable identity adds its own correspondence judgment.
            // Neither transfer imports retained scalar range annotations.
            if access.Inputs |> List.forall (fun (_, value) ->
                graph.Nodes.TryFind value |> Option.exists _.IsReachable) then
                Some(node, access)
            else None
        | _ -> None)
    // Current is consumed through the iterator protocol, so its slot need not
    // have an explicit FrameRead citizen. Validate its writers through the
    // same slot census before classifying those stores as private effects.
    let cutOwners =
        graph.Edges |> List.choose (fun edge ->
            match edge.Class, edge.Role, edge.Sources with
            | EdgeClass.Suspension, EdgeRole.SuspensionCut _, [owner; _; _] -> Some(edge.Target, owner)
            | _ -> None)
        |> List.groupBy fst
        |> Map.ofList
    let currentAccesses =
        graph.Edges |> List.choose (fun edge ->
            match edge.Class, edge.Role, edge.Sources, graph.Nodes.TryFind edge.Target with
            | EdgeClass.Provenance, EdgeRole.ContinuationValue, [source], Some { Kind = SemanticKind.FrameWrite(_, slot, _); IsReachable = true } ->
                match cutOwners.TryFind source with
                | Some [_, owner] -> Some(owner, slot)
                | _ -> None
            | _ -> None)
        |> List.distinct
        |> List.choose (fun (owner, slot) -> CallableIngress.trySlotAccess ingress.Value owner slot)
    // A second owner may write a shared cell without reading it. Its stores
    // must participate before any owner may read the logical cell enclosure.
    let sharedAccesses =
        graph.Nodes.Values |> Seq.collect (fun node ->
            match node.Kind with
            | SemanticKind.SeqExpr(_, captured) when node.IsReachable ->
                captured |> List.choose (fun capture ->
                    if capture.IsMutable then
                        capture.SourceNodeId |> Option.bind (CallableIngress.trySlotAccess ingress.Value node.Id)
                    else None)
            | _ -> []) |> Seq.toList
    let allAccesses = (accesses |> List.map snd) @ currentAccesses @ sharedAccesses
    let sharedCells =
        allAccesses |> List.choose (fun access -> access.SharedCell |> Option.map (fun cell -> cell, access.Inputs))
        |> List.groupBy fst
        |> List.choose (fun (cell, owners) ->
            let admitted = owners |> List.collect snd |> Set.ofList
            let actual = graph.Nodes.Values |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.FrameWrite(_, slot, value) when node.IsReachable && slot = cell -> Some(node.Id, value)
                | _ -> None) |> Set.ofSeq
            if admitted = actual && not (unaccountedCells.Contains cell) then Some cell else None)
        |> Set.ofList
    let admittedAccess (access: CallableIngress.StorageAccess) =
        access.SharedCell |> Option.forall (fun cell -> Set.contains cell sharedCells)
    let ranges = accesses |> List.choose (fun (node, access) ->
        if not (isRanged node) || access.SharedCell.IsSome then None else
        let initial = access.InitialState |> Option.map (snd >> ValueRange.point) |> Option.defaultValue ValueRange.Empty
        Some(node.Id, (initial, access.Inputs))) |> Map.ofList
    let cells = accesses |> List.choose (fun (node, access) ->
        if not (isRanged node) || not (admittedAccess access) then None else
        access.SharedCell |> Option.map (fun cell -> node.Id, cell)) |> Map.ofList
    let writes =
        allAccesses |> List.filter admittedAccess |> List.collect (fun access ->
            access.Inputs |> List.choose (fun (writer, value) ->
                match graph.Nodes.TryFind writer with
                | Some { Kind = SemanticKind.FrameWrite(_, slot, actual) } when actual = value && slot = access.Source -> Some(writer, slot)
                | _ -> None))
        |> List.groupBy fst
        |> List.choose (fun (writer, inputs) ->
            match inputs |> List.map snd |> List.distinct with [slot] -> Some(writer, slot) | _ -> None)
        |> Map.ofList
    ranges, cells, writes

/// An occurrence can specialize only suppliers already represented by the
/// shared formal enclosure. CallableOrigins remains the boundary authority.
let internal completeApplications
  (reachable: Map<NodeId, SemanticNode>)
  (inactiveCalls: Set<NodeId>)
  (callArguments: Map<NodeId, (NodeId * NodeId) list>)
  (calls: Map<NodeId, CallableOrigins.ResolvedCall>) =
  calls
  |> Map.filter (fun id call ->
    not (inactiveCalls.Contains id) && reachable.ContainsKey id &&
    call.Complete && not call.Unknown && not call.Targets.IsEmpty &&
    (call.Targets |> List.forall (fun target ->
      target.Parameters.Length = target.Arguments.Length &&
      List.forall2 (fun (_, _, formal) actual ->
        callArguments.TryFind formal
        |> Option.exists (List.contains (id, actual))) target.Parameters target.Arguments)))
  |> Map.map (fun _ call -> call.Targets)

let private readProgram (context: PlatformContext option) (graph: SemanticGraph) : Program =
    let reachableNodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let purposes = Reachability.declarationPurposes graph
    let ordered = reachableNodes |> Map.toList |> List.map snd
    let omittedFormals =
        OrdinaryDemand.tryRead graph
        |> Result.map (fun reading -> reading.Formals.Keys |> Set.ofSeq)
        |> Result.defaultValue Set.empty
    let inactivity = OrdinaryDemand.tryInactivity graph |> Result.toOption
    let inactiveFormals = inactivity |> Option.map _.Formals |> Option.defaultValue Set.empty
    let inactiveOccurrences = inactivity |> Option.map _.Excluded |> Option.defaultValue Set.empty
    let inactiveCalls = inactivity |> Option.map _.Calls |> Option.defaultValue Set.empty
    let deferred =
        Set.unionMany [OrdinaryDemand.tryDeferredOnly graph |> Result.defaultValue Set.empty; omittedFormals
                       inactiveFormals; inactiveOccurrences]
    let parents = parentIndex reachableNodes
    let candidates = escapingOf reachableNodes ordered parents
    let poisons = poisoningOf reachableNodes ordered
    let continuationIngress = lazy (CallableIngress.analyze graph)
    let currentCorrespondence = lazy (
        if graph.Edges |> List.exists (fun edge -> edge.Role = EdgeRole.IteratorCurrentAdmitted && edge.Sources.Length > 3) then
            Clef.Compiler.Baker.Ingredients.SequenceCurrentCorrespondence.read graph continuationIngress.Value
        else [])
    let sequencePulls, sequenceInitializations, sequenceCurrentReads = sequenceEffectSources currentCorrespondence graph
    let lazyResults, lazyCaptures, lazyPrivateWrites = lazyRangeSources graph
    let environmentCaptures = environmentCaptureSources graph
    // The shared cell may also be written by a closure or a lazy body. Every
    // such store must enter the existing checked assignment census before a
    // sequence read can use that cell's fresh enclosure.
    let unaccountedCells =
        ordered |> List.choose (fun node ->
            match node.Kind with
            | SemanticKind.EnvironmentWrite(_, slot, _)
                when not (environmentCaptures.TryFind slot |> Option.exists fst) -> Some slot
            | SemanticKind.LazyWrite(_, slot, _) ->
                match lazyCaptures.TryFind node.Id with
                | Some(source, true, _, _) when source = slot -> None
                | _ -> Some slot
            | _ -> None) |> Set.ofList
    let continuationInputs, continuationCells, continuationWrites = continuationSources continuationIngress unaccountedCells graph
    let baseProgram = {
        Graph = graph
        Context = context
        Reachable = reachableNodes
        Ordered = ordered
        CommitmentSites =
            reachableNodes.Keys
            |> Seq.filter (Reachability.requiresRepresentation purposes)
            |> Set.ofSeq
            |> fun sites -> Set.difference sites deferred
        Parents = parents
        Callees = Map.empty
        Applications = Map.empty
        ForeignDeclarations = Map.empty
        ForeignEntryCalls = Map.empty
        ForeignBodies = Set.empty
        ForeignEffectBodies = Set.empty
        ForeignDeclarationFailure = None
        ForeignResultRanges = Map.empty
        ForeignAbi = Map.empty
        Effects = Map.empty
        LoopRecognition = { Accumulations = []; Linear = []; Tail = []; Edges = [] }
        SequenceAccumulations = []
        SequenceAccumulationTargets = Map.empty
        LoopAccumulations = Map.empty
        LoopLinear = Map.empty
        TailRecurrences = Map.empty
        LazyEffects = Map.empty
        FiniteCells = Map.empty
        SequenceElements = sequenceElements continuationIngress currentCorrespondence graph
        SequencePullBodies = sequencePulls
        SequenceInitializations = sequenceInitializations
        SequenceCurrentReads = sequenceCurrentReads
        EnvironmentCaptures = environmentCaptures
        ContinuationInputs = continuationInputs
        ContinuationCells = continuationCells
        ContinuationWrites = continuationWrites
        LazyResults = lazyResults
        LazyCaptures = lazyCaptures
        LazyPrivateWrites = lazyPrivateWrites
        CallArguments = Map.empty
        IndexSeeds = Map.empty
        Escaping = Map.empty
        EscapingLambdas = Map.empty
        Parameters = Set.empty
        InactiveFormals = inactiveFormals
        InactiveOccurrences = inactiveOccurrences
        RootParameters = Map.empty
        Assignments = Map.empty
        Refinements = Map.empty
        GuardRefinements = Map.empty
        ContinuationRefinements = Map.empty
        Constructions = Map.empty
        IntegerFields = Map.empty
        InputSeeds = Map.empty
        BoundarySeeds = Map.empty
        ArrayLengths = Map.empty
        DeclaredFields = []
        DeclaredParameters = []
        ElementStores = Map.empty
        ElementSeeds = Map.empty
        Thresholds = thresholdsOf context
        Fabric = context |> Option.exists (fun ctx -> PlatformContext.substrateKind ctx = SubstrateKind.FPGA)
        AtomsCache = System.Collections.Generic.Dictionary<NodeId * bool * int, (Compared * Refinement) list>()
        SourceEdgesByTarget =
            lazy (
                graph.Edges
                |> List.filter (fun edge -> edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference)
                |> List.groupBy _.Target
                |> Map.ofList)
        RecordIncidenceCache = System.Collections.Generic.Dictionary<NodeId, bool>()
        ImmutableRecordFieldCache = System.Collections.Generic.Dictionary<NodeId * string, (TypeIdentity * TypeIdentity) option>()
        AggregateElementCache = System.Collections.Generic.Dictionary<NodeId * AggregateProjection list, bool * Set<NodeId>>()
    }
    let parameters =
        ordered
        |> List.collect (fun node ->
            match node.Kind with
            | SemanticKind.Lambda (parameters, _, _, _, _) -> parameters |> List.map (fun (_, _, id) -> id)
            | _ -> [])
        |> Set.ofList
    let rootParameters =
        graph.DeclarationRoots
        |> List.collect (fun (rootId, root) ->
            match lambdaOf reachableNodes rootId with
            | Some (_, parameters, _) -> parameters |> List.map (fun (_, _, id) -> (id, root))
            | None -> [])
        |> Map.ofList
    let kernelIngress = Clef.Compiler.Baker.Recipes.KernelDeclarations.admitted graph
    let kernelParameters = kernelIngress |> List.collect (fun ingress -> ingress.Parameters |> List.map snd) |> Set.ofList
    let kernelImplementations = kernelIngress |> List.map _.Implementation |> Set.ofList
    let escaping =
        candidates
        |> List.collect (fun c -> c.Parameters |> List.skip (min c.Offset c.Parameters.Length) |> List.map (fun (_, _, id) -> (id, c.Escape)))
        |> List.fold (fun acc (id, why) -> if kernelParameters.Contains id || Map.containsKey id acc then acc else Map.add id why acc) Map.empty
    let escapingLambdas =
        candidates
        |> List.fold (fun acc c -> if kernelImplementations.Contains c.LambdaId || Map.containsKey c.LambdaId acc then acc else Map.add c.LambdaId c.Escape acc) Map.empty
    let callableFlow = CallableOrigins.resolve graph
    let callees =
        ordered
        |> List.filter (fun node -> not (inactiveCalls.Contains node.Id))
        |> List.fold (fun acc node ->
            match node.Kind with
            | SemanticKind.Application (funcId, args) ->
                let resolved =
                    match resolveCallee reachableNodes candidates poisons funcId args with
                    | Some (Callee.Intrinsic { Module = IntrinsicModule.FnPtr; Operation = "invoke" }, pointer :: _) as intrinsic
                        when Clef.Compiler.Baker.Recipes.BoundaryDeclarations.entryFormation graph pointer |> Option.isSome ->
                        // Imported entries retain the original declaration correspondence.
                        // Their placeholder is not an ordinary callback invocation body.
                        intrinsic
                    | Some (Callee.Intrinsic { Module = IntrinsicModule.FnPtr; Operation = "invoke" }, _pointer :: actuals) ->
                        match callableFlow.NativeCalls.TryFind node.Id with
                        | Some native ->
                            let targets = native.Targets |> List.map (fun target ->
                                { LambdaId = target.Lambda; Parameters = target.Parameters; Body = target.Body
                                  Offset = 0; Escape = "invoked through a native entry" })
                            Some(Callee.Value(targets, native.Unknown), actuals)
                        | None -> Some(Callee.Value([], true), actuals)
                    | Some (Callee.Intrinsic _, _) as intrinsic -> intrinsic
                    // Keep direct formal identity for ABI seeds and partial
                    // frontiers only at this occurrence's callable boundary.
                    // Flattening syntax can cross an already completed call
                    // into the function its body returns; its outer parameters
                    // and body do not describe the later invocation.
                    | Some (Callee.Direct (parameters, body), actuals) as direct
                        when (match callableFlow.Calls.TryFind node.Id with
                              | Some actual when actual.Complete ->
                                  not actual.Unknown && not actual.Targets.IsEmpty && (actual.Targets |> List.forall (fun target ->
                                      target.Parameters = parameters && target.Body = body && target.Arguments = actuals))
                              | _ -> true) -> direct
                    | fallback ->
                        match callableFlow.Calls.TryFind node.Id with
                        | Some actual when actual.Unknown || not actual.Targets.IsEmpty ->
                            let targets = actual.Targets |> List.map (fun target ->
                                { LambdaId = target.Lambda; Parameters = target.Parameters; Body = target.Body
                                  Offset = 0; Escape = escapeOf reachableNodes parents target.Lambda })
                            match actual.Targets |> List.map _.Arguments |> List.distinct with
                            | [actuals] -> Some(Callee.Value(targets, actual.Unknown), actuals)
                            | [] -> Some(Callee.Value(targets, actual.Unknown), args)
                            // This transfer joins bodies with a shared actual
                            // vector. Distinct bound actuals require their own
                            // correspondence; never zip one arm's inputs to another.
                            | _ -> Some(Callee.Value([], true), args)
                        | _ -> fallback
                match resolved with
                | Some resolved -> Map.add node.Id resolved acc
                | None -> acc
            | _ -> acc) Map.empty
    let supply (paramId: NodeId) (callId: NodeId) (argId: NodeId) (acc: Map<NodeId, (NodeId * NodeId) list>) =
        let existing = Map.tryFind paramId acc |> Option.defaultValue []
        Map.add paramId ((callId, argId) :: existing) acc
    let supplyAll (parameters: (string * NativeType * NodeId) list) (offset: int) (callId: NodeId) (args: NodeId list) (acc: Map<NodeId, (NodeId * NodeId) list>) =
        let openParams = parameters |> List.skip (min offset parameters.Length)
        let n = min openParams.Length args.Length
        List.zip (List.truncate n openParams) (List.truncate n args)
        |> List.fold (fun acc ((_, _, paramId), argId) -> supply paramId callId argId acc) acc
    // The lambdas a function-valued argument of an intrinsic names: applied in place, a named
    // binding's, or every candidate the value may be.
    let lambdasOfValue (id: NodeId) : (string * NativeType * NodeId) list list =
        match Map.tryFind id reachableNodes with
        | Some { Kind = SemanticKind.Lambda _ } -> lambdaShape reachableNodes id |> Option.map (fst >> List.singleton) |> Option.defaultValue []
        | Some { Kind = SemanticKind.VarRef (_, Some defId) } ->
            match lambdaOf reachableNodes defId with
            | Some (_, parameters, _) -> [ parameters ]
            | None -> reachable reachableNodes candidates [] |> List.map (fun c -> c.Parameters |> List.skip (min c.Offset c.Parameters.Length))
        | _ -> []
    let (callArguments, indexSeeds) =
        callees
        |> Map.fold (fun (calls: Map<NodeId, (NodeId * NodeId) list>, seeds: Map<NodeId, (NodeId * NodeId) list>) callId (callee, args) ->
            match callee with
            | Callee.Direct (parameters, _) ->
                let calls = supplyAll parameters 0 callId args calls
                // surplus arguments go to the value the body returns: a call through a value
                if args.Length > parameters.Length then
                    let surplus = args |> List.skip parameters.Length
                    let calls = reachable reachableNodes candidates surplus |> List.fold (fun calls c -> supplyAll c.Parameters c.Offset callId surplus calls) calls
                    (calls, seeds)
                else (calls, seeds)
            | Callee.Value (cs, _) -> (cs |> List.fold (fun calls c -> supplyAll c.Parameters c.Offset callId args calls) calls, seeds)
            | Callee.Intrinsic info ->
                RangeSources.calls info
                |> List.fold (fun (calls, seeds) (position, supplies) ->
                    match List.tryItem position args with
                    | None -> (calls, seeds)
                    | Some fId ->
                        lambdasOfValue fId
                        |> List.fold (fun (calls, seeds) parameters ->
                            List.zip (List.truncate (min parameters.Length supplies.Length) parameters)
                                     (List.truncate (min parameters.Length supplies.Length) supplies)
                            |> List.fold (fun (calls, seeds) ((_, _, paramId), seed) ->
                                match seed with
                                | RangeSources.Seed.IndexBelow nIndex ->
                                    match List.tryItem nIndex args with
                                    | Some nId -> (calls, supply paramId callId nId seeds)
                                    | None -> (calls, seeds)
                                | RangeSources.Seed.Unknown -> (calls, seeds)) (calls, seeds)) (calls, seeds)) (calls, seeds))
            (callableFlow.ParameterInputs |> Map.map (fun _ inputs ->
                inputs |> List.filter (fun (site, _) -> not (inactiveCalls.Contains site)))
             // No remaining supplier is no observation, not an empty aggregate
             // alternative. Only the separate inactive-formal proof authorizes
             // an Empty scalar execution join.
             |> Map.filter (fun _ inputs -> not inputs.IsEmpty), Map.empty)
    // A parameter an intrinsic hands a value the pass does not model (a sequence or list
    // element): named as such when nothing else supplies it.
    let unknownSupplied =
        callees
        |> Map.fold (fun (acc: Map<NodeId, string>) _ (callee, args) ->
            match callee with
            | Callee.Intrinsic info ->
                RangeSources.calls info
                |> List.fold (fun acc (position, supplies) ->
                    match List.tryItem position args with
                    | None -> acc
                    | Some fId ->
                        lambdasOfValue fId
                        |> List.fold (fun acc parameters ->
                            List.zip (List.truncate (min parameters.Length supplies.Length) parameters)
                                     (List.truncate (min parameters.Length supplies.Length) supplies)
                            |> List.fold (fun acc ((_, _, paramId), seed) ->
                                match seed with
                                | RangeSources.Seed.Unknown -> Map.add paramId (sprintf "handed to '%s', which supplies values the pass does not model" info.FullName) acc
                                | _ -> acc) acc) acc) acc
            | _ -> acc) Map.empty
    let escaping = unknownSupplied |> Map.fold (fun acc id why -> Map.add id why acc) escaping
    let assignments =
        ordered
        |> List.filter (fun node -> not (inactiveOccurrences.Contains node.Id))
        |> List.fold (fun acc node ->
            match node.Kind with
            | SemanticKind.Set (targetId, valueId) ->
                match Map.tryFind targetId reachableNodes with
                | Some { Kind = SemanticKind.VarRef (_, Some defId) } ->
                    let existing = Map.tryFind defId acc |> Option.defaultValue []
                    Map.add defId (valueId :: existing) acc
                | _ -> acc
            | SemanticKind.EnvironmentWrite(_, slot, value) when baseProgram.EnvironmentCaptures.TryFind slot |> Option.exists fst ->
                let existing = Map.tryFind slot acc |> Option.defaultValue []
                Map.add slot (value :: existing) acc
            | SemanticKind.LazyWrite(_, _, value) ->
                match baseProgram.LazyCaptures.TryFind node.Id with
                | Some(slot, true, _, _) ->
                    let existing = Map.tryFind slot acc |> Option.defaultValue []
                    Map.add slot (value :: existing) acc
                | _ -> acc
            | SemanticKind.FrameWrite(_, slot, value) ->
                // A represented store still updates its logical mutable cell.
                // Only the complete storage census may establish that identity.
                match baseProgram.ContinuationWrites.TryFind node.Id, graph.Nodes.TryFind slot with
                | Some source, Some { Kind = SemanticKind.Binding(_, true, _, _) } when source = slot ->
                    let existing = Map.tryFind source acc |> Option.defaultValue []
                    Map.add source (value :: existing) acc
                | _ -> acc
            | _ -> acc) Map.empty
    let constructions =
        ordered
        |> List.fold (fun acc node ->
            match node.Kind, node.Type with
            | SemanticKind.RecordExpr (fields, _), NativeType.TApp (tycon, _) ->
                let existing = Map.tryFind (NominalTypeIdentity.ofConstructor tycon) acc |> Option.defaultValue []
                Map.add (NominalTypeIdentity.ofConstructor tycon) ((node.Id, fields) :: existing) acc
            | _ -> acc) Map.empty
    let integerFields =
        graph.Nodes.Values
        |> Seq.choose (fun node ->
            match node.Kind, node.Type with
            | SemanticKind.TypeDef (_, TypeDefKind.RecordDef fields, _), NativeType.TApp(tycon, _) ->
                let integers = fields |> List.filter (fun (_, ty) -> Types.isIntegerType ty) |> List.map fst
                if List.isEmpty integers then None else Some (NominalTypeIdentity.ofConstructor tycon, integers)
            | _ -> None)
        |> Map.ofSeq
    // A hardware design's inputs: the Step function's second parameter is the pin record. Each
    // boolean pin is `[0, 1]`; a pin of any other numeric type has no declared range in this
    // changeset (CS-12 supplies boundary ranges) and so is unobservable.
    let hardwareSeeds =
        graph.DeclarationRoots
        |> List.choose (fun (rootId, root) ->
            match root with
            | DeclRoot.HardwareModule ->
                Map.tryFind rootId reachableNodes
                |> Option.bind (fun binding -> List.tryLast binding.Children)
                |> Option.bind (fun designId -> Map.tryFind designId reachableNodes)
                |> Option.bind (fun design ->
                    match design.Kind with
                    | SemanticKind.RecordExpr (fields, _) -> fields |> List.tryFind (fun (n, _) -> n = "Step") |> Option.map snd
                    | _ -> None)
                |> Option.bind (fun stepId ->
                    match Map.tryFind stepId reachableNodes with
                    | Some { Kind = SemanticKind.VarRef (_, Some defId) } -> lambdaOf reachableNodes defId
                    | _ -> None)
                |> Option.bind (fun (_, parameters, _) ->
                    match parameters with
                    | [ _; (_, (NativeType.TApp (tycon, _) as inputType), _) ] ->
                        RecordInstances.tryFields inputType graph
                        |> Option.map (fun fields ->
                            NominalTypeIdentity.ofConstructor tycon,
                            fields
                            |> List.choose (fun (name, ty) ->
                                match Types.tryGetNTUKind ty with
                                | Some NTUKind.NTUbool -> Some (name, ValueRange.boolean)
                                | Some NTUKind.NTUchar -> Some (name, ValueRange.codePoint)
                                | Some k when NTUKind.isInteger k -> Some (name, ValueRange.Unbounded)
                                | _ -> None)
                            |> Map.ofList)
                    | _ -> None)
            | _ -> None)
        |> Map.ofList
    // The declared boundaries (§1.1 last bullet, §4.1; ruling 1 of CS-12), read by the one
    // structural reader: a wire-schema field or an MMIO register at its layout descriptor's
    // declared representation seeds the record type's field, through the same path as a hardware
    // design's pins; an extern's parameters and result at its binding descriptor's declared bits
    // and signedness seed the nodes that cross. A record or field no descriptor declares takes no
    // seed and stays unobservable (CCS8011 names the missing declaration); nothing is invented.
    let descriptors = PlatformResolution.readDescriptors graph
    let descriptors = { descriptors with Functions = descriptors.Functions @ ((CallbackDeclarations.read graph).Callbacks |> List.map (fun c -> c.Function)) }
    let foreignDeclarations =
        graph.Edges |> List.choose (fun edge ->
            match edge.Class, edge.Role with
            | EdgeClass.Boundary, EdgeRole.BoundaryDeclaration declaration
                when edge.Target = declaration.Binding && edge.Sources = declaration.Path @ declaration.Formals @ [declaration.Body] &&
                     (graph.Nodes.TryFind declaration.Binding |> Option.exists (fun node ->
                         node.Metadata.ContainsKey "FidelityExtern.Library" || node.Metadata.ContainsKey "FidelityExtern.Symbol")) &&
                     (graph.Nodes.TryFind declaration.Body |> Option.exists (fun node -> Types.isIntegerType node.Type)) -> Some declaration
            | _ -> None)
        |> List.groupBy _.Body |> Map.ofList
    // The existing boundary identity owner supplies the expected source census.
    // Missing incidence removes authority; it must not make the placeholder an
    // ordinary body or turn its physical ABI into promised behavior.
    let expectedExternal =
        graph.Nodes |> Map.toList |> List.choose (fun (_, node) ->
            if not (Clef.Compiler.Baker.Recipes.BoundaryDeclarations.isExternal node) then None else
            match Clef.Compiler.Baker.Recipes.BoundaryDeclarations.bindingPath graph node.Id with
            | Ok(path, formals, body) -> Some(node.Id, path, formals |> List.map (fun (_, _, formal) -> formal), body)
            | _ -> None)
    let foreignEffectBodies = expectedExternal |> List.map (fun (_, _, _, body) -> body) |> Set.ofList
    let expectedForeign = expectedExternal |> List.filter (fun (_, _, _, body) ->
        graph.Nodes.TryFind body |> Option.exists (fun body -> Types.isIntegerType body.Type))
    let foreignBodies = expectedForeign |> List.map (fun (_, _, _, body) -> body) |> Set.ofList
    let missingForeign = expectedForeign |> List.filter (fun (binding, path, formals, body) ->
        let matching = foreignDeclarations.TryFind body |> Option.defaultValue [] |> List.filter (fun declaration ->
            declaration.Binding = binding && declaration.Path = path && declaration.Implementation = List.last path && declaration.Formals = formals)
        matching.Length <> 1)
    let foreignDeclarationFailure =
        missingForeign |> List.tryHead |> Option.map (fun (binding, _, _, _) ->
            let range = graph.Nodes[binding].Range
            binding, sprintf "The integer foreign boundary declaration at %s:%d has no unique current identity row." range.File range.Start.Line)
    let foreignResultRanges = descriptors.ResultRanges |> List.groupBy (fun range -> range.Declaration.Binding) |> Map.ofList
    let foreignEntryCalls =
        callees
        |> Map.toList
        |> List.choose (fun (call, (callee, arguments)) ->
            match callee, arguments with
            | Callee.Intrinsic {
                                   Module = IntrinsicModule.FnPtr
                                   Operation = "invoke"
                               },
              pointer :: actuals ->
                Clef.Compiler.Baker.Recipes.BoundaryDeclarations.entryFormation graph pointer
                |> Option.bind (fun entry ->
                    let declarations =
                        foreignDeclarations.Values
                        |> Seq.collect id
                        |> Seq.filter (fun declaration -> declaration.Binding = entry.Declaration)
                        |> Seq.toList

                    match declarations with
                    | [ declaration ] when declaration.Formals.Length = actuals.Length ->
                        Some(call, (declaration, actuals, entry.Transport))
                    | _ -> None)
            | _ -> None)
        |> Map.ofList

    let foreignAbi = descriptors.Functions |> List.choose (fun abi -> abi.Body |> Option.map (fun body -> body, abi))
                     |> List.groupBy fst |> List.map (fun (body, rows) -> body, rows |> List.map snd) |> Map.ofList
    let inputSeeds =
        descriptors.Layouts
        |> List.fold (fun (acc: Map<NominalTypeIdentity, Map<string, ValueRange>>) layout ->
            match layout.RecordType with
            | Some typeName ->
                let existing = Map.tryFind typeName acc |> Option.defaultValue Map.empty
                Map.add typeName (layout.Fields |> List.fold (fun m f -> Map.add f.Name f.Range m) existing) acc
            | None -> acc) hardwareSeeds
    let declaredFields =
        descriptors.Layouts
        |> List.collect (fun layout ->
            match layout.RecordType with
            | Some typeName -> layout.Fields |> List.map (fun f -> typeName, f)
            | None -> [])
    let (boundarySeeds, declaredParameters) =
        descriptors.Functions
        |> List.fold (fun (seeds: Map<NodeId, ValueRange>, declared: (NodeId * PlatformResolution.DeclaredParameter) list) f ->
            let seeds = f.Parameters |> List.fold (fun s (paramId, d) -> match d with Some d -> Map.add paramId d.Range s | None -> s) seeds
            let seeds =
                match f.Body, f.Return with
                | Some body, Some _ when foreignBodies.Contains body -> seeds
                | Some body, Some r -> Map.add body r.Range seeds
                | _ -> seeds
            (seeds, declared @ (f.Parameters |> List.choose (fun (paramId, d) -> d |> Option.map (fun d -> paramId, d))))) (Map.empty, [])
    // A receiving contract states the native incoming domain, including unused
    // formals. It supplies no observed callback arguments or body result range.
    let boundarySeeds, declaredParameters =
        CallbackDeclarations.presentReceiving graph
        |> List.fold (fun (seeds, declared) entry ->
            entry.Signature.Parameters |> List.fold (fun (seeds, declared) (formal, parameter) ->
                match parameter with
                | Some parameter -> Map.add formal parameter.Range seeds, (formal, parameter) :: declared
                | None -> seeds, declared) (seeds, declared)) (boundarySeeds, declaredParameters)
    let boundarySeeds =
        Clef.Compiler.Baker.Recipes.KernelDeclarations.seeds graph
        |> Map.fold (fun seeds formal range -> Map.add formal range seeds) boundarySeeds
    let boundarySeeds =
        ordered |> List.fold (fun seeds node ->
            match CallbackDeclarations.invocationResult graph node.Id |> Option.orElseWith (fun () -> Mmio.numericBoundary graph node.Id) |> Option.orElseWith (fun () -> BorrowedViews.numericBoundary graph node.Id) |> Option.orElseWith (fun () -> MappedBindings.numericBoundary graph node.Id) with
            | Some result -> Map.add node.Id result.Range seeds
            | None -> seeds) boundarySeeds
    let boundarySeeds =
        // Logical string bytes have a source codomain independently of any
        // offered storage width. Keep this fact at the exact read occurrence.
        Clef.Compiler.Baker.Ingredients.StringBytes.logicalReadRanges graph
        |> Map.fold (fun seeds site range -> Map.add site range seeds) boundarySeeds
    let boundarySeeds =
        ordered |> List.fold (fun seeds node ->
            match StringByteStorage.readRange graph node.Id with
            | Some range -> Map.add node.Id range seeds
            | None -> seeds) boundarySeeds
    // Every value stored into an array, by element type (§3.3): an array literal's elements (a
    let boundarySeeds =
        graph.Edges |> List.fold (fun seeds edge ->
            match edge.Role with
            | EdgeRole.StringExtent extent when not extent.StaticOrigins.IsEmpty ->
                let values = extent.StaticOrigins.Values |> Seq.toList
                Map.add extent.Site (ValueRange.bounded (List.min values) (List.max values)) seeds
            | EdgeRole.StringExtent extent ->
                Map.add extent.Site (RangeSources.lengthRange graph.Platform) seeds
            | _ -> seeds) boundarySeeds
    // A local byte view retains the exact source string's descriptor extent.
    // Known origin lengths refine its ordinary Array.length observation; the
    // dynamic value remains a descriptor read, never a chosen maximum length.
    let boundarySeeds =
        let views = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringByteView view -> Some(view.Site,view) | _ -> None) |> Map.ofList
        ordered |> List.fold (fun seeds node ->
            match node.Kind with
            | SemanticKind.Application(callee,[buffer]) ->
                match graph.Nodes.TryFind callee,views.TryFind buffer with
                | Some { Kind=SemanticKind.Intrinsic { Module=IntrinsicModule.Array; Operation="length" } },Some view when not view.StaticOrigins.IsEmpty ->
                    let lengths = view.StaticOrigins.Values |> Seq.toList
                    Map.add node.Id (ValueRange.bounded (List.min lengths) (List.max lengths)) seeds
                | _ -> seeds
            | _ -> seeds) boundarySeeds
    // comprehension's yields), an indexer or `Array.set` assignment, `Array.create`'s seed,
    // `Array.init`'s function result (a named lambda's body, or every candidate's through a value),
    // and `Array.zeroCreate`'s zero for an integer element type.
    let store (key: TypeIdentity) (storer: NodeId) (value: NodeId) (acc: Map<TypeIdentity, (NodeId * NodeId) list>) =
        let existing = Map.tryFind key acc |> Option.defaultValue []
        Map.add key ((storer, value) :: existing) acc
    /// The bodies a function value's results come from; None when a poisoning value may be the
    /// value (its results are unobservable)
    let bodiesOfValue (id: NodeId) : NodeId list option =
        match Map.tryFind id reachableNodes with
        | Some { Kind = SemanticKind.Lambda (_, body, _, _, _) } -> Some [ body ]
        | Some { Kind = SemanticKind.VarRef (_, Some defId) } ->
            match lambdaOf reachableNodes defId with
            | Some (_, _, body) -> Some [ body ]
            | None when poisonReaches reachableNodes poisons [] -> None
            | None -> Some (reachable reachableNodes candidates [] |> List.map (fun c -> c.Body))
        | Some { Kind = SemanticKind.Intrinsic _ } -> None
        | _ -> Some []
    let referenceParameters = descriptors.Functions |> List.collect (fun f -> f.References) |> Map.ofList
    let arrayAllocationDefaults =
        graph.Edges
        |> List.choose (fun edge ->
            match edge.Role with
            | EdgeRole.ArrayAllocationConstruction construction ->
                construction.Default |> Option.map (fun value -> construction.Site, value)
            | _ -> None)
        |> List.groupBy fst
        |> Map.ofList
    let (elementStores, elementSeeds) =
        ordered
        |> List.fold (fun (stores: Map<TypeIdentity, (NodeId * NodeId) list>, seeds: Map<TypeIdentity, ValueRange>) node ->
            let typeOf (id: NodeId) = Map.tryFind id reachableNodes |> Option.map (fun n -> n.Type)
            match node.Kind with
            | SemanticKind.ArrayAllocate _ ->
                match arrayElementType node.Type, Map.tryFind node.Id arrayAllocationDefaults with
                | Some elem, Some [(_, value)] -> store (elementKey elem) node.Id value stores,seeds
                | _ -> stores,seeds
            | SemanticKind.ArrayExpr elements ->
                match arrayElementType node.Type with
                | Some elem ->
                    let key = elementKey elem
                    let values =
                        elements
                        |> List.collect (fun e ->
                            match Map.tryFind e reachableNodes with
                            | Some en when arrayElementType en.Type = Some (applySubst elem) || (match applySubst en.Type with NativeType.TSeq _ -> true | _ -> false) ->
                                // a comprehension: its yields are the elements
                                yieldsWithin reachableNodes e
                            | Some { Kind = SemanticKind.SeqExpr _ } -> yieldsWithin reachableNodes e
                            | _ -> [ e ])
                    (values |> List.fold (fun s v -> store key node.Id v s) stores, seeds)
                | None -> (stores, seeds)
            | SemanticKind.IndexSet (exprId, _, valueId) ->
                match typeOf exprId |> Option.bind arrayElementType with
                | Some elem -> (store (elementKey elem) node.Id valueId stores, seeds)
                | None -> (stores, seeds)
            | SemanticKind.Application (funcId, _) ->
                // an array handed to a boundary (a platform endpoint, a C call through a binding
                // descriptor) is written where the pass sees no store: an unbounded store
                let isBoundaryCall =
                    match Map.tryFind node.Id callees with
                    | Some (Callee.Intrinsic { Module = IntrinsicModule.Sys }, _) -> true
                    | _ ->
                        let (rootId, _) = flattenApplication reachableNodes funcId []
                        match Map.tryFind rootId reachableNodes with
                        | Some { Kind = SemanticKind.VarRef (_, Some defId) } ->
                            Map.tryFind defId reachableNodes |> Option.exists (fun d -> Map.containsKey "FidelityExtern.Library" d.Metadata)
                        | _ -> false
                let seeds =
                    if isBoundaryCall then
                        let supplied =
                            match Map.tryFind node.Id callees with
                            | Some (Callee.Direct (parameters, _), args) when parameters.Length = args.Length ->
                                List.zip parameters args |> List.map (fun ((_, _, paramId), arg) -> arg, Map.tryFind paramId referenceParameters)
                            | _ -> node.Children |> List.map (fun arg -> arg, None)
                        supplied
                        |> List.fold (fun (s: Map<TypeIdentity, ValueRange>) (argId, declared) ->
                            match typeOf argId |> Option.bind arrayElementType with
                            | Some elem ->
                                let key = elementKey elem
                                let incoming = declared |> Option.map (fun d -> d.Range) |> Option.defaultValue ValueRange.Unbounded
                                Map.add key (ValueRange.join (Map.tryFind key s |> Option.defaultValue ValueRange.Empty) incoming) s
                            | None -> s) seeds
                    else seeds
                match Map.tryFind node.Id callees with
                | Some (Callee.Intrinsic { Module = IntrinsicModule.Array; Operation = "set" }, [ arrId; _; valueId ]) ->
                    match typeOf arrId |> Option.bind arrayElementType with
                    | Some elem -> (store (elementKey elem) node.Id valueId stores, seeds)
                    | None -> (stores, seeds)
                | Some (Callee.Intrinsic { Module = IntrinsicModule.Array; Operation = "create" }, [ _; seedId ]) ->
                    match arrayElementType node.Type with
                    | Some elem -> (store (elementKey elem) node.Id seedId stores, seeds)
                    | None -> (stores, seeds)
                | Some (Callee.Intrinsic ({ Module = IntrinsicModule.Array } as info), args) when RangeSources.elementsFromFunction info ->
                    // Array.init / map / mapi / collect / choose: the elements are the function
                    // value's results; through a poisoning value they are unobservable
                    match arrayElementType node.Type, RangeSources.functionArgument info args with
                    | Some elem, Some fId ->
                        match bodiesOfValue fId with
                        | Some bodies -> (bodies |> List.fold (fun s b -> store (elementKey elem) node.Id b s) stores, seeds)
                        | None -> (stores, Map.add (elementKey elem) ValueRange.Unbounded seeds)
                    | Some elem, None -> (stores, Map.add (elementKey elem) ValueRange.Unbounded seeds)
                    | None, _ -> (stores, seeds)
                | Some (Callee.Intrinsic { Module = IntrinsicModule.Array; Operation = "zeroCreate" }, _) ->
                    match arrayElementType node.Type with
                    | Some elem when Types.isIntegerType elem || Types.tryGetNTUKind elem = Some NTUKind.NTUbool || Types.tryGetNTUKind elem = Some NTUKind.NTUchar ->
                        let key = elementKey elem
                        (stores, Map.add key (ValueRange.join (Map.tryFind key seeds |> Option.defaultValue ValueRange.Empty) (ValueRange.point bigint.Zero)) seeds)
                    | _ -> (stores, seeds)
                | Some (Callee.Intrinsic { Module = IntrinsicModule.String; Operation = "toBytes" }, _) ->
                    match arrayElementType node.Type, StringByteStorage.element graph node.Id with
                    | Some elem, Some(SettledSlot.Integer(8, _)) ->
                        let key = elementKey elem
                        stores, Map.add key (ValueRange.join (Map.tryFind key seeds |> Option.defaultValue ValueRange.Empty) (ValueRange.bounded 0I 255I)) seeds
                    | Some elem, _ -> stores, Map.add (elementKey elem) ValueRange.Unbounded seeds
                    | None, _ -> stores, seeds
                // The element rule is closed (the reviewer's arrmap2 probe, CS-11): an intrinsic that
                // produces an array from anything but same-element operations on an array (the
                // `RangeSources.sameElements` table) builds elements the fold does not see, so its
                // element type takes an unbounded seed; a user function's array comes from the
                // literals, stores and intrinsics inside it, which the fold does see.
                | Some (Callee.Intrinsic info, _) when not (RangeSources.sameElements info) ->
                    match arrayElementType node.Type with
                    | Some elem -> (stores, Map.add (elementKey elem) ValueRange.Unbounded seeds)
                    | None -> (stores, seeds)
                | _ -> (stores, seeds)
            | _ -> (stores, seeds)) (Map.empty, Map.empty)
    let program =
        { baseProgram with
            Callees = callees
            Applications = completeApplications reachableNodes inactiveCalls callArguments callableFlow.Calls
            ForeignDeclarations = foreignDeclarations
            ForeignEntryCalls = foreignEntryCalls
            ForeignBodies = foreignBodies
            ForeignEffectBodies = foreignEffectBodies
            ForeignDeclarationFailure = foreignDeclarationFailure
            ForeignResultRanges = foreignResultRanges
            ForeignAbi = foreignAbi
            CallArguments = callArguments
            IndexSeeds = indexSeeds
            Escaping = escaping
            EscapingLambdas = escapingLambdas
            Parameters = parameters
            RootParameters = rootParameters
            Assignments = assignments
            Constructions = constructions
            IntegerFields = integerFields
            InputSeeds = inputSeeds
            BoundarySeeds = boundarySeeds
            ArrayLengths = Clef.Compiler.Baker.Ingredients.ArrayShapes.observations graph
            DeclaredFields = declaredFields
            DeclaredParameters = declaredParameters
            ElementStores = elementStores
            ElementSeeds = elementSeeds }
    let lazyEffects = LazyEffectRanges.recognize graph
    let lazyTargets = lazyEffects |> List.collect (fun bound ->
        (bound.Cell, bound) :: (bound.Contributions |> List.map (fun contribution -> contribution.Value, bound))) |> Map.ofList
    let finiteCells = FiniteCellRanges.recognize graph
    let finiteTargets = finiteCells |> List.collect (fun bound ->
        (bound.Cell, bound) :: (bound.Writes |> List.choose (fun write -> if write.MaximumActivations > 0I || not (inactiveOccurrences.Contains write.Store) then Some(write.Value, bound) else None))) |> Map.ofList
    let program =
        { program with Effects = effectsOf program; LazyEffects = lazyTargets; FiniteCells = finiteTargets }
    let inputs: LoopRecipes.Inputs = {
        Operators = program.Callees |> Map.toList |> List.choose (fun (id, (callee, arguments)) ->
            match callee with
            | Callee.Intrinsic info when info.Module = IntrinsicModule.Operators -> Some(id, (info.Operation, arguments))
            | _ -> None) |> Map.ofList
        Assignments = program.Assignments
        Effects = program.Effects |> Map.map (fun _ effect -> effect.Definitions, effect.Unknown) }
    let graph, loops = LoopRanges.recognize inputs program.Graph
    let tailInputs: LoopRecipes.TailInputs = {
        Calls = program.Applications |> Map.toList |> List.choose (fun (site, alternatives) ->
            match alternatives with
            | [target] -> Some(site, (target.Lambda, target.Parameters |> List.map (fun (_, _, id) -> id), target.Arguments))
            | _ -> None) |> Map.ofList
        Suppliers = program.CallArguments
        OpenParameters = Set.unionMany [program.RootParameters.Keys |> Set.ofSeq; program.Escaping.Keys |> Set.ofSeq; program.IndexSeeds.Keys |> Set.ofSeq] }
    let graph, loops = LoopRanges.recognizeTail inputs tailInputs graph loops
    let graph, sequences = SequenceAccumulations.recognize inputs graph
    let program = { program with
                        Graph = graph
                        LoopRecognition = loops
                        SequenceAccumulations = sequences
                        SequenceAccumulationTargets = sequences |> List.collect (fun item -> [item.Cell, item; item.Update, item]) |> Map.ofList
                        LoopAccumulations = loops.Accumulations |> List.collect (fun item -> [item.Cell, item; item.Update, item]) |> Map.ofList
                        LoopLinear = loops.Linear |> List.collect (fun item -> item.Targets |> List.map (fun (id, index) -> id, (item, index))) |> Map.ofList
                        TailRecurrences = loops.Tail |> List.collect (fun item -> (item.Counter :: item.CounterUpdate :: (item.Targets |> List.map fst)) |> List.distinct |> List.map (fun id -> id, item)) |> Map.ofList }
    let continuationRefinements =
        Clef.Compiler.Baker.Recipes.ContinuationGuardRecipes.forGraph program.Graph (fun id ->
            match program.Effects.TryFind id with
            | Some effect -> effect.Definitions, effect.Unknown
            | None -> Set.empty, true)
        |> List.collect (fun proof ->
            atoms program 0 proof.Guard proof.Polarity
            |> List.choose (fun (compared, refinement) ->
                match compared with
                | Compared.Node operand when operand = proof.Operand -> Some(proof.Read, refinement)
                | Compared.Definition cell when cell = proof.Cell -> Some(proof.Read, refinement)
                | _ -> None))
        |> List.groupBy fst
        |> List.map (fun (read, rows) -> read, rows |> List.map snd |> List.distinct)
        |> Map.ofList
    let refinements, guards = refinementsOf program
    { program with
        Refinements = refinements
        GuardRefinements = guards
        ContinuationRefinements = continuationRefinements }

//-------------------------------------------------------------------------
// The transfer function
//-------------------------------------------------------------------------

type private State = Map<NodeId, ValueRange>

type private Reading = NodeId -> ValueRange

/// Retain the source invocation, callback site and generated adapter call.
/// Longer histories merge in this finite space under the owning fixed point.
let [<Literal>] private InvocationContextDepth = 3

type private ContextProgram = {
    Invocations: RangeInvocationRow list
    Members: Map<RangeContext, Set<NodeId>>
    Parameters: Map<RangeContext * NodeId, (RangeContext * NodeId * NodeId) list>
    Calls: Map<RangeContext * NodeId, RangeInvocationRow list>
    Occurrences: Map<NodeId, RangeContext list>
    Coordinates: (RangeContext * SemanticNode) list
}

type private ContextState = {
    Values: Map<RangeContext * NodeId, ValueRange>
    Reads: Map<RangeContext * NodeId, Set<RangeContext * NodeId>>
}

/// The range a node has so far; a node not yet computed contributes nothing (the least element).
let private current (state: State) (id: NodeId) : ValueRange =
    Map.tryFind id state |> Option.defaultValue ValueRange.Empty

/// The range a bound reads: one node's, or the interval difference or sum of two nodes'.
let private currentBound (value: Reading) (bound: Bound) : ValueRange =
    match bound with
    | Bound.Of id -> value id
    | Bound.Diff (a, b) -> ValueRange.sub (value a) (value b)
    | Bound.Sum (a, b) -> ValueRange.add (value a) (value b)

/// A range met with every bound of a use edge.
let private refineBy (value: Reading) (refs: Refinement list) (r: ValueRange) : ValueRange =
    refs |> List.fold (fun acc x -> refine acc x.Relation (currentBound value x.Bound)) r

/// Necessary guard atoms constrain source occurrences independently of which
/// tested declaration a particular operand reads. Unknown guards add no fact.
let private feasibleAtoms (value: Reading) (bounds: (Compared * Refinement) list) =
    bounds |> List.forall (fun (compared, refinement) ->
        let id = match compared with Compared.Definition id | Compared.Node id -> id
        refine (value id) refinement.Relation (currentBound value refinement.Bound) <> ValueRange.Empty)

let private guardFeasible program value guard polarity =
    not (isLiteralBool program guard (not polarity)) &&
    feasibleAtoms value (atoms program 0 guard polarity)

let private occurrenceFeasible (program: Program) value id =
    program.GuardRefinements.TryFind id |> Option.defaultValue [] |> feasibleAtoms value

/// What `consumer` reads of `operand`: the operand's range met with the bounds in force on that
/// use edge (a read inside a guarded branch).
let private read (program: Program) (value: Reading) (consumer: NodeId) (operand: NodeId) : ValueRange =
    match Map.tryFind consumer program.Refinements |> Option.bind (Map.tryFind operand) with
    | Some refs -> refineBy value refs (value operand)
    | None -> value operand

/// The range of a record field (`FieldRanges` in the making): the declared range where a
/// descriptor declares one that is observable (the declaration binds, §4.4; a construction whose
/// value leaves it is witnessed by CCS8012, never merged), else the join of the field over the
/// type's reachable constructions and the seed a hardware design's pin carries; the empty range
/// where nothing constructs it and nothing declares it.
let private fieldRange (program: Program) (value: Reading) (typeName: NominalTypeIdentity) (field: string) : ValueRange =
    let declared =
        Map.tryFind typeName program.InputSeeds
        |> Option.bind (Map.tryFind field)
    match declared with
    | Some d when ValueRange.isObservable d -> d
    | _ ->
        Map.tryFind typeName program.Constructions
        |> Option.defaultValue []
        |> List.fold (fun acc (recordId, fields) ->
            fields
            |> List.filter (fun (name, _) -> name = field)
            |> List.fold (fun acc (_, valueId) -> ValueRange.join acc (read program value recordId valueId)) acc) (declared |> Option.defaultValue ValueRange.Empty)

/// The interim declared boundary of a width-named carrier (§1.1 last bullet; `RangeSources`
/// source 2): a source node whose carrier names a declared representation (a parameter nothing
/// supplies, an untabled intrinsic result, a boundary call's result, a field of a record nothing
/// constructs) holds a value of that representation, so its unobservable transfer is the whole
/// declared range, the carrier's physical set; never the meet with a half-line, which a wrapping
/// carrier does not respect (the reviewer's carrierloop probe). An arithmetic cycle the program
/// never bounds stays unobservable, CCS8011 on every substrate (§1.3), whatever its carrier. A
/// bounded transfer is kept. The bare kind is untouched. Deleted in CS-12 with the spellings.
let private boundByCarrier (program: Program) (node: SemanticNode) (r: ValueRange) : ValueRange =
    if ValueRange.isObservable r then r
    else
        match Types.tryGetNTUKind node.Type |> Option.bind (RangeSources.declaredRangeOfKind program.Context) with
        | Some declared -> declared
        | None -> r

/// A node whose value enters the program from outside the pass's view: the carrier boundary
/// applies to it and to nothing computed from it.
let private isSource (program: Program) (node: SemanticNode) : bool =
    match node.Kind with
    | SemanticKind.PatternBinding _ -> Set.contains node.Id program.Parameters
    | SemanticKind.FieldGet _ | SemanticKind.IndexGet _ | SemanticKind.VarRef (_, None) -> true
    | SemanticKind.Application _ ->
        match Map.tryFind node.Id program.Callees with
        | Some (Callee.Intrinsic _, _) -> true
        | Some (Callee.Value (_, poisoned), _) -> poisoned
        | Some (Callee.Direct _, _) -> false
        | None -> true  // a call the pass could not resolve: a binding descriptor, a boundary
    | _ -> false

/// The range of an element of an array of element type `elem` (`ElementRanges` in the making):
/// a width-named element carrier is its declared range regardless of the stores (the byte view of
/// a buffer is `[0, 255]`: a platform endpoint or a C call writes into such a buffer where the pass
/// sees no store, so the carrier's declared boundary is the only sound element range; interim,
/// CS-12); otherwise the join of every value stored into such an array and its constant seeds, an
/// array handed to a boundary call recording an unbounded store (`ElementStores`); a type nothing
/// reachable stores into came from a source the pass did not see, and is unobservable.
let private elementRange (program: Program) (value: Reading) (elem: NativeType) : ValueRange =
    match Types.tryGetNTUKind elem |> Option.bind (RangeSources.declaredRangeOfKind program.Context) with
    | Some declared -> declared
    | None ->
        let key = elementKey elem
        let stores = Map.tryFind key program.ElementStores |> Option.defaultValue []
        let seed = Map.tryFind key program.ElementSeeds
        match stores, seed with
        | [], None -> ValueRange.Unbounded
        | _ ->
            stores
            |> List.fold (fun acc (storer, valueId) -> ValueRange.join acc (read program value storer valueId))
                         (seed |> Option.defaultValue ValueRange.Empty)

/// `[0, n - 1]` for an index below `n`.
let private indexBelow (n: ValueRange) : ValueRange =
    match ValueRange.endpoints n with
    | Some (_, ValueRange.Endpoint.Finite h) -> ValueRange.bounded bigint.Zero (h - bigint.One)
    | Some (_, ValueRange.Endpoint.PosInf) -> ValueRange.Above bigint.Zero
    | _ -> ValueRange.Empty

/// Kind/Children own syntax incidence. Native F can omit cached copies, but
/// every recorded copy must agree and must occur only once.
let private recordIncidenceAgrees (program: Program) (node: SemanticNode) =
    match program.RecordIncidenceCache.TryGetValue node.Id with
    | true, cached -> cached
    | false, _ ->
        let sourceEdge (edge: Hyperedge) = edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference
        let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Target, edge.Sources
        let expected =
            Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence node
            |> List.filter sourceEdge
            |> List.map key
        let agrees =
            program.SourceEdgesByTarget.Value.TryFind node.Id
            |> Option.forall (fun edges ->
                let actual = edges |> List.map key
                actual.Length = (List.distinct actual).Length && List.forall (fun row -> List.contains row expected) actual)
        program.RecordIncidenceCache[node.Id] <- agrees
        agrees

/// A construction can supply an aggregate-valued field only when the exact
/// source declaration makes that field immutable. Mutable field stores need a
/// separate complete write census; a cached scalar FieldRanges entry is not it.
let private immutableRecordField (program: Program) recordId field =
    match program.ImmutableRecordFieldCache.TryGetValue((recordId, field)) with
    | true, cached -> cached
    | false, _ ->
        let computed =
            match Map.tryFind recordId program.Reachable with
            | Some receiver ->
                match applySubst receiver.Type with
                | NativeType.TApp(constructor, _) ->
                    let nominal = NominalTypeIdentity.ofConstructor constructor
                    match RecordInstances.tryDefinition nominal program.Graph with
                    | Some declaration ->
                        match declaration.Kind, declaration.Metadata.TryFind "TypeDef.MutableFields" with
                        | SemanticKind.TypeDef(_, TypeDefKind.RecordDef _, _), Some(MetadataValue.StringList mutableFields)
                            when not (List.contains field mutableFields) ->
                            let affects receiverId name =
                                name = field &&
                                (match Map.tryFind receiverId program.Reachable with
                                 | Some target ->
                                     match applySubst target.Type with
                                     | NativeType.TApp(actual, _) -> NominalTypeIdentity.ofConstructor actual = nominal
                                     | _ -> true
                                 | None -> true)
                            let written =
                                program.Ordered
                                |> List.exists (fun node ->
                                    match node.Kind with
                                    | SemanticKind.FieldSet(receiver, name, _) | SemanticKind.FieldAddress(receiver, name) -> affects receiver name
                                    | SemanticKind.Set(target, _) ->
                                        match Map.tryFind target program.Reachable with
                                        | Some { Kind = SemanticKind.FieldGet(receiver, name) } -> affects receiver name
                                        | _ -> false
                                    | SemanticKind.AddressOf(target, _) ->
                                        match Map.tryFind target program.Reachable with
                                        | Some { Kind = SemanticKind.FieldGet(receiver, name) } -> affects receiver name
                                        // No address-origin algebra is claimed by this
                                        // bounded immutable-field reader.
                                        | _ -> true
                                    | SemanticKind.CellAddress _ -> true
                                    | _ -> false)
                            if written then None
                            else
                                match RecordInstances.tryFields receiver.Type program.Graph |> Option.map (List.filter (fst >> (=) field)) with
                                | Some [_, fieldType] -> Some(RecordInstances.layoutKey receiver.Type, RecordInstances.layoutKey fieldType)
                                | _ -> None
                        | _ -> None
                    | None -> None
                | _ -> None
            | None -> None
        program.ImmutableRecordFieldCache[(recordId, field)] <- computed
        computed

/// The range of a projection of an aggregate-valued expression, read through the constructions the
/// expression can evaluate to (a tuple is not a node with one range; its elements are joined by
/// position, as a record's fields are by name): through references, bindings (a mutable one's
/// assignments included), the parameters' supplies, branch joins, blocks, annotations, function
/// results (a named lambda's body, or every candidate's through a value) and an element read of
/// an array of tuples. An expression that is not traced to constructions has no observable
/// element range.
/// Projection paths compose: extracting a tuple slot from a DU payload first selects the
/// union payload, then the slot. Tags never stand in for payload values. Opaque alternatives
/// and recursive aggregate origins remain unbounded rather than disappearing from a join.
let rec private aggregateElementOrigins (program: Program) (visited: Set<NodeId>) (exprId: NodeId) (path: AggregateProjection list) : bool * bool * Set<NodeId> =
    if List.isEmpty path then false, false, Set.singleton exprId
    elif Set.contains exprId visited then true, true, Set.empty
    else
        match program.AggregateElementCache.TryGetValue((exprId, path)) with
        | true, (u, l) -> false, u, l
        | false, _ ->
            let visited = Set.add exprId visited
            let project id nextPath = aggregateElementOrigins program visited id nextPath
            let recurse id = project id path
            let emptyResult = false, false, Set.empty
            let unboundedResult = false, true, Set.empty
            let combine (c1, u1, l1) (c2, u2, l2) =
                c1 || c2, u1 || u2, Set.union l1 l2
            let joinAll (ids: NodeId list) =
                ids |> List.fold (fun acc id -> combine acc (recurse id)) emptyResult
            let hadCycle, u, l =
                match Map.tryFind exprId program.Reachable with
                | None -> unboundedResult
                | Some node ->
                    match node.Kind with
                    | SemanticKind.TupleExpr elements ->
                        match path with
                        | TupleSlot index :: rest ->
                            match List.tryItem index elements with
                            | Some elementId -> project elementId rest
                            | None -> unboundedResult
                        | _ -> unboundedResult
                    | SemanticKind.RecordExpr(fields, copied) ->
                        match path with
                        | RecordField(expected, field) :: rest
                            when node.Children = (Option.toList copied @ List.map snd fields) && recordIncidenceAgrees program node ->
                            match immutableRecordField program node.Id field with
                            | Some(actual, fieldType) when actual = expected ->
                                match fields |> List.filter (fst >> (=) field) with
                                | [_, value] ->
                                    match Map.tryFind value program.Reachable with
                                    | Some valueNode when RecordInstances.layoutKey valueNode.Type = fieldType -> project value rest
                                    | _ -> unboundedResult
                                | [] -> copied |> Option.map recurse |> Option.defaultValue unboundedResult
                                | _ -> unboundedResult
                            | _ -> unboundedResult
                        | _ -> unboundedResult
                    | SemanticKind.UnionCase(name, tag, payload)
                    | SemanticKind.DUConstruct(name, tag, payload, _) ->
                        match path with
                        | UnionPayload(expectedTag, expectedName) :: rest ->
                            if tag <> expectedTag then emptyResult
                            elif name <> expectedName then unboundedResult
                            else payload |> Option.map (fun id -> project id rest) |> Option.defaultValue unboundedResult
                        | _ -> unboundedResult
                    | SemanticKind.DUEliminate(value, tag, name, _) -> project value (UnionPayload(tag, name) :: path)
                    | SemanticKind.TupleGet(value, index) -> project value (TupleSlot index :: path)
                    | SemanticKind.FieldGet(value, field) ->
                        match immutableRecordField program value field with
                        | Some(identity, fieldType)
                            when node.Children = [value] && RecordInstances.layoutKey node.Type = fieldType && recordIncidenceAgrees program node ->
                            project value (RecordField(identity, field) :: path)
                        | _ -> unboundedResult
                    | SemanticKind.VarRef (_, Some defId) -> recurse defId
                    | SemanticKind.Binding (_, isMutable, _, _) ->
                        let value =
                            match List.tryLast node.Children with
                            | Some valueId -> recurse valueId
                            | None -> unboundedResult
                        if isMutable then
                            Map.tryFind node.Id program.Assignments |> Option.defaultValue [] |> List.fold (fun acc a -> combine acc (recurse a)) value
                        else value
                    | SemanticKind.PatternBinding _ when Set.contains node.Id program.Parameters ->
                        if program.RootParameters.TryFind node.Id = Some DeclRoot.LibraryExport then
                            unboundedResult
                        else
                            match Map.tryFind node.Id program.CallArguments with
                            | Some args ->
                                args
                                |> List.fold (fun acc (_, a) -> combine acc (recurse a)) emptyResult
                            | None -> unboundedResult
                    | SemanticKind.PatternBinding _ ->
                        match List.tryLast node.Children with
                        | Some valueId -> recurse valueId
                        | None -> unboundedResult
                    | SemanticKind.IfThenElse (_, tBranch, eBranch) ->
                        combine (recurse tBranch) (eBranch |> Option.map recurse |> Option.defaultValue emptyResult)
                    | SemanticKind.Match (_, cases) -> joinAll (cases |> List.map (fun c -> c.Body))
                    | SemanticKind.CaseElimination (_, arms) -> joinAll (arms |> List.map (fun a -> a.Body))
                    | SemanticKind.Sequential ids ->
                        match List.tryLast ids with
                        | Some lastId -> recurse lastId
                        | None -> unboundedResult
                    | SemanticKind.TypeAnnotation (inner, _) -> recurse inner
                    | SemanticKind.Application _ ->
                        match Map.tryFind node.Id program.Callees with
                        | Some (Callee.Direct (_, bodyId), _) -> recurse bodyId
                        | Some (Callee.Value (candidates, false), _) when not (List.isEmpty candidates) -> joinAll (candidates |> List.map (fun c -> c.Body))
                        | Some (Callee.Intrinsic { Module = IntrinsicModule.Array; Operation = "get" }, arrId :: _) ->
                            match Map.tryFind arrId program.Reachable |> Option.map (fun n -> n.Type) |> Option.bind arrayElementType with
                            | Some elem -> joinAll (Map.tryFind (elementKey elem) program.ElementStores |> Option.defaultValue [] |> List.map snd)
                            | None -> unboundedResult
                        | _ -> unboundedResult
                    | SemanticKind.IndexGet (arrId, _) ->
                        match Map.tryFind arrId program.Reachable |> Option.map (fun n -> n.Type) |> Option.bind arrayElementType with
                        | Some elem ->
                            match Map.tryFind (elementKey elem) program.ElementStores with
                            | Some stores -> joinAll (stores |> List.map snd)
                            | None -> unboundedResult
                        | None -> unboundedResult
                    | _ -> unboundedResult
            if not hadCycle then
                program.AggregateElementCache[(exprId, path)] <- (u, l)
            hadCycle, u, l

let private aggregateElement (program: Program) (value: Reading) (visited: Set<NodeId>) (exprId: NodeId) (path: AggregateProjection list) : ValueRange =
    let _, unbounded, leaves = aggregateElementOrigins program visited exprId path
    let initial = if unbounded then ValueRange.Unbounded else ValueRange.Empty
    leaves |> Set.fold (fun acc leafId -> ValueRange.join acc (value leafId)) initial

/// Match existing direct formal/body correspondence, never a C symbol or a new callee walk.
let private foreignDeclaration (program: Program) call =
    match program.ForeignEntryCalls.TryFind call with
    | Some(declaration, actuals, _) -> Some(declaration, actuals)
    | None ->
        match program.Callees.TryFind call with
        | Some (Callee.Direct(formals, body), actuals) when program.ForeignDeclarations.ContainsKey body ->
            let declarations = program.ForeignDeclarations[body] |> List.filter (fun declaration ->
                declaration.Formals = (formals |> List.map (fun (_, _, formal) -> formal)))
            match declarations with
            | [declaration] when actuals.Length = declaration.Formals.Length -> Some(declaration, actuals)
            | _ -> None
        | _ -> None

let private foreignResultDescriptor (program: Program) (declaration: BoundaryDeclaration) =
    match program.ForeignResultRanges.TryFind declaration.Binding with Some [descriptor] -> Some descriptor | _ -> None

/// A conditional enclosure reads each actual with the existing use-edge refinement.
/// It authorizes no proof, representation choice, or foreign execution by itself.
let private foreignRange (program: Program) value call =
    match foreignDeclaration program call with
    | None -> ValueRange.Unbounded
    | Some(declaration, actuals) ->
        match foreignResultDescriptor program declaration with
        | None ->
            // This is the ingress value domain of the exact declared ABI,
            // not a behavioral relation or a promise of registration success.
            match program.ForeignAbi.TryFind declaration.Body with
            | Some [abi] -> abi.Return |> Option.map _.Range |> Option.defaultValue ValueRange.Unbounded
            | _ -> ValueRange.Unbounded
        | Some descriptor ->
            let endpoint = function
                | ForeignResultBound.Constant value -> ValueRange.point value
                | ForeignResultBound.Argument ordinal ->
                    actuals |> List.tryItem ordinal |> Option.map (read program value call) |> Option.defaultValue ValueRange.Unbounded
            match endpoint descriptor.Hypothesis.Lower, endpoint descriptor.Hypothesis.Upper with
            | ValueRange.Empty, _ | _, ValueRange.Empty -> ValueRange.Empty
            | ValueRange.Bounded(lo, _), ValueRange.Bounded(_, hi) -> ValueRange.bounded lo hi
            | _ -> ValueRange.Unbounded

/// The range an application computes: the table's fact for an intrinsic (`RangeSources`), the
/// element range for an element read, or every complete target's contextual
/// body fact. Other established calls retain shared body
/// enclosures; unresolved calls and untabled intrinsics remain unobservable.
let private applicationRange (program: Program) (shared: Reading) (value: Reading) (application: NodeId -> ValueRange option) (node: SemanticNode) (fallback: ValueRange) : ValueRange =
    match Map.tryFind node.Id program.Callees with
    | _ when program.ForeignEntryCalls.ContainsKey node.Id -> foreignRange program value node.Id
    | Some (Callee.Direct(_, body), _) when program.ForeignEffectBodies.Contains body ->
        if program.ForeignBodies.Contains body then foreignRange program value node.Id else fallback
    | Some (Callee.Value(candidates, _), _) when candidates |> List.exists (fun candidate -> program.ForeignEffectBodies.Contains candidate.Body) ->
        fallback
    | Some (Callee.Intrinsic { Module = IntrinsicModule.SeqEnumerator; Operation = "current" }, [iterator]) ->
        match program.SequenceElements.TryFind node.Id with
        | Some (actual, payloads) when actual = iterator ->
            payloads |> List.fold (fun range (writer, payload) -> ValueRange.join range (read program shared writer payload)) ValueRange.Empty
        | _ -> fallback
    | Some (Callee.Intrinsic info, args) ->
        let arguments =
            args
            |> List.map (fun a ->
                match Map.tryFind a program.Reachable with
                | Some an ->
                    { RangeSources.Argument.Range = (if isRanged an then read program value node.Id a else ValueRange.Unbounded)
                      RangeSources.Argument.Type = an.Type
                      RangeSources.Argument.Literal = (match an.Kind with SemanticKind.Literal l -> Some l | _ -> None) }
                | None -> { RangeSources.Argument.Range = ValueRange.Unbounded; RangeSources.Argument.Type = NativeType.TError "unreachable"; RangeSources.Argument.Literal = None })
        match RangeSources.intrinsic program.Context info arguments with
        | RangeSources.Result.Fact r -> r
        | RangeSources.Result.ElementOf i ->
            match List.tryItem i arguments |> Option.bind (fun a -> arrayElementType a.Type) with
            | Some elem -> elementRange program shared elem
            | None -> fallback
        | RangeSources.Result.Untabled -> fallback
    | _ when program.Applications.ContainsKey node.Id ->
        application node.Id |> Option.defaultValue fallback
    | Some (Callee.Direct (_, bodyId), _) -> shared bodyId
    | Some (Callee.Value (candidates, false), _) when not (List.isEmpty candidates) ->
        candidates |> List.fold (fun acc c -> ValueRange.join acc (shared c.Body)) ValueRange.Empty
    | _ -> fallback

/// The transfer function: the range of one node from the ranges of the nodes it reads. `None` for
/// a node that is not ranged (not an integer, boolean or char), except that a union tag is a point
/// and a tag read is `[0, cases - 1]`. An integer node's unobservable transfer is met with its
/// width-named carrier's declared range, where it has one (`boundByCarrier`).
let private transfer (program: Program) (shared: Reading) (value: Reading) (application: NodeId -> ValueRange option) (node: SemanticNode) : ValueRange option =
    let get = read program value node.Id
    let ranged = isRanged node
    // what an integer node with no rule is; a boolean or a char is bounded by its type
    let fallback =
        if isBoolNode node then ValueRange.boolean
        elif isCharNode node then ValueRange.codePoint
        else ValueRange.Unbounded
    let computed =
        match node.Kind with
        | SemanticKind.UnionCase (_, caseIndex, _)
        | SemanticKind.DUConstruct (_, caseIndex, _, _) -> Some (ValueRange.point (bigint caseIndex))
        | SemanticKind.DUGetTag (_, duType) ->
            let cases =
                match duType with
                | NativeType.TUnion (_, cases) -> List.length cases
                | NativeType.TApp (tycon, _) -> tycon.CaseCount
                | _ -> 0
            Some (ValueRange.Bounded (bigint.Zero, bigint (max 0 (cases - 1))))
        | _ when not ranged -> None
        | _ when program.ArrayLengths.ContainsKey node.Id ->
            program.ArrayLengths[node.Id].Sources |> List.fold (fun range source ->
                let value =
                    match source with
                    | Clef.Compiler.Baker.Ingredients.ArrayShapes.Length.Constant value -> ValueRange.point value
                    | Clef.Compiler.Baker.Ingredients.ArrayShapes.Length.Count count -> shared count
                ValueRange.join range value) ValueRange.Empty |> Some
        | _ when program.ForeignBodies.Contains node.Id -> Some ValueRange.Unbounded
        // ABI parameter carriers remain declaration inputs; foreign return widths
        // do not constitute a behavioral source range.
        | _ when Map.containsKey node.Id program.BoundarySeeds -> Map.tryFind node.Id program.BoundarySeeds
        | _ when program.LazyResults.ContainsKey node.Id ->
            // Read the thunk's whole result enclosure. A guard on a mutable
            // capture at this later force cannot refine an earlier cached value.
            Some (shared program.LazyResults[node.Id])
        | SemanticKind.Literal (NativeLiteral.Int (v, _)) -> Some (ValueRange.point (bigint v))
        | SemanticKind.Literal (NativeLiteral.UInt (v, _)) -> Some (ValueRange.point (bigint v))
        | SemanticKind.Literal (NativeLiteral.Bool _) -> Some ValueRange.boolean
        | SemanticKind.Literal (NativeLiteral.Char c) -> Some (ValueRange.point (bigint (int c)))
        | SemanticKind.Literal _ -> Some fallback
        | SemanticKind.Application _ -> Some (applicationRange program shared value application node fallback)
        | SemanticKind.VarRef (_, Some defId) -> Some (get defId)
        | SemanticKind.VarRef (_, None) -> Some fallback
        | SemanticKind.EnvironmentRead(_, slot) ->
            match program.EnvironmentCaptures.TryFind slot with
            | Some (true, _) when program.Reachable.ContainsKey slot -> Some (get slot)
            | Some (false, initializers) ->
                initializers |> List.fold (fun range (formation, value) ->
                    let valueRange = if program.Reachable.ContainsKey value then read program shared formation value else fallback
                    ValueRange.join range valueRange) ValueRange.Empty |> Some
            | _ -> Some fallback
        | SemanticKind.FrameRead _ ->
            let value =
                match program.ContinuationCells.TryFind node.Id, program.ContinuationInputs.TryFind node.Id with
                | Some cell, _ -> get cell
                | None, Some(initial, inputs) ->
                    inputs |> List.fold (fun range (writer, value) ->
                        ValueRange.join range (read program shared writer value)) initial
                | None, None -> fallback
            let refinements = program.ContinuationRefinements.TryFind node.Id |> Option.defaultValue []
            Some (refineBy shared refinements value)
        | SemanticKind.LazyRead _ ->
            match program.LazyCaptures.TryFind node.Id with
            | Some(slot, true, _, _) when program.Reachable.ContainsKey slot -> Some (get slot)
            | Some(_, false, formation, value) when program.Reachable.ContainsKey value ->
                Some (read program shared formation value)
            | _ -> Some fallback
        | SemanticKind.PatternBinding _ when Set.contains node.Id program.Parameters ->
            // a parameter is the join of the arguments at every call that supplies it, directly or
            // through a function value, and of the index seeds an intrinsic hands it; one nothing
            // supplies (a declaration root's, an entry the platform calls, an escaping lambda's no
            // seen call reaches) has no observable range here
            let supplied = Map.tryFind node.Id program.CallArguments |> Option.defaultValue []
            let seeded = Map.tryFind node.Id program.IndexSeeds |> Option.defaultValue []
            // Internal callers do not enumerate a retained API's external
            // callers. Their exact inputs remain invocation-context facts;
            // the source formal keeps its open shared domain.
            if program.RootParameters.TryFind node.Id = Some DeclRoot.LibraryExport then Some fallback
            elif program.InactiveFormals.Contains node.Id then Some ValueRange.Empty
            elif List.isEmpty supplied && List.isEmpty seeded then Some fallback
            else
                let fromCalls = supplied |> List.fold (fun acc (callId, a) -> ValueRange.join acc (read program shared callId a)) ValueRange.Empty
                Some (seeded |> List.fold (fun acc (callId, nId) -> ValueRange.join acc (indexBelow (read program shared callId nId))) fromCalls)
        | SemanticKind.PatternBinding _ ->
            match List.tryLast node.Children with
            | Some valueId -> Some (get valueId)
            | None -> Some fallback
        | SemanticKind.Binding (_, isMutable, _, _) ->
            let value =
                match List.tryLast node.Children with
                | Some valueId -> get valueId
                | None -> fallback
            if isMutable then
                Map.tryFind node.Id program.Assignments
                |> Option.defaultValue []
                |> List.fold (fun acc a -> ValueRange.join acc (get a)) value
                |> Some
            else Some value
        | SemanticKind.Sequential ids ->
            match List.tryLast ids with
            | Some lastId -> Some (get lastId)
            | None -> Some fallback
        | SemanticKind.IfThenElse (guard, t, e) ->
            let yes = if guardFeasible program value guard true then get t else ValueRange.Empty
            let no = if guardFeasible program value guard false then e |> Option.map get |> Option.defaultValue ValueRange.Empty else ValueRange.Empty
            Some (ValueRange.join yes no)
        | SemanticKind.Match (_, cases) ->
            Some (cases |> List.fold (fun acc c -> ValueRange.join acc (get c.Body)) ValueRange.Empty)
        | SemanticKind.CaseElimination (_, arms) ->
            Some (arms |> List.fold (fun acc a -> ValueRange.join acc (get a.Body)) ValueRange.Empty)
        | SemanticKind.ContinuationDispatch (_, cases, otherwise) ->
            Some (cases |> List.fold (fun range (_, body) -> ValueRange.join range (get body)) (get otherwise))
        | SemanticKind.TypeAnnotation (inner, _)
        | SemanticKind.EagerExpr inner
        | SemanticKind.Upcast (inner, _)
        | SemanticKind.Downcast (inner, _) -> Some (get inner)
        | SemanticKind.FieldGet (exprId, field) ->
            match Map.tryFind exprId program.Reachable with
            | Some { Type = NativeType.TApp (tycon, _) } when Map.containsKey (NominalTypeIdentity.ofConstructor tycon) program.Constructions || Map.containsKey (NominalTypeIdentity.ofConstructor tycon) program.InputSeeds ->
                Some (fieldRange program shared (NominalTypeIdentity.ofConstructor tycon) field)
            // A read of a field of a record type nothing reachable constructs and nothing declares
            // came from a source the pass did not see: unobservable (CCS8011), never a fabricated width.
            // (`Empty` remains right for FieldRanges of a field nothing reads.)
            | _ -> Some fallback
        | SemanticKind.TupleGet (tupleId, index) -> Some (aggregateElement program shared Set.empty tupleId [TupleSlot index])
        | SemanticKind.DUEliminate (value, tag, name, _) when isRanged node ->
            Some (aggregateElement program shared Set.empty value [UnionPayload(tag, name)])
        | SemanticKind.IndexGet (exprId, _) ->
            match Map.tryFind exprId program.Reachable |> Option.map (fun n -> n.Type) |> Option.bind arrayElementType with
            | Some elem -> Some (elementRange program shared elem)
            | None -> Some fallback
        | _ -> Some fallback
    let computed =
        match computed, program.LoopAccumulations.TryFind node.Id with
        | Some range, Some recurrence ->
            match LoopRecipes.saturate shared recurrence with
            | Result.Ok result -> Some(ValueRange.meet range (ValueRange.Bounded(result.Invariant.Lower, result.Invariant.Upper)))
            | Result.Error _ -> Some range
        | _ -> computed
    let computed =
        match computed, program.SequenceAccumulationTargets.TryFind node.Id with
        | Some range, Some recurrence ->
            match SequenceAccumulation.saturate shared recurrence with
            | Some invariant -> Some(ValueRange.meet range (ValueRange.Bounded(invariant.Lower, invariant.Upper)))
            | None -> Some range
        | _ -> computed
    let computed =
        match computed, program.LoopLinear.TryFind node.Id with
        | Some range, Some(recurrence, index) ->
            match LoopRecipes.saturateLinear shared recurrence with
            | Result.Ok result ->
                Some(ValueRange.meet range (ValueRange.Bounded(result.Invariant.Lower[index], result.Invariant.Upper[index])))
            | Result.Error _ -> Some range
        | _ -> computed
    let computed =
        match computed, program.TailRecurrences.TryFind node.Id with
        | Some range, Some recurrence ->
            match LoopRecipes.saturateTail shared recurrence with
            | Result.Ok result -> Some(ValueRange.meet range result.Ranges[node.Id])
            | Result.Error _ -> Some range
        | _ -> computed
    match computed with
    | Some range when program.FiniteCells.ContainsKey node.Id ->
        Some(ValueRange.meet range (FiniteCellRanges.range program.FiniteCells[node.Id]))
    | Some range when program.LazyEffects.ContainsKey node.Id ->
        let bound = program.LazyEffects[node.Id]
        Some(ValueRange.meet range (ValueRange.Bounded(bound.Lower, bound.Upper)))
    | Some r when isIntegerNode node && isSource program node -> Some (boundByCarrier program node r)
    | other -> other

/// Contextual facts admit scalar transfers explicitly. Storage, recurrence and
/// unfamiliar source kinds remain observations of the shared owning analysis.
let private contextualNode (program: Program) (node: SemanticNode) =
    let sharedOwner =
        program.ArrayLengths.ContainsKey node.Id || program.BoundarySeeds.ContainsKey node.Id ||
        program.LazyResults.ContainsKey node.Id || program.LoopAccumulations.ContainsKey node.Id ||
        program.LoopLinear.ContainsKey node.Id || program.TailRecurrences.ContainsKey node.Id || program.SequenceAccumulationTargets.ContainsKey node.Id ||
        program.FiniteCells.ContainsKey node.Id || program.LazyEffects.ContainsKey node.Id
    if sharedOwner || not (isRanged node) then false
    else
        match node.Kind with
        | SemanticKind.Literal (NativeLiteral.Int _ | NativeLiteral.UInt _ | NativeLiteral.Bool _ | NativeLiteral.Char _)
        | SemanticKind.VarRef _ | SemanticKind.PatternBinding _
        | SemanticKind.Binding (_, false, _, _) | SemanticKind.Sequential _
        | SemanticKind.IfThenElse _ | SemanticKind.Match _ | SemanticKind.CaseElimination _
        | SemanticKind.TypeAnnotation _ | SemanticKind.EagerExpr _
        | SemanticKind.Upcast _ | SemanticKind.Downcast _ -> true
        | SemanticKind.Application _ when program.Applications.ContainsKey node.Id -> true
        | SemanticKind.Application _ ->
            match program.Callees.TryFind node.Id with
            | Some(Callee.Intrinsic info, arguments) ->
                let arguments = arguments |> List.map (fun id ->
                    match program.Reachable.TryFind id with
                    | Some node ->
                        { RangeSources.Argument.Range = ValueRange.Unbounded
                          RangeSources.Argument.Type = node.Type
                          RangeSources.Argument.Literal = match node.Kind with SemanticKind.Literal literal -> Some literal | _ -> None }
                    | None ->
                        { RangeSources.Argument.Range = ValueRange.Unbounded
                          RangeSources.Argument.Type = NativeType.TError "unreachable"
                          RangeSources.Argument.Literal = None })
                match RangeSources.contextualIntrinsic program.Context info arguments with
                | RangeSources.Result.Fact _ -> true
                | _ -> false
            | _ -> false
        | _ -> false

/// The reachable occurrences inside each lexical body, read only from nodes this
/// graph revision holds. A body, or a child a retained occurrence still lists,
/// that is absent from the graph is refused with its exact identity: range facts
/// are never read through a lookup that throws on a removed node (clef #120).
let private lexicalBodies (program: Program) (roots: NodeId list) : Result<Map<NodeId, Set<NodeId>>, NodeId * string> =
    let absent parent id =
        match parent with
        | Some parent ->
            parent, sprintf "RangeAnalysis: occurrence %d lists child %d, which is absent from the graph; source settlement is required before range facts are read." (NodeId.value parent) (NodeId.value id)
        | None ->
            id, sprintf "RangeAnalysis: lexical body %d is absent from the graph; source settlement is required before range facts are read." (NodeId.value id)
    let bodyOccurrences root =
        let rec walk state (parent, id) =
            match state with
            | Result.Error _ -> state
            | Result.Ok (visited, _) when Set.contains id visited -> state
            | Result.Ok (visited, members) ->
                match program.Graph.Nodes.TryFind id with
                | None -> Result.Error(absent parent id)
                | Some node ->
                    let visited = Set.add id visited
                    let members = if program.Reachable.ContainsKey id then Set.add id members else members
                    // Reachability is not downward closed: an inactive retained
                    // wrapper may contain an independently reachable occurrence.
                    match node.Kind with
                    | SemanticKind.Lambda _ -> Result.Ok(visited, members)
                    | _ -> node.Children |> List.fold (fun state child -> walk state (Some id, child)) (Result.Ok(visited, members))
        walk (Result.Ok(Set.empty, Set.empty)) (None, root) |> Result.map snd
    roots |> List.fold (fun bodies root ->
        bodies |> Result.bind (fun (bodies: Map<NodeId, Set<NodeId>>) ->
            if bodies.ContainsKey root then Result.Ok bodies
            else bodyOccurrences root |> Result.map (fun members -> bodies.Add(root, members)))) (Result.Ok Map.empty)

/// A lexical body supplies occurrence context, never proof of activation or a
/// dependency region. CallableOrigins supplies invocation rows, and every fact
/// retains its actual reads. Nested lambda definitions do not activate bodies.
let private contextProgramOf (program: Program) (applications: Map<NodeId, CallableOrigins.CallTarget list>) (targets: CallableOrigins.CallTarget list) (lexical: Map<NodeId, Set<NodeId>>) =
    let fullParameters (target: CallableOrigins.CallTarget) =
        match program.Reachable.TryFind target.Lambda with
        | Some { Kind = SemanticKind.Lambda (parameters, _, _, _, _) } -> parameters |> List.map (fun (_, _, id) -> id)
        | _ -> target.Parameters |> List.map (fun (_, _, id) -> id)
    let bodies = targets |> List.map (fun target ->
        target.Lambda, Set.union lexical[target.Body] (fullParameters target |> Set.ofList)) |> Map.ofList
    let owned = bodies.Values |> Seq.fold Set.union Set.empty
    let rootMembers = Set.difference (program.Reachable.Keys |> Set.ofSeq) owned
    // Intrinsic-owned suppliers and declared ingress remain shared sources.
    // They do not acquire invented ordinary argument correspondence.
    let rootMembers = targets |> List.fold (fun members target ->
        let hasOtherIngress = fullParameters target |> List.exists (fun parameter ->
            program.RootParameters.ContainsKey parameter || program.IndexSeeds.ContainsKey parameter ||
            (program.CallArguments.TryFind parameter |> Option.defaultValue []
             |> List.exists (fun (call, _) -> not (program.Applications.ContainsKey call))))
        if hasOtherIngress then Set.union members bodies[target.Lambda] else members) rootMembers
    let root = RangeContext.Invocation []
    let childContext parent call =
        let sites = match parent with RangeContext.Invocation sites -> sites | RangeContext.Shared -> []
        let sites = sites @ [call]
        RangeContext.Invocation (sites |> List.skip (max 0 (sites.Length - InvocationContextDepth)))
    let callSites = applications.Keys |> Set.ofSeq
    let callsByTarget = bodies |> Map.map (fun _ bodyNodes -> Set.intersect bodyNodes callSites)
    let appTargetsWithArgs =
        applications |> Map.map (fun _ appTargets ->
            appTargets |> List.map (fun target ->
                target, List.zip (target.Parameters |> List.map (fun (_, _, id) -> id)) target.Arguments))
    let targetsInContext = System.Collections.Generic.Dictionary<RangeContext, System.Collections.Generic.HashSet<NodeId>>()
    let expandedCallsInContext = System.Collections.Generic.Dictionary<RangeContext, System.Collections.Generic.HashSet<NodeId>>()
    let allContexts = System.Collections.Generic.HashSet<RangeContext>()
    allContexts.Add(root) |> ignore
    let rootCalls = Set.intersect rootMembers callSites
    expandedCallsInContext[root] <- System.Collections.Generic.HashSet<NodeId>(rootCalls)
    let queue = System.Collections.Generic.Queue<RangeContext * NodeId list>()
    if not rootCalls.IsEmpty then
        queue.Enqueue(root, Set.toList rootCalls)
    let rowsAcc = ResizeArray<RangeInvocationRow>()
    while queue.Count > 0 do
        let parent, callsToExpand = queue.Dequeue()
        for call in callsToExpand do
            match appTargetsWithArgs.TryFind call with
            | None -> ()
            | Some targetRows ->
                let ctx = childContext parent call
                allContexts.Add(ctx) |> ignore
                for (target, zippedArgs) in targetRows do
                    rowsAcc.Add(
                        { RangeInvocationRow.Context = ctx
                          Caller = parent
                          Call = call
                          Target = target.Lambda
                          Body = target.Body
                          Arguments = zippedArgs })
                    let tSet =
                        match targetsInContext.TryGetValue(ctx) with
                        | true, s -> s
                        | false, _ ->
                            let s = System.Collections.Generic.HashSet<NodeId>()
                            targetsInContext[ctx] <- s
                            s
                    if tSet.Add(target.Lambda) then
                        let cSet =
                            match expandedCallsInContext.TryGetValue(ctx) with
                            | true, s -> s
                            | false, _ ->
                                let s = System.Collections.Generic.HashSet<NodeId>()
                                expandedCallsInContext[ctx] <- s
                                s
                        let newCalls =
                            [ for c in callsByTarget[target.Lambda] do
                                  if cSet.Add(c) then yield c ]
                        if not newCalls.IsEmpty then
                            queue.Enqueue(ctx, newCalls)
    let rows = rowsAcc |> Set.ofSeq |> Set.toList
    let parameters =
        rows |> List.collect (fun row ->
            row.Arguments |> List.map (fun (formal, actual) -> (row.Context, formal), (row.Caller, row.Call, actual)))
        |> List.groupBy fst |> List.map (fun (key, inputs) -> key, inputs |> List.map snd |> List.distinct) |> Map.ofList
    let contextualNodes =
        program.Ordered
        |> List.choose (fun n -> if contextualNode program n then Some n.Id else None)
        |> Set.ofList
    let contextualParams = Set.intersect contextualNodes program.Parameters
    let targetContextualAll = bodies |> Map.map (fun _ b -> Set.intersect b contextualNodes)
    let targetContextualNonParam = targetContextualAll |> Map.map (fun _ b -> Set.difference b contextualParams)
    let targetContextualParam = targetContextualAll |> Map.map (fun _ b -> Set.intersect b contextualParams)
    let rootContextualAll = Set.intersect rootMembers contextualNodes
    let rootContextualNonParam = Set.difference rootContextualAll contextualParams
    let rootContextualParam = Set.intersect rootContextualAll contextualParams
    let members =
        [ for context in allContexts do
              let baseSet =
                  if context = root then
                      let activeRootParams = rootContextualParam |> Set.filter (fun id -> parameters.ContainsKey (context, id))
                      Set.union rootContextualNonParam activeRootParams
                  else Set.empty
              let ctxMembers =
                  match targetsInContext.TryGetValue(context) with
                  | false, _ -> baseSet
                  | true, tSet ->
                      let mutable acc = baseSet
                      for targetLambda in tSet do
                          let tParams = targetContextualParam[targetLambda]
                          let tSetForCtx =
                              if tParams |> Set.forall (fun id -> parameters.ContainsKey (context, id)) then
                                  targetContextualAll[targetLambda]
                              else
                                  Set.union targetContextualNonParam[targetLambda] (tParams |> Set.filter (fun id -> parameters.ContainsKey (context, id)))
                          acc <- if acc.IsEmpty then tSetForCtx else Set.union acc tSetForCtx
                      acc
              yield context, ctxMembers ]
        |> Map.ofList
    let occurrences = members |> Map.toList |> List.collect (fun (context, nodes) -> nodes |> Set.toList |> List.map (fun id -> id, context))
                      |> List.groupBy fst |> List.map (fun (id, entries) -> id, entries |> List.map snd) |> Map.ofList
    let isCoordinateNode (node: SemanticNode) =
        isRanged node ||
        (match node.Kind with
         | SemanticKind.UnionCase _ | SemanticKind.DUConstruct _ | SemanticKind.DUGetTag _ -> true
         | _ -> false)
    let coordinates =
        (program.Ordered |> List.choose (fun node -> if isCoordinateNode node then Some(RangeContext.Shared, node) else None)) @
        (members |> Map.toList |> List.collect (fun (context, nodes) ->
            nodes |> Set.toList |> List.map (fun id -> context, program.Reachable[id])))
    { Invocations = rows; Members = members; Parameters = parameters
      Calls = rows |> List.groupBy (fun row -> row.Caller, row.Call) |> Map.ofList
      Occurrences = occurrences; Coordinates = coordinates }

let private contextProgram (program: Program) : Result<ContextProgram, NodeId * string> =
    // External execution has no source body activation. Its application stays
    // in the caller's lexical region, where the result contract reads actuals.
    let applications = program.Applications |> Map.map (fun _ targets ->
        targets |> List.filter (fun target -> not (program.ForeignEffectBodies.Contains target.Body)))
    let targets = applications.Values |> Seq.collect id |> Seq.distinctBy _.Lambda |> Seq.toList
    lexicalBodies program (targets |> List.map _.Body)
    |> Result.map (contextProgramOf program applications targets)

let private contextReading (contexts: ContextProgram) get context id =
    if context <> RangeContext.Shared &&
       (contexts.Members.TryFind context |> Option.exists (Set.contains id)) then get (context, id)
    else get (RangeContext.Shared, id)

/// Every transfer reads already-issued state cells. No reader calls transfer;
/// context cycles therefore have the same convergence owner as shared facts.
let private evaluate (program: Program) (contexts: ContextProgram) (state: ContextState) context (node: SemanticNode) =
    let mutable reads = Set.empty
    let get key =
        reads <- Set.add key reads
        state.Values.TryFind key |> Option.defaultValue ValueRange.Empty
    let shared id = get (RangeContext.Shared, id)
    let reading context id = contextReading contexts get context id
    let application context call =
        contexts.Calls.TryFind (context, call) |> Option.map (fun rows ->
            rows |> List.fold (fun range row -> ValueRange.join range (reading row.Context row.Body)) ValueRange.Empty)
    let computed =
        match context with
        | RangeContext.Shared when program.Applications.ContainsKey node.Id ->
            match contexts.Occurrences.TryFind node.Id with
            | Some occurrences -> Some(occurrences |> List.fold (fun range context -> ValueRange.join range (get (context, node.Id))) ValueRange.Empty)
            | None -> transfer program shared shared (application context) node
        | RangeContext.Shared -> transfer program shared shared (application context) node
        | _ ->
            if not (occurrenceFeasible program (reading context) node.Id) then Some ValueRange.Empty
            else
                match contexts.Parameters.TryFind (context, node.Id) with
                | Some inputs ->
                    inputs |> List.fold (fun range (caller, call, actual) ->
                        if occurrenceFeasible program (reading caller) call then
                            ValueRange.join range (read program (reading caller) call actual)
                        else range) ValueRange.Empty |> Some
                | None -> transfer program shared (reading context) (application context) node
    computed, reads

//-------------------------------------------------------------------------
// The fixpoint
//-------------------------------------------------------------------------

/// Rounds of plain ascent before the widening operator engages.
let [<Literal>] private WideningDelay = 8

/// Rounds of narrowing after the ascent has settled.
let [<Literal>] private NarrowingRounds = 8

/// The most rounds an ascent may take; past it the pass has a defect, and says so. A widening
/// steps through the thresholds, so a genuinely unbounded value takes a few rounds per constant
/// the program has; this is a stop for a defect, not a figure of the design.
let [<Literal>] private AscentLimit = 8192

type private ElementReadPlan =
    | ElemConst of ValueRange
    | ElemStores of init: ValueRange * unrefinedKeys: int[] * refinedPairs: struct(NodeId * NodeId)[]

type private IntrinsicArgPlan =
    struct
        val NodeId: NodeId
        val IsRanged: bool
        val Type: NativeType
        val Literal: NativeLiteral option
        val ElemPlan: ElementReadPlan voption
        new(nodeId, isRanged, ty, lit, elemPlan) =
            { NodeId = nodeId; IsRanged = isRanged; Type = ty; Literal = lit; ElemPlan = elemPlan }
    end

[<RequireQualifiedAccess>]
type private NodeTransferPlan =
    | Unset
    | NotRanged
    | Constant of ValueRange
    | SingleRead of operand: NodeId * carrier: ValueRange voption
    | Parameter of unrefinedKeys: int[] * refinedSupplied: struct(NodeId * NodeId)[] * seeded: struct(NodeId * NodeId)[] * carrier: ValueRange voption
    | MutableBinding of initId: NodeId voption * fallback: ValueRange * assignments: NodeId[] * carrier: ValueRange voption
    | IfThenElse of t: NodeId * e: NodeId voption * trueOk: bool * trueAtoms: (Compared * Refinement)[] * falseOk: bool * falseAtoms: (Compared * Refinement)[]
    | BranchJoin of bodies: NodeId[]
    | SharedStores of init: ValueRange * unrefinedKeys: int[] * refinedPairs: struct(NodeId * NodeId)[] * carrier: ValueRange voption
    | SharedLeaves of init: ValueRange * leafKeys: int[] * carrier: ValueRange voption
    | ContextualApp of fallback: ValueRange * carrier: ValueRange voption
    | DirectApp of bodyKeyId: int
    | IntrinsicApp of info: IntrinsicInfo * args: IntrinsicArgPlan[] * fallback: ValueRange * carrier: ValueRange voption
    | General of node: SemanticNode

let private fixpoint (program: Program) (contexts: ContextProgram) : State * RangeContextFacts =
    let ctxToId = System.Collections.Generic.Dictionary<RangeContext, int>()
    let idToCtxList = ResizeArray<RangeContext>()
    let getOrAddCtx (ctx: RangeContext) =
        match ctxToId.TryGetValue(ctx) with
        | true, id -> id
        | false, _ ->
            let id = idToCtxList.Count
            ctxToId[ctx] <- id
            idToCtxList.Add(ctx)
            id
    let _ = getOrAddCtx RangeContext.Shared
    for kvp in contexts.Members do getOrAddCtx kvp.Key |> ignore
    for (ctx, _) in contexts.Coordinates do getOrAddCtx ctx |> ignore
    for row in contexts.Invocations do
        getOrAddCtx row.Context |> ignore
        getOrAddCtx row.Caller |> ignore
    for kvp in contexts.Calls do
        getOrAddCtx (fst kvp.Key) |> ignore
        for row in kvp.Value do getOrAddCtx row.Context |> ignore
    for kvp in contexts.Parameters do
        getOrAddCtx (fst kvp.Key) |> ignore
        for (caller, _, _) in kvp.Value do getOrAddCtx caller |> ignore
    for kvp in contexts.Occurrences do
        for ctx in kvp.Value do getOrAddCtx ctx |> ignore
    let idToCtx = idToCtxList.ToArray()
    let mutable maxNodeVal = Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.maxNodeId program.Graph
    let inline observeNode (NodeId n) =
        if n > maxNodeVal then maxNodeVal <- n
    for (_, node) in contexts.Coordinates do observeNode node.Id
    for kvp in contexts.Members do
        for id in kvp.Value do observeNode id
    for kvp in contexts.Calls do
        observeNode (snd kvp.Key)
        for row in kvp.Value do observeNode row.Body
    for kvp in contexts.Parameters do
        observeNode (snd kvp.Key)
        for (_, call, actual) in kvp.Value do
            observeNode call
            observeNode actual
    for kvp in contexts.Occurrences do observeNode kvp.Key
    let sharedKeyByNode = Array.create (max 0 maxNodeVal + 1) -1
    let sharedOverflow = System.Collections.Generic.Dictionary<NodeId, int>()
    let ctxKeyDict = System.Collections.Generic.Dictionary<int64, int>(contexts.Coordinates.Length + 16)
    let keyToPairList = ResizeArray<RangeContext * NodeId>(contexts.Coordinates.Length + program.Graph.Nodes.Count + 16)
    let keyToSharedNodeList = ResizeArray<NodeId voption>(contexts.Coordinates.Length + program.Graph.Nodes.Count + 16)
    let inline packRaw (ctxId: int) (NodeId nodeId) : int64 =
        (int64 ctxId <<< 32) ||| int64 (uint32 nodeId)
    let getOrAddSharedKey (NodeId n as nodeId) : int =
        if n >= 0 && n < sharedKeyByNode.Length then
            let k = sharedKeyByNode.[n]
            if k >= 0 then k
            else
                let newKey = keyToPairList.Count
                sharedKeyByNode.[n] <- newKey
                keyToPairList.Add(RangeContext.Shared, nodeId)
                keyToSharedNodeList.Add(ValueSome nodeId)
                newKey
        else
            match sharedOverflow.TryGetValue(nodeId) with
            | true, k -> k
            | false, _ ->
                let newKey = keyToPairList.Count
                sharedOverflow[nodeId] <- newKey
                keyToPairList.Add(RangeContext.Shared, nodeId)
                keyToSharedNodeList.Add(ValueSome nodeId)
                newKey
    let getOrAddKey (ctxId: int) (nodeId: NodeId) : int =
        if ctxId = 0 then getOrAddSharedKey nodeId
        else
            let raw = packRaw ctxId nodeId
            match ctxKeyDict.TryGetValue(raw) with
            | true, k -> k
            | false, _ ->
                let newKey = keyToPairList.Count
                ctxKeyDict[raw] <- newKey
                keyToPairList.Add(idToCtx.[ctxId], nodeId)
                keyToSharedNodeList.Add(ValueNone)
                newKey
    for nodeId in program.Graph.Nodes.Keys do
        getOrAddSharedKey nodeId |> ignore
    for edge in program.Graph.Edges do
        getOrAddSharedKey edge.Target |> ignore
        for s in edge.Sources do getOrAddSharedKey s |> ignore
    let nodeArraySize = max 0 maxNodeVal + 1
    let isContextualNode : bool[] = Array.create nodeArraySize false
    let contextualNodeIndex : int[] = Array.create nodeArraySize -1
    let mutable numContextualNodes = 0
    for kvp in contexts.Occurrences do
        let (NodeId n) = kvp.Key
        if n >= 0 && n < nodeArraySize then
            isContextualNode.[n] <- true
            contextualNodeIndex.[n] <- numContextualNodes
            numContextualNodes <- numContextualNodes + 1
    let useFlatCtxTable = numContextualNodes > 0 && int64 idToCtx.Length * int64 numContextualNodes <= 8_000_000L
    let ctxKeyTable : int[] =
        if useFlatCtxTable then Array.create (idToCtx.Length * numContextualNodes) -1
        else Array.empty
    let memberMapsByCtxId : System.Collections.Generic.Dictionary<int, int> voption[] =
        Array.init idToCtx.Length (fun ctxId ->
            if ctxId = 0 then ValueNone
            else
                match contexts.Members.TryFind idToCtx.[ctxId] with
                | Some s ->
                    if useFlatCtxTable then
                        let rowOffset = ctxId * numContextualNodes
                        for (NodeId n as id) in s do
                            let kId = getOrAddKey ctxId id
                            if n >= 0 && n < nodeArraySize then
                                let cIdx = contextualNodeIndex.[n]
                                if cIdx >= 0 then
                                    ctxKeyTable.[rowOffset + cIdx] <- kId
                        ValueNone
                    else
                        let dict = System.Collections.Generic.Dictionary<int, int>(s.Count)
                        for (NodeId n as id) in s do
                            dict[n] <- getOrAddKey ctxId id
                        ValueSome dict
                | None -> ValueNone)
    let resolveKeyInCtx (cId: int) (NodeId n as id) : int =
        if cId = 0 then getOrAddSharedKey id
        elif useFlatCtxTable && n >= 0 && n < nodeArraySize then
            let cIdx = contextualNodeIndex.[n]
            if cIdx >= 0 then
                let kId = ctxKeyTable.[cId * numContextualNodes + cIdx]
                if kId >= 0 then kId else getOrAddSharedKey id
            else getOrAddSharedKey id
        else
            match memberMapsByCtxId.[cId] with
            | ValueSome memberMap ->
                match memberMap.TryGetValue(n) with
                | true, kId -> kId
                | false, _ -> getOrAddSharedKey id
            | ValueNone -> getOrAddSharedKey id
    let coords =
        contexts.Coordinates
        |> List.map (fun (ctx, node) ->
            let ctxId = getOrAddCtx ctx
            let keyId = getOrAddKey ctxId node.Id
            struct(ctxId, keyId, node))
        |> List.toArray
    let tempCalls = ResizeArray<int * int[]>()
    for kvp in contexts.Calls do
        let callerCtx, callId = kvp.Key
        let callKeyId = getOrAddKey (getOrAddCtx callerCtx) callId
        let rowKeyIds =
            kvp.Value
            |> List.map (fun row -> resolveKeyInCtx (getOrAddCtx row.Context) row.Body)
            |> List.toArray
        tempCalls.Add(callKeyId, rowKeyIds)
    let tempParams = ResizeArray<int * (int * NodeId * NodeId)[]>()
    for kvp in contexts.Parameters do
        let ctx, paramId = kvp.Key
        let paramKeyId = getOrAddKey (getOrAddCtx ctx) paramId
        let rows = kvp.Value |> List.map (fun (caller, call, actual) -> getOrAddCtx caller, call, actual) |> List.toArray
        tempParams.Add(paramKeyId, rows)
    let isApplicationNode : bool[] = Array.create nodeArraySize false
    for appId in program.Applications.Keys do
        let (NodeId n) = appId
        if n >= 0 && n < nodeArraySize then
            isApplicationNode.[n] <- true
    let occurrencesByNodeArr : int[] voption[] = Array.create nodeArraySize ValueNone
    for kvp in contexts.Occurrences do
        let (NodeId n as nodeId) = kvp.Key
        if n >= 0 && n < nodeArraySize then
            occurrencesByNodeArr.[n] <- ValueSome (kvp.Value |> List.map (fun ctx -> getOrAddKey (getOrAddCtx ctx) nodeId) |> List.toArray)
    let numKeys = keyToPairList.Count + 64
    let valuesArr : ValueRange[] = Array.create numKeys ValueRange.Empty
    let hasValueArr : bool[] = Array.create numKeys false
    let callsByKey : int[] voption[] = Array.create numKeys ValueNone
    for (callKeyId, rowKeyIds) in tempCalls do
        callsByKey.[callKeyId] <- ValueSome rowKeyIds
    let paramsByKey : (int * NodeId * NodeId)[] voption[] = Array.create numKeys ValueNone
    for (paramKeyId, rows) in tempParams do
        paramsByKey.[paramKeyId] <- ValueSome rows
    let hasReads : bool[] = Array.create coords.Length false
    let climbLastReads : int[][] = Array.create coords.Length Array.empty
    let descendLastReads : int[][] = Array.create coords.Length Array.empty
    let extraReadsAcc : ResizeArray<int> voption[] = Array.create coords.Length ValueNone
    let lastRecordedDeps : int[] voption[] = Array.create coords.Length ValueNone
    let dependentsOfKey : ResizeArray<int> voption[] = Array.create numKeys ValueNone
    let inline addDependentFirst (depKey: int) (coordIdx: int) =
        match dependentsOfKey.[depKey] with
        | ValueSome list ->
            list.Add(coordIdx)
        | ValueNone ->
            let list = ResizeArray<int>(4)
            list.Add(coordIdx)
            dependentsOfKey.[depKey] <- ValueSome list
    let addDependent (depKey: int) (coordIdx: int) =
        match dependentsOfKey.[depKey] with
        | ValueSome list ->
            let n = list.Count
            if n = 0 || list.[n - 1] < coordIdx then
                list.Add(coordIdx)
            elif list.[n - 1] <> coordIdx then
                let mutable found = false
                let mutable j = 0
                while not found && j < n do
                    if list.[j] = coordIdx then found <- true
                    j <- j + 1
                if not found then list.Add(coordIdx)
        | ValueNone ->
            let list = ResizeArray<int>(4)
            list.Add(coordIdx)
            dependentsOfKey.[depKey] <- ValueSome list
    let addNewDependents (prev: int[]) (currentReads: int[]) (coordIdx: int) =
        let mutable i = 0
        let mutable j = 0
        let nPrev = prev.Length
        let nCur = currentReads.Length
        while j < nCur do
            let curKey = currentReads.[j]
            while i < nPrev && prev.[i] < curKey do
                i <- i + 1
            if i < nPrev && prev.[i] = curKey then
                i <- i + 1
            else
                addDependent curKey coordIdx
            j <- j + 1
    let usedConstSetIds : Set<int>[] = Array.create coords.Length Set.empty
    let constSetArrays = ResizeArray<int[]>()
    let readsBuffer = Array.zeroCreate<int> 1024
    let mutable readCursor = 0
    let readsOverflow = ResizeArray<int>()
    let inline get (kId: int) =
        let idx = readCursor
        if idx < readsBuffer.Length then
            readsBuffer.[idx] <- kId
        else
            readsOverflow.Add(kId)
        readCursor <- idx + 1
        valuesArr.[kId]
    let extractDeps (prevOpt: int[] voption) : struct(int[] * bool) =
        let n = readCursor
        if n = 0 then
            match prevOpt with
            | ValueSome prev when prev.Length = 0 -> struct(prev, false)
            | _ -> struct(Array.empty, true)
        elif n = 1 then
            let k0 = readsBuffer.[0]
            match prevOpt with
            | ValueSome prev when prev.Length = 1 && prev.[0] = k0 -> struct(prev, false)
            | _ -> struct([| k0 |], true)
        elif n = 2 then
            let k0 = readsBuffer.[0]
            let k1 = readsBuffer.[1]
            if k0 = k1 then
                match prevOpt with
                | ValueSome prev when prev.Length = 1 && prev.[0] = k0 -> struct(prev, false)
                | _ -> struct([| k0 |], true)
            else
                let lo = if k0 < k1 then k0 else k1
                let hi = if k0 < k1 then k1 else k0
                match prevOpt with
                | ValueSome prev when prev.Length = 2 && prev.[0] = lo && prev.[1] = hi -> struct(prev, false)
                | _ -> struct([| lo; hi |], true)
        elif n <= readsBuffer.Length then
            if n <= 16 then
                for i = 1 to n - 1 do
                    let key = readsBuffer.[i]
                    let mutable j = i - 1
                    while j >= 0 && readsBuffer.[j] > key do
                        readsBuffer.[j + 1] <- readsBuffer.[j]
                        j <- j - 1
                    readsBuffer.[j + 1] <- key
            else
                System.Array.Sort(readsBuffer, 0, n)
            let mutable uniqueCount = 1
            for i = 1 to n - 1 do
                let v = readsBuffer.[i]
                if v <> readsBuffer.[uniqueCount - 1] then
                    readsBuffer.[uniqueCount] <- v
                    uniqueCount <- uniqueCount + 1
            match prevOpt with
            | ValueSome prev when prev.Length = uniqueCount ->
                let mutable same = true
                let mutable i = 0
                while same && i < uniqueCount do
                    if prev.[i] <> readsBuffer.[i] then same <- false
                    i <- i + 1
                if same then struct(prev, false)
                else
                    let arr = Array.zeroCreate<int> uniqueCount
                    System.Array.Copy(readsBuffer, 0, arr, 0, uniqueCount)
                    struct(arr, true)
            | _ ->
                let arr = Array.zeroCreate<int> uniqueCount
                System.Array.Copy(readsBuffer, 0, arr, 0, uniqueCount)
                struct(arr, true)
        else
            let total = readsBuffer.Length + readsOverflow.Count
            let arr = Array.zeroCreate<int> total
            System.Array.Copy(readsBuffer, 0, arr, 0, readsBuffer.Length)
            readsOverflow.CopyTo(arr, readsBuffer.Length)
            readsOverflow.Clear()
            System.Array.Sort(arr)
            let mutable uniqueCount = 1
            for i = 1 to total - 1 do
                if arr.[i] <> arr.[uniqueCount - 1] then
                    arr.[uniqueCount] <- arr.[i]
                    uniqueCount <- uniqueCount + 1
            let finalArr =
                if uniqueCount = total then arr
                else
                    let trimmed = Array.zeroCreate<int> uniqueCount
                    System.Array.Copy(arr, 0, trimmed, 0, uniqueCount)
                    trimmed
            match prevOpt with
            | ValueSome prev when prev.Length = finalArr.Length ->
                let mutable same = true
                let mutable i = 0
                while same && i < finalArr.Length do
                    if prev.[i] <> finalArr.[i] then same <- false
                    i <- i + 1
                if same then struct(prev, false) else struct(finalArr, true)
            | _ -> struct(finalArr, true)
    let shared (NodeId n as id) =
        if n >= 0 && n < nodeArraySize then
            let k = sharedKeyByNode.[n]
            if k >= 0 then get k else get (getOrAddSharedKey id)
        else get (getOrAddSharedKey id)
    let inline readInCtx (ctxId: int) (NodeId n as id) : ValueRange =
        if ctxId = 0 then
            if n >= 0 && n < nodeArraySize then
                let k = sharedKeyByNode.[n]
                if k >= 0 then get k else get (getOrAddSharedKey id)
            else get (getOrAddSharedKey id)
        elif n >= 0 && n < nodeArraySize then
            let cIdx = contextualNodeIndex.[n]
            if cIdx < 0 then
                let k = sharedKeyByNode.[n]
                if k >= 0 then get k else get (getOrAddSharedKey id)
            elif useFlatCtxTable then
                let kId = ctxKeyTable.[ctxId * numContextualNodes + cIdx]
                if kId >= 0 then get kId
                else
                    let k = sharedKeyByNode.[n]
                    if k >= 0 then get k else get (getOrAddSharedKey id)
            else
                match memberMapsByCtxId.[ctxId] with
                | ValueSome memberMap ->
                    match memberMap.TryGetValue(n) with
                    | true, kId -> get kId
                    | false, _ ->
                        let k = sharedKeyByNode.[n]
                        if k >= 0 then get k else get (getOrAddSharedKey id)
                | ValueNone ->
                    let k = sharedKeyByNode.[n]
                    if k >= 0 then get k else get (getOrAddSharedKey id)
        else
            match memberMapsByCtxId.[ctxId] with
            | ValueSome memberMap ->
                match memberMap.TryGetValue(n) with
                | true, kId -> get kId
                | false, _ -> get (getOrAddSharedKey id)
            | ValueNone -> get (getOrAddSharedKey id)
    let readingByCtxId : (NodeId -> ValueRange)[] =
        Array.init idToCtx.Length (fun cId ->
            if cId = 0 then shared
            else
                fun id -> readInCtx cId id)
    let applicationByCtxId : (NodeId -> ValueRange option)[] =
        Array.init idToCtx.Length (fun cId ->
            fun (call: NodeId) ->
                let callKeyId = getOrAddKey cId call
                match callsByKey.[callKeyId] with
                | ValueSome rowKeyIds ->
                    let mutable range = ValueRange.Empty
                    for i = 0 to rowKeyIds.Length - 1 do
                        range <- ValueRange.join range (get rowKeyIds.[i])
                    Some range
                | ValueNone -> None)
    let refinementsByConsumer : struct(NodeId * Refinement[])[] voption[] = Array.create nodeArraySize ValueNone
    for kvp in program.Refinements do
        let (NodeId c) = kvp.Key
        if c >= 0 && c < nodeArraySize && not kvp.Value.IsEmpty then
            let arr =
                kvp.Value
                |> Seq.map (fun inner -> struct(inner.Key, List.toArray inner.Value))
                |> Seq.toArray
            refinementsByConsumer.[c] <- ValueSome arr
    let inline currentBoundCtx (ctxId: int) (bound: Bound) : ValueRange =
        match bound with
        | Bound.Of id -> readInCtx ctxId id
        | Bound.Diff (a, b) -> ValueRange.sub (readInCtx ctxId a) (readInCtx ctxId b)
        | Bound.Sum (a, b) -> ValueRange.add (readInCtx ctxId a) (readInCtx ctxId b)
    let inline readFastCtx (ctxId: int) (NodeId c as consumer) (operand: NodeId) : ValueRange =
        let initial = readInCtx ctxId operand
        if c >= 0 && c < nodeArraySize then
            match refinementsByConsumer.[c] with
            | ValueNone -> initial
            | ValueSome arr ->
                let mutable acc = initial
                for i = 0 to arr.Length - 1 do
                    let struct(opId, refs) = arr.[i]
                    if opId = operand then
                        for j = 0 to refs.Length - 1 do
                            let x = refs.[j]
                            acc <- refine acc x.Relation (currentBoundCtx ctxId x.Bound)
                acc
        else
            read program readingByCtxId.[ctxId] consumer operand
    let guardAtomsByNode : (Compared * Refinement)[] voption[] = Array.create nodeArraySize ValueNone
    for kvp in program.GuardRefinements do
        let (NodeId n) = kvp.Key
        if n >= 0 && n < nodeArraySize && not kvp.Value.IsEmpty then
            guardAtomsByNode.[n] <- ValueSome (List.toArray kvp.Value)
    let inline feasibleAtomsArrCtx (ctxId: int) (bounds: (Compared * Refinement)[]) =
        let mutable ok = true
        let mutable i = 0
        while ok && i < bounds.Length do
            let (compared, refinement) = bounds.[i]
            let id = match compared with Compared.Definition id | Compared.Node id -> id
            if refine (readInCtx ctxId id) refinement.Relation (currentBoundCtx ctxId refinement.Bound) = ValueRange.Empty then
                ok <- false
            i <- i + 1
        ok
    let inline occurrenceFeasibleFastCtx (ctxId: int) (NodeId n as id) =
        if n >= 0 && n < nodeArraySize then
            match guardAtomsByNode.[n] with
            | ValueNone -> true
            | ValueSome bounds -> feasibleAtomsArrCtx ctxId bounds
        else occurrenceFeasible program readingByCtxId.[ctxId] id
    let inline applyCarrier (carrier: ValueRange voption) (r: ValueRange) : ValueRange =
        match carrier with
        | ValueNone -> r
        | ValueSome declared -> if ValueRange.isObservable r then r else declared
    let hasRefinementOn (NodeId c) (operand: NodeId) =
        if c >= 0 && c < nodeArraySize then
            match refinementsByConsumer.[c] with
            | ValueNone -> false
            | ValueSome arr ->
                let mutable found = false
                for i = 0 to arr.Length - 1 do
                    let struct(opId, _) = arr.[i]
                    if opId = operand then found <- true
                found
        else
            program.Refinements.TryFind(NodeId c) |> Option.exists (fun m -> m.ContainsKey operand)
    let splitSharedPairs (pairs: (NodeId * NodeId) list) : int[] * struct(NodeId * NodeId)[] =
        let unrefined = ResizeArray<int>()
        let refined = ResizeArray<struct(NodeId * NodeId)>()
        for (c, op) in pairs do
            if hasRefinementOn c op then
                refined.Add(struct(c, op))
            else
                unrefined.Add(getOrAddSharedKey op)
        let uArr = unrefined.ToArray()
        if uArr.Length > 1 then
            System.Array.Sort(uArr)
            let mutable uCount = 1
            for i = 1 to uArr.Length - 1 do
                if uArr.[i] <> uArr.[uCount - 1] then
                    uArr.[uCount] <- uArr.[i]
                    uCount <- uCount + 1
            if uCount = uArr.Length then uArr, refined.ToArray()
            else
                let trimmed = Array.zeroCreate<int> uCount
                System.Array.Copy(uArr, 0, trimmed, 0, uCount)
                trimmed, refined.ToArray()
        else
            uArr, refined.ToArray()
    let elemPlanCache = System.Collections.Generic.Dictionary<TypeIdentity, ElementReadPlan>()
    let fieldPlanCache = System.Collections.Generic.Dictionary<NominalTypeIdentity * string, ValueRange * int[] * struct(NodeId * NodeId)[]>()
    let buildElementReadPlan (elem: NativeType) : ElementReadPlan =
        match Types.tryGetNTUKind elem |> Option.bind (RangeSources.declaredRangeOfKind program.Context) with
        | Some declared -> ElemConst declared
        | None ->
            let key = elementKey elem
            match elemPlanCache.TryGetValue(key) with
            | true, cached -> cached
            | false, _ ->
                let stores = Map.tryFind key program.ElementStores |> Option.defaultValue []
                let seed = Map.tryFind key program.ElementSeeds
                let plan =
                    match stores, seed with
                    | [], None -> ElemConst ValueRange.Unbounded
                    | _ ->
                        let uKeys, rPairs = splitSharedPairs stores
                        ElemStores (seed |> Option.defaultValue ValueRange.Empty, uKeys, rPairs)
                elemPlanCache[key] <- plan
                plan
    let buildNodePlan (node: SemanticNode) : NodeTransferPlan =
        let nodeId = node.Id
        let hasSpecialOwner =
            program.ArrayLengths.ContainsKey nodeId ||
            program.ForeignBodies.Contains nodeId ||
            program.BoundarySeeds.ContainsKey nodeId ||
            program.LazyResults.ContainsKey nodeId ||
            program.LoopAccumulations.ContainsKey nodeId ||
            program.SequenceAccumulationTargets.ContainsKey nodeId ||
            program.LoopLinear.ContainsKey nodeId ||
            program.TailRecurrences.ContainsKey nodeId ||
            program.FiniteCells.ContainsKey nodeId ||
            program.LazyEffects.ContainsKey nodeId
        if hasSpecialOwner then
            NodeTransferPlan.General node
        else
            match node.Kind with
            | SemanticKind.UnionCase (_, caseIndex, _)
            | SemanticKind.DUConstruct (_, caseIndex, _, _) ->
                NodeTransferPlan.Constant (ValueRange.point (bigint caseIndex))
            | SemanticKind.DUGetTag (_, duType) ->
                let cases =
                    match duType with
                    | NativeType.TUnion (_, cases) -> List.length cases
                    | NativeType.TApp (tycon, _) -> tycon.CaseCount
                    | _ -> 0
                NodeTransferPlan.Constant (ValueRange.Bounded (bigint.Zero, bigint (max 0 (cases - 1))))
            | _ when not (isRanged node) ->
                NodeTransferPlan.NotRanged
            | _ ->
                let fallback =
                    if isBoolNode node then ValueRange.boolean
                    elif isCharNode node then ValueRange.codePoint
                    else ValueRange.Unbounded
                let carrier =
                    if isIntegerNode node && isSource program node then
                        match Types.tryGetNTUKind node.Type |> Option.bind (RangeSources.declaredRangeOfKind program.Context) with
                        | Some declared -> ValueSome declared
                        | None -> ValueNone
                    else ValueNone
                match node.Kind with
                | SemanticKind.Literal (NativeLiteral.Int (v, _)) ->
                    NodeTransferPlan.Constant (applyCarrier carrier (ValueRange.point (bigint v)))
                | SemanticKind.Literal (NativeLiteral.UInt (v, _)) ->
                    NodeTransferPlan.Constant (applyCarrier carrier (ValueRange.point (bigint v)))
                | SemanticKind.Literal (NativeLiteral.Bool _) ->
                    NodeTransferPlan.Constant (applyCarrier carrier ValueRange.boolean)
                | SemanticKind.Literal (NativeLiteral.Char c) ->
                    NodeTransferPlan.Constant (applyCarrier carrier (ValueRange.point (bigint (int c))))
                | SemanticKind.Literal _ ->
                    NodeTransferPlan.Constant (applyCarrier carrier fallback)
                | SemanticKind.VarRef (_, Some defId)
                | SemanticKind.TypeAnnotation (defId, _)
                | SemanticKind.EagerExpr defId
                | SemanticKind.Upcast (defId, _)
                | SemanticKind.Downcast (defId, _) ->
                    NodeTransferPlan.SingleRead (defId, carrier)
                | SemanticKind.VarRef (_, None) ->
                    NodeTransferPlan.Constant (applyCarrier carrier fallback)
                | SemanticKind.PatternBinding _ when Set.contains nodeId program.Parameters ->
                    let supplied = Map.tryFind nodeId program.CallArguments |> Option.defaultValue []
                    let seeded = Map.tryFind nodeId program.IndexSeeds |> Option.defaultValue []
                    if program.RootParameters.TryFind nodeId = Some DeclRoot.LibraryExport then
                        NodeTransferPlan.Constant (applyCarrier carrier fallback)
                    elif program.InactiveFormals.Contains nodeId then
                        NodeTransferPlan.Constant (applyCarrier carrier ValueRange.Empty)
                    elif List.isEmpty supplied && List.isEmpty seeded then
                        NodeTransferPlan.Constant (applyCarrier carrier fallback)
                    else
                        let uKeys, rSup = splitSharedPairs supplied
                        let seedArr = seeded |> List.map (fun (c, n) -> struct(c, n)) |> List.toArray
                        NodeTransferPlan.Parameter (uKeys, rSup, seedArr, carrier)
                | SemanticKind.PatternBinding _ ->
                    match List.tryLast node.Children with
                    | Some valueId -> NodeTransferPlan.SingleRead (valueId, carrier)
                    | None -> NodeTransferPlan.Constant (applyCarrier carrier fallback)
                | SemanticKind.Binding (_, false, _, _) ->
                    match List.tryLast node.Children with
                    | Some valueId -> NodeTransferPlan.SingleRead (valueId, carrier)
                    | None -> NodeTransferPlan.Constant (applyCarrier carrier fallback)
                | SemanticKind.Binding (_, true, _, _) ->
                    let initOpt = match List.tryLast node.Children with Some v -> ValueSome v | None -> ValueNone
                    let assigns = Map.tryFind nodeId program.Assignments |> Option.defaultValue [] |> List.toArray
                    NodeTransferPlan.MutableBinding (initOpt, fallback, assigns, carrier)
                | SemanticKind.Sequential ids ->
                    match List.tryLast ids with
                    | Some lastId -> NodeTransferPlan.SingleRead (lastId, carrier)
                    | None -> NodeTransferPlan.Constant (applyCarrier carrier fallback)
                | SemanticKind.IfThenElse (guard, t, e) ->
                    let trueOk = not (isLiteralBool program guard false)
                    let trueAtoms = if trueOk then atoms program 0 guard true |> List.toArray else Array.empty
                    let falseOk = not (isLiteralBool program guard true)
                    let falseAtoms = if falseOk then atoms program 0 guard false |> List.toArray else Array.empty
                    let eOpt = match e with Some eid -> ValueSome eid | None -> ValueNone
                    NodeTransferPlan.IfThenElse (t, eOpt, trueOk, trueAtoms, falseOk, falseAtoms)
                | SemanticKind.Match (_, cases) ->
                    NodeTransferPlan.BranchJoin (cases |> List.map (fun c -> c.Body) |> List.toArray)
                | SemanticKind.CaseElimination (_, arms) ->
                    NodeTransferPlan.BranchJoin (arms |> List.map (fun a -> a.Body) |> List.toArray)
                | SemanticKind.FieldGet (exprId, field) ->
                    match Map.tryFind exprId program.Reachable with
                    | Some { Type = NativeType.TApp (tycon, _) } ->
                        let typeName = NominalTypeIdentity.ofConstructor tycon
                        if Map.containsKey typeName program.Constructions || Map.containsKey typeName program.InputSeeds then
                            let declared = Map.tryFind typeName program.InputSeeds |> Option.bind (Map.tryFind field)
                            match declared with
                            | Some d when ValueRange.isObservable d ->
                                NodeTransferPlan.Constant (applyCarrier carrier d)
                            | _ ->
                                let init, uKeys, rPairs =
                                    match fieldPlanCache.TryGetValue((typeName, field)) with
                                    | true, cached -> cached
                                    | false, _ ->
                                        let pairs =
                                            Map.tryFind typeName program.Constructions
                                            |> Option.defaultValue []
                                            |> List.collect (fun (recordId, fields) ->
                                                fields |> List.choose (fun (name, valueId) -> if name = field then Some (recordId, valueId) else None))
                                        let uKeys, rPairs = splitSharedPairs pairs
                                        let computed = declared |> Option.defaultValue ValueRange.Empty, uKeys, rPairs
                                        fieldPlanCache[(typeName, field)] <- computed
                                        computed
                                NodeTransferPlan.SharedStores (init, uKeys, rPairs, carrier)
                        else
                            NodeTransferPlan.Constant (applyCarrier carrier fallback)
                    | _ ->
                        NodeTransferPlan.Constant (applyCarrier carrier fallback)
                | SemanticKind.TupleGet (tupleId, index) ->
                    let _, unbounded, leaves = aggregateElementOrigins program Set.empty tupleId [TupleSlot index]
                    let init = if unbounded then ValueRange.Unbounded else ValueRange.Empty
                    if leaves.IsEmpty then NodeTransferPlan.Constant (applyCarrier carrier init)
                    else
                        let leafKeys = leaves |> Seq.map getOrAddSharedKey |> Seq.toArray
                        System.Array.Sort(leafKeys)
                        NodeTransferPlan.SharedLeaves (init, leafKeys, carrier)
                | SemanticKind.DUEliminate (value, tag, name, _) ->
                    let _, unbounded, leaves = aggregateElementOrigins program Set.empty value [UnionPayload(tag, name)]
                    let init = if unbounded then ValueRange.Unbounded else ValueRange.Empty
                    if leaves.IsEmpty then NodeTransferPlan.Constant (applyCarrier carrier init)
                    else
                        let leafKeys = leaves |> Seq.map getOrAddSharedKey |> Seq.toArray
                        System.Array.Sort(leafKeys)
                        NodeTransferPlan.SharedLeaves (init, leafKeys, carrier)
                | SemanticKind.IndexGet (exprId, _) ->
                    match Map.tryFind exprId program.Reachable |> Option.map (fun n -> n.Type) |> Option.bind arrayElementType with
                    | Some elem ->
                        match buildElementReadPlan elem with
                        | ElemConst r -> NodeTransferPlan.Constant (applyCarrier carrier r)
                        | ElemStores (init, uKeys, rPairs) -> NodeTransferPlan.SharedStores (init, uKeys, rPairs, carrier)
                    | None ->
                        NodeTransferPlan.Constant (applyCarrier carrier fallback)
                | SemanticKind.Application _ ->
                    if program.ForeignEntryCalls.ContainsKey nodeId then
                        NodeTransferPlan.General node
                    else
                        match Map.tryFind nodeId program.Callees with
                        | Some (Callee.Direct(_, body), _) when program.ForeignEffectBodies.Contains body ->
                            NodeTransferPlan.General node
                        | Some (Callee.Value(candidates, _), _) when candidates |> List.exists (fun candidate -> program.ForeignEffectBodies.Contains candidate.Body) ->
                            NodeTransferPlan.Constant (applyCarrier carrier fallback)
                        | Some (Callee.Intrinsic { Module = IntrinsicModule.SeqEnumerator; Operation = "current" }, [_]) ->
                            NodeTransferPlan.General node
                        | Some (Callee.Intrinsic info, args) ->
                            let argPlans =
                                args
                                |> List.map (fun a ->
                                    match Map.tryFind a program.Reachable with
                                    | Some an ->
                                        let lit = match an.Kind with SemanticKind.Literal l -> Some l | _ -> None
                                        let elemPlan =
                                            match arrayElementType an.Type with
                                            | Some elem -> ValueSome (buildElementReadPlan elem)
                                            | None -> ValueNone
                                        IntrinsicArgPlan(a, isRanged an, an.Type, lit, elemPlan)
                                    | None ->
                                        IntrinsicArgPlan(a, false, NativeType.TError "unreachable", None, ValueNone))
                                |> List.toArray
                            NodeTransferPlan.IntrinsicApp (info, argPlans, fallback, carrier)
                        | _ when program.Applications.ContainsKey nodeId ->
                            NodeTransferPlan.ContextualApp (fallback, carrier)
                        | Some (Callee.Direct (_, bodyId), _) ->
                            NodeTransferPlan.DirectApp (getOrAddSharedKey bodyId)
                        | _ ->
                            NodeTransferPlan.General node
                | _ ->
                    NodeTransferPlan.General node
    let planByNode : NodeTransferPlan[] = Array.create nodeArraySize NodeTransferPlan.Unset
    for i = 0 to coords.Length - 1 do
        let struct(_, _, node) = coords.[i]
        let (NodeId n) = node.Id
        if n >= 0 && n < nodeArraySize then
            match planByNode.[n] with
            | NodeTransferPlan.Unset -> planByNode.[n] <- buildNodePlan node
            | _ -> ()
    let evalPlan (ctxId: int) (keyId: int) (nodeId: NodeId) (plan: NodeTransferPlan) : ValueRange option =
        match plan with
        | NodeTransferPlan.NotRanged -> None
        | NodeTransferPlan.Constant r -> Some r
        | NodeTransferPlan.SingleRead (operand, carrier) ->
            Some (applyCarrier carrier (readFastCtx ctxId nodeId operand))
        | NodeTransferPlan.Parameter (uKeys, rSup, seeded, carrier) ->
            let mutable range = ValueRange.Empty
            for i = 0 to uKeys.Length - 1 do
                range <- ValueRange.join range (get uKeys.[i])
            for i = 0 to rSup.Length - 1 do
                let struct(callId, a) = rSup.[i]
                range <- ValueRange.join range (readFastCtx 0 callId a)
            for i = 0 to seeded.Length - 1 do
                let struct(callId, nId) = seeded.[i]
                range <- ValueRange.join range (indexBelow (readFastCtx 0 callId nId))
            Some (applyCarrier carrier range)
        | NodeTransferPlan.MutableBinding (initOpt, fallback, assigns, carrier) ->
            let mutable range =
                match initOpt with
                | ValueSome valueId -> readFastCtx ctxId nodeId valueId
                | ValueNone -> fallback
            for i = 0 to assigns.Length - 1 do
                range <- ValueRange.join range (readFastCtx ctxId nodeId assigns.[i])
            Some (applyCarrier carrier range)
        | NodeTransferPlan.IfThenElse (t, eOpt, trueOk, trueAtoms, falseOk, falseAtoms) ->
            let yes =
                if trueOk && feasibleAtomsArrCtx ctxId trueAtoms then readFastCtx ctxId nodeId t
                else ValueRange.Empty
            let no =
                match eOpt with
                | ValueSome e when falseOk && feasibleAtomsArrCtx ctxId falseAtoms -> readFastCtx ctxId nodeId e
                | _ -> ValueRange.Empty
            Some (ValueRange.join yes no)
        | NodeTransferPlan.BranchJoin bodies ->
            let mutable range = ValueRange.Empty
            for i = 0 to bodies.Length - 1 do
                range <- ValueRange.join range (readFastCtx ctxId nodeId bodies.[i])
            Some range
        | NodeTransferPlan.SharedStores (init, uKeys, rPairs, carrier) ->
            let mutable range = init
            for i = 0 to uKeys.Length - 1 do
                range <- ValueRange.join range (get uKeys.[i])
            for i = 0 to rPairs.Length - 1 do
                let struct(storer, valueId) = rPairs.[i]
                range <- ValueRange.join range (readFastCtx 0 storer valueId)
            Some (applyCarrier carrier range)
        | NodeTransferPlan.SharedLeaves (init, leafKeys, carrier) ->
            let mutable range = init
            for i = 0 to leafKeys.Length - 1 do
                range <- ValueRange.join range (get leafKeys.[i])
            Some (applyCarrier carrier range)
        | NodeTransferPlan.ContextualApp (fallback, carrier) ->
            let raw =
                match callsByKey.[keyId] with
                | ValueSome rowKeyIds ->
                    let mutable range = ValueRange.Empty
                    for i = 0 to rowKeyIds.Length - 1 do
                        range <- ValueRange.join range (get rowKeyIds.[i])
                    range
                | ValueNone -> fallback
            Some (applyCarrier carrier raw)
        | NodeTransferPlan.DirectApp bodyKeyId ->
            Some (get bodyKeyId)
        | NodeTransferPlan.IntrinsicApp (info, argPlans, fallback, carrier) ->
            let arguments =
                match argPlans.Length with
                | 0 -> []
                | 1 ->
                    let p0 = argPlans.[0]
                    [ { RangeSources.Argument.Range = (if p0.IsRanged then readFastCtx ctxId nodeId p0.NodeId else ValueRange.Unbounded)
                        RangeSources.Argument.Type = p0.Type
                        RangeSources.Argument.Literal = p0.Literal } ]
                | 2 ->
                    let p0 = argPlans.[0]
                    let r0 = if p0.IsRanged then readFastCtx ctxId nodeId p0.NodeId else ValueRange.Unbounded
                    let p1 = argPlans.[1]
                    let r1 = if p1.IsRanged then readFastCtx ctxId nodeId p1.NodeId else ValueRange.Unbounded
                    [ { RangeSources.Argument.Range = r0; RangeSources.Argument.Type = p0.Type; RangeSources.Argument.Literal = p0.Literal }
                      { RangeSources.Argument.Range = r1; RangeSources.Argument.Type = p1.Type; RangeSources.Argument.Literal = p1.Literal } ]
                | len ->
                    [ for i = 0 to len - 1 do
                        let p = argPlans.[i]
                        let r = if p.IsRanged then readFastCtx ctxId nodeId p.NodeId else ValueRange.Unbounded
                        yield { RangeSources.Argument.Range = r; RangeSources.Argument.Type = p.Type; RangeSources.Argument.Literal = p.Literal } ]
            let raw =
                match RangeSources.intrinsic program.Context info arguments with
                | RangeSources.Result.Fact r -> r
                | RangeSources.Result.ElementOf i ->
                    if i >= 0 && i < argPlans.Length then
                        match argPlans.[i].ElemPlan with
                        | ValueSome (ElemConst r) -> r
                        | ValueSome (ElemStores (init, uKeys, rPairs)) ->
                            let mutable range = init
                            for j = 0 to uKeys.Length - 1 do
                                range <- ValueRange.join range (get uKeys.[j])
                            for j = 0 to rPairs.Length - 1 do
                                let struct(storer, valueId) = rPairs.[j]
                                range <- ValueRange.join range (readFastCtx 0 storer valueId)
                            range
                        | ValueNone -> fallback
                    else fallback
                | RangeSources.Result.Untabled -> fallback
            Some (applyCarrier carrier raw)
        | NodeTransferPlan.General node ->
            transfer program shared readingByCtxId.[ctxId] applicationByCtxId.[ctxId] node
        | NodeTransferPlan.Unset ->
            None
    let splitParams : struct(int[] * struct(int * NodeId * NodeId)[]) voption[] = Array.create numKeys ValueNone
    for (paramKeyId, rows) in tempParams do
        let uKeys = ResizeArray<int>(rows.Length)
        let rInputs = ResizeArray<struct(int * NodeId * NodeId)>()
        for (callerId, call, actual) in rows do
            let (NodeId cn) = call
            let hasGuard = cn < 0 || cn >= nodeArraySize || guardAtomsByNode.[cn].IsSome
            if hasGuard || hasRefinementOn call actual then
                rInputs.Add(struct(callerId, call, actual))
            else
                uKeys.Add(resolveKeyInCtx callerId actual)
        let uArr = uKeys.ToArray()
        let finalUArr =
            if uArr.Length > 1 then
                System.Array.Sort(uArr)
                let mutable uCount = 1
                for i = 1 to uArr.Length - 1 do
                    if uArr.[i] <> uArr.[uCount - 1] then
                        uArr.[uCount] <- uArr.[i]
                        uCount <- uCount + 1
                if uCount = uArr.Length then uArr
                else
                    let trimmed = Array.zeroCreate<int> uCount
                    System.Array.Copy(uArr, 0, trimmed, 0, uCount)
                    trimmed
            else uArr
        splitParams.[paramKeyId] <- ValueSome (struct(finalUArr, rInputs.ToArray()))
    let singleKeyArrayCache : int[] voption[] = Array.create numKeys ValueNone
    let getSingleKeyArray (k: int) =
        match singleKeyArrayCache.[k] with
        | ValueSome arr -> arr
        | ValueNone ->
            let arr = [| k |]
            singleKeyArrayCache.[k] <- ValueSome arr
            arr
    let coordDirectReadKey : int[] = Array.create coords.Length -1
    let coordDirectCarrier : ValueRange voption[] = Array.create coords.Length ValueNone
    let coordConstValue : ValueRange voption[] = Array.create coords.Length ValueNone
    let coordNotRanged : bool[] = Array.create coords.Length false
    for coordIdx = 0 to coords.Length - 1 do
        let struct(ctxId, keyId, node) = coords.[coordIdx]
        let (NodeId n as nodeId) = node.Id
        if n >= 0 && n < nodeArraySize then
            let isApp0 = ctxId = 0 && isApplicationNode.[n]
            let hasGuard = ctxId <> 0 && guardAtomsByNode.[n].IsSome
            let hasParam = ctxId <> 0 && paramsByKey.[keyId].IsSome
            if not isApp0 && not hasGuard && not hasParam then
                match planByNode.[n] with
                | NodeTransferPlan.NotRanged ->
                    coordNotRanged.[coordIdx] <- true
                | NodeTransferPlan.Constant r ->
                    coordConstValue.[coordIdx] <- ValueSome r
                | NodeTransferPlan.SingleRead (operand, carrier) when not (hasRefinementOn nodeId operand) ->
                    let dk = resolveKeyInCtx ctxId operand
                    coordDirectReadKey.[coordIdx] <- dk
                    coordDirectCarrier.[coordIdx] <- carrier
                    let singleArr = getSingleKeyArray dk
                    lastRecordedDeps.[coordIdx] <- ValueSome singleArr
                    climbLastReads.[coordIdx] <- singleArr
                    descendLastReads.[coordIdx] <- singleArr
                    hasReads.[coordIdx] <- true
                    addDependentFirst dk coordIdx
                | NodeTransferPlan.DirectApp bodyKeyId ->
                    coordDirectReadKey.[coordIdx] <- bodyKeyId
                    coordDirectCarrier.[coordIdx] <- ValueNone
                    let singleArr = getSingleKeyArray bodyKeyId
                    lastRecordedDeps.[coordIdx] <- ValueSome singleArr
                    climbLastReads.[coordIdx] <- singleArr
                    descendLastReads.[coordIdx] <- singleArr
                    hasReads.[coordIdx] <- true
                    addDependentFirst bodyKeyId coordIdx
                | _ -> ()
    let inline evaluateCoord (coordIdx: int) (ctxId: int) (keyId: int) (node: SemanticNode) =
        readCursor <- 0
        if readsOverflow.Count > 0 then readsOverflow.Clear()
        let directKey = coordDirectReadKey.[coordIdx]
        if directKey >= 0 then
            Some (applyCarrier coordDirectCarrier.[coordIdx] (get directKey))
        else
            let (NodeId n as nodeId) = node.Id
            let plan = if n >= 0 && n < nodeArraySize then planByNode.[n] else NodeTransferPlan.General node
            if ctxId = 0 then
                if n >= 0 && n < nodeArraySize && isApplicationNode.[n] then
                    match occurrencesByNodeArr.[n] with
                    | ValueSome occs ->
                        let mutable range = ValueRange.Empty
                        for i = 0 to occs.Length - 1 do
                            range <- ValueRange.join range (get occs.[i])
                        Some range
                    | ValueNone ->
                        evalPlan 0 keyId nodeId plan
                else
                    evalPlan 0 keyId nodeId plan
            else
                if not (occurrenceFeasibleFastCtx ctxId nodeId) then Some ValueRange.Empty
                else
                    match splitParams.[keyId] with
                    | ValueSome (struct(uKeys, rInputs)) ->
                        let mutable range = ValueRange.Empty
                        for i = 0 to uKeys.Length - 1 do
                            range <- ValueRange.join range (get uKeys.[i])
                        for i = 0 to rInputs.Length - 1 do
                            let struct(callerId, call, actual) = rInputs.[i]
                            if occurrenceFeasibleFastCtx callerId call then
                                range <- ValueRange.join range (readFastCtx callerId call actual)
                        Some range
                    | ValueNone ->
                        evalPlan ctxId keyId nodeId plan
    let hasUintThresholds = program.Thresholds |> List.exists (fun t -> t.Family = "uint")
    let buildSortedBigints (baseList: bigint list) (constPairs: seq<bigint>) : bigint[] =
        let s = System.Collections.Generic.SortedSet<bigint>(baseList)
        for v in constPairs do s.Add(v) |> ignore
        let arr = Array.zeroCreate<bigint> s.Count
        s.CopyTo(arr)
        arr
    let baseUintHi = program.Thresholds |> List.choose (fun t -> if t.Family = "uint" then Some t.Hi else None)
    let baseIntHi = program.Thresholds |> List.choose (fun t -> if t.Family = "int" then Some t.Hi else None)
    let baseUintLo = program.Thresholds |> List.choose (fun t -> if t.Family = "uint" then Some t.Lo else None)
    let baseIntLo = program.Thresholds |> List.choose (fun t -> if t.Family = "int" then Some t.Lo else None)
    let uintHiNoConsts = buildSortedBigints baseUintHi Seq.empty
    let intHiNoConsts = buildSortedBigints baseIntHi Seq.empty
    let uintLoNoConsts = buildSortedBigints baseUintLo Seq.empty
    let intLoNoConsts = buildSortedBigints baseIntLo Seq.empty
    let mutable uintHiWithConsts = uintHiNoConsts
    let mutable intHiWithConsts = intHiNoConsts
    let mutable uintLoWithConsts = uintLoNoConsts
    let mutable intLoWithConsts = intLoNoConsts
    let inline minAbove (arr: bigint[]) (g: bigint) : ValueRange.Endpoint =
        let idx = System.Array.BinarySearch(arr, g)
        let i = if idx >= 0 then idx else ~~~idx
        if i < arr.Length then ValueRange.Endpoint.Finite arr.[i] else ValueRange.Endpoint.PosInf
    let inline maxBelow (arr: bigint[]) (g: bigint) : ValueRange.Endpoint =
        let idx = System.Array.BinarySearch(arr, g)
        let i = if idx >= 0 then idx else (~~~idx) - 1
        if i >= 0 then ValueRange.Endpoint.Finite arr.[i] else ValueRange.Endpoint.NegInf
    let inline widenWithSorted (hiUint: bigint[]) (hiInt: bigint[]) (loUint: bigint[]) (loInt: bigint[]) (old: ValueRange) (grown: ValueRange) : ValueRange =
        match ValueRange.endpoints old, ValueRange.endpoints grown with
        | _, None -> old
        | None, _ -> grown
        | Some (olo, ohi), Some (glo, ghi) ->
            let isUint =
                hasUintThresholds &&
                (match glo with ValueRange.Endpoint.Finite g -> g >= bigint.Zero | ValueRange.Endpoint.PosInf -> true | ValueRange.Endpoint.NegInf -> false)
            let hi =
                if ghi <= ohi then ohi
                else
                    match ghi with
                    | ValueRange.Endpoint.Finite g -> minAbove (if isUint then hiUint else hiInt) g
                    | _ -> ValueRange.Endpoint.PosInf
            let lo =
                if glo >= olo then olo
                else
                    match glo with
                    | ValueRange.Endpoint.Finite g -> maxBelow (if isUint then loUint else loInt) g
                    | _ -> ValueRange.Endpoint.NegInf
            ValueRange.ofEndpoints lo hi
    let pointKeysByVal = System.Collections.Generic.Dictionary<bigint, System.Collections.Generic.HashSet<int>>()
    let mutable pointConstantsDirty = true
    let updatePointConstant (kId: int) (hasPrev: bool) (old: ValueRange) (next: ValueRange) =
        if hasPrev then
            match old with
            | ValueRange.Bounded(lo, hi) when lo = hi ->
                match pointKeysByVal.TryGetValue(lo) with
                | true, s ->
                    if s.Remove(kId) then
                        if s.Count = 0 then
                            pointKeysByVal.Remove(lo) |> ignore
                            pointConstantsDirty <- true
                | false, _ -> ()
            | _ -> ()
        match next with
        | ValueRange.Bounded(lo, hi) when lo = hi ->
            match pointKeysByVal.TryGetValue(lo) with
            | true, s ->
                s.Add(kId) |> ignore
            | false, _ ->
                let s = System.Collections.Generic.HashSet<int>()
                s.Add(kId) |> ignore
                pointKeysByVal[lo] <- s
                pointConstantsDirty <- true
        | _ -> ()
    let refreshConstantsIfNeeded () =
        if pointConstantsDirty then
            pointConstantsDirty <- false
            let hiConsts = ResizeArray<bigint>(pointKeysByVal.Count * 2)
            let loConsts = ResizeArray<bigint>(pointKeysByVal.Count * 2)
            for c in pointKeysByVal.Keys do
                hiConsts.Add(c - bigint.One)
                hiConsts.Add(c)
                loConsts.Add(c)
                loConsts.Add(c + bigint.One)
            uintHiWithConsts <- buildSortedBigints baseUintHi hiConsts
            intHiWithConsts <- buildSortedBigints baseIntHi hiConsts
            uintLoWithConsts <- buildSortedBigints baseUintLo loConsts
            intLoWithConsts <- buildSortedBigints baseIntLo loConsts
    let mutable activeThis = Array.init coords.Length (fun i -> not coordNotRanged.[i])
    let mutable activeNext = Array.create coords.Length false
    let rec climb round (minActive: int) (maxActive: int) =
        if round > AscentLimit then
            failwithf "RangeAnalysis: the range fixpoint did not settle in %d rounds; the widening did not terminate the ascent" AscentLimit
        elif minActive <= maxActive then
            let roundConstants =
                if round > WideningDelay then
                    refreshConstantsIfNeeded ()
                    let keys = pointKeysByVal.Values |> Seq.collect id |> Seq.toArray
                    let setId = constSetArrays.Count
                    constSetArrays.Add keys
                    ValueSome setId
                else ValueNone
            let mutable curMaxActive = maxActive
            let mutable nextMinActive = coords.Length
            let mutable nextMaxActive = -1
            let mutable coordIdx = minActive
            while coordIdx <= curMaxActive do
                if activeThis.[coordIdx] then
                    activeThis.[coordIdx] <- false
                    let struct(ctxId, keyId, node) = coords.[coordIdx]
                    let directKey = coordDirectReadKey.[coordIdx]
                    let computed =
                        if directKey >= 0 then
                            Some (applyCarrier coordDirectCarrier.[coordIdx] valuesArr.[directKey])
                        else
                            match coordConstValue.[coordIdx] with
                            | ValueSome r ->
                                hasReads.[coordIdx] <- true
                                Some r
                            | ValueNone ->
                                evaluateCoord coordIdx ctxId keyId node
                    match computed with
                    | None -> ()
                    | Some computed ->
                        if directKey < 0 && coordConstValue.[coordIdx].IsNone then
                            let struct(currentReads, depsChanged) = extractDeps lastRecordedDeps.[coordIdx]
                            hasReads.[coordIdx] <- true
                            climbLastReads.[coordIdx] <- currentReads
                            if depsChanged then
                                match lastRecordedDeps.[coordIdx] with
                                | ValueSome prev ->
                                    let acc =
                                        match extraReadsAcc.[coordIdx] with
                                        | ValueSome list -> list
                                        | ValueNone ->
                                            let list = ResizeArray<int>(prev.Length)
                                            extraReadsAcc.[coordIdx] <- ValueSome list
                                            list
                                    for i = 0 to prev.Length - 1 do
                                        acc.Add(prev.[i])
                                    lastRecordedDeps.[coordIdx] <- ValueSome currentReads
                                    addNewDependents prev currentReads coordIdx
                                | ValueNone ->
                                    lastRecordedDeps.[coordIdx] <- ValueSome currentReads
                                    for i = 0 to currentReads.Length - 1 do
                                        addDependentFirst currentReads.[i] coordIdx
                        let hasPrev = hasValueArr.[keyId]
                        let old = valuesArr.[keyId]
                        let next =
                            if not hasPrev then computed
                            else
                                let grown = ValueRange.join old computed
                                if ValueRange.contains old grown then old
                                elif round > WideningDelay then
                                    match roundConstants with
                                    | ValueSome setId -> usedConstSetIds.[coordIdx] <- usedConstSetIds.[coordIdx].Add setId
                                    | ValueNone -> ()
                                    widenWithSorted uintHiWithConsts intHiWithConsts uintLoWithConsts intLoWithConsts old grown
                                else grown
                        if not hasPrev then
                            hasValueArr.[keyId] <- true
                        if old <> next then
                            updatePointConstant keyId hasPrev old next
                            valuesArr.[keyId] <- next
                            match dependentsOfKey.[keyId] with
                            | ValueSome depCoords ->
                                for i = 0 to depCoords.Count - 1 do
                                    let depCoord = depCoords.[i]
                                    if depCoord > coordIdx then
                                        activeThis.[depCoord] <- true
                                        if depCoord > curMaxActive then curMaxActive <- depCoord
                                    else
                                        activeNext.[depCoord] <- true
                                        if depCoord < nextMinActive then nextMinActive <- depCoord
                                        if depCoord > nextMaxActive then nextMaxActive <- depCoord
                            | ValueNone -> ()
                coordIdx <- coordIdx + 1
            if nextMinActive <= nextMaxActive then
                let swap = activeThis
                activeThis <- activeNext
                activeNext <- swap
                climb (round + 1) nextMinActive nextMaxActive
    let rec descend round (minActive: int) (maxActive: int) =
        if round <= NarrowingRounds && minActive <= maxActive then
            let mutable curMaxActive = maxActive
            let mutable nextMinActive = coords.Length
            let mutable nextMaxActive = -1
            let mutable coordIdx = minActive
            while coordIdx <= curMaxActive do
                if activeThis.[coordIdx] then
                    activeThis.[coordIdx] <- false
                    let struct(ctxId, keyId, node) = coords.[coordIdx]
                    let directKey = coordDirectReadKey.[coordIdx]
                    let computed =
                        if directKey >= 0 then
                            Some (applyCarrier coordDirectCarrier.[coordIdx] valuesArr.[directKey])
                        else
                            evaluateCoord coordIdx ctxId keyId node
                    match computed with
                    | None -> ()
                    | Some computed ->
                        if directKey < 0 then
                            let struct(currentReads, depsChanged) = extractDeps lastRecordedDeps.[coordIdx]
                            hasReads.[coordIdx] <- true
                            descendLastReads.[coordIdx] <- currentReads
                            if depsChanged then
                                match lastRecordedDeps.[coordIdx] with
                                | ValueSome prev ->
                                    let acc =
                                        match extraReadsAcc.[coordIdx] with
                                        | ValueSome list -> list
                                        | ValueNone ->
                                            let list = ResizeArray<int>(prev.Length)
                                            extraReadsAcc.[coordIdx] <- ValueSome list
                                            list
                                    for i = 0 to prev.Length - 1 do
                                        acc.Add(prev.[i])
                                    lastRecordedDeps.[coordIdx] <- ValueSome currentReads
                                    addNewDependents prev currentReads coordIdx
                                | ValueNone ->
                                    lastRecordedDeps.[coordIdx] <- ValueSome currentReads
                                    for i = 0 to currentReads.Length - 1 do
                                        addDependentFirst currentReads.[i] coordIdx
                        let old = if hasValueArr.[keyId] then valuesArr.[keyId] else ValueRange.Empty
                        let next = if ValueRange.contains computed old || not (ValueRange.contains old computed) then old else computed
                        let valueChanged = old <> next
                        if valueChanged then
                            hasValueArr.[keyId] <- true
                            valuesArr.[keyId] <- next
                            match dependentsOfKey.[keyId] with
                            | ValueSome depCoords ->
                                for i = 0 to depCoords.Count - 1 do
                                    let depCoord = depCoords.[i]
                                    if depCoord > coordIdx then
                                        activeThis.[depCoord] <- true
                                        if depCoord > curMaxActive then curMaxActive <- depCoord
                                    else
                                        activeNext.[depCoord] <- true
                                        if depCoord < nextMinActive then nextMinActive <- depCoord
                                        if depCoord > nextMaxActive then nextMaxActive <- depCoord
                            | ValueNone -> ()
                coordIdx <- coordIdx + 1
            if nextMinActive <= nextMaxActive then
                let swap = activeThis
                activeThis <- activeNext
                activeNext <- swap
                descend (round + 1) nextMinActive nextMaxActive
    if coords.Length > 0 then
        climb 1 0 (coords.Length - 1)
    if coords.Length > 0 then
        for i = 0 to coords.Length - 1 do
            activeThis.[i] <- not coordNotRanged.[i] && coordConstValue.[i].IsNone
        System.Array.Fill(activeNext, false)
        descend 1 0 (coords.Length - 1)
    let keyToPair = keyToPairList.ToArray()
    let keyToSharedNode = keyToSharedNodeList.ToArray()
    let valuesMap =
        seq {
            for kId = 0 to keyToPair.Length - 1 do
                if hasValueArr.[kId] then
                    yield keyToPair.[kId], valuesArr.[kId]
        }
        |> Map.ofSeq
    let readsMap =
        let singleConstSetCache = System.Collections.Generic.Dictionary<int, Set<RangeContext * NodeId>>()
        let getSingleConstSet (constSetId: int) =
            match singleConstSetCache.TryGetValue(constSetId) with
            | true, s -> s
            | false, _ ->
                let arr = constSetArrays.[constSetId]
                let s = arr |> Array.map (fun kId -> keyToPair.[kId]) |> Set.ofArray
                singleConstSetCache[constSetId] <- s
                s
        let comboCache = System.Collections.Generic.Dictionary<Set<int>, Set<RangeContext * NodeId>>()
        let getComboSet (combo: Set<int>) =
            if combo.IsEmpty then Set.empty
            elif combo.Count = 1 then getSingleConstSet (Seq.head combo)
            else
                match comboCache.TryGetValue(combo) with
                | true, s -> s
                | false, _ ->
                    let s =
                        combo
                        |> Seq.fold (fun (acc: Set<RangeContext * NodeId>) constSetId ->
                            let part = getSingleConstSet constSetId
                            if acc.IsEmpty then part else Set.union acc part) Set.empty
                    comboCache[combo] <- s
                    s
        seq {
            for coordIdx = 0 to coords.Length - 1 do
                if hasReads.[coordIdx] then
                    let struct(_, keyId, _) = coords.[coordIdx]
                    let mutable unpackedDeps = getComboSet usedConstSetIds.[coordIdx]
                    let cReads = climbLastReads.[coordIdx]
                    for i = 0 to cReads.Length - 1 do
                        unpackedDeps <- unpackedDeps.Add(keyToPair.[cReads.[i]])
                    let dReads = descendLastReads.[coordIdx]
                    for i = 0 to dReads.Length - 1 do
                        unpackedDeps <- unpackedDeps.Add(keyToPair.[dReads.[i]])
                    match extraReadsAcc.[coordIdx] with
                    | ValueSome extra ->
                        for i = 0 to extra.Count - 1 do
                            unpackedDeps <- unpackedDeps.Add(keyToPair.[extra.[i]])
                    | ValueNone -> ()
                    yield keyToPair.[keyId], unpackedDeps
        }
        |> Map.ofSeq
    let shared =
        seq {
            for kId = 0 to keyToSharedNode.Length - 1 do
                if hasValueArr.[kId] then
                    match keyToSharedNode.[kId] with
                    | ValueSome nodeId -> yield nodeId, valuesArr.[kId]
                    | ValueNone -> ()
        }
        |> Map.ofSeq
    shared,
    { ContextDepth = InvocationContextDepth; Invocations = contexts.Invocations
      Values = valuesMap; Reads = readsMap; Premises = Map.empty
      CaptureRelations = []; SourceRelations = Ok []; Platform = None; Roots = [] }

/// Diagnostics follow issued read incidence; they never replay the solver.
let private contextProvenance (facts: RangeContextFacts) (diagnostics: Diagnostic list) =
    let merged = facts.Invocations |> List.groupBy _.Context |> List.choose (fun (context, rows) ->
        let callers = rows |> List.map _.Caller |> List.distinct
        if callers.Length > 1 then Some context else None) |> Set.ofList
    let rec dependencies seen pending =
        match pending with
        | [] -> seen
        | key :: rest when Set.contains key seen -> dependencies seen rest
        | key :: rest ->
            let next = facts.Reads.TryFind key |> Option.defaultValue Set.empty |> Set.toList
            dependencies (Set.add key seen) (next @ rest)
    diagnostics |> List.map (fun diagnostic ->
        if diagnostic.Code <> DiagnosticCodes.CCS8011_UnobservableRange then diagnostic
        else
            let support = diagnostic.RelatedNodes |> List.map (fun id -> RangeContext.Shared, id) |> dependencies Set.empty
            let contexts = support |> Seq.map fst |> Set.ofSeq |> Set.intersect merged
            if contexts.IsEmpty then diagnostic
            else
                let rows = facts.Invocations |> List.filter (fun row -> contexts.Contains row.Context)
                let names = contexts |> Set.toList |> List.choose (function
                    | RangeContext.Invocation sites -> Some("[" + (sites |> List.map (NodeId.value >> string) |> String.concat ", ") + "]")
                    | RangeContext.Shared -> None) |> String.concat ", "
                { diagnostic with
                    Message = diagnostic.Message + "; its retained range support includes merged invocation contexts " + names
                    RelatedNodes = (diagnostic.RelatedNodes @ (rows |> List.collect (fun row -> [row.Call; row.Target]))) |> List.distinct })

//-------------------------------------------------------------------------
// Selection (§3.1): the platform's declared set, the range's choice
//-------------------------------------------------------------------------

/// The offered integer representations of a context, by family.
let private offeredIntegers (ctx: PlatformContext) (family: string) : NumericRepresentation list =
    ctx.Representations
    |> Map.toList
    |> List.map snd
    |> List.filter (fun r -> r.Family = family && NumericRepresentation.isOffered r)

/// The family a range selects from: `uint` for a non-negative range where the context offers one,
/// `int` otherwise.
let private familyOf (ctx: PlatformContext) (range: ValueRange) : string =
    if ValueRange.isNonNegative range && not (List.isEmpty (offeredIntegers ctx "uint")) then "uint" else "int"

/// The widest offered integer representation of the family, the fallback of an uncovered range.
let private widestOf (ctx: PlatformContext) (family: string) : NumericRepresentation option =
    offeredIntegers ctx family |> List.sortByDescending (fun r -> r.Bits) |> List.tryHead

/// What the range selects on a context with declared representations: the offered representation
/// of the family the sign selects with the fewest bits whose declared range covers the range
/// (`Covered = true`), or the widest of the family when none does (`Covered = false`, CCS8012);
/// nothing for an unobservable range or a context with no integer representation.
type Selection = { Representation: NumericRepresentation option; Covered: bool }

/// The selection for a range of the bare kind (§3.1).
let private selectRange (ctx: PlatformContext) (range: ValueRange) : Selection =
    if not (ValueRange.isObservable range) then { Representation = None; Covered = false }
    else
        let family = familyOf ctx range
        let covering =
            offeredIntegers ctx family
            |> List.filter (fun r -> RangeSources.declaredRange r |> Option.exists (fun d -> ValueRange.contains d range))
            |> List.sortBy (fun r -> r.Bits)
            |> List.tryHead
        match covering with
        | Some r -> { Representation = Some r; Covered = true }
        | None ->
            match widestOf ctx family with
            | Some r -> { Representation = Some r; Covered = false }
            | None -> { Representation = None; Covered = false }

/// The kind a node's declaration is read from (CS-12 step 5a): its own type's, except that a
/// reference to a binding or a parameter reads its definition's, since the declaration is the
/// annotated site's and a reference is the value of its binding; under the alias the checker
/// may type the reference by the context it unifies with, and the derivation (the SSA meet)
/// reads the definition. A value stored at a spelled binding keeps its own kind: the binding's
/// meet (SSAAssignment) brings it to the binding's representation, so a value and its binding
/// never claim the same width by fiat.
let private declaredKindOf (nodes: Map<NodeId, SemanticNode>) (node: SemanticNode) : NTUKind option =
    match node.Kind with
    | SemanticKind.VarRef (_, Some defId) ->
        match Map.tryFind defId nodes with
        | Some def when isIntegerNode def -> Types.tryGetNTUKind def.Type
        | _ -> Types.tryGetNTUKind node.Type
    | _ -> Types.tryGetNTUKind node.Type

/// The selection for a node: a spelled site selects the representation its declaration names
/// (`RangeSources.declarationOfKind`, the interim declared boundary of CS-12 step 5a; its
/// coverage is `spelledDiagnostics`, CCS8012); the bare kind selects by its range.
let private selectNode (ctx: PlatformContext) (nodes: Map<NodeId, SemanticNode>) (node: SemanticNode) (range: ValueRange) : Selection =
    match declaredKindOf nodes node with
    | Some kind when (RangeSources.declarationOfKind (Some ctx) kind).IsSome ->
        { Representation = RangeSources.representationOfKind ctx kind; Covered = true }
    | _ -> selectRange ctx range

//-------------------------------------------------------------------------
// The value-call boundary (Dimensional_Range_Design.md, ruling 1; §4.1 second row; CS-11 slice 1)
//-------------------------------------------------------------------------

/// Where a node sits at the boundary a declaration, not the range, fixes.
[<RequireQualifiedAccess>]
type private Boundary =
    /// A parameter of an escaping lambda, or of a declaration root: the closure calling
    /// convention, or the exported entry's ABI, at the declared Register width.
    | Parameter of lambdaId: NodeId
    /// The result of such a lambda (its body, or the last value of its body through a block or
    /// an annotation): held at the Register width for the same reason.
    | Result of lambdaId: NodeId
    /// A call through a function value, or a direct call to a lambda that also escapes: the
    /// call site cannot know which lambda it reaches, so its result is the word's.
    | ValueCall

/// The lambdas of the graph's declaration roots (an entry point, an exported function), whose
/// parameters and results are ABI-governed (§1.1 last bullet, §4.1 second row).
let private rootLambdas (nodes: Map<NodeId, SemanticNode>) (roots: (NodeId * DeclRoot) list) : Set<NodeId> =
    roots
    |> List.collect (fun (rootId, _) ->
        match Map.tryFind rootId nodes with
        | Some { Kind = SemanticKind.Lambda _ } -> [ rootId ]
        | Some { Kind = SemanticKind.Binding _ } -> lambdaOf nodes rootId |> Option.map (fun (l, _, _) -> l) |> Option.toList
        | Some { Kind = SemanticKind.ModuleDef (_, members) } ->
            members
            |> List.choose (fun memberId ->
                match Map.tryFind memberId nodes with
                | Some { Kind = SemanticKind.Binding (_, _, _, Some DeclRoot.HardwareModule) } -> None
                | Some { Kind = SemanticKind.Binding (_, _, _, Some _) } -> lambdaOf nodes memberId |> Option.map (fun (l, _, _) -> l)
                | Some { Kind = SemanticKind.Binding ("main", _, _, None) } -> lambdaOf nodes memberId |> Option.map (fun (l, _, _) -> l)
                | _ -> None)
        | _ -> [])
    |> Set.ofList

/// The lambda whose result this node is: the lambda's body, or the last value of the body
/// through a block's last child or an annotation.
let rec private lambdaOfResult (nodes: Map<NodeId, SemanticNode>) (id: NodeId) : NodeId option =
    match Map.tryFind id nodes |> Option.bind (fun n -> n.Parent) with
    | Some parentId ->
        match Map.tryFind parentId nodes with
        | Some { Kind = SemanticKind.Lambda (_, body, _, _, _) } when body = id -> Some parentId
        | Some { Kind = SemanticKind.Sequential ids } when List.tryLast ids = Some id -> lambdaOfResult nodes parentId
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } when inner = id -> lambdaOfResult nodes parentId
        | _ -> None
    | None -> None

/// The boundary a node sits at, if any, read from the graph's structure: `escaping` is the
/// escaping-lambda map (`Program.EscapingLambdas`, written to the graph as `Escaping`) and `roots`
/// the declaration roots' lambdas. A call is through a value when its root is no lambda named
/// directly or applied in place (a parameter, a field, a tuple element, an unresolved reference),
/// when the lambda it names also escapes, or when it hands surplus arguments to the value its
/// body returns.
let private boundaryOf (nodes: Map<NodeId, SemanticNode>) (escaping: Map<NodeId, string>) (roots: Set<NodeId>) (node: SemanticNode) : Boundary option =
    let bounded (lambdaId: NodeId) = Map.containsKey lambdaId escaping || Set.contains lambdaId roots
    // The result position comes first, whatever the node's kind: the body of an escaping lambda
    // is at the word even when it is itself a direct call (Baker's eta-expanded lambda for a named
    // function in value position has exactly that body, `f _eta0`), so that the value the caller
    // reads through the closure pair and the value the body returns are one width (ruling 1).
    match lambdaOfResult nodes node.Id with
    | Some lambdaId when bounded lambdaId -> Some (Boundary.Result lambdaId)
    | _ ->
    match node.Kind with
    | SemanticKind.PatternBinding _ ->
        match node.Parent |> Option.bind (fun p -> Map.tryFind p nodes) with
        | Some { Id = lambdaId; Kind = SemanticKind.Lambda (parameters, _, _, _, _) }
            when bounded lambdaId && parameters |> List.exists (fun (_, _, id) -> id = node.Id) -> Some (Boundary.Parameter lambdaId)
        | _ -> None
    | SemanticKind.Application (funcId, args) ->
        let (rootId, allArgs) = flattenApplication nodes funcId args
        match Map.tryFind rootId nodes with
        | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.FnPtr; Operation = "invoke" } } -> Some Boundary.ValueCall
        | Some { Kind = SemanticKind.Intrinsic _ } -> None
        | Some { Kind = SemanticKind.Lambda (parameters, _, _, _, _) } ->
            if bounded rootId || allArgs.Length > parameters.Length then Some Boundary.ValueCall else None
        | Some { Kind = SemanticKind.VarRef (_, Some defId) } ->
            match lambdaOf nodes defId with
            | Some (lambdaId, parameters, _) ->
                if bounded lambdaId || allArgs.Length > parameters.Length then Some Boundary.ValueCall else None
            | None ->
                // a binding that is no lambda: a function value, or a binding descriptor
                // (a boundary call, whose result is the declaration's, CS-12); both sit at the word
                Some Boundary.ValueCall
        | Some { Kind = SemanticKind.VarRef (_, None) } -> Some Boundary.ValueCall
        | Some _ -> Some Boundary.ValueCall
        | None -> None
    | _ -> None

/// The representation the Register boundary holds a range in: the offered representation of the
/// family the range's sign selects (§3.1) at the declared Register width; None where the
/// description declares no Register or offers no integer representation at it.
let private registerRepresentation (ctx: PlatformContext) (range: ValueRange) : NumericRepresentation option =
    match PlatformContext.tryWidth ctx (WidthDimension.name WidthDimension.Register) with
    | Result.Ok bits ->
        let family = familyOf ctx range
        offeredIntegers ctx family
        |> List.tryFind (fun r -> r.Bits = bits)
        |> Option.orElse (offeredIntegers ctx "int" |> List.tryFind (fun r -> r.Bits = bits))
    | Result.Error _ -> None

//-------------------------------------------------------------------------
// CCS8011, CCS8012
//-------------------------------------------------------------------------

/// The spelling of the value at a node, for the diagnostic.
let rec private spelling (program: Program) (node: SemanticNode) : string option =
    match node.Kind with
    | SemanticKind.VarRef (name, _) -> Some name
    | SemanticKind.Binding (name, _, _, _) -> Some name
    | SemanticKind.PatternBinding name -> Some name
    | SemanticKind.FieldGet (exprId, field) ->
        Map.tryFind exprId program.Reachable
        |> Option.bind (spelling program)
        |> Option.map (fun s -> s + "." + field)
        |> Option.orElse (Some field)
    | SemanticKind.TupleGet (tupleId, index) ->
        Map.tryFind tupleId program.Reachable
        |> Option.bind (spelling program)
        |> Option.map (fun s -> sprintf "%s.Item%d" s (index + 1))
    | SemanticKind.IndexGet (exprId, _) ->
        Map.tryFind exprId program.Reachable
        |> Option.bind (spelling program)
        |> Option.map (fun s -> sprintf "%s.[…]" s)
    | SemanticKind.Application (funcId, _) ->
        match Map.tryFind funcId program.Reachable with
        | Some { Kind = SemanticKind.VarRef (name, _) } -> Some (name + " …")
        | Some { Kind = SemanticKind.Intrinsic info } ->
            let op =
                match info.Operation with
                | "op_Addition" -> "+" | "op_Subtraction" -> "-" | "op_Multiply" -> "*" | "op_Division" -> "/"
                | "op_Modulus" -> "%" | "op_UnaryNegation" -> "-" | "op_LeftShift" -> "<<<" | "op_RightShift" -> ">>>"
                | "op_BitwiseAnd" -> "&&&" | "op_BitwiseOr" -> "|||" | "op_ExclusiveOr" -> "^^^"
                | other -> other
            Some (sprintf "the result of '%s'" op)
        | Some { Kind = SemanticKind.Application _ } | Some { Kind = SemanticKind.TypeAnnotation _ } ->
            let (rootId, _) = flattenApplication program.Reachable funcId []
            match Map.tryFind rootId program.Reachable with
            | Some { Kind = SemanticKind.VarRef (name, _) } -> Some (name + " …")
            | _ -> None
        | _ -> None
    | _ -> None

/// The nearest enclosing binding of a node (a binding's is itself; a parameter's is its
/// function's), and the nearest enclosing function binding.
let private enclosing (program: Program) (node: SemanticNode) : SemanticNode option * SemanticNode option =
    let rec up (id: NodeId option) (binding: SemanticNode option) =
        match id with
        | None -> (binding, None)
        | Some i ->
            match Map.tryFind i program.Reachable with
            | Some ({ Kind = SemanticKind.Binding _ } as b) ->
                let isFunction = lambdaOf program.Reachable b.Id |> Option.isSome
                if isFunction then ((match binding with Some _ -> binding | None -> Some b), Some b)
                else up (Map.tryFind i program.Parents) (match binding with Some _ -> binding | None -> Some b)
            | Some _ -> up (Map.tryFind i program.Parents) binding
            | None -> (binding, None)
    match node.Kind with
    | SemanticKind.Binding _ when (lambdaOf program.Reachable node.Id).IsNone ->
        let (_, func) = up (Map.tryFind node.Id program.Parents) None
        (Some node, func)
    | _ -> up (Map.tryFind node.Id program.Parents) None

/// One diagnostic per enclosing binding, at the first qualifying node in node order; `make`
/// receives the node, the value's spelling and the " in 'f'" suffix.
let private oncePerBinding (program: Program) (nodes: SemanticNode list) (make: SemanticNode -> string -> string -> Diagnostic) : Diagnostic list =
    nodes
    |> List.fold (fun (reported: Set<NodeId option>, acc) node ->
        let (binding, func) = enclosing program node
        let key = binding |> Option.map (fun b -> b.Id)
        if Set.contains key reported then (reported, acc)
        else
            let bindingName = binding |> Option.bind (spelling program)
            let name = spelling program node |> Option.orElse bindingName |> Option.defaultValue "this value"
            let where =
                match func |> Option.bind (spelling program) with
                | Some f -> sprintf " in '%s'" f
                | None -> ""
            (Set.add key reported, make node name where :: acc)) (Set.empty, [])
    |> snd
    |> List.rev

/// Why a parameter nothing supplies is unobservable, when the pass can say: its lambda escapes as
/// a value and no call through a value reaches it, or it is a declaration root's and takes the
/// declared boundary range at CS-12.
let private parameterReason (program: Program) (node: SemanticNode) : string option =
    match node.Kind with
    | SemanticKind.PatternBinding _ when Set.contains node.Id program.Parameters ->
        let supplied = Map.tryFind node.Id program.CallArguments |> Option.exists (List.isEmpty >> not)
        let seeded = Map.tryFind node.Id program.IndexSeeds |> Option.exists (List.isEmpty >> not)
        if supplied || seeded then None
        else
            match Map.tryFind node.Id program.Escaping, Map.tryFind node.Id program.RootParameters with
            | Some why, _ when why.StartsWith "handed to" -> Some (sprintf ": its function is %s" why)
            | Some why, _ -> Some (sprintf ": its function is %s and no call through a value reaches it" why)
            | None, Some _ -> Some ": its function is a declaration root and the parameter's range is the declared boundary's (CS-12)"
            | None, None -> Some ": no reachable call supplies it"
    | _ -> None

/// Why a field read is unobservable, when the pass can say: no descriptor declares the field's
/// representation (ruling 4 of CS-12: the declaration is owed, never invented).
let private fieldReason (program: Program) (node: SemanticNode) : string option =
    match node.Kind with
    | SemanticKind.FieldGet (exprId, field) ->
        match Map.tryFind exprId program.Reachable with
        | Some { Type = NativeType.TApp (tycon, _) } ->
            let declared = Map.tryFind (NominalTypeIdentity.ofConstructor tycon) program.InputSeeds |> Option.exists (Map.containsKey field)
            if declared then None
            else Some (sprintf ": no descriptor declares the representation of field '%s' of '%s'" field tycon.Name)
        | _ -> None
    | _ -> None

/// CCS8011 for every reachable integer whose range has no width: once per enclosing binding, at
/// the first such node in node order, naming the value. A reference whose own binding is
/// unobservable is that binding's finding, not a second one, and so is a binding that merely
/// names such a reference (`let _ = acc`). A parameter of a lambda reached only through a function
/// value names the escape.
let private unobservableDiagnostics (program: Program) (state: State) : Diagnostic list =
    let unobservable (id: NodeId) =
        match Map.tryFind id state with
        | Some r -> not (ValueRange.isObservable r)
        | None -> false
    let aliasOfUnobservable (id: NodeId) =
        match Map.tryFind id program.Reachable with
        | Some { Kind = SemanticKind.VarRef (_, Some defId) } -> unobservable defId
        | _ -> false
    // An unobservable range has no width on any substrate: no representation is
    // selected for it and no carrier is supplied in its place (§1.3).
    let severity = NativeDiagnosticSeverity.Error
    program.Ordered
    |> List.filter (fun node ->
        program.CommitmentSites.Contains node.Id && isIntegerNode node
        && unobservable node.Id
        && (match node.Kind with
            | SemanticKind.VarRef (_, Some defId) -> not (unobservable defId)
            | SemanticKind.Binding _ -> not (List.tryLast node.Children |> Option.exists aliasOfUnobservable)
            | _ -> true))
    |> fun nodes ->
        oncePerBinding program nodes (fun node name where ->
            let reason = parameterReason program node |> Option.orElse (fieldReason program node) |> Option.defaultValue ""
            { Severity = severity
              Code = DiagnosticCodes.CCS8011_UnobservableRange
              Message = sprintf "The range of '%s'%s cannot be observed%s; bound it with a comparison, a modulus or a clamp" name where reason
              Range = node.Range
              RelatedNodes = [ node.Id ]
              Reachability = ReachabilityContext.Reachable })

/// CCS8012 for every reachable integer of the bare kind whose bounded range no declared integer
/// representation covers (§4.2): a required conformance error, naming the range and the
/// widest representation selected in its place; once per enclosing binding. Only on a context that
/// declares integer representations (fabric declares none and synthesises the exact width).
let private coverageDiagnostics (program: Program) (state: State) : Diagnostic list =
    match program.Context with
    | Some ctx when not program.Fabric && not (List.isEmpty (offeredIntegers ctx "int" @ offeredIntegers ctx "uint")) ->
        let uncovered (node: SemanticNode) =
            match Map.tryFind node.Id state with
            | Some r when ValueRange.isObservable r ->
                let s = selectNode ctx program.Reachable node r
                if s.Covered then None else s.Representation |> Option.map (fun rep -> (r, rep))
            | _ -> None
        let reported =
            program.Ordered
            |> List.filter (fun node ->
                program.CommitmentSites.Contains node.Id && isIntegerNode node
                && (match node.Kind with
                    | SemanticKind.VarRef (_, Some defId) -> Map.tryFind defId program.Reachable |> Option.exists (fun d -> (uncovered d).IsNone)
                    | _ -> true))
            |> List.choose (fun node -> uncovered node |> Option.map (fun found -> (node.Id, found)))
            |> Map.ofList
        program.Ordered
        |> List.filter (fun node -> Map.containsKey node.Id reported)
        |> fun nodes ->
            oncePerBinding program nodes (fun node name where ->
                let (r, rep) = Map.find node.Id reported
                { Severity = NativeDiagnosticSeverity.Error
                  Code = DiagnosticCodes.CCS8012_RangeNotCovered
                  Message =
                    sprintf "The range %s of '%s'%s is not covered by any integer representation the platform description of '%s' declares; the widest, '%s' (%d bits, %s), is insufficient; bound the value with a comparison, a modulus or a clamp, or declare a wider representation"
                        (ValueRange.render r) name where ctx.PlatformId rep.Name rep.Bits
                        (RangeSources.declaredRange rep |> Option.map ValueRange.render |> Option.defaultValue "?")
                  Range = node.Range
                  RelatedNodes = [ node.Id ]
                  Reachability = ReachabilityContext.Reachable })
    | _ -> []

/// CCS8012 at the value-call boundary (ruling 1, §4.2): a parameter or a result of an escaping
/// lambda (or of a declaration root) whose bounded range leaves the declared range of the
/// Register representation, naming the value, the lambda, the range and the representation, with
/// the two remedies. An unobservable one stays CCS8011; no CCS8014 fires here, since there is no
/// developer declaration to tighten and it would fire on every closure.
let private boundaryDiagnostics (program: Program) (state: State) : Diagnostic list =
    match program.Context with
    | Some ctx when not program.Fabric ->
        let roots = rootLambdas program.Reachable program.Graph.DeclarationRoots
        let lambdaName (lambdaId: NodeId) =
            Map.tryFind lambdaId program.Reachable
            |> Option.bind (fun l -> l.Parent)
            |> Option.bind (fun p -> Map.tryFind p program.Reachable)
            |> Option.bind (spelling program)
            |> Option.defaultValue (sprintf "the lambda at node %d" (NodeId.value lambdaId))
        let uncovered (node: SemanticNode) =
            match Map.tryFind node.Id state with
            | Some r when ValueRange.isObservable r && isIntegerNode node ->
                match boundaryOf program.Reachable program.EscapingLambdas roots node with
                | Some (Boundary.Parameter lambdaId) | Some (Boundary.Result lambdaId) ->
                    match registerRepresentation ctx r with
                    | Some rep when not (RangeSources.declaredRange rep |> Option.exists (fun d -> ValueRange.contains d r)) -> Some (lambdaId, r, rep)
                    | _ -> None
                | _ -> None
            | _ -> None
        program.Ordered
        |> List.filter (fun node -> program.CommitmentSites.Contains node.Id)
        |> List.choose (fun node -> uncovered node |> Option.map (fun found -> (node, found)))
        |> fun found ->
            let byNode = found |> List.map (fun (n, f) -> (n.Id, f)) |> Map.ofList
            oncePerBinding program (found |> List.map fst) (fun node name where ->
                let (lambdaId, r, rep) = Map.find node.Id byNode
                let why = Map.tryFind lambdaId program.EscapingLambdas |> Option.map (sprintf ", which is %s,") |> Option.defaultValue ", a declaration root,"
                { Severity = NativeDiagnosticSeverity.Error
                  Code = DiagnosticCodes.CCS8012_RangeNotCovered
                  Message =
                    sprintf "The range %s of '%s'%s is not covered by '%s' (%d bits, %s), the representation of the platform description of '%s' at its declared Register width, the calling convention of '%s'%s so its parameters and result sit at the word; bound the value with a comparison, a modulus or a clamp, or change the declaration"
                        (ValueRange.render r) name where rep.Name rep.Bits
                        (RangeSources.declaredRange rep |> Option.map ValueRange.render |> Option.defaultValue "?")
                        ctx.PlatformId (lambdaName lambdaId) why
                  Range = node.Range
                  RelatedNodes = [ node.Id ]
                  Reachability = ReachabilityContext.Reachable })
    | _ -> []

/// CCS8012 and CCS8014 at a declared boundary (§4.2; ruling 1 of CS-12): a value stored into a
/// wire field whose layout descriptor declares its representation, or passed to an extern
/// parameter whose binding descriptor declares it, lies within the declared range or is CCS8012
/// at the value, naming the range, the declaration and the two remedies; and where every value
/// that crosses lies within a narrower offered representation than the declared one, CCS8014
/// information at the declaration, since here, unlike the closure boundary, the developer can
/// tighten it. An unobservable value stays CCS8011.
let private declaredDiagnostics (program: Program) (state: State) : Diagnostic list =
    match program.Context with
    | Some ctx when not program.Fabric ->
        let ranged (values: (NodeId * NodeId) list) =
            values |> List.filter (fun (consumer, _) -> program.CommitmentSites.Contains consumer)
            |> List.map (fun (consumer, v) -> v, read program (current state) consumer v)
        let leaving (declared: ValueRange) (values: (NodeId * ValueRange) list) =
            values |> List.filter (fun (_, r) -> ValueRange.isObservable r && not (ValueRange.contains declared r))
        let tightening (declared: ValueRange) (bits: int) (values: (NodeId * ValueRange) list) : (ValueRange * NumericRepresentation) option =
            let joined = values |> List.fold (fun acc (_, r) -> ValueRange.join acc r) ValueRange.Empty
            match joined with
            | ValueRange.Empty -> None
            | _ when not (ValueRange.isObservable joined) || not (ValueRange.contains declared joined) -> None
            | _ ->
                match (selectRange ctx joined).Representation with
                | Some r when r.Bits < bits -> Some (joined, r)
                | _ -> None
        let at (nodeId: NodeId) (severity: NativeDiagnosticSeverity) (code: string) (message: string) : Diagnostic option =
            SemanticGraph.tryGetNode nodeId program.Graph
            |> Option.map (fun node ->
                { Severity = severity; Code = code; Message = message; Range = node.Range; RelatedNodes = [ node.Id ]
                  Reachability = (if node.IsReachable then ReachabilityContext.Reachable else ReachabilityContext.Unknown) })
        let fields =
            program.DeclaredFields
            |> List.collect (fun (typeName, f) ->
                let values =
                    Map.tryFind typeName program.Constructions
                    |> Option.defaultValue []
                    |> List.collect (fun (recordId, fs) -> fs |> List.filter (fun (n, _) -> n = f.Name) |> List.map (fun (_, v) -> recordId, v))
                    |> ranged
                let uncovered =
                    leaving f.Range values
                    |> List.choose (fun (v, r) ->
                        at v NativeDiagnosticSeverity.Error DiagnosticCodes.CCS8012_RangeNotCovered
                            (sprintf "The range %s of the value stored into field '%s' of '%s' is not covered by its declared representation '%s' (%d bits, %s); bound the value with a comparison, a modulus or a clamp, or change the declaration"
                                (ValueRange.render r) f.Name (NominalTypeIdentity.display typeName) f.Repr f.Bits (ValueRange.render f.Range)))
                let wider =
                    tightening f.Range f.Bits values
                    |> Option.bind (fun (joined, r) ->
                        at f.Node NativeDiagnosticSeverity.Info DiagnosticCodes.CCS8014_RepresentationWiderThanRange
                            (sprintf "The field '%s' of '%s' is declared '%s' (%d bits, %s); every value stored lies within %s, which '%s' (%d bits) holds; the declaration can be tightened"
                                f.Name (NominalTypeIdentity.display typeName) f.Repr f.Bits (ValueRange.render f.Range) (ValueRange.render joined) r.Name r.Bits))
                uncovered @ Option.toList wider)
        let parameters =
            program.DeclaredParameters
            |> List.collect (fun (paramId, d) ->
                let values = Map.tryFind paramId program.CallArguments |> Option.defaultValue [] |> ranged
                let owner =
                    Map.tryFind paramId program.Reachable
                    |> Option.bind (fun p -> p.Parent)
                    |> Option.bind (fun l -> Map.tryFind l program.Reachable)
                    |> Option.bind (fun l -> l.Parent)
                    |> Option.bind (fun b -> Map.tryFind b program.Reachable)
                    |> Option.bind (spelling program)
                    |> Option.defaultValue "the extern"
                let uncovered =
                    leaving d.Range values
                    |> List.choose (fun (v, r) ->
                        at v NativeDiagnosticSeverity.Error DiagnosticCodes.CCS8012_RangeNotCovered
                            (sprintf "The range %s of the argument passed to parameter '%s' of '%s' is not covered by its declared representation (%d bits, %s) in the binding descriptor; bound the value with a comparison, a modulus or a clamp, or change the declaration"
                                (ValueRange.render r) d.Name owner d.Bits (ValueRange.render d.Range)))
                let wider =
                    tightening d.Range d.Bits values
                    |> Option.bind (fun (joined, r) ->
                        at d.Node NativeDiagnosticSeverity.Info DiagnosticCodes.CCS8014_RepresentationWiderThanRange
                            (sprintf "The parameter '%s' of '%s' is declared at %d bits (%s); every argument lies within %s, which '%s' (%d bits) holds; the declaration can be tightened"
                                d.Name owner d.Bits (ValueRange.render d.Range) (ValueRange.render joined) r.Name r.Bits))
                uncovered @ Option.toList wider)
        fields @ parameters
    | _ -> []

/// CCS8012 and CCS8014 at a spelled site (CS-12 step 5a; ruling 5: during the alias period a
/// width-named spelling is an interim declared boundary of the same shape as a descriptor's,
/// `RangeSources.declarationOfKind`): a value whose settled range leaves the representation its
/// spelling declares is CCS8012 at the value, once per enclosing binding, naming the range, the
/// declaration and the two remedies; a binding or a parameter whose declared representation is
/// wider than every value it holds needs is CCS8014 information at the declaration. An
/// unobservable value stays CCS8011; a conversion's image lies within its target by construction.
let private spelledDiagnostics (program: Program) (state: State) : Diagnostic list =
    match program.Context with
    | Some ctx when not program.Fabric ->
        // a reference is its binding's value: the binding's finding is the finding
        let declarationOf (node: SemanticNode) =
            match node.Kind with
            | SemanticKind.VarRef (_, Some _) -> None
            | _ when isIntegerNode node -> Types.tryGetNTUKind node.Type |> Option.bind (RangeSources.declarationOfKind (Some ctx))
            | _ -> None
        let leaving =
            program.Ordered
            |> List.filter (fun node -> program.CommitmentSites.Contains node.Id)
            |> List.choose (fun node ->
                match declarationOf node, Map.tryFind node.Id state with
                | Some d, Some r when ValueRange.isObservable r && not (ValueRange.contains d.Range r) -> Some (node, (d, r))
                | _ -> None)
        let byNode = leaving |> List.map (fun (n, f) -> n.Id, f) |> Map.ofList
        let uncovered =
            oncePerBinding program (leaving |> List.map fst) (fun node name where ->
                let (d, r) = Map.find node.Id byNode
                { Severity = NativeDiagnosticSeverity.Error
                  Code = DiagnosticCodes.CCS8012_RangeNotCovered
                  Message =
                    sprintf "The range %s of '%s'%s is not covered by '%s' (%d bits, %s), the representation its width-named spelling declares; bound the value with a comparison, a modulus or a clamp, or write `int` and declare the representation at the boundary"
                        (ValueRange.render r) name where d.Repr d.Bits (ValueRange.render d.Range)
                  Range = node.Range
                  RelatedNodes = [ node.Id ]
                  Reachability = ReachabilityContext.Reachable })
        let wider =
            program.Ordered
            |> List.filter (fun node -> program.CommitmentSites.Contains node.Id)
            |> List.choose (fun node ->
                match node.Kind with
                | SemanticKind.Binding _ | SemanticKind.PatternBinding _ ->
                    match declarationOf node, Map.tryFind node.Id state with
                    | Some d, Some r when ValueRange.isObservable r && r <> ValueRange.Empty && ValueRange.contains d.Range r ->
                        match (selectRange ctx r).Representation with
                        | Some rep when rep.Bits < d.Bits ->
                            Some { Severity = NativeDiagnosticSeverity.Info
                                   Code = DiagnosticCodes.CCS8014_RepresentationWiderThanRange
                                   Message =
                                    sprintf "'%s' is declared '%s' (%d bits, %s) by its width-named spelling; every value it holds lies within %s, which '%s' (%d bits) holds; write `int` and declare the representation at the boundary"
                                        (spelling program node |> Option.defaultValue "the value") d.Repr d.Bits (ValueRange.render d.Range) (ValueRange.render r) rep.Name rep.Bits
                                   Range = node.Range
                                   RelatedNodes = [ node.Id ]
                                   Reachability = ReachabilityContext.Reachable }
                        | _ -> None
                    | _ -> None
                | _ -> None)
        uncovered @ wider
    | _ -> []

//-------------------------------------------------------------------------
// Entry
//-------------------------------------------------------------------------

/// Run the range pass over the reachable graph: every ranged node carries its range, every record
/// type its per-field ranges, every array element type its element range, and every unobservable
/// integer is CCS8011, every uncovered one CCS8012. The graph is returned with the annotations
/// written and the field and element ranges settled.
let private retainSupport (graph: SemanticGraph) (facts: RangeContextFacts) =
    { facts with
        Premises = Clef.Compiler.Baker.Ingredients.NumericValues.rangeContextPremises graph
        CaptureRelations = Clef.Compiler.Baker.Ingredients.NumericValues.captureRelations graph
        SourceRelations = Clef.Compiler.Baker.Ingredients.NumericValues.rangeContextRelations graph
        Platform = Clef.Compiler.Baker.Ingredients.Boundaries.platformPremise graph.Platform
        Roots = graph.DeclarationRoots }

let private runValidated (context: PlatformContext option) (graph: SemanticGraph) : SemanticGraph * Diagnostic list =
    let program = readProgram context graph
    let graph = program.Graph
    // The check-time pass reads the graph the checker built; a lexical body
    // that lists a node the graph lacks is an internal invariant breach, named
    // exactly. Publication-side readers refuse the same case instead.
    let contexts =
        match contextProgram program with
        | Result.Ok contexts -> contexts
        | Result.Error (_, reason) -> invalidOp reason
    let state, contextFacts = fixpoint program contexts
    let nodes =
        graph.Nodes
        |> Map.map (fun id node ->
            match Map.tryFind id state with
            | Some r -> { node with ValueRange = Some r }
            | None -> node)
    let fieldRanges =
        // every record type with an integer field, from its definition; every reachable
        // construction of any record type joins in
        let declared =
            program.IntegerFields
            |> Map.map (fun typeName fields ->
                fields |> List.map (fun f -> f, fieldRange program (current state) typeName f) |> Map.ofList)
        let declared =
            program.InputSeeds
            |> Map.fold (fun (acc: Map<NominalTypeIdentity, Map<string, ValueRange>>) typeName seeds ->
                let existing = Map.tryFind typeName acc |> Option.defaultValue Map.empty
                Map.add typeName (seeds |> Map.fold (fun m f _ -> Map.add f (fieldRange program (current state) typeName f) m) existing) acc) declared
        program.Constructions
        |> Map.fold (fun (acc: Map<NominalTypeIdentity, Map<string, ValueRange>>) typeName constructions ->
            let fields = constructions |> List.collect (snd >> List.map fst) |> List.distinct
            let existing = Map.tryFind typeName acc |> Option.defaultValue Map.empty
            let joined =
                fields
                |> List.fold (fun (m: Map<string, ValueRange>) f ->
                    if Map.containsKey f m then m
                    else
                        let r = fieldRange program (current state) typeName f
                        // only a field whose values are ranged nodes has a range; a nested record
                        // or a boolean-only field contributes nothing here
                        let ranged =
                            constructions
                            |> List.exists (fun (_, cs) -> cs |> List.exists (fun (n, v) -> n = f && Map.containsKey v state))
                        if ranged then Map.add f r m else m) existing
            Map.add typeName joined acc) declared
    let elementRanges =
        let keys = Set.union (program.ElementStores |> Map.toSeq |> Seq.map fst |> Set.ofSeq) (program.ElementSeeds |> Map.toSeq |> Seq.map fst |> Set.ofSeq)
        // the element type behind each key, from any store of it or from an array node of the type
        let typeOfKey (key: TypeIdentity) : NativeType option =
            program.Ordered
            |> List.tryPick (fun n -> arrayElementType n.Type |> Option.filter (fun e -> elementKey e = key))
        keys
        |> Set.toList
        |> List.choose (fun key -> typeOfKey key |> Option.map (fun elem -> key, elementRange program (current state) elem))
        |> Map.ofList
    let resourceDiagnostics = program.LoopRecognition.Linear |> List.filter (fun recurrence ->
        recurrence.Cells |> List.exists program.CommitmentSites.Contains) |> List.choose (fun recurrence ->
        match LoopRecipes.saturateLinear (current state) recurrence with
        | Result.Error LoopRangeResidual.ProofResources ->
            let node = graph.Nodes[recurrence.Cells.Head]
            Some { Severity = NativeDiagnosticSeverity.Error
                   Code = DiagnosticCodes.CCS8011_UnobservableRange
                   Message = sprintf "The finite recurrence proof exceeded its %s-bit aggregate certificate-work budget; numeric range remains pending. This compiler analysis limit supplies no runtime representation or width." (string LoopRecipes.defaultCertificateBits)
                   Range = node.Range; RelatedNodes = LoopRecipes.linearSources recurrence
                   Reachability = ReachabilityContext.Reachable }
        | _ -> None)
    let resourceDiagnostics = resourceDiagnostics @ (program.LoopRecognition.Tail |> List.choose (fun recurrence ->
        match LoopRecipes.saturateTail (current state) recurrence with
        | Result.Error LoopRangeResidual.ProofResources when recurrence.Participants |> List.exists program.CommitmentSites.Contains ->
            let node = graph.Nodes[recurrence.Counter]
            Some { Severity = NativeDiagnosticSeverity.Error; Code = DiagnosticCodes.CCS8011_UnobservableRange
                   Message = "The finite tail-transition proof exceeded its aggregate certificate-work budget; numeric range remains pending."
                   Range = node.Range; RelatedNodes = recurrence.Participants; Reachability = ReachabilityContext.Reachable }
        | _ -> None))
    let diagnostics = unobservableDiagnostics program state @ coverageDiagnostics program state @ boundaryDiagnostics program state @ declaredDiagnostics program state @ spelledDiagnostics program state @ resourceDiagnostics
                      |> contextProvenance contextFacts
    let graph = { graph with Nodes = nodes; FieldRanges = lazy fieldRanges; ElementRanges = lazy elementRanges; Escaping = lazy program.EscapingLambdas }
    let graph = LazyEffectRanges.settle (program.LazyEffects.Values |> Seq.distinctBy _.Cell |> Seq.toList) graph
    let graph = FiniteCellRanges.settle (program.FiniteCells.Values |> Seq.distinctBy _.Cell |> Seq.toList) graph
    let graph = LoopRanges.saturate (current state) program.LoopRecognition graph
    let graph = SequenceAccumulations.saturate (current state) program.SequenceAccumulations graph
    { graph with RangeContextFacts = Some(retainSupport graph contextFacts) }, diagnostics

/// Issue the owner's fixed-point facts for this graph revision. A consumer may
/// request renewal after rewriting passes, but the held annotations, widths,
/// layouts and obligations remain unchanged and must enclose these fresh facts.
let issue (graph: SemanticGraph) : Result<RangeContextFacts, string> =
    match OrdinaryDemand.tryRead graph with
    | Result.Error _ -> Result.Error "Current ordinary binding demand evidence is required before range issuance."
    | Result.Ok _ ->
        let program = readProgram graph.Platform graph
        match contextProgram program with
        | Result.Error (_, reason) -> Result.Error reason
        | Result.Ok contexts ->
            let _, facts = fixpoint program contexts
            let facts = retainSupport graph facts
            facts.SourceRelations |> Result.map (fun _ -> facts)

/// Passive source evidence from the existing context-state/read owner. Numeric
/// recipes consume it without reconstructing guards or executing range transfer.
type ForeignResultEvidence = {
    Application: ForeignResultApplication
    Descriptor: PlatformResolution.DeclaredResultRange option
    Abi: PlatformResolution.DeclaredFunction option
    ResultRange: ValueRange
    Support: NodeId list
    Reads: Set<RangeContext * NodeId>
}

let foreignResultApplications (graph: SemanticGraph) (facts: RangeContextFacts option) : Result<ForeignResultEvidence list, NodeId * string> =
    let facts = facts |> Option.filter (Clef.Compiler.Baker.Ingredients.NumericValues.rangeContextCurrent graph)
    let program = readProgram graph.Platform graph
    let contexts =
        match program.ForeignDeclarationFailure with
        | Some reason -> Result.Error reason
        | None -> contextProgram program
    match contexts with
    | Result.Error reason -> Result.Error reason
    | Result.Ok contexts ->
        let rows = contexts.Coordinates |> List.choose (fun (context, node) ->
            let summarized = context = RangeContext.Shared && contexts.Occurrences.ContainsKey node.Id
            if summarized then None else
            foreignDeclaration program node.Id |> Option.map (fun (declaration, actuals) ->
                let mutable reads = facts |> Option.bind (fun facts -> facts.Reads.TryFind(context, node.Id)) |> Option.defaultValue Set.empty
                let get key =
                    reads <- reads.Add key
                    facts |> Option.bind (fun facts -> facts.Values.TryFind key) |> Option.defaultValue ValueRange.Unbounded
                let value = contextReading contexts get context
                let descriptor = foreignResultDescriptor program declaration
                let arguments = actuals |> List.mapi (fun index actual ->
                    let ranged = program.Reachable.TryFind actual |> Option.exists isRanged
                    { Index = index; Node = actual; Enclosure = if ranged && facts.IsSome then read program value node.Id actual else ValueRange.Unbounded } : ForeignResultArgument)
                let abi = match program.ForeignAbi.TryFind declaration.Body with Some [abi] -> Some abi | _ -> None
                let coordinates = match context with RangeContext.Invocation calls -> calls | RangeContext.Shared -> []
                { Application = { Declaration = declaration.Binding; Call = node.Id; Context = coordinates
                                  Hypothesis = descriptor |> Option.map _.Hypothesis; Arguments = arguments }
                  Descriptor = descriptor; Abi = abi
                  ResultRange = facts |> Option.bind (fun facts -> facts.Values.TryFind(context, node.Id)) |> Option.defaultValue ValueRange.Unbounded
                  Support = declaration.Path @ declaration.Formals @ [declaration.Body; node.Id] @ actuals @
                            (program.ForeignEntryCalls.TryFind node.Id |> Option.map (fun (_, _, transport) -> Set.toList transport) |> Option.defaultValue []) @
                            (descriptor |> Option.map _.Participants |> Option.defaultValue []) @
                            (abi |> Option.map (fun abi -> [abi.Node]) |> Option.defaultValue []) @ (reads |> Set.toList |> List.map snd)
                  Reads = reads }))
        Result.Ok rows

/// Fresh logical source facts for a Baker recipe checking current premises.
/// This computes the existing range rules without publishing annotations,
/// selecting carriers or discharging obligations. Invalid demand supplies no facts.
let sourceFacts (graph: SemanticGraph) : Map<NodeId, ValueRange> =
    match issue graph with
    | Result.Error _ -> Map.empty
    | Result.Ok facts ->
        facts.Values |> Map.toList |> List.choose (function
            | (RangeContext.Shared, id), range -> Some(id, range)
            | _ -> None) |> Map.ofList

/// A closed tail family with zero transitions at every entry never evaluates
/// its continuing call or actuals. Source formals and their ABI positions stay
/// present. This reads current producer evidence; Empty alone is no authority.
let tailInactiveOccurrences (graph: SemanticGraph) =
    match graph.RangeContextFacts with
    | Some facts when Clef.Compiler.Baker.Ingredients.NumericValues.rangeContextCurrent graph facts ->
        let values = facts.Values |> Map.toList |> List.choose (function
            | (RangeContext.Shared, id), range -> Some(id, range)
            | _ -> None) |> Map.ofList
        let subtree id =
            let mutable seen = Set.empty
            let mutable pending = Set.singleton id
            while not pending.IsEmpty do
                let frontier = pending
                seen <- Set.union seen frontier
                pending <- frontier |> Seq.collect (fun current ->
                    graph.Nodes.TryFind current |> Option.map _.Children |> Option.defaultValue [])
                           |> Set.ofSeq |> fun children -> Set.difference children seen
            seen
        (readProgram graph.Platform graph).LoopRecognition.Tail
        |> List.fold (fun excluded item ->
            match LoopRecipes.saturateTail (current values) item with
            | Result.Ok result when not result.Certificates.IsEmpty &&
                                    (result.Certificates |> List.forall (fun (_, _, model) -> model.MaximumIterations = 0I)) ->
                Set.union excluded (subtree item.Call)
            | _ -> excluded) Set.empty
    | _ -> Set.empty

/// Re-read the complete current source call/effect/origin and consumer census
/// before a representation rewrite transports a finite-pull proof. This does
/// not run the range fixed point, publish annotations or select a carrier.
let sequenceAccumulationFacts (graph: SemanticGraph) : SequenceAccumulation.Accumulation list option =
    match OrdinaryDemand.tryRead graph with
    | Result.Error _ -> None
    | Result.Ok _ -> Some (readProgram graph.Platform graph).SequenceAccumulations

/// The commitment sites are the values the settled demand projection retains.
/// A demand relation that disagrees with the current use proof is reported
/// (CCS8403/CCS8415). Withdraw this owner's earlier ranges; no new range is
/// settled over rejected demand, and a former Empty is not current authority.
let run (context: PlatformContext option) (graph: SemanticGraph) : SemanticGraph * Diagnostic list =
    SemanticGraph.withEnrichment graph (fun () ->
        match OrdinaryDemand.tryRead graph with
        | Result.Error failures ->
            let nodes = graph.Nodes |> Map.map (fun _ node ->
                if node.ValueRange.IsSome then { node with ValueRange = None } else node)
            let withdrawn =
                { graph with Nodes = nodes; FieldRanges = lazy Map.empty
                             ElementRanges = lazy Map.empty; Escaping = lazy Map.empty; RangeContextFacts = None }
            withdrawn, OrdinaryDemand.diagnostics graph failures
        | Result.Ok _ -> runValidated context graph)

//-------------------------------------------------------------------------
// Reads for the witnesses (Composer transcribes; it computes no range and no width)
//-------------------------------------------------------------------------

/// The range an operation node works in, for a witness that transcribes it: the join of the
/// operation's operand ranges and its result range, read from the annotations the pass settled
/// (the operand extension and the operation width follow from its width and sign). A read of
/// settled facts, so that no witness computes a range; None when any of them is unannotated.
let private joinOfNodes (nodes: SemanticNode list) : ValueRange option =
    let ranges = nodes |> List.map (fun n -> n.ValueRange)
    if ranges |> List.exists Option.isNone then None
    else Some (ranges |> List.choose id |> List.fold ValueRange.join ValueRange.Empty)

/// The join of an application's operand ranges alone: what a comparison works in (its own result
/// is a boolean and no part of the operands' width).
let operandRange (graph: SemanticGraph) (applicationId: NodeId) : ValueRange option =
    match SemanticGraph.tryGetNode applicationId graph with
    | Some { Kind = SemanticKind.Application (_, argIds) } ->
        joinOfNodes (argIds |> List.choose (fun a -> SemanticGraph.tryGetNode a graph))
    | _ -> None

let operationRange (graph: SemanticGraph) (applicationId: NodeId) : ValueRange option =
    match SemanticGraph.tryGetNode applicationId graph with
    | Some ({ Kind = SemanticKind.Application (_, argIds) } as node) ->
        joinOfNodes (node :: (argIds |> List.choose (fun a -> SemanticGraph.tryGetNode a graph)))
    | _ -> None

/// The range of element `index` of a tuple-valued node, read through the settled annotations of
/// the constructions the node can evaluate to (a reference, a binding, a block, a branch join, an
/// annotation, a named lambda's result); None where the trace is lost.
let tupleElementRange (graph: SemanticGraph) (nodeId: NodeId) (index: int) : ValueRange option =
    let nodes = graph.Nodes
    let rec trace (visited: Set<NodeId>) (id: NodeId) : ValueRange option =
        if Set.contains id visited then Some ValueRange.Empty
        else
            let visited = Set.add id visited
            let joinAll (ids: NodeId list) =
                ids |> List.fold (fun acc i -> match acc, trace visited i with Some a, Some b -> Some (ValueRange.join a b) | _ -> None) (Some ValueRange.Empty)
            match Map.tryFind id nodes with
            | Some { Kind = SemanticKind.TupleExpr ids } -> List.tryItem index ids |> Option.bind (fun e -> Map.tryFind e nodes) |> Option.bind (fun n -> n.ValueRange)
            | Some { Kind = SemanticKind.VarRef (_, Some defId) } -> trace visited defId
            | Some ({ Kind = SemanticKind.Binding _ } as b) -> List.tryLast b.Children |> Option.bind (trace visited)
            | Some ({ Kind = SemanticKind.PatternBinding _ } as b) -> List.tryLast b.Children |> Option.bind (trace visited)
            | Some { Kind = SemanticKind.Sequential ids } -> List.tryLast ids |> Option.bind (trace visited)
            | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> trace visited inner
            | Some { Kind = SemanticKind.IfThenElse (_, t, e) } -> joinAll (t :: Option.toList e)
            | Some { Kind = SemanticKind.Match (_, cases) } -> joinAll (cases |> List.map (fun c -> c.Body))
            | Some { Kind = SemanticKind.CaseElimination (_, arms) } -> joinAll (arms |> List.map (fun a -> a.Body))
            | Some { Kind = SemanticKind.Application (funcId, args) } ->
                let (rootId, _) = flattenApplication nodes funcId args
                match Map.tryFind rootId nodes with
                | Some { Kind = SemanticKind.VarRef (_, Some defId) } -> lambdaOf nodes defId |> Option.bind (fun (_, _, body) -> trace visited body)
                | Some { Kind = SemanticKind.Lambda (_, body, _, _, _) } -> trace visited body
                | _ -> None
            | _ -> None
    trace Set.empty nodeId

/// The escape reason of a lambda that escapes as a value (ruling 1; slice 1), read from the map
/// RangeAnalysis wrote on the graph; None for a lambda that never escapes. Composer reads this
/// for the closure calling convention; every width at that boundary comes through
/// `selectedWidth` / `heldWidth`, never from here.
let escapes (graph: SemanticGraph) (lambdaId: NodeId) : string option =
    Map.tryFind lambdaId graph.Escaping.Value

/// The boundary a node of the settled graph sits at, if any (ruling 1): read from the graph's
/// structure, its escaping map and its declaration roots.
let private boundaryOfNode (graph: SemanticGraph) (node: SemanticNode) : Boundary option =
    boundaryOf graph.Nodes graph.Escaping.Value (rootLambdas graph.Nodes graph.DeclarationRoots) node

/// The declared Register width of the graph's platform, the representation of every value at the
/// value-call boundary (§4.1's second row); None where the description declares none.
let private registerWidth (ctx: PlatformContext) : int option =
    PlatformContext.tryWidth ctx (WidthDimension.name WidthDimension.Register) |> Result.toOption

/// Whether the graph's platform is a core with declared integer representations: the leg that
/// selects from a declared set (§3.1). Fabric, and a description offering no integer
/// representation, hold a value at exactly its range's width.
let private selectsFromDeclared (ctx: PlatformContext) : bool =
    PlatformContext.substrateKind ctx <> SubstrateKind.FPGA
    && not (List.isEmpty (offeredIntegers ctx "int" @ offeredIntegers ctx "uint"))

/// The integer representation a range of the bare kind selects on the graph's platform (§3.1):
/// the offered representation of the sign's family with the fewest bits whose declared range
/// covers the range, or the widest when none does (CCS8012 was reported); None for an
/// unobservable range, or a context declaring no integer representation. A read of the settled
/// range against the declaration. Baker materializes this selection and its
/// declaration/range evidence before publication; witnesses read that carrier.
let selectedRepresentationOf (graph: SemanticGraph) (range: ValueRange) : NumericRepresentation option =
    match graph.Platform with
    | Some ctx when selectsFromDeclared ctx -> (selectRange ctx range).Representation
    | _ -> None

let private numericBoundary graph nodeId =
    CallbackDeclarations.numericBoundary graph nodeId
    |> Option.orElseWith (fun () -> Mmio.numericBoundary graph nodeId)
    |> Option.orElseWith (fun () -> BorrowedViews.numericBoundary graph nodeId)
    |> Option.orElseWith (fun () -> MappedBindings.numericBoundary graph nodeId)

/// A Sequential forwards its final value; it is not a separate scalar store or
/// conversion. Preserve that occurrence's physical carrier, including a call's
/// ABI width, instead of independently narrowing the block from its range.
/// Explicit native declarations still own their boundary. The terminal value's
/// lambdaOfResult reading preserves entry/escaping-result rules through blocks.
let private integerCarrierSource (graph: SemanticGraph) nodeId =
    let rec follow seen id =
        if Set.contains id seen then None else
        match graph.Nodes.TryFind id with
        | None -> None
        | Some node ->
            let declared = if isIntegerNode node then numericBoundary graph id else None
            match node.Kind with
            | SemanticKind.Sequential values when isIntegerNode node && declared.IsNone ->
                if values <> node.Children then None else
                values |> List.tryLast |> Option.bind (fun last ->
                    match graph.Nodes.TryFind last with
                    | Some value when isIntegerNode value && applySubst value.Type = applySubst node.Type ->
                        follow (Set.add id seen) last
                    | _ -> None)
            // An ascription forwards its operand unchanged, exactly as `lastValueOf` and
            // `lambdaOfResult` read it; like a block it is neither a store nor a conversion.
            // Without this a return annotation over a value-call result was re-selected from its
            // own range while the value it forwards stays at the Register width, publishing two
            // carriers for one value with no meet between them (Farscape #108). An annotation
            // whose operand is not the same integer type keeps its own selection.
            | SemanticKind.TypeAnnotation (inner, _) when isIntegerNode node && declared.IsNone ->
                match graph.Nodes.TryFind inner with
                | Some value when isIntegerNode value && applySubst value.Type = applySubst node.Type ->
                    follow (Set.add id seen) inner
                | _ -> Some(node, declared)
            | _ -> Some(node, declared)
    follow Set.empty nodeId

/// The integer representation a node selects on the graph's platform (§3.1), derived on read from
/// the node's range, its carrier, its boundary and the declared representations: at the
/// value-call boundary (ruling 1) the Register representation of the range's sign; a width-named
/// carrier's own; for the bare kind, `selectedRepresentationOf` its range. None for an
/// unobservable range, a context declaring no integer representation, or a node that is not an
/// integer. Transparent integer blocks and ascriptions retain their final value's representation.
/// This source selector is consumed by Baker's carrier settlement;
/// witness consumers use NumericWitnessProjection instead.
let selectedRepresentation (graph: SemanticGraph) (nodeId: NodeId) : NumericRepresentation option =
    match graph.Platform, integerCarrierSource graph nodeId with
    | Some ctx, Some(node, declared) when isIntegerNode node && selectsFromDeclared ctx ->
        match declared with
        | Some declared -> (selectRange ctx declared.Range).Representation
        | None ->
        match node.ValueRange, boundaryOfNode graph node with
        | Some r, Some _ -> registerRepresentation ctx r
        | Some r, None -> (selectNode ctx graph.Nodes node r).Representation
        | None, _ -> None
    | _ -> None

/// The width a range of the bare kind selects on the graph's platform: on fabric, which declares
/// no core, the exact width of the range (§3, `ValueRange.width`); on a core, the bits of the
/// selected representation, or of the widest declared one for a range no representation covers
/// (CCS8012 named it). None for Empty or an unobservable range on any substrate: no width is fabricated for it
/// (C3, width-inference.md §6). None where the graph carries no platform context: no target
/// selects a width, and no substrate's rule is borrowed in its place.
let selectedWidthOf (graph: SemanticGraph) (range: ValueRange) : int option =
    // Empty is an execution-join fact, not a one-bit physical carrier. The
    // inhabited, observable-range prerequisite applies on fabric and cores.
    if range = ValueRange.Empty || not (ValueRange.isObservable range) then None else
    match graph.Platform with
    | Some ctx when selectsFromDeclared ctx ->
        (selectRange ctx range).Representation |> Option.map _.Bits
    | Some _ -> ValueRange.width range
    | None -> None

/// The width a range is held at: exactly its selection. CCS8011 is an error on every substrate
/// (§1.3), so an unobservable range is a stop here, never held at the declared Register width.
/// Source record/union placement and carrier settlement use this rule.
let heldWidthOf (graph: SemanticGraph) (range: ValueRange) : int option =
    selectedWidthOf graph range

/// The width a node's value is selected at on the graph's platform (§3.1, width-inference.md
/// §8): at the value-call boundary (ruling 1: a parameter or the result of a lambda that escapes
/// as a value or is a declaration root, and a call through a value) the declared Register width,
/// regardless of the range; a width-named carrier at its own representation's bits (interim,
/// CS-12), or at the bits its spelling states where the context offers no such representation;
/// otherwise `selectedWidthOf` its range. Transparent integer blocks and ascriptions retain their
/// final value's physical width. None for a node with no range, an invalid block
/// value path, or an unobservable range on a core (see `heldWidth`).
let selectedWidth (graph: SemanticGraph) (nodeId: NodeId) : int option =
    match graph.Platform, integerCarrierSource graph nodeId with
    | Some ctx, Some(node, declared) when isIntegerNode node && PlatformContext.substrateKind ctx <> SubstrateKind.FPGA ->
        match declared with
        | Some declared -> Some declared.Bits
        | None ->
        match boundaryOfNode graph node with
        | Some _ -> registerWidth ctx
        | None ->
            // a spelled site is held at the representation its declaration names (CS-12 step 5a)
            match declaredKindOf graph.Nodes node |> Option.bind (RangeSources.declarationOfKind (Some ctx)) with
            | Some d -> Some d.Bits
            | None -> node.ValueRange |> Option.bind (selectedWidthOf graph)
    | _, Some(node, _) -> node.ValueRange |> Option.bind (selectedWidthOf graph)
    | _ -> None

/// The bits a spelled kind's declaration names on the graph's platform (CS-12 step 5a): the read
/// source carrier settlement makes for a width-named spelling where no node is at hand
/// (a signature, a capture's type); None for the bare kind, whose width is the node's selection.
let declaredWidthOfKind (graph: SemanticGraph) (kind: NTUKind) : int option =
    RangeSources.declarationOfKind graph.Platform kind |> Option.map (fun d -> d.Bits)

/// The physical convention an integer occurrence selects on the graph's platform: the
/// declared representation (`selectedRepresentation`, always one of the platform's declared
/// records, so record equality is identity of the declared convention) paired with the width
/// the value is selected at (`selectedWidth`). None when either is unavailable or when the
/// occurrence's range is Empty, the proved-inactive case `heldWidth` also refuses. The mutable
/// callable storage owner compares this across a family's alternatives and treats None as no
/// agreement; each occurrence's own range and coverage obligation are not part of it.
let selectedConvention (graph: SemanticGraph) (nodeId: NodeId) : (NumericRepresentation * int) option =
    match SemanticGraph.tryGetNode nodeId graph with
    | Some { ValueRange = Some ValueRange.Empty } -> None
    | _ ->
    match selectedRepresentation graph nodeId, selectedWidth graph nodeId with
    | Some representation, Some bits -> Some(representation, bits)
    | _ -> None

/// The width a node's value is held at: `selectedWidth`, or `heldWidthOf` its settled range.
/// Baker's held-carrier rule for each integer node; None is a source stop (a node with
/// no range, an unobservable range, or no platform context).
let heldWidth (graph: SemanticGraph) (nodeId: NodeId) : int option =
    // A declaration can retain its signature width while its proved-inactive
    // occurrence has no held value. Do not reintroduce storage for that join.
    match SemanticGraph.tryGetNode nodeId graph with
    | Some { ValueRange = Some ValueRange.Empty } -> None
    | _ ->
    match selectedWidth graph nodeId with
    | Some bits -> Some bits
    | None ->
        match SemanticGraph.tryGetNode nodeId graph with
        // Failed transparent transport cannot regain a fabricated independent
        // carrier from the wrapper's range after its value path was refused.
        | Some { Kind = SemanticKind.Sequential _ } -> None
        | Some node when isIntegerNode node -> node.ValueRange |> Option.bind (heldWidthOf graph)
        | _ -> None
