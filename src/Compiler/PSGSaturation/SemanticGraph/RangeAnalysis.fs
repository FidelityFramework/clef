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
/// The pass is a least fixed point over an immutable `Map<NodeId, ValueRange>`: a transfer
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
/// A reachable integer whose final range has no width is CCS8011 (§1.3, §7): an error on fabric,
/// where the width has no other source, and information on every other substrate while the
/// migration inventory is open (CS-11 slice 3 records the residual). A bounded range of the bare
/// kind that no declared integer representation covers is CCS8012, a warning promoted by
/// `--warnaserror` (§4.2). Runs on every substrate, over reachable nodes only, after the declared
/// platform has filled the context and before it is checked (NativeService.buildResult).
module Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.NativeTypedTree.Expressions.Types
open Clef.Compiler.NativeTypedTree.Expressions.Intrinsics
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module PlatformResolution = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

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

/// A bound in force on a read: the value read stands in `Relation` to `Bound`'s range.
type private Refinement = { Bound: NodeId; Relation: Relation }

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

/// What the pass reads of the graph, computed once: the reachable nodes, the parent index, the
/// callee of every application, what supplies every parameter, the assignments to every mutable
/// binding, the refinement at every reference, the reachable constructions of every record type
/// and the integer fields its definition declares, the values stored into arrays by element type,
/// and the widening thresholds the platform declares.
type private Program = {
    Graph: SemanticGraph
    Context: PlatformContext option
    Reachable: Map<NodeId, SemanticNode>
    /// Reachable nodes in node order.
    Ordered: SemanticNode list
    Parents: Map<NodeId, NodeId>
    /// An application node -> what it calls and its whole argument list (curried calls flattened).
    Callees: Map<NodeId, Callee * NodeId list>
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
    /// A Lambda parameter node -> its lambda's declaration root, for a root's parameters.
    RootParameters: Map<NodeId, DeclRoot>
    /// A mutable binding -> every value assigned to it.
    Assignments: Map<NodeId, NodeId list>
    /// The bounds in force on a read, by use edge: consumer node -> operand node -> bounds. A
    /// read under a comparison guard is a use edge inside the guarded branch (or the branch edge
    /// of the `if` itself), which is what makes a refinement representable when a node is shared
    /// between the guard and a branch.
    Refinements: Map<NodeId, Map<NodeId, Refinement list>>
    /// A record type name -> its reachable constructions: the construction node and its (field, value) list.
    Constructions: Map<string, (NodeId * (string * NodeId) list) list>
    /// A record type name -> the fields its definition declares at an integer type.
    IntegerFields: Map<string, string list>
    /// The declared inputs of a hardware design (§1.1: an input arrives through a declaration):
    /// the record type of a `[<HardwareModule>]` design's Step inputs parameter, each pin field at
    /// its declared range, a boolean pin `[0, 1]`. No program constructs this record; the pins do.
    InputSeeds: Map<string, Map<string, ValueRange>>
    /// A node whose value a binding descriptor declares (§4.1, the C ABI row; ruling 1 of
    /// CS-12): an extern's parameter node at its declared range, the extern's body at the
    /// declared return. The declaration binds (§4.4); the arguments are checked against it.
    BoundarySeeds: Map<NodeId, ValueRange>
    /// The declared wire fields seeded into `InputSeeds`, for the boundary check (§4.2): the
    /// record type and the field's declaration.
    DeclaredFields: (string * PlatformResolution.DeclaredField) list
    /// The declared extern parameters seeded into `BoundarySeeds`: the parameter node and its
    /// declaration.
    DeclaredParameters: (NodeId * PlatformResolution.DeclaredParameter) list
    /// An array element type (rendered) -> every value stored into an array of that type, as
    /// (the storing node, the value node): an array literal's elements, an indexer or `Array.set`
    /// assignment, `Array.create`'s seed, `Array.init`'s function result.
    ElementStores: Map<string, (NodeId * NodeId) list>
    /// An array element type (rendered) -> the constant seeds stored into it: `Array.zeroCreate`'s
    /// zero, and the unbounded store of an array handed to a boundary call.
    ElementSeeds: Map<string, ValueRange>
    Thresholds: ValueRange.Threshold list
    Fabric: bool
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
let private elementKey (elem: NativeType) : string = formatType (applySubst elem)

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

/// The Lambda a function binding holds, if any (through a type annotation of the value).
let private lambdaOf (reachable: Map<NodeId, SemanticNode>) (bindingId: NodeId) : (NodeId * (string * NativeType * NodeId) list * NodeId) option =
    let rec ofValue (id: NodeId) (depth: int) =
        if depth > 4 then None
        else
            match Map.tryFind id reachable with
            | Some { Kind = SemanticKind.Lambda (parameters, body, _, _, _) } -> Some (id, parameters, body)
            | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> ofValue inner (depth + 1)
            | _ -> None
    match Map.tryFind bindingId reachable with
    | Some ({ Kind = SemanticKind.Binding _ } as binding) ->
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
    | Some { Kind = SemanticKind.Lambda (parameters, body, _, _, _) } -> Some (Callee.Direct (parameters, body), allArgs)
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
            | SemanticKind.Lambda (parameters, body, _, _, _) ->
                let ownedByBinding =
                    match Map.tryFind node.Id parents |> Option.bind (fun p -> Map.tryFind p nodes) with
                    | Some { Kind = SemanticKind.Binding _ } -> true
                    | Some { Kind = SemanticKind.TypeAnnotation _ } ->
                        // `let f : t = fun ...`: the annotation's parent is the binding
                        Map.tryFind node.Id parents
                        |> Option.bind (fun a -> Map.tryFind a parents)
                        |> Option.bind (fun p -> Map.tryFind p nodes)
                        |> Option.exists (fun p -> match p.Kind with SemanticKind.Binding _ -> true | _ -> false)
                    | _ -> false
                if ownedByBinding || Set.contains node.Id calleePositions then None
                else Some { LambdaId = node.Id; Parameters = parameters; Body = body; Offset = 0; Escape = escapeOf nodes parents node.Id }
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
    match Map.tryFind defId program.Reachable with
    | Some { Kind = SemanticKind.Binding (_, false, _, _) } -> true
    | Some { Kind = SemanticKind.PatternBinding _ } -> true
    | _ -> false

let private isMutableDefinition (program: Program) (defId: NodeId) : bool =
    match Map.tryFind defId program.Reachable with
    | Some { Kind = SemanticKind.Binding (_, true, _, _) } -> true
    | _ -> false

let private isLiteralBool (program: Program) (id: NodeId) (value: bool) : bool =
    match Map.tryFind id program.Reachable with
    | Some { Kind = SemanticKind.Literal (NativeLiteral.Bool b) } -> b = value
    | _ -> false

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
        match Map.tryFind guardId program.Reachable with
        | Some { Kind = SemanticKind.Application (funcId, args) } ->
            match intrinsicOf program funcId, args with
            | Some { Module = IntrinsicModule.Operators; Operation = "not" }, [ x ] ->
                atoms program (depth + 1) x (not polarity)
            | Some { Module = IntrinsicModule.Operators; Operation = "op_BooleanAnd" }, [ x; y ] ->
                if polarity then atoms program (depth + 1) x true @ atoms program (depth + 1) y true else []
            | Some { Module = IntrinsicModule.Operators; Operation = "op_BooleanOr" }, [ x; y ] ->
                if polarity then [] else atoms program (depth + 1) x false @ atoms program (depth + 1) y false
            | Some { Module = IntrinsicModule.Operators; Operation = op }, [ x; y ] ->
                match relationOf op with
                | None -> []
                | Some relation ->
                    let relation = if polarity then relation else complement relation
                    let ofSide (side: NodeId) (other: NodeId) (r: Relation) =
                        match Map.tryFind side program.Reachable with
                        | Some { Kind = SemanticKind.VarRef (_, Some defId) } when isImmutableDefinition program defId || isMutableDefinition program defId ->
                            [ (Compared.Definition defId, { Bound = other; Relation = r }) ]
                        | Some { Kind = SemanticKind.Literal _ } -> []
                        | Some _ -> [ (Compared.Node side, { Bound = other; Relation = r }) ]
                        | None -> []
                    ofSide x y relation @ ofSide y x (flip relation)
            | _ -> []
        | Some { Kind = SemanticKind.IfThenElse (g, t, Some e) } ->
            // `g && t` is `if g then t else false`; `g || e` is `if g then true else e`
            if isLiteralBool program e false then
                (if polarity then atoms program (depth + 1) g true @ atoms program (depth + 1) t true else [])
            elif isLiteralBool program t true then
                (if polarity then [] else atoms program (depth + 1) g false @ atoms program (depth + 1) e false)
            else []
        | Some { Kind = SemanticKind.VarRef (_, Some defId) } ->
            match Map.tryFind defId program.Reachable with
            | Some ({ Kind = SemanticKind.Binding (_, false, _, _) } as binding) ->
                match List.tryLast binding.Children with
                | Some valueId -> atoms program (depth + 1) valueId polarity
                | None -> []
            | _ -> []
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> atoms program (depth + 1) inner polarity
        | _ -> []

/// The descendants of a node through its children, the node included.
let private subtreeOf (program: Program) (rootId: NodeId) : Set<NodeId> =
    let rec walk (acc: Set<NodeId>) (id: NodeId) =
        if Set.contains id acc then acc
        else
            match Map.tryFind id program.Reachable with
            | None -> acc
            | Some node -> node.Children |> List.fold walk (Set.add id acc)
    walk Set.empty rootId

/// The bounds among `bounds` that a read of `operand` is subject to: through a reference, the
/// bounds on its binding; of a binding itself (a reference's own read of its definition), the
/// bounds on that binding; otherwise the bounds on that very node.
let private boundsOn (program: Program) (bounds: (Compared * Refinement) list) (operand: NodeId) : Refinement list =
    let keys =
        match Map.tryFind operand program.Reachable with
        | Some { Kind = SemanticKind.VarRef (_, Some defId) } -> [ Compared.Definition defId ]
        | Some { Kind = SemanticKind.Binding _ } | Some { Kind = SemanticKind.PatternBinding _ } -> [ Compared.Definition operand; Compared.Node operand ]
        | _ -> [ Compared.Node operand ]
    bounds |> List.filter (fun (k, _) -> List.contains k keys) |> List.map snd

let private addEdge (consumer: NodeId) (operand: NodeId) (refs: Refinement list)
                    (acc: Map<NodeId, Map<NodeId, Refinement list>>) : Map<NodeId, Map<NodeId, Refinement list>> =
    if List.isEmpty refs then acc
    else
        let edges = Map.tryFind consumer acc |> Option.defaultValue Map.empty
        let existing = Map.tryFind operand edges |> Option.defaultValue []
        Map.add consumer (Map.add operand (existing @ refs) edges) acc

/// The mutable definitions assigned anywhere in a subtree (a `Set` whose target is a reference
/// to the definition), for the loop rule below.
let private assignedWithin (program: Program) (rootId: NodeId) : Set<NodeId> =
    let rec walk (acc: Set<NodeId>) (id: NodeId) =
        match Map.tryFind id program.Reachable with
        | None -> acc
        | Some node ->
            let acc =
                match node.Kind with
                | SemanticKind.Set (targetId, _) ->
                    match Map.tryFind targetId program.Reachable with
                    | Some { Kind = SemanticKind.VarRef (_, Some defId) } -> Set.add defId acc
                    | _ -> acc
                | _ -> acc
            node.Children |> List.fold walk acc
    walk Set.empty rootId

/// The refinements a guarded subtree's use edges carry. The subtree is walked in evaluation
/// order; every read (a node's child, a reference's binding) by a node exclusive to the subtree
/// (not also in `excluded`: the guard, the other branch) of a compared binding or node carries
/// the bound. A mutable binding's bound holds only until the first assignment to it in the
/// subtree (the value assigned is evaluated before the store, so it still carries the bound),
/// and never inside a nested lambda, whose body runs at some other time.
let private refineEdges (program: Program) (rootId: NodeId) (excluded: Set<NodeId>) (bounds: (Compared * Refinement) list)
                        (acc: Map<NodeId, Map<NodeId, Refinement list>>) : Map<NodeId, Map<NodeId, Refinement list>> =
    if List.isEmpty bounds then acc
    else
        let mutableDefs =
            bounds |> List.choose (fun (k, _) -> match k with Compared.Definition d when isMutableDefinition program d -> Some d | _ -> None) |> Set.ofList
        let live (assigned: Set<NodeId>) (inLambda: bool) (refs: Refinement list) (operand: NodeId) =
            match Map.tryFind operand program.Reachable with
            | Some { Kind = SemanticKind.VarRef (_, Some defId) } when Set.contains defId mutableDefs ->
                if Set.contains defId assigned || inLambda then [] else refs
            | _ -> refs
        // walk: (assigned mutable definitions so far, edges) -> node -> the same
        let rec walk (inLambda: bool) (state: Set<NodeId> * Map<NodeId, Map<NodeId, Refinement list>>) (id: NodeId) =
            let (assigned, edges) = state
            match Map.tryFind id program.Reachable with
            | None -> state
            | Some node ->
                let exclusive = not (Set.contains id excluded)
                let reads =
                    match node.Kind with
                    | SemanticKind.VarRef (_, Some defId) -> [ defId ]
                    | _ -> node.Children
                // A reference to a compared mutable that has been assigned since the guard (or that
                // is read inside a lambda) reads its definition unrefined: the bound is dead on the
                // reference's own edge to its definition, not only on the edges that read the
                // reference.
                let deadReference =
                    match node.Kind with
                    | SemanticKind.VarRef (_, Some defId) when Set.contains defId mutableDefs -> Set.contains defId assigned || inLambda
                    | _ -> false
                let edges =
                    if exclusive && not deadReference then
                        reads |> List.fold (fun e operand ->
                            addEdge id operand (live assigned inLambda (boundsOn program bounds operand) operand) e) edges
                    else edges
                match node.Kind with
                | SemanticKind.Set (targetId, valueId) ->
                    let (assigned, edges) = walk inLambda (assigned, edges) valueId
                    match Map.tryFind targetId program.Reachable with
                    | Some { Kind = SemanticKind.VarRef (_, Some defId) } -> (Set.add defId assigned, edges)
                    | _ -> (assigned, edges)
                | SemanticKind.Lambda _ -> node.Children |> List.fold (walk true) (assigned, edges)
                | SemanticKind.WhileLoop _ ->
                    // A loop nested in the guarded subtree runs its iterations without re-checking
                    // this guard: a compared mutable it assigns anywhere in its body is unbound from
                    // the loop's first read, not from its first assignment in tree order (the
                    // CS-10 review's `if n < 100 then while c < 5 do (read n; n <- n + 50; ...)`).
                    let deadFromHere = Set.intersect (assignedWithin program id) mutableDefs
                    node.Children |> List.fold (walk inLambda) (Set.union assigned deadFromHere, edges)
                | _ -> node.Children |> List.fold (walk inLambda) (assigned, edges)
        snd (walk false (Set.empty, acc) rootId)

/// The refinements of the whole program: for every reachable `if`, the guard's bounds on the
/// then-branch's reads and their complements on the else-branch's, the `if`'s own read of each
/// branch included; for every `while`, the guard's bounds on the body's reads.
let private refinementsOf (program: Program) : Map<NodeId, Map<NodeId, Refinement list>> =
    program.Ordered
    |> List.fold (fun acc node ->
        match node.Kind with
        | SemanticKind.IfThenElse (guardId, thenId, elseId) ->
            let positive = atoms program 0 guardId true
            let negative = atoms program 0 guardId false
            if List.isEmpty positive && List.isEmpty negative then acc
            else
                let guardSet = subtreeOf program guardId
                let thenSet = subtreeOf program thenId
                let elseSet = elseId |> Option.map (subtreeOf program) |> Option.defaultValue Set.empty
                let acc = refineEdges program thenId (Set.union guardSet elseSet) positive acc
                let acc = addEdge node.Id thenId (boundsOn program positive thenId) acc
                match elseId with
                | Some e ->
                    let acc = refineEdges program e (Set.union guardSet thenSet) negative acc
                    addEdge node.Id e (boundsOn program negative e) acc
                | None -> acc
        | SemanticKind.WhileLoop (guardId, bodyId) ->
            let positive = atoms program 0 guardId true
            if List.isEmpty positive then acc
            else refineEdges program bodyId (subtreeOf program guardId) positive acc
        | _ -> acc) Map.empty

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
        | Relation.Ne -> r

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

let private readProgram (context: PlatformContext option) (graph: SemanticGraph) : Program =
    let reachableNodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let ordered = reachableNodes |> Map.toList |> List.map snd
    let parents = parentIndex reachableNodes
    let candidates = escapingOf reachableNodes ordered parents
    let poisons = poisoningOf reachableNodes ordered
    let baseProgram = {
        Graph = graph
        Context = context
        Reachable = reachableNodes
        Ordered = ordered
        Parents = parents
        Callees = Map.empty
        CallArguments = Map.empty
        IndexSeeds = Map.empty
        Escaping = Map.empty
        EscapingLambdas = Map.empty
        Parameters = Set.empty
        RootParameters = Map.empty
        Assignments = Map.empty
        Refinements = Map.empty
        Constructions = Map.empty
        IntegerFields = Map.empty
        InputSeeds = Map.empty
        BoundarySeeds = Map.empty
        DeclaredFields = []
        DeclaredParameters = []
        ElementStores = Map.empty
        ElementSeeds = Map.empty
        Thresholds = thresholdsOf context
        Fabric = context |> Option.exists (fun ctx -> PlatformContext.substrateKind ctx = SubstrateKind.FPGA)
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
    let escaping =
        candidates
        |> List.collect (fun c -> c.Parameters |> List.skip (min c.Offset c.Parameters.Length) |> List.map (fun (_, _, id) -> (id, c.Escape)))
        |> List.fold (fun acc (id, why) -> if Map.containsKey id acc then acc else Map.add id why acc) Map.empty
    let escapingLambdas =
        candidates
        |> List.fold (fun acc c -> if Map.containsKey c.LambdaId acc then acc else Map.add c.LambdaId c.Escape acc) Map.empty
    let callees =
        ordered
        |> List.fold (fun acc node ->
            match node.Kind with
            | SemanticKind.Application (funcId, args) ->
                match resolveCallee reachableNodes candidates poisons funcId args with
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
        | Some { Kind = SemanticKind.Lambda (parameters, _, _, _, _) } -> [ parameters ]
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
                                | RangeSources.Seed.Unknown -> (calls, seeds)) (calls, seeds)) (calls, seeds)) (calls, seeds)) (Map.empty, Map.empty)
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
        |> List.fold (fun acc node ->
            match node.Kind with
            | SemanticKind.Set (targetId, valueId) ->
                match Map.tryFind targetId reachableNodes with
                | Some { Kind = SemanticKind.VarRef (_, Some defId) } ->
                    let existing = Map.tryFind defId acc |> Option.defaultValue []
                    Map.add defId (valueId :: existing) acc
                | _ -> acc
            | _ -> acc) Map.empty
    let constructions =
        ordered
        |> List.fold (fun acc node ->
            match node.Kind, node.Type with
            | SemanticKind.RecordExpr (fields, _), NativeType.TApp (tycon, _) ->
                let existing = Map.tryFind tycon.Name acc |> Option.defaultValue []
                Map.add tycon.Name ((node.Id, fields) :: existing) acc
            | _ -> acc) Map.empty
    let integerFields =
        graph.Types.Value
        |> Map.toList
        |> List.choose (fun (name, id) ->
            match Map.tryFind id graph.Nodes with
            | Some { Kind = SemanticKind.TypeDef (_, TypeDefKind.RecordDef fields, _) } ->
                let integers = fields |> List.filter (fun (_, ty) -> Types.isIntegerType ty) |> List.map fst
                if List.isEmpty integers then None else Some (name, integers)
            | _ -> None)
        |> Map.ofList
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
                    | [ _; (_, NativeType.TApp (tycon, _), _) ] ->
                        SemanticGraph.tryGetRecordFields tycon.Name graph
                        |> Option.map (fun fields ->
                            tycon.Name,
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
    let inputSeeds =
        descriptors.Layouts
        |> List.fold (fun (acc: Map<string, Map<string, ValueRange>>) layout ->
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
                | Some body, Some r -> Map.add body r.Range seeds
                | _ -> seeds
            (seeds, declared @ (f.Parameters |> List.choose (fun (paramId, d) -> d |> Option.map (fun d -> paramId, d))))) (Map.empty, [])
    // Every value stored into an array, by element type (§3.3): an array literal's elements (a
    // comprehension's yields), an indexer or `Array.set` assignment, `Array.create`'s seed,
    // `Array.init`'s function result (a named lambda's body, or every candidate's through a value),
    // and `Array.zeroCreate`'s zero for an integer element type.
    let store (key: string) (storer: NodeId) (value: NodeId) (acc: Map<string, (NodeId * NodeId) list>) =
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
    let (elementStores, elementSeeds) =
        ordered
        |> List.fold (fun (stores: Map<string, (NodeId * NodeId) list>, seeds: Map<string, ValueRange>) node ->
            let typeOf (id: NodeId) = Map.tryFind id reachableNodes |> Option.map (fun n -> n.Type)
            match node.Kind with
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
                        node.Children
                        |> List.fold (fun (s: Map<string, ValueRange>) argId ->
                            match typeOf argId |> Option.bind arrayElementType with
                            | Some elem -> Map.add (elementKey elem) ValueRange.Unbounded s
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
            DeclaredFields = declaredFields
            DeclaredParameters = declaredParameters
            ElementStores = elementStores
            ElementSeeds = elementSeeds }
    { program with Refinements = refinementsOf program }

//-------------------------------------------------------------------------
// The transfer function
//-------------------------------------------------------------------------

type private State = Map<NodeId, ValueRange>

/// The range a node has so far; a node not yet computed contributes nothing (the least element).
let private current (state: State) (id: NodeId) : ValueRange =
    Map.tryFind id state |> Option.defaultValue ValueRange.Empty

/// A range met with every bound of a use edge.
let private refineBy (state: State) (refs: Refinement list) (r: ValueRange) : ValueRange =
    refs |> List.fold (fun acc x -> refine acc x.Relation (current state x.Bound)) r

/// What `consumer` reads of `operand`: the operand's range met with the bounds in force on that
/// use edge (a read inside a guarded branch).
let private read (program: Program) (state: State) (consumer: NodeId) (operand: NodeId) : ValueRange =
    match Map.tryFind consumer program.Refinements |> Option.bind (Map.tryFind operand) with
    | Some refs -> refineBy state refs (current state operand)
    | None -> current state operand

/// The range of a record field (`FieldRanges` in the making): the declared range where a
/// descriptor declares one that is observable (the declaration binds, §4.4; a construction whose
/// value leaves it is witnessed by CCS8012, never merged), else the join of the field over the
/// type's reachable constructions and the seed a hardware design's pin carries; the empty range
/// where nothing constructs it and nothing declares it.
let private fieldRange (program: Program) (state: State) (typeName: string) (field: string) : ValueRange =
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
            |> List.fold (fun acc (_, valueId) -> ValueRange.join acc (read program state recordId valueId)) acc) (declared |> Option.defaultValue ValueRange.Empty)

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
let private elementRange (program: Program) (state: State) (elem: NativeType) : ValueRange =
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
            |> List.fold (fun acc (storer, valueId) -> ValueRange.join acc (read program state storer valueId))
                         (seed |> Option.defaultValue ValueRange.Empty)

/// `[0, n - 1]` for an index below `n`.
let private indexBelow (n: ValueRange) : ValueRange =
    match ValueRange.endpoints n with
    | Some (_, ValueRange.Endpoint.Finite h) -> ValueRange.bounded bigint.Zero (h - bigint.One)
    | Some (_, ValueRange.Endpoint.PosInf) -> ValueRange.Above bigint.Zero
    | _ -> ValueRange.Empty

/// The range of element `index` of a tuple-valued expression, read through the constructions the
/// expression can evaluate to (a tuple is not a node with one range; its elements are joined by
/// position, as a record's fields are by name): through references, bindings (a mutable one's
/// assignments included), the parameters' supplies, branch joins, blocks, annotations, function
/// results (a named lambda's body, or every candidate's through a value) and an element read of
/// an array of tuples. An expression that is not traced to constructions has no observable
/// element range.
let rec private tupleElement (program: Program) (state: State) (visited: Set<NodeId>) (exprId: NodeId) (index: int) : ValueRange =
    if Set.contains exprId visited then ValueRange.Empty
    else
        let visited = Set.add exprId visited
        let recurse id = tupleElement program state visited id index
        let joinAll (ids: NodeId list) = ids |> List.fold (fun acc id -> ValueRange.join acc (recurse id)) ValueRange.Empty
        match Map.tryFind exprId program.Reachable with
        | None -> ValueRange.Unbounded
        | Some node ->
            match node.Kind with
            | SemanticKind.TupleExpr elements ->
                match List.tryItem index elements with
                | Some elementId -> current state elementId
                | None -> ValueRange.Unbounded
            | SemanticKind.VarRef (_, Some defId) -> recurse defId
            | SemanticKind.Binding (_, isMutable, _, _) ->
                let value =
                    match List.tryLast node.Children with
                    | Some valueId -> recurse valueId
                    | None -> ValueRange.Unbounded
                if isMutable then
                    Map.tryFind node.Id program.Assignments |> Option.defaultValue [] |> List.fold (fun acc a -> ValueRange.join acc (recurse a)) value
                else value
            | SemanticKind.PatternBinding _ when Set.contains node.Id program.Parameters ->
                match Map.tryFind node.Id program.CallArguments with
                | Some args -> args |> List.fold (fun acc (_, a) -> ValueRange.join acc (recurse a)) ValueRange.Empty
                | None -> ValueRange.Unbounded
            | SemanticKind.PatternBinding _ ->
                match List.tryLast node.Children with
                | Some valueId -> recurse valueId
                | None -> ValueRange.Unbounded
            | SemanticKind.IfThenElse (_, t, e) ->
                ValueRange.join (recurse t) (e |> Option.map recurse |> Option.defaultValue ValueRange.Empty)
            | SemanticKind.Match (_, cases) -> joinAll (cases |> List.map (fun c -> c.Body))
            | SemanticKind.CaseElimination (_, arms) -> joinAll (arms |> List.map (fun a -> a.Body))
            | SemanticKind.Sequential ids ->
                match List.tryLast ids with
                | Some lastId -> recurse lastId
                | None -> ValueRange.Unbounded
            | SemanticKind.TypeAnnotation (inner, _) -> recurse inner
            | SemanticKind.Application _ ->
                match Map.tryFind node.Id program.Callees with
                | Some (Callee.Direct (_, bodyId), _) -> recurse bodyId
                | Some (Callee.Value (candidates, false), _) when not (List.isEmpty candidates) -> joinAll (candidates |> List.map (fun c -> c.Body))
                | Some (Callee.Intrinsic { Module = IntrinsicModule.Array; Operation = "get" }, arrId :: _) ->
                    match Map.tryFind arrId program.Reachable |> Option.map (fun n -> n.Type) |> Option.bind arrayElementType with
                    | Some elem -> joinAll (Map.tryFind (elementKey elem) program.ElementStores |> Option.defaultValue [] |> List.map snd)
                    | None -> ValueRange.Unbounded
                | _ -> ValueRange.Unbounded
            | SemanticKind.IndexGet (arrId, _) ->
                match Map.tryFind arrId program.Reachable |> Option.map (fun n -> n.Type) |> Option.bind arrayElementType with
                | Some elem ->
                    match Map.tryFind (elementKey elem) program.ElementStores with
                    | Some stores -> joinAll (stores |> List.map snd)
                    | None -> ValueRange.Unbounded
                | None -> ValueRange.Unbounded
            | _ -> ValueRange.Unbounded

/// The range an application computes: the table's fact for an intrinsic (`RangeSources`), the
/// element range for an element read, a named lambda's body for a call of it, the join of every
/// candidate's body for a call through a function value; a call the pass cannot resolve, and an
/// intrinsic result the table does not hold, is unobservable here.
let private applicationRange (program: Program) (state: State) (node: SemanticNode) (fallback: ValueRange) : ValueRange =
    match Map.tryFind node.Id program.Callees with
    | Some (Callee.Intrinsic info, args) ->
        let arguments =
            args
            |> List.map (fun a ->
                match Map.tryFind a program.Reachable with
                | Some an ->
                    { RangeSources.Argument.Range = (if isRanged an then read program state node.Id a else ValueRange.Unbounded)
                      RangeSources.Argument.Type = an.Type
                      RangeSources.Argument.Literal = (match an.Kind with SemanticKind.Literal l -> Some l | _ -> None) }
                | None -> { RangeSources.Argument.Range = ValueRange.Unbounded; RangeSources.Argument.Type = NativeType.TError "unreachable"; RangeSources.Argument.Literal = None })
        match RangeSources.intrinsic program.Context info arguments with
        | RangeSources.Result.Fact r -> r
        | RangeSources.Result.ElementOf i ->
            match List.tryItem i arguments |> Option.bind (fun a -> arrayElementType a.Type) with
            | Some elem -> elementRange program state elem
            | None -> fallback
        | RangeSources.Result.Untabled -> fallback
    | Some (Callee.Direct (_, bodyId), _) -> current state bodyId
    | Some (Callee.Value (candidates, false), _) when not (List.isEmpty candidates) ->
        candidates |> List.fold (fun acc c -> ValueRange.join acc (current state c.Body)) ValueRange.Empty
    | _ -> fallback

/// The transfer function: the range of one node from the ranges of the nodes it reads. `None` for
/// a node that is not ranged (not an integer, boolean or char), except that a union tag is a point
/// and a tag read is `[0, cases - 1]`. An integer node's unobservable transfer is met with its
/// width-named carrier's declared range, where it has one (`boundByCarrier`).
let private transfer (program: Program) (state: State) (node: SemanticNode) : ValueRange option =
    let get = read program state node.Id
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
        // a node a binding descriptor declares (an extern's parameter, its result): the declaration binds
        | _ when Map.containsKey node.Id program.BoundarySeeds -> Map.tryFind node.Id program.BoundarySeeds
        | SemanticKind.Literal (NativeLiteral.Int (v, _)) -> Some (ValueRange.point (bigint v))
        | SemanticKind.Literal (NativeLiteral.UInt (v, _)) -> Some (ValueRange.point (bigint v))
        | SemanticKind.Literal (NativeLiteral.Bool _) -> Some ValueRange.boolean
        | SemanticKind.Literal (NativeLiteral.Char c) -> Some (ValueRange.point (bigint (int c)))
        | SemanticKind.Literal _ -> Some fallback
        | SemanticKind.Application _ -> Some (applicationRange program state node fallback)
        | SemanticKind.VarRef (_, Some defId) -> Some (get defId)
        | SemanticKind.VarRef (_, None) -> Some fallback
        | SemanticKind.PatternBinding _ when Set.contains node.Id program.Parameters ->
            // a parameter is the join of the arguments at every call that supplies it, directly or
            // through a function value, and of the index seeds an intrinsic hands it; one nothing
            // supplies (a declaration root's, an entry the platform calls, an escaping lambda's no
            // seen call reaches) has no observable range here
            let supplied = Map.tryFind node.Id program.CallArguments |> Option.defaultValue []
            let seeded = Map.tryFind node.Id program.IndexSeeds |> Option.defaultValue []
            if List.isEmpty supplied && List.isEmpty seeded then Some fallback
            else
                let fromCalls = supplied |> List.fold (fun acc (callId, a) -> ValueRange.join acc (read program state callId a)) ValueRange.Empty
                Some (seeded |> List.fold (fun acc (callId, nId) -> ValueRange.join acc (indexBelow (read program state callId nId))) fromCalls)
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
        | SemanticKind.IfThenElse (_, t, e) ->
            Some (ValueRange.join (get t) (e |> Option.map get |> Option.defaultValue ValueRange.Empty))
        | SemanticKind.Match (_, cases) ->
            Some (cases |> List.fold (fun acc c -> ValueRange.join acc (get c.Body)) ValueRange.Empty)
        | SemanticKind.CaseElimination (_, arms) ->
            Some (arms |> List.fold (fun acc a -> ValueRange.join acc (get a.Body)) ValueRange.Empty)
        | SemanticKind.TypeAnnotation (inner, _)
        | SemanticKind.Upcast (inner, _)
        | SemanticKind.Downcast (inner, _) -> Some (get inner)
        | SemanticKind.FieldGet (exprId, field) ->
            match Map.tryFind exprId program.Reachable with
            | Some { Type = NativeType.TApp (tycon, _) } when Map.containsKey tycon.Name program.Constructions || Map.containsKey tycon.Name program.InputSeeds ->
                Some (fieldRange program state tycon.Name field)
            // A read of a field of a record type nothing reachable constructs and nothing declares
            // came from a source the pass did not see: unobservable (CCS8011), never a fabricated width.
            // (`Empty` remains right for FieldRanges of a field nothing reads.)
            | _ -> Some fallback
        | SemanticKind.TupleGet (tupleId, index) -> Some (tupleElement program state Set.empty tupleId index)
        | SemanticKind.IndexGet (exprId, _) ->
            match Map.tryFind exprId program.Reachable |> Option.map (fun n -> n.Type) |> Option.bind arrayElementType with
            | Some elem -> Some (elementRange program state elem)
            | None -> Some fallback
        | _ -> Some fallback
    match computed with
    | Some r when isIntegerNode node && isSource program node -> Some (boundByCarrier program node r)
    | other -> other

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

/// The constants the analysis has settled so far: every point range in the state. They are the
/// widening's thresholds beside the declared representations (`ValueRange.widen`).
let private constantsOf (state: State) : bigint list =
    state
    |> Map.toSeq
    |> Seq.choose (fun (_, r) -> match r with ValueRange.Bounded (lo, hi) when lo = hi -> Some lo | _ -> None)
    |> Seq.distinct
    |> List.ofSeq

/// One ascending round in node order: every node's range becomes the join of what it has and its
/// transfer; past the widening delay, a range that still grows is widened. Returns the new state
/// and whether anything changed.
let private ascend (program: Program) (round: int) (state: State) : State * bool =
    let constants = if round > WideningDelay then constantsOf state else []
    program.Ordered
    |> List.fold (fun (state: State, changed) node ->
        match transfer program state node with
        | None -> (state, changed)
        | Some computed ->
            match Map.tryFind node.Id state with
            | None -> (Map.add node.Id computed state, true)   // first sight: recorded, empty or not
            | Some old ->
                let grown = ValueRange.join old computed
                if ValueRange.contains old grown then (state, changed)
                else
                    let next = if round > WideningDelay then ValueRange.widen program.Thresholds constants old grown else grown
                    (Map.add node.Id next state, true)) (state, false)

/// One narrowing round: every node's range becomes its transfer, which from a post-fixpoint can
/// only tighten (a monotone transfer function applied below a post-fixpoint stays above the least
/// fixpoint, so the result is sound); a transfer that would grow is not taken.
let private narrow (program: Program) (state: State) : State * bool =
    program.Ordered
    |> List.fold (fun (state: State, changed) node ->
        match transfer program state node with
        | None -> (state, changed)
        | Some computed ->
            let old = current state node.Id
            if ValueRange.contains computed old || not (ValueRange.contains old computed) then (state, changed)
            else (Map.add node.Id computed state, true)) (state, false)

/// The least fixed point with widening, then the bounded narrowing.
let private fixpoint (program: Program) : State =
    let rec climb (round: int) (state: State) =
        if round > AscentLimit then
            failwithf "RangeAnalysis: the range fixpoint did not settle in %d rounds; the widening did not terminate the ascent" AscentLimit
        else
            let (next, changed) = ascend program round state
            if changed then climb (round + 1) next else next
    let rec descend (round: int) (state: State) =
        if round > NarrowingRounds then state
        else
            let (next, changed) = narrow program state
            if changed then descend (round + 1) next else next
    climb 1 Map.empty |> descend 1

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
            let declared = Map.tryFind tycon.Name program.InputSeeds |> Option.exists (Map.containsKey field)
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
    let severity = if program.Fabric then NativeDiagnosticSeverity.Error else NativeDiagnosticSeverity.Info
    program.Ordered
    |> List.filter (fun node ->
        isIntegerNode node
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
/// representation covers (§4.2): a warning, promoted by `--warnaserror`, naming the range and the
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
                isIntegerNode node
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
                { Severity = NativeDiagnosticSeverity.Warning
                  Code = DiagnosticCodes.CCS8012_RangeNotCovered
                  Message =
                    sprintf "The range %s of '%s'%s is not covered by any integer representation the platform description of '%s' declares; the widest, '%s' (%d bits, %s), is selected; bound the value with a comparison, a modulus or a clamp, or declare a wider representation"
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
        |> List.choose (fun node -> uncovered node |> Option.map (fun found -> (node, found)))
        |> fun found ->
            let byNode = found |> List.map (fun (n, f) -> (n.Id, f)) |> Map.ofList
            oncePerBinding program (found |> List.map fst) (fun node name where ->
                let (lambdaId, r, rep) = Map.find node.Id byNode
                let why = Map.tryFind lambdaId program.EscapingLambdas |> Option.map (sprintf ", which is %s,") |> Option.defaultValue ", a declaration root,"
                { Severity = NativeDiagnosticSeverity.Warning
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
        let short (name: string) = match name.LastIndexOf '.' with -1 -> name | i -> name.Substring(i + 1)
        let ranged (values: (NodeId * NodeId) list) = values |> List.map (fun (consumer, v) -> v, read program state consumer v)
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
                        at v NativeDiagnosticSeverity.Warning DiagnosticCodes.CCS8012_RangeNotCovered
                            (sprintf "The range %s of the value stored into field '%s' of '%s' is not covered by its declared representation '%s' (%d bits, %s); bound the value with a comparison, a modulus or a clamp, or change the declaration"
                                (ValueRange.render r) f.Name (short typeName) f.Repr f.Bits (ValueRange.render f.Range)))
                let wider =
                    tightening f.Range f.Bits values
                    |> Option.bind (fun (joined, r) ->
                        at f.Node NativeDiagnosticSeverity.Info DiagnosticCodes.CCS8014_RepresentationWiderThanRange
                            (sprintf "The field '%s' of '%s' is declared '%s' (%d bits, %s); every value stored lies within %s, which '%s' (%d bits) holds; the declaration can be tightened"
                                f.Name (short typeName) f.Repr f.Bits (ValueRange.render f.Range) (ValueRange.render joined) r.Name r.Bits))
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
                        at v NativeDiagnosticSeverity.Warning DiagnosticCodes.CCS8012_RangeNotCovered
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
            |> List.choose (fun node ->
                match declarationOf node, Map.tryFind node.Id state with
                | Some d, Some r when ValueRange.isObservable r && not (ValueRange.contains d.Range r) -> Some (node, (d, r))
                | _ -> None)
        let byNode = leaving |> List.map (fun (n, f) -> n.Id, f) |> Map.ofList
        let uncovered =
            oncePerBinding program (leaving |> List.map fst) (fun node name where ->
                let (d, r) = Map.find node.Id byNode
                { Severity = NativeDiagnosticSeverity.Warning
                  Code = DiagnosticCodes.CCS8012_RangeNotCovered
                  Message =
                    sprintf "The range %s of '%s'%s is not covered by '%s' (%d bits, %s), the representation its width-named spelling declares; bound the value with a comparison, a modulus or a clamp, or write `int` and declare the representation at the boundary"
                        (ValueRange.render r) name where d.Repr d.Bits (ValueRange.render d.Range)
                  Range = node.Range
                  RelatedNodes = [ node.Id ]
                  Reachability = ReachabilityContext.Reachable })
        let wider =
            program.Ordered
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
let run (context: PlatformContext option) (graph: SemanticGraph) : SemanticGraph * Diagnostic list =
    let program = readProgram context graph
    let state = fixpoint program
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
                fields |> List.map (fun f -> f, fieldRange program state typeName f) |> Map.ofList)
        let declared =
            program.InputSeeds
            |> Map.fold (fun (acc: Map<string, Map<string, ValueRange>>) typeName seeds ->
                let existing = Map.tryFind typeName acc |> Option.defaultValue Map.empty
                Map.add typeName (seeds |> Map.fold (fun m f _ -> Map.add f (fieldRange program state typeName f) m) existing) acc) declared
        program.Constructions
        |> Map.fold (fun (acc: Map<string, Map<string, ValueRange>>) typeName constructions ->
            let fields = constructions |> List.collect (snd >> List.map fst) |> List.distinct
            let existing = Map.tryFind typeName acc |> Option.defaultValue Map.empty
            let joined =
                fields
                |> List.fold (fun (m: Map<string, ValueRange>) f ->
                    if Map.containsKey f m then m
                    else
                        let r = fieldRange program state typeName f
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
        let typeOfKey (key: string) : NativeType option =
            program.Ordered
            |> List.tryPick (fun n -> arrayElementType n.Type |> Option.filter (fun e -> elementKey e = key))
        keys
        |> Set.toList
        |> List.choose (fun key -> typeOfKey key |> Option.map (fun elem -> key, elementRange program state elem))
        |> Map.ofList
    let diagnostics = unobservableDiagnostics program state @ coverageDiagnostics program state @ boundaryDiagnostics program state @ declaredDiagnostics program state @ spelledDiagnostics program state
    ({ graph with Nodes = nodes; FieldRanges = lazy fieldRanges; ElementRanges = lazy elementRanges; Escaping = lazy program.EscapingLambdas }, diagnostics)

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
/// range against the declaration, never stored (C3).
let selectedRepresentationOf (graph: SemanticGraph) (range: ValueRange) : NumericRepresentation option =
    match graph.Platform with
    | Some ctx when selectsFromDeclared ctx -> (selectRange ctx range).Representation
    | _ -> None

/// The integer representation a node selects on the graph's platform (§3.1), derived on read from
/// the node's range, its carrier, its boundary and the declared representations: at the
/// value-call boundary (ruling 1) the Register representation of the range's sign; a width-named
/// carrier's own; for the bare kind, `selectedRepresentationOf` its range. None for an
/// unobservable range, a context declaring no integer representation, or a node that is not an
/// integer. Never stored beside the range (Horizon C3).
let selectedRepresentation (graph: SemanticGraph) (nodeId: NodeId) : NumericRepresentation option =
    match graph.Platform, SemanticGraph.tryGetNode nodeId graph with
    | Some ctx, Some node when isIntegerNode node && selectsFromDeclared ctx ->
        match node.ValueRange, boundaryOfNode graph node with
        | Some r, Some _ -> registerRepresentation ctx r
        | Some r, None -> (selectNode ctx graph.Nodes node r).Representation
        | None, _ -> None
    | _ -> None

/// The width a range of the bare kind selects on the graph's platform: on fabric, which declares
/// no core, the exact width of the range (§3, `ValueRange.width`); on a core, the bits of the
/// selected representation, or of the widest declared one for a range no representation covers
/// (CCS8012 named it). None for an unobservable range on a core: no width is fabricated for it
/// here (C3, width-inference.md §6); `heldWidthOf` is the one site that holds such a value at
/// the declared word while CCS8011 is information there.
let selectedWidthOf (graph: SemanticGraph) (range: ValueRange) : int option =
    match graph.Platform with
    | Some ctx when selectsFromDeclared ctx ->
        match ValueRange.isObservable range, (selectRange ctx range).Representation with
        | false, _ -> None
        | true, Some r -> Some r.Bits
        | true, None -> None
    | _ -> ValueRange.width range

/// THE ONE INTERIM of the node-reading CPU leg (Dimensional_Range_Design.md, "CS-11 as built, the
/// CPU leg"; §1.3): an integer value on a core whose range is unobservable has no selection
/// (`selectedWidthOf` is None; CCS8011 is information on cores until the migration inventory is
/// drained and promoted, §1.3 and the slice-4 rule) and is held at the declared Register width
/// read from the context. Nothing else defaults: on fabric an unobservable range stays None and
/// the leg stops naming the node. When CCS8011 is promoted to an error on every substrate this
/// site becomes a stop naming the range, since no such value reaches emission. The record and
/// union placement (Placement.fs) and Composer's width reads both come through here, so the
/// interim has one site.
let heldWidthOf (graph: SemanticGraph) (range: ValueRange) : int option =
    match selectedWidthOf graph range with
    | Some bits -> Some bits
    | None ->
        match graph.Platform with
        | Some ctx when PlatformContext.substrateKind ctx <> SubstrateKind.FPGA && not (ValueRange.isObservable range) ->
            registerWidth ctx   // the interim: an unobservable range on a core, CCS8011 information
        | _ -> None

/// The width a node's value is selected at on the graph's platform (§3.1, width-inference.md
/// §8): at the value-call boundary (ruling 1: a parameter or the result of a lambda that escapes
/// as a value or is a declaration root, and a call through a value) the declared Register width,
/// regardless of the range; a width-named carrier at its own representation's bits (interim,
/// CS-12), or at the bits its spelling states where the context offers no such representation;
/// otherwise `selectedWidthOf` its range. None for a node with no range, or an unobservable one
/// on a core (see `heldWidth`).
let selectedWidth (graph: SemanticGraph) (nodeId: NodeId) : int option =
    match graph.Platform, SemanticGraph.tryGetNode nodeId graph with
    | Some ctx, Some node when isIntegerNode node && PlatformContext.substrateKind ctx <> SubstrateKind.FPGA ->
        match boundaryOfNode graph node with
        | Some _ -> registerWidth ctx
        | None ->
            // a spelled site is held at the representation its declaration names (CS-12 step 5a)
            match declaredKindOf graph.Nodes node |> Option.bind (RangeSources.declarationOfKind (Some ctx)) with
            | Some d -> Some d.Bits
            | None -> node.ValueRange |> Option.bind (selectedWidthOf graph)
    | _, Some node -> node.ValueRange |> Option.bind (selectedWidthOf graph)
    | _ -> None

/// The bits a spelled kind's declaration names on the graph's platform (CS-12 step 5a): the read
/// Composer's type mapping makes for a value of a width-named spelling where no node is at hand
/// (a signature, a capture's type); None for the bare kind, whose width is the node's selection.
let declaredWidthOfKind (graph: SemanticGraph) (kind: NTUKind) : int option =
    RangeSources.declarationOfKind graph.Platform kind |> Option.map (fun d -> d.Bits)

/// The width a node's value is held at: `selectedWidth`, or, for an unobservable range on a core,
/// the interim word of `heldWidthOf`. The read Composer's CPU leg makes for every integer node;
/// None is a stop there (fabric, or a node with no range).
let heldWidth (graph: SemanticGraph) (nodeId: NodeId) : int option =
    match selectedWidth graph nodeId with
    | Some bits -> Some bits
    | None ->
        match SemanticGraph.tryGetNode nodeId graph with
        | Some node when isIntegerNode node -> node.ValueRange |> Option.bind (heldWidthOf graph)
        | _ -> None
