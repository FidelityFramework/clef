// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// The range pass (Dimensional_Range_Design.md §1; width-inference.md §2, §3, §6; CS-10).
///
/// Every reachable integer value carries its analysed range as a coeffect beside its type
/// (`SemanticNode.ValueRange`), and every record type carries the join of each field's range
/// over its reachable constructions (`SemanticGraph.FieldRanges`). The width is derived from the
/// range wherever it is read (`ValueRange.width`) and is never stored beside it (Horizon C3).
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
/// A reachable integer whose final range has no width is CCS8011 (§1.3, §7): an error on fabric,
/// where the width has no other source, and information on every other substrate in this
/// changeset, because the CPU leg reads the carrier's width until CS-12 supplies the declared
/// boundary ranges. Runs on every substrate, over reachable nodes only, after the declared platform
/// has filled the context and before it is checked (NativeService.buildResult).
module Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.Expressions.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

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

/// What the pass reads of the graph, computed once: the reachable nodes, the parent index, the
/// call sites of every parameter, the assignments to every mutable binding, the refinement at
/// every reference, the reachable constructions of every record type and the integer fields its
/// definition declares, and the widening thresholds the platform declares.
type private Program = {
    Graph: SemanticGraph
    Reachable: Map<NodeId, SemanticNode>
    /// Reachable nodes in node order.
    Ordered: SemanticNode list
    Parents: Map<NodeId, NodeId>
    /// A Lambda parameter node -> (the call node, the argument node) at every reachable call of
    /// its function; the parameter reads the argument as the call does.
    CallArguments: Map<NodeId, (NodeId * NodeId) list>
    /// Every Lambda parameter node (a parameter with no reachable call has no argument list).
    Parameters: Set<NodeId>
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

/// The Lambda a function binding holds, if any.
let private lambdaOf (program: Program) (bindingId: NodeId) : (NodeId * (string * NativeType * NodeId) list * NodeId) option =
    match Map.tryFind bindingId program.Reachable with
    | Some binding ->
        binding.Children
        |> List.tryPick (fun childId ->
            match Map.tryFind childId program.Reachable with
            | Some { Kind = SemanticKind.Lambda (parameters, body, _, _, _) } -> Some (childId, parameters, body)
            | _ -> None)
    | None -> None

/// The function a callee expression names: the binding of the VarRef at the root of a possibly
/// curried application, with every argument along the chain in order.
let rec private flattenApplication (program: Program) (funcId: NodeId) (args: NodeId list) : (NodeId * NodeId list) option =
    match Map.tryFind funcId program.Reachable with
    | Some { Kind = SemanticKind.VarRef (_, Some defId) } -> Some (defId, args)
    | Some { Kind = SemanticKind.Application (innerFunc, innerArgs) } -> flattenApplication program innerFunc (innerArgs @ args)
    | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> flattenApplication program inner args
    | _ -> None

/// The intrinsic an application calls, if its callee is one.
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

/// The refinements a guarded subtree's use edges carry. The subtree is walked in evaluation
/// order; every read (a node's child, a reference's binding) by a node exclusive to the subtree
/// (not also in `excluded`: the guard, the other branch) of a compared binding or node carries
/// the bound. A mutable binding's bound holds only until the first assignment to it in the
/// subtree (the value assigned is evaluated before the store, so it still carries the bound),
/// and never inside a nested lambda, whose body runs at some other time.
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
            | ValueRange.Endpoint.Finite h when h > System.Int64.MinValue -> ValueRange.meet r (ValueRange.Below (h - 1L))
            | _ -> r
        | Relation.Le ->
            match khi with
            | ValueRange.Endpoint.Finite h -> ValueRange.meet r (ValueRange.Below h)
            | _ -> r
        | Relation.Gt ->
            match klo with
            | ValueRange.Endpoint.Finite l when l < System.Int64.MaxValue -> ValueRange.meet r (ValueRange.Above (l + 1L))
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
                match System.Int64.TryParse r.MinMagnitude, System.Int64.TryParse r.MaxMagnitude with
                | (true, lo), (true, hi) -> Some { ValueRange.Threshold.Family = r.Family; Lo = lo; Hi = hi }
                | _ -> None   // a range int64 does not hold (uint64) is above every int64 endpoint: the infinity serves
            else None)

let private readProgram (context: PlatformContext option) (graph: SemanticGraph) : Program =
    let reachable = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let ordered = reachable |> Map.toList |> List.map snd
    let baseProgram = {
        Graph = graph
        Reachable = reachable
        Ordered = ordered
        Parents = parentIndex reachable
        CallArguments = Map.empty
        Parameters = Set.empty
        Assignments = Map.empty
        Refinements = Map.empty
        Constructions = Map.empty
        IntegerFields = Map.empty
        InputSeeds = Map.empty
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
    let callArguments =
        ordered
        |> List.fold (fun acc node ->
            match node.Kind with
            | SemanticKind.Application (funcId, args) ->
                match flattenApplication baseProgram funcId args with
                | Some (defId, allArgs) ->
                    match lambdaOf baseProgram defId with
                    | Some (_, parameters, _) ->
                        List.zip (List.truncate (min parameters.Length allArgs.Length) parameters)
                                 (List.truncate (min parameters.Length allArgs.Length) allArgs)
                        |> List.fold (fun acc ((_, _, paramId), argId) ->
                            let existing = Map.tryFind paramId acc |> Option.defaultValue []
                            Map.add paramId ((node.Id, argId) :: existing) acc) acc
                    | None -> acc
                | None -> acc
            | _ -> acc) Map.empty
    let assignments =
        ordered
        |> List.fold (fun acc node ->
            match node.Kind with
            | SemanticKind.Set (targetId, valueId) ->
                match Map.tryFind targetId reachable with
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
    let inputSeeds =
        graph.DeclarationRoots
        |> List.choose (fun (rootId, root) ->
            match root with
            | DeclRoot.HardwareModule ->
                Map.tryFind rootId reachable
                |> Option.bind (fun binding -> List.tryLast binding.Children)
                |> Option.bind (fun designId -> Map.tryFind designId reachable)
                |> Option.bind (fun design ->
                    match design.Kind with
                    | SemanticKind.RecordExpr (fields, _) -> fields |> List.tryFind (fun (n, _) -> n = "Step") |> Option.map snd
                    | _ -> None)
                |> Option.bind (fun stepId ->
                    match Map.tryFind stepId reachable with
                    | Some { Kind = SemanticKind.VarRef (_, Some defId) } -> lambdaOf baseProgram defId
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
    let program =
        { baseProgram with
            CallArguments = callArguments
            Parameters = parameters
            Assignments = assignments
            Constructions = constructions
            IntegerFields = integerFields
            InputSeeds = inputSeeds }
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

/// The join of a record field over the type's reachable constructions (`FieldRanges` in the
/// making): the empty range where nothing constructs it.
let private fieldRange (program: Program) (state: State) (typeName: string) (field: string) : ValueRange =
    let declared =
        Map.tryFind typeName program.InputSeeds
        |> Option.bind (Map.tryFind field)
        |> Option.defaultValue ValueRange.Empty
    Map.tryFind typeName program.Constructions
    |> Option.defaultValue []
    |> List.fold (fun acc (recordId, fields) ->
        fields
        |> List.filter (fun (name, _) -> name = field)
        |> List.fold (fun acc (_, valueId) -> ValueRange.join acc (read program state recordId valueId)) acc) declared

/// The range of element `index` of a tuple-valued expression, read through the constructions the
/// expression can evaluate to (a tuple is not a node with one range; its elements are joined by
/// position, as a record's fields are by name). An expression that is not traced to constructions
/// has no observable element range.
let rec private tupleElement (program: Program) (state: State) (visited: Set<NodeId>) (exprId: NodeId) (index: int) : ValueRange =
    if Set.contains exprId visited then ValueRange.Empty
    else
        let visited = Set.add exprId visited
        let recurse id = tupleElement program state visited id index
        match Map.tryFind exprId program.Reachable with
        | None -> ValueRange.Unbounded
        | Some node ->
            match node.Kind with
            | SemanticKind.TupleExpr elements ->
                match List.tryItem index elements with
                | Some elementId -> current state elementId
                | None -> ValueRange.Unbounded
            | SemanticKind.VarRef (_, Some defId) -> recurse defId
            | SemanticKind.Binding _ ->
                match List.tryLast node.Children with
                | Some valueId -> recurse valueId
                | None -> ValueRange.Unbounded
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
            | SemanticKind.Match (_, cases) ->
                cases |> List.fold (fun acc c -> ValueRange.join acc (recurse c.Body)) ValueRange.Empty
            | SemanticKind.CaseElimination (_, arms) ->
                arms |> List.fold (fun acc a -> ValueRange.join acc (recurse a.Body)) ValueRange.Empty
            | SemanticKind.Sequential ids ->
                match List.tryLast ids with
                | Some lastId -> recurse lastId
                | None -> ValueRange.Unbounded
            | SemanticKind.TypeAnnotation (inner, _) -> recurse inner
            | SemanticKind.Application (funcId, args) ->
                match flattenApplication program funcId args |> Option.bind (fun (defId, _) -> lambdaOf program defId) with
                | Some (_, _, bodyId) -> recurse bodyId
                | None -> ValueRange.Unbounded
            | _ -> ValueRange.Unbounded

/// The range an application computes: the interval rules for the operators (§1.1, §1.2), `[0, 1]`
/// for a comparison, a user function's body for a call of it; any other integer-valued intrinsic
/// (a length, a read, a rounding of a real: the real domain is CS-13's) is unobservable here.
let private applicationRange (program: Program) (state: State) (node: SemanticNode) (funcId: NodeId) (args: NodeId list) (fallback: ValueRange) : ValueRange =
    let get = read program state node.Id
    match intrinsicOf program funcId with
    | Some info ->
        match info.Category, info.Module, info.Operation, args with
        | IntrinsicCategory.Comparison, _, _, _ -> ValueRange.boolean
        | _, IntrinsicModule.Operators, "op_Addition", [ x; y ] -> ValueRange.add (get x) (get y)
        | _, IntrinsicModule.Operators, "op_Subtraction", [ x; y ] -> ValueRange.sub (get x) (get y)
        | _, IntrinsicModule.Operators, "op_Multiply", [ x; y ] -> ValueRange.mul (get x) (get y)
        | _, IntrinsicModule.Operators, "op_Division", [ x; y ] -> ValueRange.div (get x) (get y)
        | _, IntrinsicModule.Operators, "op_Modulus", [ x; y ] -> ValueRange.rem (get x) (get y)
        | _, IntrinsicModule.Operators, "op_UnaryNegation", [ x ] -> ValueRange.neg (get x)
        | _, IntrinsicModule.Operators, "op_UnaryPlus", [ x ] -> get x
        | _, IntrinsicModule.Operators, "op_BitwiseAnd", [ x; y ] -> ValueRange.band (get x) (get y)
        | _, IntrinsicModule.Operators, ("op_BitwiseOr" | "op_ExclusiveOr"), [ x; y ] -> ValueRange.bor (get x) (get y)
        | _, IntrinsicModule.Operators, "op_LogicalNot", [ x ] -> ValueRange.bnot (get x)
        | _, IntrinsicModule.Operators, "op_LeftShift", [ x; n ] -> ValueRange.shl (get x) (get n)
        | _, IntrinsicModule.Operators, "op_RightShift", [ x; n ] -> ValueRange.shr (get x) (get n)
        | _ -> fallback
    | None ->
        match flattenApplication program funcId args |> Option.bind (fun (defId, _) -> lambdaOf program defId) with
        | Some (_, _, bodyId) -> current state bodyId
        | None -> fallback

/// The transfer function: the range of one node from the ranges of the nodes it reads. `None` for
/// a node that is not ranged (not an integer, boolean or char), except that a union tag is a point
/// and a tag read is `[0, cases - 1]`.
let private transfer (program: Program) (state: State) (node: SemanticNode) : ValueRange option =
    let get = read program state node.Id
    let ranged = isRanged node
    // what an integer node with no rule is; a boolean or a char is bounded by its type
    let fallback =
        if isBoolNode node then ValueRange.boolean
        elif isCharNode node then ValueRange.codePoint
        else ValueRange.Unbounded
    match node.Kind with
    | SemanticKind.UnionCase (_, caseIndex, _)
    | SemanticKind.DUConstruct (_, caseIndex, _, _) -> Some (ValueRange.point (int64 caseIndex))
    | SemanticKind.DUGetTag (_, duType) ->
        let cases =
            match duType with
            | NativeType.TUnion (_, cases) -> List.length cases
            | NativeType.TApp (tycon, _) -> tycon.CaseCount
            | _ -> 0
        Some (ValueRange.Bounded (0L, int64 (max 0 (cases - 1))))
    | _ when not ranged -> None
    | SemanticKind.Literal (NativeLiteral.Int (v, _)) -> Some (ValueRange.point v)
    | SemanticKind.Literal (NativeLiteral.UInt (v, _)) ->
        Some (if v <= uint64 System.Int64.MaxValue then ValueRange.point (int64 v) else ValueRange.Above System.Int64.MaxValue)
    | SemanticKind.Literal (NativeLiteral.Bool _) -> Some ValueRange.boolean
    | SemanticKind.Literal (NativeLiteral.Char c) -> Some (ValueRange.point (int64 c))
    | SemanticKind.Literal _ -> Some fallback
    | SemanticKind.Application (funcId, args) -> Some (applicationRange program state node funcId args fallback)
    | SemanticKind.VarRef (_, Some defId) -> Some (get defId)
    | SemanticKind.VarRef (_, None) -> Some fallback
    | SemanticKind.PatternBinding _ when Set.contains node.Id program.Parameters ->
        // a parameter is the join of the arguments at every reachable call of its function; one no
        // reachable call supplies (a declaration root's, an entry the platform calls) has no
        // observable range here, and takes the declared boundary range at CS-12
        match Map.tryFind node.Id program.CallArguments with
        | Some args -> Some (args |> List.fold (fun acc (callId, a) -> ValueRange.join acc (read program state callId a)) ValueRange.Empty)
        | None -> Some fallback
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
    | _ -> Some fallback

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
let private constantsOf (state: State) : int64 list =
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
// CCS8011
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
                let isFunction = lambdaOf program b.Id |> Option.isSome
                if isFunction then ((match binding with Some _ -> binding | None -> Some b), Some b)
                else up (Map.tryFind i program.Parents) (match binding with Some _ -> binding | None -> Some b)
            | Some _ -> up (Map.tryFind i program.Parents) binding
            | None -> (binding, None)
    match node.Kind with
    | SemanticKind.Binding _ when (lambdaOf program node.Id).IsNone ->
        let (_, func) = up (Map.tryFind node.Id program.Parents) None
        (Some node, func)
    | _ -> up (Map.tryFind node.Id program.Parents) None

/// CCS8011 for every reachable integer whose range has no width: once per enclosing binding, at
/// the first such node in node order, naming the value. A reference whose own binding is
/// unobservable is that binding's finding, not a second one, and so is a binding that merely
/// names such a reference (`let _ = acc`).
let private diagnostics (program: Program) (state: State) : Diagnostic list =
    let unobservable (id: NodeId) =
        match Map.tryFind id state with
        | Some r -> not (ValueRange.isObservable r)
        | None -> false
    let aliasOfUnobservable (id: NodeId) =
        match Map.tryFind id program.Reachable with
        | Some { Kind = SemanticKind.VarRef (_, Some defId) } -> unobservable defId
        | _ -> false
    program.Ordered
    |> List.filter (fun node ->
        isIntegerNode node
        && unobservable node.Id
        && (match node.Kind with
            | SemanticKind.VarRef (_, Some defId) -> not (unobservable defId)
            | SemanticKind.Binding _ -> not (List.tryLast node.Children |> Option.exists aliasOfUnobservable)
            | _ -> true))
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
            let severity = if program.Fabric then NativeDiagnosticSeverity.Error else NativeDiagnosticSeverity.Info
            let diagnostic =
                { Severity = severity
                  Code = DiagnosticCodes.CCS8011_UnobservableRange
                  Message = sprintf "The range of '%s'%s cannot be observed; bound it with a comparison, a modulus or a clamp" name where
                  Range = node.Range
                  RelatedNodes = [ node.Id ]
                  Reachability = ReachabilityContext.Reachable }
            (Set.add key reported, diagnostic :: acc)) (Set.empty, [])
    |> snd
    |> List.rev

//-------------------------------------------------------------------------
// Entry
//-------------------------------------------------------------------------

/// Run the range pass over the reachable graph: every ranged node carries its range, every record
/// type its per-field ranges, and every unobservable integer is CCS8011. The graph is returned
/// with the annotations written and the field ranges settled.
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
    ({ graph with Nodes = nodes; FieldRanges = lazy fieldRanges }, diagnostics program state)

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
