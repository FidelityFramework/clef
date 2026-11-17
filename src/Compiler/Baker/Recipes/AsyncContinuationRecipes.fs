// SPDX-License-Identifier: MIT
/// Realize a settled async continuation frame as explicit PSG operations in
/// the formation's deferred callable (clef#163, A-01 and A-02): the frame
/// allocation, capture and state initialization, the stores and the state
/// transition before each suspension cut, and one resumption dispatch per cut
/// whose case region reloads the retained slots and evaluates the resumed
/// computation.
///
/// The callable is evaluated within one activation. Slot identities and the
/// frame layout are settled by the caller; this recipe selects no storage,
/// width or liveness.
///
/// The join of a settled orchestration (A-03) is realized the same way: each
/// child is bound once (`bindChildren`), and the join is a block that binds
/// the orchestration's result storage as its result array and holds one
/// explicit activation per child and the store of each result into that
/// array (`join`).
module Clef.Compiler.Baker.Recipes.AsyncContinuationRecipes

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Ingredients.Closures
module C = Clef.Compiler.Baker.Ingredients.Continuations

/// One suspension cut of a formation.
type Cut =
    { /// The Async.Await application.
      Site: NodeId
      /// The binding of the awaited result, or the site when it is unbound.
      Statement: NodeId
      /// The settled state ordinal of the cut.
      Ordinal: int
      /// The frame slots retained across the cut, in settled order.
      Retained: NodeId list }

type Plan =
    { Formation: NodeId
      /// The identity the continuation frame is published under.
      Frame: NodeId
      Callable: NodeId
      Body: NodeId
      /// The typed state field declaration: the formation's state anchor.
      State: NodeId
      /// The capture slots, in frame order.
      Captures: NodeId list
      Cuts: Cut list
      /// The resumed computations whose value has a frame slot.
      Results: Set<NodeId> }

type Elaboration =
    { /// Every created node and the current version of every edited node.
      Nodes: SemanticNode list
      /// The existing nodes this elaboration gives a current version.
      Edited: Set<NodeId>
      Allocation: NodeId
      /// The allocation, its binding and every reference to it.
      FrameReferences: NodeId list
      /// Capture slot and the value occurrence stored into it at entry.
      CaptureInitializers: (NodeId * NodeId) list
      /// Frame read occurrence and its slot.
      Reads: (NodeId * NodeId) list
      /// Frame write occurrence, its slot and the stored value occurrence.
      Writes: (NodeId * NodeId * NodeId) list
      /// Resumption dispatch occurrence and the state ordinal it selects.
      Dispatches: (NodeId * int) list }

type Residual = { Formation: NodeId; Site: NodeId; Reason: string }

let private isUnit (ty: NativeType) =
    match applySubst ty with
    | NativeType.TApp({ NTUKind = Some NTUKind.NTUunit }, []) -> true
    | _ -> false

/// The nodes one activation of a callable evaluates below a root: its
/// structure without the bodies of nested deferred callables.
let private activation (graph: SemanticGraph) (root: NodeId) : Set<NodeId> =
    let rec walk pending seen =
        match pending with
        | [] -> seen
        | head :: rest when Set.contains head seen -> walk rest seen
        | head :: rest ->
            match graph.Nodes.TryFind head with
            | Some { Kind = SemanticKind.Lambda _ } -> walk rest (Set.add head seen)
            | Some node -> walk (node.Children @ rest) (Set.add head seen)
            | None -> walk rest seen
    walk [ root ] Set.empty

let private declaredName (graph: SemanticGraph) (id: NodeId) =
    match graph.Nodes.TryFind id with
    | Some { Kind = SemanticKind.Binding(name, _, _, _) }
    | Some { Kind = SemanticKind.PatternBinding name } -> Some name
    | _ -> None

let private readDeclaration (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.VarRef(_, Some definition) -> Some definition
    | SemanticKind.EnvironmentRead(_, slot) -> Some slot
    | _ -> None

/// The block that directly sequences a statement.
let private sequencingBlock (graph: SemanticGraph) (statement: NodeId) =
    match graph.Nodes.TryFind statement |> Option.bind _.Parent |> Option.bind graph.Nodes.TryFind with
    | Some ({ Kind = SemanticKind.Sequential items } as block) when List.contains statement items -> Some(block, items)
    | _ -> None

/// The computation resumed after a statement: every item its sequencing block
/// evaluates after it. The settlement reads suspension liveness over the same
/// items. A statement outside a block has none, and `build` does not settle a
/// cut in that position.
let resumed (graph: SemanticGraph) (statement: NodeId) : NodeId list =
    match sequencingBlock graph statement with
    | Some(_, items) ->
        match items |> List.skipWhile ((<>) statement) with
        | _ :: following -> following
        | [] -> []
    | None -> []

/// The value-producing item of a resumed computation.
let resumedValue (graph: SemanticGraph) (statement: NodeId) : NodeId option =
    resumed graph statement |> List.tryLast

let build (graph: SemanticGraph) (plan: Plan) : Result<Elaboration, Residual> =
    let residual site reason = Error { Formation = plan.Formation; Site = site; Reason = reason }
    match graph.Nodes.TryFind plan.Formation, graph.Nodes.TryFind plan.Callable, graph.Nodes.TryFind plan.Body, graph.Nodes.TryFind plan.State with
    | Some owner, Some ({ Kind = SemanticKind.Lambda(parameters, bodyId, captures, enclosing, context) } as callable), Some body, Some stateSlot
        when bodyId = plan.Body ->
        let scope = activation graph body.Id
        let cutByStatement = plan.Cuts |> List.map (fun cut -> cut.Statement, cut) |> Map.ofList
        let regions =
            plan.Cuts
            |> List.map (fun cut ->
                cut.Ordinal,
                resumed graph cut.Statement |> List.fold (fun nodes item -> Set.union nodes (activation graph item)) Set.empty)
            |> Map.ofList
        let regionOf (cut: Cut) =
            match regions.TryFind cut.Ordinal with
            | Some nodes -> nodes
            | None -> Set.empty
        // The innermost cut whose resumed computation contains the position
        // and which retains the slot: its reload is the value in scope there.
        let reaching (position: NodeId) (slot: NodeId) =
            plan.Cuts
            |> List.filter (fun cut -> List.contains slot cut.Retained && Set.contains position (regionOf cut))
            |> List.sortBy (fun cut -> Set.count (regionOf cut))
            |> function
                | cut :: _ -> Some cut
                | [] -> None
        let range = { owner.Range with End = owner.Range.Start }
        let state = SaturationState.create range "Async.frame" (NodeId.value owner.Id) owner.Id graph.Platform
        let storage = Types.internalStorageType
        let unsettled (reason: string) = fail (XParsec.ErrorType.Message reason)
        let recipe =
            saturation {
                // Every cut statement is sequenced by a block: the items after it
                // are the computation its dispatch region resumes. A cut in any
                // other position has no such items, and no node is elaborated
                // for the formation.
                let! _ =
                    plan.Cuts |> C.collect (fun cut ->
                        saturation {
                            if (sequencingBlock graph cut.Statement).IsNone then
                                return! unsettled (sprintf "Suspension cut %d is not sequenced by a block; its resumed computation has no settled dispatch region." (NodeId.value cut.Site))
                            else
                                return ()
                        })
                // The typed state field declaration is the current version of the
                // formation's state anchor.
                do! enrich stateSlot stateSlot.Kind stateSlot.Type stateSlot.Children stateSlot.EmissionStrategy false
                let! allocation = C.create (SemanticKind.ContinuationAllocate plan.Frame) storage []
                let! frameBinding = letBind "__async_frame" allocation storage
                let frame = varRef "__async_frame" (Some frameBinding) storage

                // The reload of every slot retained across a cut that resumes
                // a computation in its block.
                let! reloads =
                    plan.Cuts |> C.collect (fun cut ->
                        saturation {
                            if (resumed graph cut.Statement).IsEmpty then
                                return cut.Ordinal, []
                            else
                                let! bindings =
                                    cut.Retained |> C.collect (fun slot ->
                                        saturation {
                                            match graph.Nodes.TryFind slot, declaredName graph slot with
                                            | Some source, Some name ->
                                                let! storageReference = frame
                                                let! value = C.read storageReference source
                                                let reloadName = sprintf "%s__resume_%d" name cut.Ordinal
                                                let! binding =
                                                    C.createWithRange source.ValueRange (SemanticKind.Binding(reloadName, false, false, None)) source.Type [ value ]
                                                return slot, (reloadName, binding)
                                            | _ ->
                                                return! unsettled (sprintf "Retained slot %d of suspension cut %d is not a named declaration." (NodeId.value slot) (NodeId.value cut.Site))
                                        })
                                return cut.Ordinal, bindings
                        })
                let reloadOf = reloads |> List.map (fun (ordinal, rows) -> ordinal, Map.ofList rows) |> Map.ofList
                let reloadAt (cut: Cut) (slot: NodeId) =
                    reloadOf.TryFind cut.Ordinal |> Option.bind (Map.tryFind slot)

                // The value of a slot at a position of the activation.
                let valueAt (position: NodeId) (slot: NodeId) : SaturationParser<NodeId> =
                    saturation {
                        match graph.Nodes.TryFind slot, declaredName graph slot with
                        | Some source, Some name ->
                            match reaching position slot with
                            | Some cut ->
                                match reloadAt cut slot with
                                | Some(reloadName, binding) ->
                                    return! C.createWithRange source.ValueRange (SemanticKind.VarRef(reloadName, Some binding)) source.Type []
                                | None ->
                                    return! unsettled (sprintf "Slot %d has no reload in the resumed computation of cut ordinal %d." (NodeId.value slot) cut.Ordinal)
                            | None ->
                                return! C.createWithRange source.ValueRange (SemanticKind.VarRef(name, Some slot)) source.Type []
                        | _ ->
                            return! unsettled (sprintf "Frame slot %d is not a named declaration." (NodeId.value slot))
                    }

                // A captured value at callable entry, read the way the
                // callable's own activation already reads that capture.
                let captureValue (slot: NodeId) : SaturationParser<NodeId> =
                    saturation {
                        let template =
                            scope |> Set.toList |> List.tryPick (fun id ->
                                match graph.Nodes.TryFind id with
                                | Some node when readDeclaration node = Some slot -> Some node
                                | _ -> None)
                        match template, graph.Nodes.TryFind slot, declaredName graph slot with
                        | Some({ Kind = SemanticKind.EnvironmentRead(environment, _) } as read), _, _ ->
                            match graph.Nodes.TryFind environment with
                            | Some({ Kind = SemanticKind.VarRef _ } as reference) ->
                                let! environmentReference = C.createWithRange reference.ValueRange reference.Kind reference.Type []
                                return! C.createWithRange read.ValueRange (SemanticKind.EnvironmentRead(environmentReference, slot)) read.Type [ environmentReference ]
                            | _ ->
                                return! unsettled (sprintf "Capture %d is read through an environment operand that is not a reference." (NodeId.value slot))
                        | Some { Kind = SemanticKind.VarRef _ }, Some source, Some name ->
                            return! C.createWithRange source.ValueRange (SemanticKind.VarRef(name, Some slot)) source.Type []
                        | None, Some source, Some name when captures |> List.exists (fun capture -> capture.SourceNodeId = Some slot) ->
                            return! C.createWithRange source.ValueRange (SemanticKind.VarRef(name, Some slot)) source.Type []
                        | _ ->
                            return! unsettled (sprintf "Capture %d has no settled read in the deferred callable." (NodeId.value slot))
                    }

                // Reads of a retained slot inside a resumed computation use
                // that computation's reload. Nested deferred callables keep
                // their capture references.
                let! _ =
                    scope |> Set.toList |> C.collect (fun id ->
                        saturation {
                            match graph.Nodes.TryFind id with
                            | Some node ->
                                match readDeclaration node with
                                | Some slot ->
                                    match reaching id slot with
                                    | Some cut ->
                                        match reloadAt cut slot with
                                        | Some(reloadName, binding) ->
                                            do! enrich node (SemanticKind.VarRef(reloadName, Some binding)) node.Type [] node.EmissionStrategy false
                                            return ()
                                        | None ->
                                            return! unsettled (sprintf "Read %d has no reload in the resumed computation of cut ordinal %d." (NodeId.value id) cut.Ordinal)
                                    | None -> return ()
                                | None -> return ()
                            | None -> return ()
                        })

                let stateWrite (ordinal: int) : SaturationParser<NodeId> =
                    saturation {
                        let! target = frame
                        let! value = C.integer ordinal
                        return! C.write target plan.State value
                    }

                let rec sequence (items: NodeId list) : SaturationParser<NodeId list> =
                    saturation {
                        match items |> List.tryFindIndex cutByStatement.ContainsKey with
                        | None -> return items
                        | Some index ->
                            match List.splitAt index items with
                            | before, statement :: following ->
                                match cutByStatement.TryFind statement with
                                | None ->
                                    return! unsettled (sprintf "Statement %d has no settled suspension cut." (NodeId.value statement))
                                | Some cut ->
                                    // A capture is stored at callable entry. A slot whose value
                                    // in scope is already a reload was stored before the enclosing
                                    // cut, which this statement's evaluation follows.
                                    let! spills =
                                        cut.Retained
                                        |> List.filter (fun slot -> not (List.contains slot plan.Captures) && (reaching statement slot).IsNone)
                                        |> C.collect (fun slot ->
                                            saturation {
                                                let! value = valueAt statement slot
                                                let! target = frame
                                                return! C.write target slot value
                                            })
                                    let! transition = stateWrite cut.Ordinal
                                    match following, List.tryLast following with
                                    | [], _ | _, None -> return before @ spills @ [ transition; statement ]
                                    | _, Some tail ->
                                        let! resumedItems = sequence following
                                        let reloadBindings = cut.Retained |> List.choose (fun slot -> reloadAt cut slot |> Option.map snd)
                                        let! result =
                                            saturation {
                                                match graph.Nodes.TryFind tail, List.tryLast resumedItems with
                                                | Some tailNode, Some value when plan.Results.Contains tail && value = tail ->
                                                    let! target = frame
                                                    let! store = C.write target tail value
                                                    return Some(tailNode, Some store)
                                                // A later cut of this block already stored the value.
                                                | Some tailNode, Some _ when plan.Results.Contains tail -> return Some(tailNode, None)
                                                | Some tailNode, Some _ when isUnit tailNode.Type -> return None
                                                | _ ->
                                                    return! unsettled (sprintf "The resumed computation ending at %d has a value and no settled frame slot." (NodeId.value tail))
                                            }
                                        // The store evaluates the resumed value as its operand.
                                        // The region sequences the store in the value's place, so
                                        // the frame write is the value's only parent.
                                        let regionItems =
                                            match result with
                                            | Some(_, Some store) ->
                                                let prefixItems =
                                                    if resumedItems.IsEmpty then []
                                                    else List.take (resumedItems.Length - 1) resumedItems
                                                reloadBindings @ prefixItems @ [ store ]
                                            | Some(_, None) -> reloadBindings @ resumedItems
                                            | None -> reloadBindings @ resumedItems
                                        let! region = C.block regionItems Types.unitType
                                        let! selectorFrame = frame
                                        let! selector = C.read selectorFrame stateSlot
                                        let! otherwise = unitLit
                                        let! dispatch = C.dispatch selector [ cut.Ordinal, region ] otherwise
                                        match result with
                                        | Some(tailNode, _) ->
                                            let! source = frame
                                            let! value = C.read source tailNode
                                            return before @ spills @ [ transition; statement; dispatch; value ]
                                        | None -> return before @ spills @ [ transition; statement; dispatch ]
                            | _, [] -> return items
                    }

                // Each block that directly sequences a cut statement.
                let blocks =
                    plan.Cuts
                    |> List.choose (fun cut -> sequencingBlock graph cut.Statement)
                    |> List.distinctBy (fun (block, _) -> block.Id)
                let! _ =
                    blocks |> C.collect (fun (block, items) ->
                        saturation {
                            let! elaborated = sequence items
                            do! enrich block (SemanticKind.Sequential elaborated) block.Type elaborated block.EmissionStrategy false
                            return ()
                        })

                // Callable entry: frame, captures, initial state, then the body.
                let! captureWrites =
                    plan.Captures |> C.collect (fun slot ->
                        saturation {
                            let! value = captureValue slot
                            let! target = frame
                            let! write = C.write target slot value
                            return slot, value, write
                        })
                let! initial = stateWrite (-1)
                let entryItems = frameBinding :: (captureWrites |> List.map (fun (_, _, write) -> write)) @ [ initial; body.Id ]
                let! entry = C.createWithRange body.ValueRange (SemanticKind.Sequential entryItems) body.Type entryItems
                let children = callable.Children |> List.map (fun child -> if child = body.Id then entry else child)
                do! enrich callable (SemanticKind.Lambda(parameters, entry, captures, enclosing, context)) callable.Type children callable.EmissionStrategy false
                return allocation, frameBinding, captureWrites |> List.map (fun (slot, value, _) -> slot, value)
            }
        match run state recipe with
        | Matched(allocation, frameBinding, captureInitializers), nodes ->
            let repeated = nodes |> List.countBy _.Id |> List.filter (fun (_, count) -> count > 1) |> List.map fst
            match repeated with
            | id :: _ -> residual id "An occurrence received more than one current version in the async continuation elaboration."
            | [] ->
                let references =
                    nodes |> List.choose (fun node ->
                        match node.Kind with
                        | SemanticKind.VarRef(_, Some definition) when definition = frameBinding -> Some node.Id
                        | _ -> None)
                Ok { Nodes = nodes
                     Edited = nodes |> List.filter (fun node -> graph.Nodes.ContainsKey node.Id) |> List.map _.Id |> Set.ofList
                     Allocation = allocation
                     FrameReferences = allocation :: frameBinding :: references
                     CaptureInitializers = captureInitializers
                     Reads =
                        nodes |> List.choose (fun node ->
                            match node.Kind with
                            | SemanticKind.FrameRead(_, slot) -> Some(node.Id, slot)
                            | _ -> None)
                     Writes =
                        nodes |> List.choose (fun node ->
                            match node.Kind with
                            | SemanticKind.FrameWrite(_, slot, value) -> Some(node.Id, slot, value)
                            | _ -> None)
                     Dispatches =
                        nodes |> List.collect (fun node ->
                            match node.Kind with
                            | SemanticKind.ContinuationDispatch(_, cases, _) -> cases |> List.map (fun (ordinal, _) -> node.Id, ordinal)
                            | _ -> []) }
        | NoMatch reason, _ -> residual plan.Formation reason
    | _ -> residual plan.Formation "The async formation lacks its deferred callable, body or state slot."

//-------------------------------------------------------------------------
// Orchestration join (clef#163, A-03)
//-------------------------------------------------------------------------

/// A structural edit of an existing occurrence: one child is replaced by the
/// listed occurrences, in order.
type Rewrite =
    { Target: NodeId
      Before: NodeId
      After: NodeId list }

/// The current version of an occurrence under its rewrites, applied in order.
/// A replacement by several occurrences is defined for a block only.
let rewrite (node: SemanticNode) (rewrites: Rewrite list) : Result<SemanticNode, string> =
    rewrites |> List.fold (fun current edit ->
        current |> Result.bind (fun (version: SemanticNode) ->
            match edit.After, version.Kind with
            | [ single ], _ ->
                Ok { version with
                        Kind = Clef.Compiler.Nanopass.FoldIn.remapKindReferences (Map.ofList [ edit.Before, single ]) version.Kind
                        Children = version.Children |> List.map (fun child -> if child = edit.Before then single else child) }
            | several, SemanticKind.Sequential items ->
                let spliced = items |> List.collect (fun item -> if item = edit.Before then several else [ item ])
                Ok { version with Kind = SemanticKind.Sequential spliced; Children = spliced }
            | _ ->
                Error (sprintf "Occurrence %d is not a block and cannot hold %d occurrences in place of one." (NodeId.value version.Id) edit.After.Length)))
        (Ok node)

type ChildArrayPlan =
    { /// The array expression of the child computations.
      Array: NodeId
      /// The immutable binding of that array.
      Tasks: NodeId }

/// One child computation bound to an immutable name of its own.
type ChildBinding =
    { Ordinal: int
      Name: string
      Binding: NodeId
      /// The element of the child array: a reference to the binding.
      Element: NodeId
      Computation: NativeType }

type ChildArray =
    { /// Every created node and the current version of the child array.
      Nodes: SemanticNode list
      Edited: Set<NodeId>
      Children: ChildBinding list
      /// The child bindings enter the block before the array's binding.
      Rewrite: Rewrite }

/// Bind every child computation of an orchestration's child array to an
/// immutable name. The bindings are sequenced, in element order, directly
/// in place of the array's binding in its block. A child activation reads its
/// child through that binding; the temporary descriptor array is retired.
let bindChildren (graph: SemanticGraph) (plan: ChildArrayPlan) : Result<ChildArray, Residual> =
    let residual site reason = Error { Formation = plan.Array; Site = site; Reason = reason }
    match graph.Nodes.TryFind plan.Array, graph.Nodes.TryFind plan.Tasks with
    | Some ({ Kind = SemanticKind.ArrayExpr elements } as array), Some ({ Kind = SemanticKind.Binding(_, false, _, _); Children = [ value ] } as tasks)
        when value = array.Id ->
        match sequencingBlock graph tasks.Id with
        | Some(block, _) ->
            let range = { array.Range with End = array.Range.Start }
            let state = SaturationState.create range "Async.children" (NodeId.value array.Id) array.Id graph.Platform
            let recipe =
                saturation {
                    let! children =
                        elements |> List.indexed |> C.collect (fun (ordinal, element) ->
                            saturation {
                                match graph.Nodes.TryFind element with
                                | Some source ->
                                    let name = sprintf "__async_child_%d_%d" (NodeId.value array.Id) ordinal
                                    let! binding = C.createWithRange source.ValueRange (SemanticKind.Binding(name, false, false, None)) source.Type [ element ]
                                    let! reference = C.createWithRange source.ValueRange (SemanticKind.VarRef(name, Some binding)) source.Type []
                                    return { Ordinal = ordinal; Name = name; Binding = binding; Element = reference; Computation = source.Type }
                                | None ->
                                    return! fail (XParsec.ErrorType.Message (sprintf "Child %d of the child array is not in the graph." (NodeId.value element)))
                            })
                    let references = children |> List.map _.Element
                    do! enrich array (SemanticKind.ArrayExpr references) array.Type references array.EmissionStrategy false
                    return children
                }
            match run state recipe with
            | Matched children, nodes ->
                Ok { Nodes = nodes
                     Edited = Set.singleton array.Id
                     Children = children
                     Rewrite = { Target = block.Id; Before = tasks.Id; After = children |> List.map _.Binding } }
            | NoMatch reason, _ -> residual array.Id reason
        | None -> residual tasks.Id "The binding of the child array is not sequenced by a block."
    | _ -> residual plan.Array "The child array is not an array expression bound directly to an immutable name."

/// One child work item of an orchestration, in result order.
type ChildPlan =
    { Child: ChildBinding
      /// The result type of the child's formation and its analysed range.
      Result: NativeType
      Range: ValueRange option }

type JoinPlan =
    { Orchestration: NodeId
      /// The activation that joins the orchestration.
      Join: NodeId
      /// The guarded result allocation, authored by ArrayConstructionRecipes.
      Storage: NodeId
      Children: ChildPlan list }

/// The explicit work item of one child: the application of an activator of
/// its own to the child, read through the child's binding, and the store of
/// its result into the join's result array at the child's result ordinal.
type ChildActivation =
    { Ordinal: int
      Site: SemanticNode
      /// The read of the child through its binding.
      Computation: NodeId
      /// The store of the child's result into the join's result array.
      Delivery: NodeId
      ResultTarget: NodeId
      CompletionTarget: NodeId }

type JoinElaboration =
    { /// Every created node.
      Nodes: SemanticNode list
      /// The guarded allocation the result array is bound to.
      Storage: NodeId
      /// The binding of the join's result array.
      Results: NodeId
      Activations: ChildActivation list
      /// The block of the join's operations takes the join's place in its parent.
      Rewrite: Rewrite }

/// Realize the join of a settled orchestration as explicit PSG operations.
/// The guarded result allocation is bound once. One activation
/// per child is applied to the child read through its binding, and each
/// result is stored into the result array at the child's result ordinal, in
/// result order. The block of these operations takes the join's place in its
/// parent, and the join application is no occurrence of the block. The
/// result array has no initial element: an element literal would be a store
/// into the element range that the readers of the array settled without it.
/// Formation identities, result layout and work dependencies are settled by
/// the caller.
let join (graph: SemanticGraph) (plan: JoinPlan) : Result<JoinElaboration, Residual> =
    let residual site reason = Error { Formation = plan.Orchestration; Site = site; Reason = reason }
    match graph.Nodes.TryFind plan.Join with
    | Some ({ Kind = SemanticKind.Application(callee, [ _ ]) } as site) ->
        match graph.Nodes.TryFind callee, site.Parent |> Option.bind graph.Nodes.TryFind with
        | Some ({ Kind = SemanticKind.Intrinsic _ } as activator), Some parent ->
            let anchors = activator.Children |> List.choose graph.Nodes.TryFind
            let range = { site.Range with End = site.Range.Start }
            let state = SaturationState.create range "Async.join" (NodeId.value site.Id) site.Id graph.Platform
            let resultsName = sprintf "__async_join_%d" (NodeId.value site.Id)
            let recipe =
                saturation {
                    // Each child delivers its element into the allocation
                    // before the block publishes the completed array.
                    let! results = C.create (SemanticKind.Binding(resultsName, false, false, None)) site.Type [ plan.Storage ]
                    let! activations =
                        plan.Children |> C.collect (fun child ->
                            saturation {
                                let! computation = C.create (SemanticKind.VarRef(child.Child.Name, Some child.Child.Binding)) child.Child.Computation []
                                // The child's activator has protocol anchors of its own.
                                let! protocol =
                                    anchors |> C.collect (fun anchor -> C.createWithRange anchor.ValueRange anchor.Kind anchor.Type [])
                                let! childActivator = C.create activator.Kind (NativeType.TFun(child.Child.Computation, child.Result)) protocol
                                let! activation =
                                    C.createWithRange child.Range (SemanticKind.Application(childActivator, [ computation ])) child.Result [ childActivator; computation ]
                                // Result delivery: the store at the child's result ordinal.
                                let! target = C.create (SemanticKind.VarRef(resultsName, Some results)) site.Type []
                                let! position = C.integer child.Child.Ordinal
                                let! delivery = C.create (SemanticKind.IndexSet(target, position, activation)) Types.unitType [ target; position; activation ]
                                match protocol with
                                | resultTarget :: _ :: completionTarget :: _ ->
                                    return child.Child.Ordinal, activation, computation, delivery, resultTarget, completionTarget
                                | _ ->
                                    return! fail (XParsec.ErrorType.Message (sprintf "The activator of join %d lacks its result and completion targets." (NodeId.value site.Id)))
                            })
                    let! value = C.create (SemanticKind.VarRef(resultsName, Some results)) site.Type []
                    let items = results :: (activations |> List.map (fun (_, _, _, delivery, _, _) -> delivery)) @ [ value ]
                    let! block = C.createWithRange site.ValueRange (SemanticKind.Sequential items) site.Type items
                    return results, block, activations
                }
            match run state recipe with
            | Matched(results, block, activations), nodes ->
                let created = nodes |> List.map (fun node -> node.Id, node) |> Map.ofList
                let settled =
                    activations |> List.choose (fun (ordinal, activation, computation, delivery, resultTarget, completionTarget) ->
                        created.TryFind activation |> Option.map (fun node ->
                            { Ordinal = ordinal
                              Site = node
                              Computation = computation
                              Delivery = delivery
                              ResultTarget = resultTarget
                              CompletionTarget = completionTarget }))
                if settled.Length <> plan.Children.Length || anchors.Length <> activator.Children.Length then
                    residual site.Id "A child activation of the orchestration join has no created occurrence."
                else
                    Ok { Nodes = nodes
                         Storage = plan.Storage
                         Results = results
                         Activations = settled
                         Rewrite = { Target = parent.Id; Before = site.Id; After = [ block ] } }
            | NoMatch reason, _ -> residual site.Id reason
        | _ -> residual plan.Join "The orchestration join does not apply an activation intrinsic within a parent occurrence."
    | _ -> residual plan.Join "The orchestration join is not an activation applied to its orchestration."
