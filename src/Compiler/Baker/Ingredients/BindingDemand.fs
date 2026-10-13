// SPDX-License-Identifier: MIT
/// Complete, bounded first-demand evidence for local mutable-cell snapshots.
/// This ingredient does not infer a general thunk/cache representation.
module Clef.Compiler.Baker.Ingredients.BindingDemand

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Identity = Clef.Compiler.NativeTypedTree.TypeIdentities
module Incidence = Clef.Compiler.Baker.Ingredients.Closures

type Slot = { Parent: NodeId; Ordinal: int; Statement: NodeId }
/// One conditional step on the way into an activation: the guard demanded, the
/// decision statement, the arm taken (0 then, 1 else) and the decision's own scope.
type ConditionalEntry = { Guard: NodeId; Decision: NodeId; Arm: int; Parent: NodeId }
/// A linear activation: a lambda body, or the `Sequential` arm of a reached
/// decision inside one. `Prefix` lists the enclosing activations' statements that
/// run before the decision; `Entry` the conditional path from the lambda body.
type Activation = { Owner: NodeId; Body: NodeId; Slots: Slot list; Prefix: NodeId list; Entry: ConditionalEntry list }
type Schedule = {
    Binding: NodeId
    Family: NodeId list
    Slots: Slot list
    Desired: NodeId list
    Evidence: BindingDemandEvidence
    Pending: string option
}

let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
let owned edge =
    match edge.Role with
    | EdgeRole.OrdinaryBindingDemand _ | EdgeRole.OrdinaryBindingDemandPending _ -> true
    | _ -> false

let private currentValidity (graph: SemanticGraph) (nodes: Map<NodeId, SemanticNode>) =
    let recordedAt = graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference)
                     |> List.groupBy _.Target |> Map.ofList
    let validity = System.Collections.Generic.Dictionary<NodeId, bool>()
    let valid id =
        match validity.TryGetValue id with
        | true, value -> value
        | _ ->
            let value =
                match nodes.TryFind id with
                | None -> false
                | Some node ->
                    let expected = Incidence.structuralIncidence node |> List.map key
                    let actual = recordedAt.TryFind id |> Option.defaultValue [] |> List.filter (fun edge -> edge.Role <> EdgeRole.Resides) |> List.map key
                    let children = kindEdges id node.Kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources
                    let childrenAgree = match node.Kind with SemanticKind.Binding _ -> node.Children.Length = 1 | _ -> node.Children = children
                    childrenAgree && (node.Children |> List.forall nodes.ContainsKey) &&
                    actual.Length = (List.distinct actual).Length && actual |> List.forall (fun row -> List.contains row expected)
            validity.Add(id, value)
            value
    valid

let private readActivations (nodes: Map<NodeId, SemanticNode>) (valid: NodeId -> bool) =
    // The selected arm is the demand unit (Expressions, Default Demand and Sharing):
    // one activation per lambda body and, nested in it, one per `Sequential` arm of a
    // reached decision. Runtime selection is the arm's activation condition, not a
    // claim that the guard is statically known.
    let rec walk seen parent ordinal id =
        if Set.contains id seen then None else
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.Sequential values } when valid id ->
            let children = values |> List.mapi (fun ordinal child -> walk (Set.add id seen) id ordinal child)
            if children |> List.exists Option.isNone then None else Some(List.collect Option.get children)
        | Some _ -> Some [{ Parent = parent; Ordinal = ordinal; Statement = id }]
        | None -> None
    let rec armActivations (seen: Set<NodeId>) (activation: Activation) : Activation list =
        activation.Slots |> List.indexed |> List.collect (fun (index, slot) ->
            match nodes.TryFind slot.Statement with
            | Some { Kind = SemanticKind.IfThenElse(condition, thenArm, elseArm) }
                when valid slot.Statement && not (Set.contains slot.Statement seen) ->
                let prefix = activation.Prefix @ (activation.Slots |> List.take index |> List.map _.Statement)
                [ Some(0, thenArm); elseArm |> Option.map (fun arm -> 1, arm) ] |> List.choose id |> List.collect (fun (ordinal, arm) ->
                    match nodes.TryFind arm with
                    | Some { Kind = SemanticKind.Sequential _ } when valid arm ->
                        match walk (Set.add slot.Statement seen) slot.Statement (ordinal + 1) arm with
                        | Some slots ->
                            let nested =
                                { Owner = activation.Owner; Body = arm; Slots = slots; Prefix = prefix
                                  Entry = activation.Entry @ [ { Guard = condition; Decision = slot.Statement; Arm = ordinal; Parent = activation.Body } ] }
                            nested :: armActivations (Set.add slot.Statement seen) nested
                        | None -> []
                    | _ -> [])
            | _ -> [])
    let activations =
        nodes.Values |> Seq.collect (fun code ->
            match code.Kind with
            | SemanticKind.Lambda(_, body, _, _, _) ->
                match walk Set.empty code.Id 0 body with
                | Some slots ->
                    let root = { Owner = code.Id; Body = body; Slots = slots; Prefix = []; Entry = [] }
                    root :: armActivations Set.empty root
                | None -> []
            | _ -> []) |> Seq.toList
    activations

/// Current source order in each activation, including its dominating conditional prefix.
/// Consumers still require unique statement ownership for their exact occurrence census.
let activationFacts (graph: SemanticGraph) : Activation list =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    readActivations nodes (currentValidity graph nodes)

let analyze (graph: SemanticGraph) : Schedule list =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let local (node: SemanticNode) = node.Metadata.TryFind "SourceBinding.Local" = Some(MetadataValue.Bool true)
    let scalar id =
        match nodes.TryFind id with
        | Some node ->
            match Identity.ofType node.Type with
            | TypeIdentity.Numeric _ -> true
            | identity -> identity = Identity.ofType Types.boolType
        | None -> false
    let alias (node: SemanticNode) =
        match node.Kind, node.Children with
        | SemanticKind.Binding(_, false, false, None), [value] when local node ->
            match nodes.TryFind value with
            | Some { Kind = SemanticKind.VarRef(_, Some source) } -> Some(value, source)
            | _ -> None
        | _ -> None
    let aliases = nodes.Values |> Seq.choose (fun node -> alias node |> Option.map (fun pair -> node.Id, pair)) |> Map.ofSeq
    // No source candidate means there can be no schedule. Current-row validation
    // still compares this empty result with retained rows, so stale admission is
    // not hidden by the shortcut. No global absence/capture proof is skipped for
    // an actual candidate.
    let candidates = aliases |> Map.toList |> List.filter (fun (binding, (_, cell)) ->
        match nodes.TryFind cell with
        | Some { Kind = SemanticKind.Binding(_, true, _, _) } -> scalar binding
        | _ -> false)
    if candidates.IsEmpty then [] else
    let recorded = graph.Edges |> List.filter (fun edge ->
        edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference)
    // Preserve every duplicate and its order: these are proof premises, not a
    // set. Indexing avoids rescanning the entire edge list at each scope node.
    let incidence = nodes.Values |> Seq.collect Incidence.structuralIncidence |> Seq.toList
    let census = incidence @ recorded |> List.filter (fun edge -> nodes.ContainsKey edge.Target) |> List.distinctBy key
    let uses = census |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge))
               |> List.groupBy fst |> Map.ofList |> Map.map (fun _ rows -> List.map snd rows)
    let usesOf id = uses.TryFind id |> Option.defaultValue []
    let structuralParents id = usesOf id |> List.filter (fun edge -> edge.Class = EdgeClass.Structural)
    let valid = currentValidity graph nodes
    let activations = readActivations nodes valid
    candidates |> List.choose (fun (binding, (initialRead, cell)) ->
        match nodes.TryFind cell with
        | Some { Kind = SemanticKind.Binding(_, true, _, _) } when scalar binding ->
            let mutable reason = None
            let reject text = if reason.IsNone then reason <- Some text
            let mutable participants = []
            let add role group ordinal node =
                participants <- { Node = node; Role = role; Group = group; Ordinal = ordinal } :: participants
            let rec family found =
                let next = aliases |> Map.toList |> List.choose (fun (id, (_, source)) -> if Set.contains source found then Some id else None) |> Set.ofList
                let next = Set.union found next
                if next = found then found else family next
            let familySet = family (Set.singleton binding)
            if not (valid cell) then reject "The mutable cell has malformed initialization incidence."
            add ParticipantRole.DemandBinding binding 0 binding
            add ParticipantRole.DemandCell binding 0 cell
            add ParticipantRole.DemandInitializer binding 0 initialRead
            let owners = activations |> List.filter (fun activation -> activation.Slots |> List.exists (fun slot -> slot.Statement = binding))
            let activation =
                match owners with
                | [activation] -> activation
                | _ ->
                    reject "The snapshot has no unique linear activation scope."
                    { Owner = binding; Body = binding; Slots = []; Prefix = []; Entry = [] }
            let scope, body, slots = activation.Owner, activation.Body, activation.Slots
            add ParticipantRole.DemandScope binding 0 scope
            add ParticipantRole.DemandScope binding 1 body
            // The conditional entry path is part of the proof: each decision, its guard and the
            // arm taken carry provenance, so a changed guard or arm retracts the schedule.
            for depth, entry in List.indexed activation.Entry do
                let armBody = if depth + 1 < activation.Entry.Length then activation.Entry[depth + 1].Parent else body
                add ParticipantRole.DemandPremise scope (2 + depth) entry.Decision
                add ParticipantRole.DemandPremise entry.Decision 0 entry.Guard
                add ParticipantRole.DemandPremise entry.Decision (entry.Arm + 1) armBody
                if not (valid entry.Decision) then reject "A conditional entry's Kind and attached/recorded incidence disagree."
            let statements = slots |> List.map _.Statement
            let index id = statements |> List.tryFindIndex ((=) id)
            let orderedFamily = statements |> List.filter familySet.Contains
            if orderedFamily.Length <> familySet.Count || orderedFamily |> List.distinct |> List.length <> familySet.Count then
                reject "Every immutable alias must occur exactly once in the same linear activation."
            // The cell is established earlier in this activation or in a dominating prefix of an
            // enclosing one; entering the arm does not freeze its value.
            let cellEstablished =
                match index cell, index binding with
                | Some cellAt, Some bindingAt -> cellAt < bindingAt
                | None, Some _ ->
                    match List.tryFindIndex ((=) cell) activation.Prefix with
                    | Some at ->
                        // The dominating prefix is schedule evidence: the cell and every
                        // statement after it up to the decision, in order, so a cell moved
                        // past the decision retracts the retained proof instead of keeping it.
                        activation.Prefix |> List.skip at |> List.iteri (fun ordinal statement ->
                            add ParticipantRole.DemandPremise cell ordinal statement)
                        true
                    | None -> false
                | _ -> false
            if not cellEstablished then reject "The mutable cell must be established earlier in this activation."
            for ordinal, slot in List.indexed slots do
                add ParticipantRole.DemandStatement slot.Parent ordinal slot.Statement
                add ParticipantRole.DemandPremise scope slot.Ordinal slot.Parent
                match structuralParents slot.Statement with
                | [edge] when edge.Target = slot.Parent && nodes[slot.Statement].Parent = Some slot.Parent -> ()
                | _ -> reject "A statement has missing, repeated or independent structural ownership."
                if not (valid slot.Parent) then reject "The linear scope's Kind and attached/recorded incidence disagree."
            let familyReads = aliases |> Map.filter (fun id _ -> familySet.Contains id) |> Map.toList
            let aliasReads = familyReads |> List.map (fun (_, (read, _)) -> read) |> Set.ofList
            for aliasId, (read, source) in familyReads do
                add ParticipantRole.DemandAlias aliasId 0 aliasId
                add ParticipantRole.DemandInitializer aliasId 0 read
                add ParticipantRole.DemandCell aliasId 0 source
                if not (valid aliasId && valid read) || nodes[read].Parent <> Some aliasId ||
                   Identity.ofType nodes[aliasId].Type <> Identity.ofType nodes[read].Type ||
                   Identity.ofType nodes[read].Type <> Identity.ofType nodes[source].Type then
                    reject "The alias/read/source types or exact initializer incidence disagree."
                match structuralParents read with
                | [edge] when edge.Target = aliasId -> ()
                | _ -> reject "An initializer read has independent structural uses."
                if source <> cell && index source >= index aliasId then reject "The immutable alias dependency order is cyclic or reversed."
            let references =
                familySet |> Set.toList |> List.collect (fun id ->
                    usesOf id |> List.choose (fun edge ->
                        add ParticipantRole.DemandPremise edge.Target edge.Ordinal id
                        match edge.Class, edge.Role, nodes.TryFind edge.Target with
                        | EdgeClass.Structural, _, Some { Kind = SemanticKind.Sequential _ }
                            when slots |> List.exists (fun slot -> slot.Statement = id && slot.Parent = edge.Target) -> None
                        | EdgeClass.Reference, EdgeRole.Definition, Some { Kind = SemanticKind.VarRef(_, Some source) }
                            when source = id && edge.Sources = [id] && edge.Ordinal = 0 -> Some edge.Target
                        | _ -> reject "An independent or non-reference family use has no supported demand contract."; None)) |> List.distinct
            for node in nodes.Values do
                let captures =
                    match node.Kind with
                    | SemanticKind.Lambda(_, _, captures, _, _) | SemanticKind.SeqExpr(_, captures) | SemanticKind.LazyExpr(_, captures) -> captures
                    | _ -> []
                for ordinal, capture in List.indexed captures do
                    if (capture.SourceNodeId |> Option.exists familySet.Contains) ||
                       (capture.SourceNodeId.IsNone && Identity.ofType capture.Type = Identity.ofType nodes[binding].Type) then
                        add ParticipantRole.DemandUse node.Id ordinal (capture.SourceNodeId |> Option.defaultValue node.Id)
                        reject "A captured or unresolved capture identity requires a shared runtime carrier."
            let realReads = references |> List.filter (aliasReads.Contains >> not)
            // Only total, effect-free condition operands may precede the moved
            // read. An arbitrary callee or arithmetic expression is no proof.
            let rec pureDemand seen id =
                if Set.contains id seen || not (valid id) then None else
                let seen = Set.add id seen
                add ParticipantRole.DemandPremise id 0 id
                for ordinal, child in List.indexed nodes[id].Children do add ParticipantRole.DemandPremise id ordinal child
                match nodes[id].Kind with
                | SemanticKind.Literal _ -> Some []
                | SemanticKind.VarRef(_, Some source) when familySet.Contains source -> Some [id]
                | SemanticKind.EagerExpr value when nodes.ContainsKey value && Identity.ofType nodes[id].Type = Identity.ofType nodes[value].Type ->
                    pureDemand seen value
                // A branch demands its condition and only then a selected arm (Expressions, Default
                // Demand and Sharing); `&&`/`||` reach here as a decision whose arms stay conditional.
                | SemanticKind.IfThenElse(condition, _, _) when nodes.ContainsKey condition -> pureDemand seen condition
                | SemanticKind.TypeAnnotation(value, declared)
                    when nodes.ContainsKey value && Identity.ofType nodes[id].Type = Identity.ofType declared && Identity.ofType declared = Identity.ofType nodes[value].Type ->
                    pureDemand seen value
                | SemanticKind.Application(callee, [left; _])
                    when (match nodes.TryFind callee with
                          | Some { Kind = SemanticKind.Intrinsic intrinsic } ->
                              valid callee && intrinsic.Module = IntrinsicModule.Operators &&
                              List.contains intrinsic.Operation [ "op_BooleanAnd"; "op_BooleanOr" ]
                          | _ -> false) ->
                    // `&&` and `||` demand their left operand first and retain the right as a
                    // shared deferred operand (Expressions, logical operators): only the left
                    // operand is an unconditional first demand.
                    pureDemand seen left
                | SemanticKind.Application(callee, ([left; right] as arguments)) ->
                    match nodes.TryFind callee with
                    | Some { Kind = SemanticKind.Intrinsic intrinsic }
                        when intrinsic.Category = IntrinsicCategory.Comparison && valid callee &&
                             List.contains intrinsic.Operation ["op_Equality"; "op_Inequality"; "op_LessThan"; "op_LessThanOrEqual"; "op_GreaterThan"; "op_GreaterThanOrEqual"] &&
                             Identity.ofType nodes[left].Type = Identity.ofType nodes[right].Type &&
                             Identity.ofType nodes[id].Type = Identity.ofType Types.boolType ->
                        let operands = arguments |> List.map (pureDemand seen)
                        if operands |> List.exists Option.isNone then None else Some(List.collect Option.get operands)
                    | _ -> None
                | _ -> None
            let terminal = List.tryLast statements
            let demandAt statement =
                match nodes[statement].Kind, nodes[statement].Children with
                | SemanticKind.Binding(_, false, _, _), [value] ->
                    match nodes[value].Kind with SemanticKind.EagerExpr _ -> pureDemand Set.empty value | _ -> None
                | SemanticKind.IfThenElse(condition, _, _), _ -> pureDemand Set.empty condition
                | SemanticKind.EagerExpr _, _ -> pureDemand Set.empty statement
                // A direct terminal reference, or a transparent wrapper of one, is demanded as the
                // activation's own result: its selection is the only condition.
                | SemanticKind.VarRef(_, Some source), _ when Some statement = terminal && familySet.Contains source -> Some [ statement ]
                | SemanticKind.TypeAnnotation _, _ when Some statement = terminal -> pureDemand Set.empty statement
                | _ -> None
            let demandRows =
                slots |> List.indexed |> List.choose (fun (ordinal, slot) ->
                    if familySet.Contains slot.Statement then None else
                    demandAt slot.Statement |> Option.filter (List.isEmpty >> not)
                    |> Option.map (fun reads -> ordinal, slot.Statement, reads))
            let covered = demandRows |> List.collect (fun (_, _, reads) -> reads)
            if Set.ofList covered <> Set.ofList realReads || covered.Length <> realReads.Length || realReads.IsEmpty then
                reject "Every use requires one unconditional first-demand path in the same linear activation; branches, loops, escapes and opaque consumers remain pending."
            for ordinal, statement, reads in demandRows do
                for read in reads do
                    add ParticipantRole.DemandUse statement ordinal read
                    let rec path seen id =
                        if Set.contains id seen || not (valid id) then reject "The demanding path is malformed or cyclic."
                        elif id = statement then ()
                        else
                            match structuralParents id with
                            | [edge] when nodes[id].Parent = Some edge.Target ->
                                add ParticipantRole.DemandPremise edge.Target edge.Ordinal id
                                path (Set.add id seen) edge.Target
                            | _ -> reject "The demanding read has independent, absent or repeated structural ownership."
                    path Set.empty read
            let frontier = demandRows |> List.tryHead |> Option.map (fun (_, statement, _) -> statement)
            frontier |> Option.iter (add ParticipantRole.DemandFrontier scope 0)
            let desired =
                match frontier with
                | Some first ->
                    // Other scalar snapshots at this same frontier only copy
                    // cells. Their order cannot change those cells. Keeping an
                    // existing contiguous family group avoids alternating two
                    // equivalent schedules when several roots share a demand.
                    let rec scalarSnapshot seen id =
                        if Set.contains id seen || not (scalar id) then false else
                        match aliases.TryFind id with
                        | Some(_, source) ->
                            match nodes.TryFind source with
                            | Some { Kind = SemanticKind.Binding(_, true, _, _) } -> true
                            | _ -> scalarSnapshot (Set.add id seen) source
                        | None -> false
                    let before = statements |> List.takeWhile ((<>) first)
                    let suffix = before |> List.rev |> List.takeWhile (scalarSnapshot Set.empty) |> Set.ofList
                    if familySet.IsSubsetOf suffix then statements
                    else statements |> List.filter (familySet.Contains >> not) |> List.collect (fun id -> if id = first then orderedFamily @ [id] else [id])
                | None -> statements
            let evidence =
                let occurrences = List.rev participants
                { Participants = occurrences
                  SourceTypes = occurrences |> List.map _.Node |> Set.ofList |> Set.toList |> List.choose (fun id ->
                      nodes.TryFind id |> Option.map (fun node -> id, Identity.ofType node.Type)) |> Map.ofList }
            Some { Binding = binding; Family = orderedFamily; Slots = slots; Desired = desired; Evidence = evidence; Pending = reason }
        | _ -> None)

let edges schedules =
    schedules |> List.map (fun schedule ->
        let reason =
            match schedule.Pending with
            | Some reason -> Some reason
            | None when schedule.Desired <> (schedule.Slots |> List.map _.Statement) -> Some "The initializer has not been scheduled at its proved first-demand frontier."
            | None -> None
        { Class = EdgeClass.Demand; Target = schedule.Binding; Ordinal = 0
          Sources = schedule.Evidence.Participants |> List.map _.Node
          Role = match reason with None -> EdgeRole.OrdinaryBindingDemand schedule.Evidence | Some text -> EdgeRole.OrdinaryBindingDemandPending(text, schedule.Evidence) })

let failures graph : WitnessProjectionFailure list =
    let expected = analyze graph |> edges
    let actual = graph.Edges |> List.filter owned
    let targets = expected @ actual |> List.map _.Target |> Set.ofList
    targets |> Set.toList |> List.choose (fun target ->
        let rows = expected |> List.filter (fun edge -> edge.Target = target)
        let retained = actual |> List.filter (fun edge -> edge.Target = target)
        let pending = rows |> List.tryPick (fun edge -> match edge.Role with EdgeRole.OrdinaryBindingDemandPending(reason, _) -> Some reason | _ -> None)
        let reason =
            if List.map key rows <> List.map key retained then Some "The current binding demand relation differs from its complete typed scope/use proof."
            else pending
        reason |> Option.map (fun reason ->
            { Kind = WitnessProjectionFailureKind.Settlement; Occurrence = Some target; Reason = "PSG settlement (OrdinaryBindingDemand): " + reason
              Participants = rows @ retained |> List.collect (fun edge -> edge.Target :: edge.Sources) |> Set.ofList }))
