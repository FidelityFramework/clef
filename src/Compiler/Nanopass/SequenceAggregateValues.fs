// SPDX-License-Identifier: MIT
/// Settle value snapshots of scalar-payload Option currents before continuation
/// control is realized. Allocation occurrences and all uses must share a proven
/// activation; deferred/escaping uses remain explicit residuals.
module Clef.Compiler.Nanopass.SequenceAggregateValues

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Ingredients.Closures
open Clef.Compiler.Baker.Ingredients.Obligations
open Clef.Compiler.Nanopass.Recipe
module Values = Clef.Compiler.PSGSaturation.SemanticGraph.AggregateValues
module C = Clef.Compiler.Baker.Ingredients.Continuations
module Copy = Clef.Compiler.Baker.Ingredients.AggregateCopies
module Layout = Clef.Compiler.Baker.Recipes.ContinuationObligationRecipes

/// Public for component tests: proof depends on every resident semantic use,
/// not Parent fields or a lexical module's lifetime.
let coveringActivation (graph: SemanticGraph) source =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let structural = nodes.Values |> Seq.collect (fun node ->
        let edges = kindEdges node.Id node.Kind
        let explicit = edges |> List.filter Hyperedge.isStructural |> List.collect _.Sources |> Set.ofList
        edges |> List.filter Hyperedge.isStructural
        |> fun edges -> edges @ (node.Children |> List.filter (fun id -> not (explicit.Contains id))
                               |> List.mapi (fun ordinal id -> Hyperedge.edge1 EdgeClass.Structural EdgeRole.Attached ordinal id node.Id))) |> Seq.toList
    let parents = structural |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge.Target))
                  |> List.groupBy fst |> Map.ofList |> Map.map (fun _ values -> values |> List.map snd |> List.distinct)
    let activation id =
        let rec visit seen remaining owners invalid =
            match remaining with
            | [] -> if not invalid && Set.count owners = 1 then Some(Set.minElement owners) else None
            | current :: rest when Set.contains current seen -> visit seen rest owners invalid
            | current :: rest ->
                let seen = Set.add current seen
                match nodes.TryFind current with
                | Some { Kind = SemanticKind.Lambda _ } -> visit seen rest (Set.add current owners) invalid
                | Some { Kind = SemanticKind.ModuleDef _ } -> visit seen rest owners true
                | _ -> match parents.TryFind current with
                       | Some containers when not containers.IsEmpty -> visit seen (containers @ rest) owners invalid
                       | _ -> visit seen rest owners true
        visit Set.empty [id] Set.empty false
    let uses = structural |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge))
               |> List.groupBy fst |> Map.ofList |> Map.map (fun _ uses -> List.map snd uses)
    let references =
        nodes.Values |> Seq.choose (fun node ->
            match node.Kind with SemanticKind.VarRef(_, Some definition) -> Some(definition, node.Id) | _ -> None)
        |> Seq.groupBy fst |> Seq.map (fun (id, values) -> id, values |> Seq.map snd |> Seq.toList) |> Map.ofSeq
    let captured = nodes.Values |> Seq.collect (fun node ->
        let captures = match node.Kind with SemanticKind.SeqExpr(_, captures) | SemanticKind.Lambda(_, _, captures, _, _) -> captures | _ -> []
        captures |> List.choose (fun capture -> capture.SourceNodeId |> Option.map (fun source -> source, node.Id))) |> Seq.toList
    let opaque = graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Reference)
    let mutable support = Set.empty
    let rec walk owner seen pending =
        match pending with
        | [] -> Ok(owner, Set.union seen support |> Set.toList)
        | value :: rest when Set.contains value seen -> walk owner seen rest
        | value :: rest ->
            let seen = Set.add value seen
            if activation value <> Some owner then Error value
            elif captured |> List.exists (fun (source, _) -> source = value) then Error value
            else
                let aliases = ResizeArray<NodeId>()
                let mutable invalid = None
                let alias id = aliases.Add id
                for reference in references.TryFind value |> Option.defaultValue [] do alias reference
                for edge in opaque do
                    if edge.Sources |> List.contains value then
                        match nodes.TryFind edge.Target with
                        | Some { Kind = SemanticKind.VarRef(_, Some definition) } when definition = value -> ()
                        | _ -> invalid <- Some edge.Target
                for edge in uses.TryFind value |> Option.defaultValue [] do
                    let target = nodes[edge.Target]
                    support <- Set.add target.Id support
                    if activation target.Id <> Some owner then invalid <- Some target.Id
                    else
                        match target.Kind, edge.Role with
                        | SemanticKind.Binding _, _ | SemanticKind.TypeAnnotation _, _ -> alias target.Id
                        | SemanticKind.Sequential values, _ -> if List.tryLast values = Some value then alias target.Id
                        | SemanticKind.IfThenElse _, (EdgeRole.ThenBranch | EdgeRole.ElseBranch)
                        | SemanticKind.CaseElimination _, EdgeRole.CaseBody -> alias target.Id
                        | SemanticKind.CaseElimination _, (EdgeRole.Scrutinee | EdgeRole.CaseBinding) -> ()
                        | SemanticKind.IfThenElse _, EdgeRole.Guard -> ()
                        | SemanticKind.DUConstruct _, EdgeRole.Payload -> alias target.Id
                        | SemanticKind.DUGetTag _, _ -> ()
                        | SemanticKind.DUEliminate _, _ ->
                            match Types.tryGetNTUKind target.Type with
                            | Some (NTUKind.NTUint _ | NTUKind.NTUuint _ | NTUKind.NTUfloat _ | NTUKind.NTUposit _
                                  | NTUKind.NTUbool | NTUKind.NTUchar | NTUKind.NTUunit) -> ()
                            | _ -> alias target.Id
                        | SemanticKind.Set(reference, _), EdgeRole.AssignValue ->
                            match nodes.TryFind reference with
                            | Some { Kind = SemanticKind.VarRef(_, Some declaration) } -> alias declaration
                            | _ -> invalid <- Some target.Id
                        | SemanticKind.Set _, EdgeRole.AssignTarget -> ()
                        | SemanticKind.Yield _, _ ->
                            match nodes[owner].Kind with
                            | SemanticKind.Lambda(_, _, _, _, LambdaContext.SeqGenerator) -> ()
                            | _ -> invalid <- Some target.Id
                        | SemanticKind.Application(callee, _), EdgeRole.Argument ->
                            match nodes.TryFind callee with
                            | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Operators; Operation = "ignore" } } -> ()
                            | _ -> invalid <- Some target.Id
                        | _ -> invalid <- Some target.Id
                match invalid with
                | Some site -> Error site
                | None -> walk owner seen (List.ofSeq aliases @ rest)
    match activation source with
    | None -> Error source
    | Some owner -> walk owner Set.empty [source]

type Prepared = {
    Graph: SemanticGraph
    Reads: Set<NodeId>
    Certificates: Hyperedge list
    Residences: Map<NodeId, EscapeKind>
    Unresolved: (NodeId * NodeId) list
}

let prepare (graph: SemanticGraph) admitted certificates =
    let candidates = admitted |> Set.toList |> List.choose (fun id ->
        Values.scalarOption graph graph.Nodes[id].Type |> Option.map (fun layout -> id, layout))
    let freshReads, freshCertificates = SequenceCurrentAdmission.certify graph
    let mutable certificates = certificates
    let mutable reads = admitted
    let mutable residences = Map.empty
    let mutable proofs = Enrichment.empty
    let mutable recipes = Map.empty
    let mutable unresolved = []
    for id, (inner, bytes, alignment) in candidates do
        let source = graph.Nodes[id]
        let certificateRows edges =
            edges |> List.filter (fun edge -> edge.Target = id)
            |> List.map (fun edge -> edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target)
        let certificateValid = freshReads.Contains id && certificateRows certificates = certificateRows freshCertificates
        match (if certificateValid then coveringActivation graph id else Error id) with
        | Error site -> unresolved <- (id, site) :: unresolved
        | Ok(owner, _) when (match graph.Nodes[owner].Kind with SemanticKind.Lambda(_, _, _, _, LambdaContext.SeqGenerator) -> true | _ -> false) ->
            // Machine writes already copy this current into its own selected
            // value slot before another pull. No transient descriptor escapes.
            ()
        | Ok(owner, uses) ->
            let state = SaturationState.create { source.Range with End = source.Range.Start } "Seq.currentSnapshot" (NodeId.value id) id graph.Platform
            let result, nodes = run state (saturation {
                let! state = getUserState
                let raw = { mkNode state source.Kind source.Type source.Children with ValueRange = source.ValueRange }
                do! emit raw
                let! observed = letBind "__option_current_view" raw.Id source.Type
                let! storage = C.create (SemanticKind.AggregateStorage id) source.Type []
                let! owned = letBind "__option_current_snapshot" storage source.Type
                let! input = varRef "__option_current_view" (Some observed) source.Type
                let! destination = varRef "__option_current_snapshot" (Some owned) source.Type
                let! copy, relation = Copy.option input destination inner
                let! result = varRef "__option_current_snapshot" (Some owned) source.Type
                let children = [observed; owned; copy; result]
                do! emit { source with Kind = SemanticKind.Sequential children; Children = children }
                return raw.Id, storage, relation
            })
            match result with
            | NoMatch reason -> invalidOp (sprintf "Current snapshot synthesis failed: %s" reason)
            | Matched(raw, storage, relation) ->
                let evidence = certificates |> List.find (fun edge -> edge.Target = id)
                let evidence = { evidence with Target = raw; Sources = List.distinct (id :: evidence.Sources) }
                certificates <- certificates |> List.filter (fun edge -> edge.Target <> id) |> fun others -> evidence :: others
                reads <- reads.Remove(id).Add(raw)
                let lifetime = {
                    Sources = List.distinct (raw :: storage :: owner :: evidence.Sources @ uses)
                    Target = id; Class = EdgeClass.Provenance; Role = EdgeRole.AggregateSnapshot; Ordinal = 0 }
                let layout = Layout.layout (NodeId.value storage) "option_snapshot" source [(storage, 0, bytes, alignment)] bytes alignment
                proofs <- Enrichment.concat [proofs; { layout with NewEdges = relation :: lifetime :: layout.NewEdges }]
                match graph.Nodes[owner].Kind with
                | SemanticKind.Lambda(_, _, _, _, LambdaContext.SeqGenerator) -> ()
                | _ -> residences <- residences.Add(storage, EscapeKind.StackScoped)
                recipes <- recipes.Add(id, RecipeCreated {
                    OriginalNodeId = id; ReplacementRootId = id; NewNodes = nodes
                    ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = "Seq.currentSnapshot" })
    let rewritten =
        if recipes.IsEmpty then graph
        else FoldIn.foldIn (FanOut.fanOut "SequenceAggregateValues" (fun node -> recipes.ContainsKey node.Id) (fun node _ -> recipes[node.Id]) graph) graph
    let rewritten = { rewritten with Layouts = graph.Layouts; FieldRanges = graph.FieldRanges; ElementRanges = graph.ElementRanges; StaticStringPool = graph.StaticStringPool }
    let rewritten = ObligationElaboration.foldIn proofs rewritten
    { Graph = rewritten; Reads = reads; Certificates = certificates; Residences = residences; Unresolved = List.rev unresolved }
