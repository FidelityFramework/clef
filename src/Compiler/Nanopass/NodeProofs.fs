// SPDX-License-Identifier: MIT

/// Node Proofs -- the tier 2 nanopass.
///
/// A tier 2 obligation is created when the structure it is about exists and is
/// reachable, whether or not that structure is demanded. Creation and dispatch
/// are separate: an obligation is dispatched when its premises are settled.
/// Demand decides the pool and residence. It does not decide whether a proof
/// exists.
///
/// The pass receives the new nodes as a value -- at the first reachability
/// marking, every node of the graph -- and reads no store. Today it creates
/// the storage, view and sentinel proofs of the reachable string literals among
/// them: one triple for each text, with every reachable node of that text a
/// participant. Every term of those statements is a fact of the literal's text.
///
/// Pure: `create` returns a new graph.
module Clef.Compiler.Nanopass.NodeProofs

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration
open Clef.Compiler.Baker.Ingredients.Obligations
module Recipes = Clef.Compiler.Baker.Recipes.ObligationRecipes

/// The reachable string literals among the new nodes, grouped by text in the
/// pool's order: entry-unit texts first, then by file, line and column.
let private sourceOrder (graph: SemanticGraph) =
    let entryFile =
        match graph.DeclarationRoots with
        | (entryId, _) :: _ -> SemanticGraph.tryGetNode entryId graph |> Option.map (fun n -> n.Range.File) |> Option.defaultValue ""
        | [] -> ""
    fun (n: SemanticNode) -> (if n.Range.File = entryFile then 0 else 1), n.Range.File, n.Range.Start.Line, n.Range.Start.Column

let private literalTexts (graph: SemanticGraph) (nodes: SemanticNode list) : (string * SemanticNode list) list =
    let orderBy = sourceOrder graph
    nodes
    |> List.filter (fun n -> n.IsReachable)
    |> List.choose (fun n ->
        match n.Kind with
        | SemanticKind.Literal (NativeLiteral.String s) -> Some (s, n)
        | _ -> None)
    |> List.sortBy (snd >> orderBy)
    |> List.groupBy fst
    |> List.map (fun (text, occurrences) -> text, List.map snd occurrences)

/// Create the node-level proofs of the new nodes and fold them into the graph.
let create (graph: SemanticGraph) (newNodes: NodeId seq) : SemanticGraph =
    let nodes =
        newNodes
        |> Seq.choose (fun id -> SemanticGraph.tryGetNode id graph)
        |> Seq.toList
    let enrichId = freshId ()
    let existing =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with SemanticKind.Obligation info -> Some info.Id | _ -> None) |> Set.ofSeq
    let distinctName (name, (text, participants: SemanticNode list)) =
        let rec available suffix =
            let candidate = if suffix = 0 then name else sprintf "%s_node_%d_%d" name (NodeId.value participants.Head.Id) suffix
            if ["storage_"; "view_"; "sentinel_"] |> List.exists (fun prefix -> existing.Contains(prefix + candidate)) then available (suffix + 1)
            else candidate
        available 0, (text, participants)
    let proofs =
        literalTexts graph nodes
        |> List.map (fun (text, participants) -> slug text, (text, participants))
        |> uniquify
        |> List.map distinctName
        |> List.map (Recipes.literalTriple enrichId)
        |> Enrichment.concat
    ObligationElaboration.foldIn proofs graph

let private literal (node: SemanticNode) =
    match node.Kind with SemanticKind.Literal (NativeLiteral.String text) -> Some text | _ -> None

let private refuse occurrence participants reason =
    Result.Error { Kind = WitnessProjectionFailureKind.Settlement
                   Occurrence = Some occurrence
                   Participants = Set.ofList participants
                   Reason = reason }

let private collect f initial rows =
    rows |> List.fold (fun state row -> state |> Result.bind (fun acc -> f acc row)) (Result.Ok initial)

let private roleCandidate (info: ObligationInfo) =
    match info.Kind, info.Body with
    | ("storage-reservation" | "view-containment" | "terminator-sentinel"), _ -> true
    | _, ObligationBody.StorageReservation _ -> info.Id.StartsWith "storage_"
    | _, ObligationBody.ViewContainment _ -> info.Id.StartsWith "view_"
    | _, ObligationBody.NulSentinel _ -> info.Id.StartsWith "sentinel_"
    | _ -> false

/// Read the incidence consumed by publication. Use linked literal content to identify
/// ownership, and the prospective owner's exact old facts to validate it.
let private residents (graph: SemanticGraph) (texts: Set<string>) =
    let touched id = graph.Nodes.TryFind id |> Option.bind literal |> Option.exists texts.Contains
    let anchored =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Metadata.TryFind ObligationMetadata.Anchors with
            | Some(MetadataValue.StringList names) -> Some(node.Id, names)
            | _ -> None) |> Seq.toList
    let heldNames = anchored |> List.choose (fun (id, names) -> if touched id then Some names else None) |> List.concat |> Set.ofList
    let holders =
        anchored |> List.fold (fun index (id, names) ->
            names |> List.fold (fun (current: Map<string, Set<NodeId>>) name ->
                if heldNames.Contains name then
                    current.Add(name, Set.add id (current.TryFind name |> Option.defaultValue Set.empty))
                else current) index) Map.empty
    let incoming = graph.Edges |> List.groupBy _.Target |> Map.ofList
    let claims = SemanticGraph.obligations graph
    let anchorCounts = claims |> List.countBy (fun (_, info) -> info.Id) |> Map.ofList
    let read table ((node: SemanticNode), (info: ObligationInfo)) =
        let edges = incoming.TryFind node.Id |> Option.defaultValue []
        if not (roleCandidate info) ||
           not (heldNames.Contains info.Id || (edges |> List.exists (fun e -> e.Sources |> List.exists touched))) then Result.Ok table
        else
            let failure reason = refuse node.Id (edges |> List.collect _.Sources) ("Literal proof incidence: " + reason)
            match edges with
            | _ when anchorCounts.TryFind info.Id <> Some 1 -> failure "A current claim anchor identifies several graph nodes."
            | [edge] when edge.Class = EdgeClass.Obligation && edge.Role = EdgeRole.Constrains && edge.Ordinal = 0 ->
                let sources = edge.Sources |> List.choose graph.Nodes.TryFind
                match sources with
                | head :: _ when sources.Length = edge.Sources.Length &&
                                 (List.distinct edge.Sources).Length = edge.Sources.Length ->
                    match literal head with
                    | Some text when texts.Contains text && (sources |> List.forall (fun n -> literal n = Some text)) ->
                        let ownsAnchor (n: SemanticNode) =
                            match n.Metadata.TryFind ObligationMetadata.Anchors with
                            | Some(MetadataValue.StringList names) -> names |> List.filter ((=) info.Id) |> List.length = 1
                            | _ -> false
                        let participants = Set.ofList edge.Sources
                        let outside = Set.difference (holders.TryFind info.Id |> Option.defaultValue Set.empty) participants
                        if not outside.IsEmpty then
                            refuse (Set.minElement outside) (Set.union outside participants |> Set.toList)
                                "Literal proof incidence: A literal holds the claim anchor outside its current participant list."
                        elif sources |> List.forall ownsAnchor then
                            let prior = Map.tryFind text table |> Option.defaultValue []
                            Result.Ok (Map.add text ((node, info, edge, head) :: prior) table)
                        else failure "A participant lacks the exact current claim anchor."
                    | _ -> failure "Claim participants must name one exact current literal text."
                | _ -> failure "Claim participants must exist, be nonempty, and be unique."
            | _ -> failure "A literal claim must have exactly one incoming Obligation/Constrains row at ordinal zero."
    claims |> collect read Map.empty

/// Validate a complete resident triple before editing any membership. Claim identity,
/// Required order, and incidence positions belong to the original graph.
let private widen (graph: SemanticGraph) text (added: SemanticNode list) (rows: (SemanticNode * ObligationInfo * Hyperedge * SemanticNode) list) =
    let fail message = refuse added.Head.Id (List.map (fun (n: SemanticNode) -> n.Id) added) ("Literal proof incidence: " + message)
    let role kind = rows |> List.tryFind (fun (_, info, _, _) -> info.Kind = kind)
    match rows.Length, role "storage-reservation", role "view-containment", role "terminator-sentinel" with
    | 3, Some ((_, storage, first, head) as s), Some v, Some t ->
        if not (storage.Id.StartsWith "storage_") || storage.Id.Length <= 8 then fail "The storage role has no corresponding owned anchor."
        else
            let old = [s; v; t]
            let facts = Recipes.literalClaimFacts (storage.Id.Substring(8)) text (fmtRange head.Range)
            let valid ((node: SemanticNode), info, (edge: Hyperedge), _) expected =
                info = expected && node.Range = head.Range && edge.Sources = first.Sources
            if not (List.forall2 valid old facts) then fail "The three literal roles, old source, facts, or ordered participant lists disagree."
            else
                let oldParticipants = first.Sources |> List.choose graph.Nodes.TryFind
                let orderBy = sourceOrder graph
                let current = (oldParticipants @ added) |> List.distinctBy _.Id |> List.sortBy (fun n -> orderBy n, n.Id)
                let ids = current |> List.map _.Id
                if ids = first.Sources then Result.Ok []
                else
                    Result.Ok (old |> List.map (fun ((node: SemanticNode), info, (edge: Hyperedge), _) ->
                        let first = current.Head
                        let claim = { node with Range = first.Range; Kind = SemanticKind.Obligation { info with Source = fmtRange first.Range } }
                        claim, { edge with Sources = ids }))
    | _ -> fail "A literal text must have exactly one storage, view, and sentinel claim."

/// Add newly reachable participants to their existing literal claims; fresh texts retain the birth path.
let tryExtend (graph: SemanticGraph) (newNodes: NodeId seq) =
    let wave = newNodes |> Seq.distinct |> Seq.choose graph.Nodes.TryFind |> Seq.toList |> literalTexts graph
    match wave with
    | [] -> Result.Ok graph
    | (_, first :: _) :: _ ->
        let texts = wave |> List.map fst |> Set.ofList
        residents graph texts |> Result.bind (fun owners ->
            let plan (edits, fresh) (text, participants: SemanticNode list) =
                match owners.TryFind text with
                | Some held -> widen graph text participants held |> Result.map (fun changed -> changed @ edits, fresh)
                | None -> Result.Ok (edits, participants :: fresh)
            wave |> collect plan ([], []) |> Result.bind (fun (edits, fresh) ->
                let revised =
                    if List.isEmpty edits then Result.Ok graph else
                    let claims, edges = List.unzip edits
                    let byTarget = edges |> List.map (fun (e: Hyperedge) -> e.Target, e) |> Map.ofList
                    let enrichment = { NewNodes = []; Annotated = claims; NewEdges = edges }
                    match Recipes.tryProjectAnchors enrichment graph with
                    | Result.Error reason -> refuse first.Id [first.Id] reason
                    | Result.Ok annotated ->
                        let nodes = (claims @ annotated) |> List.fold (fun map (node: SemanticNode) -> Map.add node.Id node map) graph.Nodes
                        let edges = graph.Edges |> List.map (fun edge -> byTarget.TryFind edge.Target |> Option.defaultValue edge)
                        Result.Ok ({ graph with Nodes = nodes; Edges = edges } |> SemanticGraph.invalidateWitness)
                revised |> Result.map (fun current ->
                    if List.isEmpty fresh then current
                    else fresh |> List.rev |> List.concat |> List.map _.Id |> create current)))
    | _ -> Result.Ok graph
