// SPDX-License-Identifier: MIT

/// Node Proofs -- the tier 2 nanopass.
///
/// A tier 2 obligation is created when the structure it is about exists and is
/// reachable, whether or not that structure is demanded. Creation and dispatch
/// are separate: an obligation is dispatched when its premises are settled.
/// Demand decides the pool and residence. It does not decide whether a proof
/// exists.
///
/// The pass receives the supplied source occurrences. Initial birth receives
/// the reached work set after constant branch exclusion. The pass creates
/// the storage, view and sentinel proofs of the reachable string literals among
/// them: one triple for each text, with every reachable node of that text a
/// participant. The sentinel acquires its byte only after storage settles.
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
    | _, (ObligationBody.MaterializedNulSentinel _ | ObligationBody.OmittedNulSentinel) -> info.Id.StartsWith "sentinel_"
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

/// Read the current storage supporting an already born sentinel. Reuse the pool indexes across a wave.
let private sentinelDisposition (graph: SemanticGraph) =
    let pool = graph.StaticStringPool
    let entries = pool |> Option.map (fun storage -> Array.ofList storage.Entries) |> Option.defaultValue [||]
    let placements = entries |> Array.indexed |> Array.groupBy (fun (_, entry) -> entry.Content) |> Map.ofArray
    let bytes = pool |> Option.map (fun storage -> Array.ofList storage.Bytes) |> Option.defaultValue [||]
    let readDisposition claim text sourceIds (view: ObligationInfo) =
        let fail reason = refuse claim sourceIds ("Literal sentinel settlement: " + reason)
        let row held occurrence =
            match graph.LiteralStorage.TryFind occurrence with
            | Some (LiteralStorage.Materialized ordinal) -> Result.Ok ((occurrence, ordinal) :: held)
            | Some (LiteralStorage.NotMaterialized (StoragePremise.Established (_ :: _))) -> Result.Ok held
            | _ -> refuse claim [occurrence] "Literal sentinel settlement: The literal has no current materialized or established omission row."
        sourceIds |> collect row [] |> Result.bind (function
            | [] when not (placements.ContainsKey text) -> Result.Ok ObligationBody.OmittedNulSentinel
            | [] -> fail "An omitted text still has an entry in the static string pool."
            | (_, ordinal) :: _ as materialized ->
                match placements.TryFind text, view.Body with
                | Some [| (observedOrdinal, entry) |], ObligationBody.ViewContainment (_, offset, _) ->
                    let held = materialized |> List.map fst |> Set.ofList
                    if entry.NodeIds.Length <> held.Count || Set.ofList entry.NodeIds <> held ||
                       (materialized |> List.exists (snd >> (<>) ordinal)) then
                        fail "The pool entry does not list exactly the materialized occurrences of this text."
                    elif entry.Offset < 0 || entry.Offset > bytes.Length ||
                         entry.Length < 0 || entry.Length >= entry.StorageLength ||
                         entry.Length >= bytes.Length - entry.Offset then
                        fail "The terminator offset is outside its checked pool entry."
                    else
                        let observed = bytes[entry.Offset + entry.Length]
                        Result.Ok (ObligationBody.MaterializedNulSentinel(ordinal, offset, observedOrdinal, entry.Length, observed))
                | _ -> fail "A materialized literal requires one checked pool entry and its current view claim.")
    readDisposition

/// Validate a complete resident triple before editing any membership. Claim identity,
/// Required order, and incidence positions belong to the original graph.
let private widen readSentinel (graph: SemanticGraph) text (added: SemanticNode list) (rows: (SemanticNode * ObligationInfo * Hyperedge * SemanticNode) list) =
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
            let claim, info, edge, _ = t
            let _, previousView, _, _ = v
            let priorFacts =
                match info.Body with
                | ObligationBody.MaterializedNulSentinel _ | ObligationBody.OmittedNulSentinel ->
                    readSentinel claim.Id text edge.Sources previousView |> Result.map (fun body ->
                        facts |> List.map (fun fact ->
                            if fact.Kind = "terminator-sentinel" then { fact with Body = body } else fact))
                | _ -> Result.Ok facts
            priorFacts |> Result.bind (fun expected ->
                if not (List.forall2 valid old expected) then fail "The three literal roles, old source, facts, or ordered participant lists disagree."
                else
                    let oldParticipants = first.Sources |> List.choose graph.Nodes.TryFind
                    let orderBy = sourceOrder graph
                    let current = (oldParticipants @ added) |> List.distinctBy _.Id |> List.sortBy (fun n -> orderBy n, n.Id)
                    let ids = current |> List.map _.Id
                    if ids = first.Sources then Result.Ok []
                    else
                        match current with
                        | [] -> Result.Ok []
                        | lead :: _ ->
                            // Widen the existing births. Changed incidence must settle its sentinel again.
                            Result.Ok (List.map2 (fun ((node: SemanticNode), _, (edge: Hyperedge), _) fact ->
                                let claim = { node with Range = lead.Range; Kind = SemanticKind.Obligation { fact with Source = fmtRange lead.Range } }
                                claim, { edge with Sources = ids }) old facts))
    | _ -> fail "A literal text must have exactly one storage, view, and sentinel claim."

/// Add newly reachable participants to their existing literal claims; fresh texts retain the birth path.
let tryExtend (graph: SemanticGraph) (newNodes: NodeId seq) =
    let wave = newNodes |> Seq.distinct |> Seq.choose graph.Nodes.TryFind |> Seq.toList |> literalTexts graph
    match wave with
    | [] -> Result.Ok graph
    | (_, first :: _) :: _ ->
        let texts = wave |> List.map fst |> Set.ofList
        let readSentinel = sentinelDisposition graph
        residents graph texts |> Result.bind (fun owners ->
            let plan (edits, fresh) (text, participants: SemanticNode list) =
                match owners.TryFind text with
                | Some held -> widen readSentinel graph text participants held |> Result.map (fun changed -> changed @ edits, fresh)
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

/// Complete the existing sentinel claims from checked storage. Retain the
/// anchor, claim identity and ordered literal sources in every disposition,
/// and never leave a stale materialized or omitted body on an orphaned claim.
let settleSentinels (graph: SemanticGraph) =
    let groups = literalTexts graph (graph.Nodes.Values |> Seq.toList)
    let texts = groups |> List.map fst |> Set.ofList
    let readDisposition = sentinelDisposition graph
    let isSentinelClaim (info: ObligationInfo) =
        info.Kind = "terminator-sentinel"
        || (match info.Body with
            | ObligationBody.MaterializedNulSentinel _
            | ObligationBody.OmittedNulSentinel -> true
            | _ -> false)
    residents graph texts |> Result.bind (fun owners ->
        let settle (settledIds, changed) (text, participants: SemanticNode list) =
            let sources = participants |> List.map _.Id
            let claims = owners.TryFind text |> Option.defaultValue []
            let role kind = claims |> List.filter (fun (_, info, _, _) -> info.Kind = kind)
            match role "terminator-sentinel", role "view-containment" with
            | [(node, info, edge, _)], [(_, view, viewEdge, _)] when edge.Sources = sources && viewEdge.Sources = sources ->
                readDisposition node.Id text sources view |> Result.map (fun body ->
                    let settledIds = Set.add node.Id settledIds
                    if info.Body = body then settledIds, changed
                    else settledIds, (node.Id, {node with Kind = SemanticKind.Obligation {info with Body = body}}) :: changed)
            | _ ->
                let site =
                    match participants with
                    | first :: _ -> first.Id
                    | [] -> NodeId 0
                refuse site sources "Literal sentinel settlement: The text does not have one claim with its exact ordered reachable occurrences."
        groups |> collect settle (Set.empty, []) |> Result.map (fun (settledIds, changed) ->
            let withdrawn =
                SemanticGraph.obligations graph
                |> List.choose (fun (node, info) ->
                    if settledIds.Contains node.Id || not (isSentinelClaim info) then None
                    else
                        match info.Body with
                        | ObligationBody.Pending _ -> None
                        | _ ->
                            let reset = ObligationBody.Pending ["The literal occurrences for this sentinel are no longer reachable."]
                            Some (node.Id, { node with Kind = SemanticKind.Obligation { info with Body = reset } }))
            match changed @ withdrawn with
            | [] -> graph
            | changes ->
                let nodes = changes |> List.fold (fun held (id, node) -> Map.add id node held) graph.Nodes
                {graph with Nodes = nodes} |> SemanticGraph.invalidateWitness))
