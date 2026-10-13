// SPDX-License-Identifier: MIT

/// Baker Ingredients -- Obligations.
///
/// The raw components a recipe combines to mint a proof obligation into the
/// graph: the obligation node (a citizen of V), its constraining hyperedge (a
/// member of F), the residence edge from a declared space or buffer to the
/// value that lives in it, and the naming discipline that keeps anchor names
/// unique through both dispatches.
///
/// Recipes return an `Enrichment`; the pass folds it. Nothing here mutates.
module Clef.Compiler.Baker.Ingredients.Obligations

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration

//=============================================================================
// ENRICHMENT: what an obligation recipe returns
//=============================================================================

/// What a recipe adds. `NewNodes` join V; `NewEdges` join F; `Annotated` are
/// existing nodes returned with a saturated annotation -- a hyperedge's
/// consequence on alpha (PHG paper 2.4) -- and replace their originals by id.
type Enrichment = {
    NewNodes: SemanticNode list
    NewEdges: Hyperedge list
    Annotated: SemanticNode list
}

module Enrichment =
    let empty = { NewNodes = []; NewEdges = []; Annotated = [] }
    let combine (a: Enrichment) (b: Enrichment) =
        { NewNodes = a.NewNodes @ b.NewNodes
          NewEdges = a.NewEdges @ b.NewEdges
          Annotated = a.Annotated @ b.Annotated }
    let concat (es: Enrichment list) = List.fold combine empty es

//=============================================================================
// PRIMITIVES
//=============================================================================

/// UTF-8 byte length: the length the emission places.
let byteLength (s: string) : int = System.Text.Encoding.UTF8.GetByteCount s

let fmtRange (r: SourceRange) : string =
    sprintf "%s:%d:%d" r.File r.Start.Line r.Start.Column

/// Formatting only: the workspace owns the epoch, birth and declaration
/// inventory. Length-prefix address segments so different paths cannot alias.
let declarationIdentity (epoch: System.Guid) (birth: int64) (sourceUnit: string) (qualifiedAddress: string list) : string =
    let address =
        sourceUnit :: qualifiedAddress
        |> List.map (fun segment -> string segment.Length + ":" + segment)
        |> String.concat ""
    "decl_" + epoch.ToString("N") + "_" + string birth + "_" +
        System.Convert.ToHexString(System.Text.Encoding.UTF8.GetBytes address)

/// Source lifetimes come from the project source owner. Locations only match
/// checked declarations there; the identity itself contains no source range,
/// allocated node number, proposition or premise. Record checked structural
/// paths before monomorphization and enrichment can allocate replacement nodes.
let annotateSourceClaims (nodes: Map<NodeId, SemanticNode>) : Map<NodeId, SemanticNode> =
    let declarations =
        nodes |> Map.toList |> List.choose (fun (id, node) ->
            match node.Kind, node.Metadata.TryFind "Source.DeclarationIncarnation" with
            | SemanticKind.Binding _, Some(MetadataValue.String identity) -> Some(id, identity)
            | _ -> None)
    declarations |> List.fold (fun current (declaration, identity) ->
        let initial = [declaration, ""], Set.empty, current
        initial
        |> Seq.unfold (fun (pending, seen, current: Map<NodeId, SemanticNode>) ->
            match pending with
            | [] -> None
            | (id, _) :: rest when seen.Contains id -> Some(current, (rest, seen, current))
            | (id, path) :: rest ->
                let seen = seen.Add id
                match current.TryFind id with
                | None -> Some(current, (rest, seen, current))
                | Some node when id <> declaration && node.Metadata.ContainsKey "Source.DeclarationIncarnation" ->
                    Some(current, (rest, seen, current))
                | Some node ->
                    let children =
                        (node.Children @
                         (kindEdges id node.Kind
                          |> List.filter Hyperedge.isStructural
                          |> List.map Hyperedge.soleSource))
                        |> List.distinct
                        |> List.mapi (fun ordinal child -> child, path + "/" + string ordinal)
                    let node = { node with Metadata = node.Metadata.Add("Source.ObligationSite", MetadataValue.String(identity + path)) }
                    let current = current.Add(id, node)
                    Some(current, (children @ rest, seen, current)))
        |> Seq.fold (fun _ current -> current) current) nodes

/// Encode the canonical source claim without a lossy hash. This is a symbol
/// in the existing obligation ledger, not a second identity registry.
let sourceClaimId (role: string) (subject: SemanticNode) : string option =
    match subject.Metadata.TryFind SchemeMetadata.Specialization, subject.Metadata.TryFind "Source.ObligationSite" with
    // Generated specializations have their own trace and transient claims.
    // They cannot inherit the template's claim identity. Stable specialization
    // identities and differential proof reuse remain part of D5.
    | Some(MetadataValue.Specialization _), _ -> None
    | _, Some(MetadataValue.String site) ->
        Some("claim_" + System.Convert.ToHexString(System.Text.Encoding.UTF8.GetBytes(site + ":" + role)))
    | _ -> None

let describe (content: string) : string =
    match content with
    | "" -> "the empty string"
    | c -> sprintf "\"%s\"" (c.Replace("\n", "\\n").Replace("\r", "\\r"))

/// A stable, human-readable slug from string content. Display, not identity.
let slug (content: string) : string =
    match content with
    | "" -> "empty"
    | "\n" -> "newline"
    | ", " -> "comma_space"
    | "!" -> "bang"
    | c ->
        let words =
            System.Text.RegularExpressions.Regex.Matches(c.ToLowerInvariant(), "[a-z0-9]+")
            |> Seq.map (fun m -> m.Value)
            |> Seq.truncate 3
            |> Seq.toList
        if List.isEmpty words then sprintf "str_%08x" (byteLength c)
        else String.concat "_" words

/// Anchor names are identities and must be unique; distinct contents can share
/// a slug. Uniquify in the given order by folding a Map: the first occurrence
/// keeps the slug, later ones are suffixed.
let uniquify (items: (string * 'a) list) : (string * 'a) list =
    items
    |> List.fold (fun (seen: Map<string, int>, acc) (s, x) ->
        let n = (Map.tryFind s seen |> Option.defaultValue 0) + 1
        let name = if n = 1 then s else sprintf "%s_%d" s n
        (Map.add s n seen, (name, x) :: acc)) (Map.empty, [])
    |> snd
    |> List.rev

/// An obligation node. It takes its range from the subject it is stated over,
/// is marked as Obligation enrichment for "pierce the veil" tooling, and is not
/// reachable: it lives off the emission spine, cited through F alone.
let obligationNode (subject: SemanticNode) (enrichId: int) (info: ObligationInfo) : SemanticNode =
    { Id = NodeId.fresh ()
      Kind = SemanticKind.Obligation info
      Range = subject.Range
      Type = Types.unitType
      SRTPResolution = None
      ArenaAffinity = ArenaAffinity.CurrentActor
      LayoutHint = None
      Children = []
      Parent = None
      Metadata = Map.empty
      IsReachable = false
      EmissionStrategy = EmissionStrategy.Inline
      ValueRange = None }
    |> mark ElaborationKind.Obligation info.Kind enrichId

/// The obligation's hyperedge: its constraining structure -> the obligation.
/// `sources` is the enumerated set the proposition ranges over (invariant I1).
let constrains (sources: NodeId list) (obligation: SemanticNode) : Hyperedge =
    { Sources = sources; Target = obligation.Id; Class = EdgeClass.Obligation; Role = EdgeRole.Constrains; Ordinal = 0 }

/// A declaration constrains the value that resides in it.
let resides (declaration: NodeId) (value: NodeId) : Hyperedge =
    Hyperedge.edge1 EdgeClass.Reference EdgeRole.Resides 0 declaration value

/// A site annotated with the facts of the declared buffer it reads into.
let annotateBuffer (capacity: int64) (declaration: string) (trimDelimiter: bool) (site: SemanticNode) : SemanticNode =
    { site with
        Metadata =
            site.Metadata
            |> Map.add BufferMetadata.Capacity (MetadataValue.Int64 capacity)
            |> Map.add BufferMetadata.Declaration (MetadataValue.String declaration)
            |> Map.add BufferMetadata.TrimDelimiter (MetadataValue.Bool trimDelimiter) }
