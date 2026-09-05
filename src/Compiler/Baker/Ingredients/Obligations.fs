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
