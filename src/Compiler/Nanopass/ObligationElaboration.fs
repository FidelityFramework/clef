// SPDX-License-Identifier: MIT

/// Obligation Elaboration -- Pass 5.
///
/// The pass: discover the subjects obligations are stated over (reachable
/// string literals, String.concat2 sites, the Sys.readline site), read the
/// declared platform the program was cross-compiled with, apply the Baker
/// obligation recipes, and fold the result into the graph. The recipes and
/// their ingredients live in Baker; this module only orchestrates.
///
/// Runs after final reachability, over the saturated graph: the layout
/// obligation needs the complete reachable literal set, and no obligation is
/// minted for a dead literal. Under the saturation lattice this becomes a rule
/// that fires when its sources are Saturated; today it is a fixed position.
///
/// Pure: `elaborate` projects an Enrichment; `foldIn` returns a new graph.
module Clef.Compiler.Nanopass.ObligationElaboration

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration
open Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
open Clef.Compiler.Baker.Ingredients.Obligations
module Recipes = Clef.Compiler.Baker.Recipes.ObligationRecipes

//=============================================================================
// SUBJECT DISCOVERY
//=============================================================================

/// Every reachable string literal: entry-unit strings first in source order,
/// then library strings, distinct by content -- exactly the set the emission
/// places.
let private reachableLiterals (graph: SemanticGraph) : (string * SemanticNode) list =
    let entryFile =
        match graph.DeclarationRoots with
        | (entryId, _) :: _ -> SemanticGraph.tryGetNode entryId graph |> Option.map (fun n -> n.Range.File) |> Option.defaultValue ""
        | [] -> ""
    graph.Nodes
    |> Map.toList
    |> List.map snd
    |> List.filter (fun n -> n.IsReachable)
    |> List.choose (fun n ->
        match n.Kind with
        | SemanticKind.Literal (NativeLiteral.String s) -> Some (s, n)
        | _ -> None)
    |> List.sortBy (fun (_, n) -> (if n.Range.File = entryFile then 0 else 1), n.Range.File, n.Range.Start.Line, n.Range.Start.Column)
    |> List.distinctBy fst

let rec private intrinsicOf (graph: SemanticGraph) (id: NodeId) : IntrinsicInfo option =
    match SemanticGraph.tryGetNode id graph with
    | Some ({ Kind = SemanticKind.Intrinsic info } : SemanticNode) -> Some info
    | Some ({ Kind = SemanticKind.TypeAnnotation (inner, _) } : SemanticNode) -> intrinsicOf graph inner
    | _ -> None

let private literalOperand (graph: SemanticGraph) (id: NodeId) : (int * string) option =
    match SemanticGraph.tryGetNode id graph with
    | Some ({ Kind = SemanticKind.Literal (NativeLiteral.String s) } : SemanticNode) -> Some (byteLength s, s)
    | _ -> None

/// Reachable applications of a named intrinsic, in source order.
let private intrinsicSites (graph: SemanticGraph) (m: IntrinsicModule) (op: string) : (SemanticNode * NodeId list) list =
    graph.Nodes
    |> Map.toList
    |> List.map snd
    |> List.filter (fun n -> n.IsReachable)
    |> List.choose (fun n ->
        match n.Kind with
        | SemanticKind.Application (funcId, args) ->
            match intrinsicOf graph funcId with
            | Some info when info.Module = m && info.Operation = op -> Some (n, args)
            | _ -> None
        | _ -> None)
    |> List.sortBy (fun (n, _) -> n.Range.File, n.Range.Start.Line, n.Range.Start.Column)

/// concat2 sites with their operands, named and uniquified in source order.
let private concatSites (graph: SemanticGraph) =
    intrinsicSites graph IntrinsicModule.String "concat2"
    |> List.choose (fun (site, args) ->
        match args with
        | [ leftId; rightId ] ->
            let left, right = literalOperand graph leftId, literalOperand graph rightId
            let baseSlug =
                match right, left with
                | Some (_, c), _ | _, Some (_, c) -> sprintf "concat_%s" (slug c)
                | None, None -> "concat_dynamic"
            Some (baseSlug, (site, leftId, rightId, left, right))
        | _ -> None)
    |> uniquify

//=============================================================================
// THE PASS
//=============================================================================

/// Project the obligation enrichment from the saturated graph.
let elaborate (graph: SemanticGraph) : Enrichment =
    let platform = resolve graph
    let rodata = platform |> Option.bind (spaceNamed "rodata")
    let enrichId = freshId ()
    let literals = reachableLiterals graph
    let namedLiterals = literals |> List.map (fun (c, n) -> slug c, (c, n)) |> uniquify
    let readln =
        match platform |> Option.bind (fun p -> bufferNamed "consoleReadln" p |> Option.map (fun b -> p, b)) with
        | Some (p, b) -> intrinsicSites graph IntrinsicModule.Sys "readline" |> List.map (fun (site, _) -> Recipes.readln p b enrichId site)
        | None -> []
    Enrichment.concat
        [ namedLiterals |> List.map (Recipes.literal rodata enrichId) |> Enrichment.concat
          Recipes.layout platform rodata enrichId literals
          concatSites graph |> List.map (Recipes.concat enrichId) |> Enrichment.concat
          Enrichment.concat readln ]

/// Fold the enrichment into the graph: annotated nodes replace their originals
/// by id, obligation nodes join V, their hyperedges join F.
let foldIn (e: Enrichment) (graph: SemanticGraph) : SemanticGraph =
    graph
    |> SemanticGraph.addNodes e.Annotated
    |> SemanticGraph.addNodes e.NewNodes
    |> SemanticGraph.addEdges e.NewEdges
