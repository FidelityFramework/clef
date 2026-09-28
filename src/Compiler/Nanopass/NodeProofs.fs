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
let private literalTexts (graph: SemanticGraph) (nodes: SemanticNode list) : (string * SemanticNode list) list =
    let entryFile =
        match graph.DeclarationRoots with
        | (entryId, _) :: _ -> SemanticGraph.tryGetNode entryId graph |> Option.map (fun n -> n.Range.File) |> Option.defaultValue ""
        | [] -> ""
    nodes
    |> List.filter (fun n -> n.IsReachable)
    |> List.choose (fun n ->
        match n.Kind with
        | SemanticKind.Literal (NativeLiteral.String s) -> Some (s, n)
        | _ -> None)
    |> List.sortBy (fun (_, n) -> (if n.Range.File = entryFile then 0 else 1), n.Range.File, n.Range.Start.Line, n.Range.Start.Column)
    |> List.groupBy fst
    |> List.map (fun (text, occurrences) -> text, List.map snd occurrences)

/// Create the node-level proofs of the new nodes and fold them into the graph.
let create (graph: SemanticGraph) (newNodes: NodeId seq) : SemanticGraph =
    let nodes =
        newNodes
        |> Seq.map (fun id ->
            match SemanticGraph.tryGetNode id graph with
            | Some node -> node
            | None -> invalidOp (sprintf "NodeProofs: new node %d is not in the graph." (NodeId.value id)))
        |> Seq.toList
    let enrichId = freshId ()
    let proofs =
        literalTexts graph nodes
        |> List.map (fun (text, participants) -> slug text, (text, participants))
        |> uniquify
        |> List.map (Recipes.literalTriple enrichId)
        |> Enrichment.concat
    ObligationElaboration.foldIn proofs graph
