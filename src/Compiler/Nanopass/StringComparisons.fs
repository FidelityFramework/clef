// SPDX-License-Identifier: MIT
module Clef.Compiler.Nanopass.StringComparisons

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Nanopass.Recipe
module Recipes = Clef.Compiler.Baker.Recipes.StringComparisonRecipes

/// Fold one materialized comparison into `graph`, reading its source node from
/// `graph`. The ordinary-demand rows are left as they were; the caller settles them.
let private foldComparison (graph: SemanticGraph) evidence ((candidate: SemanticNode), kind, callee, left, right) =
    let source = graph.Nodes[candidate.Id]
    if source.Kind <> candidate.Kind then
        invalidOp (sprintf "String comparison settlement error: the comparison at node %d changed form before its materialization." (NodeId.value candidate.Id))
    let structure, edges = Recipes.materializeWith evidence graph (source, kind, callee, left, right)
    let create (node: SemanticNode) _ =
        RecipeCreated { OriginalNodeId=node.Id; NewNodes=structure.NewNodes; ReplacementRootId=node.Id
                        ElaborationKind="Baker"; NewEdges=[]; ElaborationSource="String.equality" }
    let folded = FoldIn.foldIn (FanOut.fanOut "String.equality" (fun (node: SemanticNode) -> node.Id=source.Id) create graph) graph
    { folded with Edges=edges }

/// Comparisons are materialized in node order. A length comparison cites the
/// origins of its operands, read through the resident ordinary-demand rows, so
/// those rows are settled before its evidence is derived and after its rewrite,
/// and its settled evidence is then completed. A byte-traversal comparison cites
/// no origin, demand or evidence. A comparison is a `bool` value: its rewrite
/// adds no string value and changes no string's flow, so the evidence derived on
/// one settled graph holds for every byte traversal of the leading run, and the
/// run is folded under one settlement of the demand rows (clef #124). The next
/// settled graph derives the same absence of evidence for each comparison of the
/// run; a comparison for which it does not is an error at that comparison.
let rec private elaborate graph =
    match Recipes.candidates graph with
    | [] -> graph
    | head :: rest ->
        let evidence = Recipes.lengthEvidence graph
        match evidence head with
        | Some settled ->
            let demanded = foldComparison graph (Some settled) head |> OrdinaryDemand.normalize
            elaborate (Recipes.settleMaterializedLength graph demanded head)
        | None ->
            let traversals = head :: (rest |> List.takeWhile (evidence >> Option.isNone))
            let demanded =
                traversals |> List.fold (fun current candidate -> foldComparison current None candidate) graph
                |> OrdinaryDemand.normalize
            traversals |> List.iter (fun candidate ->
                let (source: SemanticNode),_,_,_,_ = candidate
                if (Recipes.lengthEvidence demanded candidate).IsSome then
                    invalidOp (sprintf "String comparison settlement error: the comparison at node %d (%s) was materialized as a byte traversal without zero-extent evidence, and the settled graph after its materialization derives zero-extent evidence for its operands."
                                   (NodeId.value source.Id) (Clef.Compiler.Baker.Ingredients.Obligations.fmtRange source.Range)))
            elaborate demanded

let normalize graph =
    let result = elaborate graph
    if obj.ReferenceEquals(graph,result) || result.DeclarationRoots.IsEmpty then result
    else Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable result
