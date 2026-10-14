// SPDX-License-Identifier: MIT
module Clef.Compiler.Nanopass.StringBorrows

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core

module Recipes = Clef.Compiler.Baker.Recipes.StringBorrowRecipes
module Bytes = Clef.Compiler.Baker.Ingredients.StringBytes

let normalize graph =
    let enrichment = Recipes.elaborate graph

    let key (edge: Hyperedge) =
        edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target

    let views =
        graph.Edges
        |> List.choose (fun edge ->
            match edge.Role with
            | EdgeRole.StringByteView view -> Some view
            | _ -> None)

    let storage = views |> List.map (Bytes.storageRow >> key)

    let rewrites =
        graph.Nodes.Values
        |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.StringByteBorrow source ->
                Some
                    {
                        Class = EdgeClass.Provenance
                        Role = EdgeRole.EnrichedWith
                        Ordinal = 0
                        Sources = [ source ]
                        Target = node.Id
                    }
            | _ -> None)
        |> Seq.map key
        |> Seq.toList

    let replaced edge =
        match edge.Role with
        | EdgeRole.StringByteView view -> key edge = key (Bytes.viewRow view)
        | EdgeRole.StringExtent extent -> key edge = key (Bytes.extentRow extent)
        | EdgeRole.IntrinsicWriteAbi import -> key edge = key (Bytes.abiRow edge.Target import)
        | EdgeRole.StringByteStorage _ -> List.contains (key edge) storage
        | EdgeRole.EnrichedWith -> List.contains (key edge) rewrites
        | _ -> false
    // Formation can introduce a descriptor after the preliminary range pass.
    // Renew this owner's logical rows at that explicit source phase boundary;
    // scalar encoding/storage premises belong to their separate producer.
    { graph with
        Edges = graph.Edges |> List.filter (replaced >> not)
    }
    |> SemanticGraph.addNodes enrichment.Annotated
    |> SemanticGraph.addNodes enrichment.NewNodes
    |> SemanticGraph.addEdges enrichment.NewEdges
