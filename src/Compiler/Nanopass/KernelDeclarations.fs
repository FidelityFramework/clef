// SPDX-License-Identifier: MIT
module Clef.Compiler.Nanopass.KernelDeclarations

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
module Recipe = Clef.Compiler.Baker.Recipes.KernelDeclarations

let normalize graph =
    let rows=Recipe.elaborate graph |> Map.toList |> List.choose (fun (_,result) -> match result with Ok ingress -> Some(Recipe.row ingress) | Error _ -> None)
    let owns edge=match edge.Role with EdgeRole.KernelIngress _ -> true | _ -> false
    let key (edge: Hyperedge)=edge.Class,edge.Role,edge.Ordinal,edge.Sources,edge.Target
    if (graph.Edges |> List.filter owns |> List.map key)=(rows |> List.map key) then graph
    else {graph with Edges=(graph.Edges |> List.filter (owns >> not)) @ rows} |> SemanticGraph.invalidateWitness
