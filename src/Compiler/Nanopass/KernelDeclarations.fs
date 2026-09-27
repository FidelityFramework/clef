// SPDX-License-Identifier: MIT
module Clef.Compiler.Nanopass.KernelDeclarations

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module Recipe = Clef.Compiler.Baker.Recipes.KernelDeclarations

let private residual (graph: SemanticGraph) site reason =
    { Severity = NativeDiagnosticSeverity.Error; Code = "CCS8403"
      Message = "Kernel ingress requires further settlement: " + reason
      Range = graph.Nodes[site].Range; RelatedNodes = [site]; Reachability = ReachabilityContext.Unknown }

/// A declaration that settles contributes its ingress row. A declaration that does
/// not settle contributes a located diagnostic and no row. Neither is dropped.
let normalize (graph: SemanticGraph) : SemanticGraph * Diagnostic list =
    let settled=Recipe.elaborate graph |> Map.toList
    let rows=settled |> List.choose (fun (_,result) -> match result with Result.Ok ingress -> Some(Recipe.row ingress) | Result.Error _ -> None)
    let residuals=settled |> List.choose (fun (site,result) -> match result with Result.Ok _ -> None | Result.Error reason -> Some(residual graph site reason))
    let owns edge=match edge.Role with EdgeRole.KernelIngress _ -> true | _ -> false
    let key (edge: Hyperedge)=edge.Class,edge.Role,edge.Ordinal,edge.Sources,edge.Target
    if (graph.Edges |> List.filter owns |> List.map key)=(rows |> List.map key) then graph,residuals
    else ({graph with Edges=(graph.Edges |> List.filter (owns >> not)) @ rows} |> SemanticGraph.invalidateWitness),residuals
