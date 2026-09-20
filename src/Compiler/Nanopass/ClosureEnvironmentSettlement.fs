// SPDX-License-Identifier: MIT
/// Physical environment placement and its bounded-use residence are settled
/// before continuation frames capture their descriptors. Codata is never forced.
module Clef.Compiler.Nanopass.ClosureEnvironmentSettlement

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.Baker.Ingredients.Obligations
module Environments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments
module Placement = Clef.Compiler.PSGSaturation.SemanticGraph.Placement
module Residence = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence
module Proof = Clef.Compiler.Baker.Recipes.ContinuationObligationRecipes

type Settlement = {
    Layouts: Map<NodeId, EnvironmentLayout>
    Residences: Map<NodeId, EscapeKind>
    Diagnostics: Diagnostic list
}

let settleWhenSourceAdmitted admitted (graph: SemanticGraph) =
    let empty = { Layouts = Map.empty; Residences = Map.empty; Diagnostics = [] }
    if not admitted || graph.Platform.IsNone then graph, empty else
    let residual site related reason =
        { Severity = NativeDiagnosticSeverity.Error; Code = "CCS8403"
          Message = "Captured callable environment requires further settlement: " + reason
          Range = graph.Nodes[site].Range; RelatedNodes = site :: related
          Reachability = ReachabilityContext.Unknown }
    let residence = Residence.analyzeEnvironments graph
    let residenceErrors = residence.Unresolved |> List.map (fun pending -> residual pending.Site [] (sprintf "%A" pending.Reason))
    let regionErrors = residence.Regions |> Map.toList |> List.map (fun (site, generator) ->
        residual site [generator] "A generator-local callback needs a settled owned environment region; activation-local backing storage cannot survive a suspension.")
    let placed = graph.Nodes.Values |> Seq.choose (fun owner ->
        match owner.Kind with
        | SemanticKind.ClosureValue(implementation, environment) when owner.IsReachable ->
            let captures = Environments.captures graph owner.Id
            let shape =
                match graph.Nodes.TryFind implementation, graph.Nodes.TryFind environment with
                | Some { Kind = SemanticKind.Lambda((_, formalType, formal) :: _, _, [], _, _) },
                  Some { Kind = SemanticKind.EnvironmentCreate(actual, initializers) }
                    when actual = owner.Id && formalType = Environments.environmentType && initializers.Length = captures.Length
                         && (List.map fst initializers = (captures |> List.choose _.SourceNodeId)) -> Some formal
                | _ -> None
            match shape with
            | None -> Some (Result.Error (residual owner.Id [implementation; environment] "Formation, exact capture incidence and the real environment formal disagree."))
            | Some formal ->
                match Placement.placeEnvironment graph captures with
                | Ok (SettledLayout.Record(_, Some bytes, Some alignment), fields) ->
                    let slots = fields |> List.map (fun (field: Placement.ContinuationField) ->
                        { Source = field.Source; ValueType = graph.Nodes[field.Source].Type
                          Field = field.Field; Holds = field.Holds; IsCapture = true })
                    let proof = Proof.layout (NodeId.value owner.Id) (sprintf "closure_%d_environment" (NodeId.value owner.Id)) owner
                                    (slots |> List.map (fun slot -> slot.Source, slot.Field.Offset.Value, slot.Field.Size.Value, slot.Field.Align.Value)) bytes alignment
                    let edges = proof.NewEdges |> List.map (fun edge -> { edge with Sources = List.distinct (edge.Sources @ [implementation; environment; formal]) })
                    let proof = { proof with NewEdges = edges }
                    let layout = { Owner = owner.Id; Implementation = implementation; Formal = formal
                                   Slots = slots; Bytes = bytes; Alignment = alignment
                                   Obligations = proof.NewNodes |> List.map _.Id }
                    Some (Ok(layout, proof))
                | Result.Error reason -> Some (Result.Error (residual owner.Id [] (sprintf "%A" reason)))
                | _ -> Some (Result.Error (residual owner.Id [] "The target did not settle an exact environment extent and alignment."))
        | _ -> None) |> Seq.toList
    let layouts = placed |> List.choose (function Ok(layout, _) -> Some(layout.Owner, layout) | _ -> None) |> Map.ofList
    let proofs = placed |> List.choose (function Ok(_, proof) -> Some proof | _ -> None) |> Enrichment.concat
    let proofs = { proofs with NewEdges = proofs.NewEdges @ residence.Evidence }
    let graph = ObligationElaboration.foldIn proofs graph
    graph, { Layouts = layouts; Residences = residence.Sites
             Diagnostics = residenceErrors @ regionErrors @ (placed |> List.choose (function Result.Error diagnostic -> Some diagnostic | _ -> None)) }

let settle graph = settleWhenSourceAdmitted true graph
