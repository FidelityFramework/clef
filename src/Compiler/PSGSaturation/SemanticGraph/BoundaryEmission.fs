// SPDX-License-Identifier: MIT
/// Validate and project Baker's settled boundary rows. This module performs
/// no descriptor parsing, identity discovery, ABI choice or semantic repair.
module Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Ingredients = Clef.Compiler.Baker.Ingredients.Boundaries
module Declarations = Clef.Compiler.Baker.Recipes.BoundaryDeclarations

let private failure occurrence participants reason =
    { Occurrence = occurrence; Participants = participants; Reason = "BoundaryEmission: " + reason }

let project (graph: SemanticGraph) : Result<BoundaryEmissionProjection, WitnessProjectionFailure list> =
    let domains = graph.Edges |> List.choose (fun edge ->
        match edge.Role with EdgeRole.BoundaryDomain domain -> Some (edge, domain) | _ -> None)
    match domains with
    | [domainRow, domain] ->
        let participants = Map.keys domain.Premises |> Set.ofSeq
        let stale reason = Error [failure (Some domainRow.Target) participants reason]
        let anchorValid = graph.Nodes.TryFind domainRow.Target |> Option.exists (fun node ->
            Ingredients.ownedNode node && match node.Kind with SemanticKind.Literal NativeLiteral.Unit -> true | _ -> false)
        if not anchorValid || domain.Premises <> Ingredients.premises graph || domain.Platform <> Ingredients.platformPremise graph.Platform || domain.Meets <> graph.Codata.Value.Meets then
            stale "A source boundary premise, membership, scope, type, range, platform claim or numeric meet changed; Baker must settle the new source graph."
        elif not domain.Failures.IsEmpty then
            Error (domain.Failures |> List.map (fun (site, participants, reason) -> failure (Some site) participants reason))
        else
            let imports = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryImport import -> Some import | _ -> None)
            let calls = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryCall call -> Some call | _ -> None)
            let coverages = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryCoverage coverage -> Some coverage | _ -> None)
            let expectedCoverage = calls |> List.collect (fun call ->
                (call.Arguments |> List.mapi (fun ordinal operand -> call.Site, ordinal, operand.Actual)) @
                (call.Result |> Option.toList |> List.map (fun _ -> call.Site, -1, call.Site))) |> List.sort
            let coverageMembership = coverages |> List.map (fun coverage -> coverage.Site, coverage.Ordinal, coverage.Operand) |> List.sort
            if (imports |> List.map _.Identity |> List.sort) <> domain.Imports || (calls |> List.map _.Site |> List.sort) <> domain.Calls || expectedCoverage <> coverageMembership then
                stale "The boundary domain lost or duplicated an import, call or ordered coverage occurrence."
            else
                let callsById = calls |> List.map (fun call -> call.Site, call) |> Map.ofList
                let proofErrors, proofRows = coverages |> List.fold (fun (errors, rows) coverage ->
                    let call = callsById[coverage.Site]
                    let body = Ingredients.coverageBody coverage
                    let outcome = Ingredients.coverageOutcome coverage
                    let obligationValid =
                        graph.Nodes.TryFind coverage.Obligation |> Option.exists (fun node ->
                            Ingredients.ownedNode node &&
                            match node.Kind with
                            | SemanticKind.Obligation info -> info.Kind = "boundary-range-coverage" && Some info.Body = body
                            | _ -> false)
                    let inputValid =
                        if coverage.Ordinal = -1 then
                            call.Result |> Option.exists (fun scalar -> snd (PlatformResolution.scalarRange scalar) = coverage.Input)
                        else
                            let operand = call.Arguments[coverage.Ordinal]
                            let input = match operand.Abi with BoundaryScalar.Boolean -> Some ValueRange.boolean | _ -> domain.Premises[operand.Actual].Range
                            input = Some coverage.Input && snd (PlatformResolution.scalarRange operand.Abi) = coverage.Destination
                    let errors =
                        if obligationValid && inputValid && outcome = BoundaryProofOutcome.Proven then errors
                        else failure (Some coverage.Site) call.Participants "The boundary coverage obligation has no valid checked proof outcome for these exact range premises." :: errors
                    errors, rows @ Ingredients.coverageRows call coverage outcome) ([], [])
                let expected =
                    [Ingredients.row (EdgeRole.BoundaryDomain domain) 0 (Map.keys domain.Premises |> Seq.toList) domainRow.Target
                     { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = Map.keys domain.Premises |> Seq.toList; Target = domainRow.Target }]
                    @ (domain.Declarations |> List.map Declarations.row)
                    @ (imports |> List.map Ingredients.importRow)
                    @ (calls |> List.collect (fun call -> Ingredients.callRow call :: Ingredients.operandRows call))
                    @ proofRows
                let ownedTargets = Set.add domainRow.Target (coverages |> List.map _.Obligation |> Set.ofList)
                let completeMembership = Set.union participants ownedTargets = (Map.keys graph.Nodes |> Set.ofSeq)
                let actual = graph.Edges |> List.filter (fun edge ->
                    edge.Class = EdgeClass.Boundary ||
                    (ownedTargets.Contains edge.Target && (edge.Role = EdgeRole.Constrains || edge.Role = EdgeRole.EnrichedWith)))
                // A multiset check preserves repetitions. Set equality would erase
                // duplicated occurrences and accidentally accept partial evidence.
                let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
                let rec subtract (remaining: Hyperedge list) = function
                    | [] -> remaining.IsEmpty
                    | expected :: rest ->
                        let rec remove prefix = function
                            | [] -> None
                            | edge :: tail when key edge = key expected -> Some (List.rev prefix @ tail)
                            | edge :: tail -> remove (edge :: prefix) tail
                        match remove [] remaining with Some remaining -> subtract remaining rest | None -> false
                if not proofErrors.IsEmpty then Error (List.rev proofErrors)
                elif not completeMembership || not (subtract actual expected) then stale "The ordered boundary relation, adaptation, rewrite record or proof outcome is missing, duplicated or inconsistent."
                else
                    let imports = imports |> List.map (fun import -> import.Identity, import) |> Map.ofList
                    let byScope = imports.Values |> Seq.groupBy _.Scope |> Seq.map (fun (scope, imports) -> scope, imports |> Seq.map _.Identity |> Seq.sort |> Seq.toList) |> Map.ofSeq
                    Ok { Imports = imports; Calls = callsById; ByScope = byScope
                         DeclarationLeaves = domain.DeclarationLeaves; DeclarationOnly = domain.DeclarationOnly; Links = domain.Links }
    | _ ->
        let site = graph.Nodes |> Map.toSeq |> Seq.tryHead |> Option.map fst
        Error [failure site (site |> Option.toList |> Set.ofList) "Exactly one Baker boundary domain is required before publication."]
