namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module CallableOrigins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins

/// clef #131: callable-origin resolution reaches its fixed point by
/// re-evaluating only the readers of changed facts. The whole-graph pass
/// schedule it replaced is retained as the reference; both must reach exactly
/// the same facts, field joins, parameter inputs, branch observations and
/// transport inputs on every graph.
module private OriginSchedules =
    let programs =
        [ "partial-application", """
module PartialApplication
let add (a: int) (b: int) = a + b
let twice (f: int -> int) (x: int) = f (f x)
let makeAdder (n: int) = fun (x: int) -> x + n
let observed =
    let increment = add 1
    let addTwo = makeAdder 2
    twice increment 3 + twice addTwo 4
"""
          "optional-callable", """
module OptionalCallable
let choose (flag: bool) : (int -> int) option = if flag then Some (fun (x: int) -> x + 1) else None
let apply (f: (int -> int) option) (x: int) = match f with Some g -> g x | None -> x
let observed = apply (choose true) 1 + apply (choose false) 2
"""
          "result-callable", """
module ResultCallable
let first (value: bool) = value
let fallback (value: bool) = false
let input () : Result<bool -> bool, bool> = Ok first
let selected = Result.defaultValue fallback (input ()) true
let observed = if selected then 1 else 0
"""
          "field-written-after-read", """
module FieldWrittenAfterRead
type Handler = { mutable Run: int -> int }
let handler = { Run = fun (x: int) -> x + 1 }
let call (x: int) = handler.Run x
let observed =
    handler.Run <- (fun (x: int) -> x + 2)
    call 3
"""
          "result-pipeline", """
module ResultPipeline
let bind (f: int -> Result<int, int>) (r: Result<int, int>) = match r with Ok v -> f v | Error e -> Error e
let check (x: int) = if x > 0 then Ok x else Error 0
let observed =
    match bind check (Ok 3) with
    | Ok v -> v
    | Error e -> e
"""
          "disjunctive-results", """
module DisjunctiveResults
let pair (left: int) (right: int) : Result<int, int> * Result<int, int> =
    ((if left > 0 then Ok left else Error left), (if right > 0 then Ok right else Error right))
let observed =
    match pair 1 -2 with
    | Error errors, _ | _, Error errors -> errors
    | Ok left, Ok right -> left + right
""" ]

    let graph (name: string, source: string) =
        let text = source + "\n[<EntryPoint>]\nlet main _ = ignore observed; 0\n"
        match parseAndCheck text (name + ".clef") with
        | Success result -> DimensionalCases.noErrors result; result.Graph
        | CheckFailure result -> failwithf "%s was rejected: %A" name result.Diagnostics
        | ParseFailure errors -> failwithf "%s did not parse: %A" name errors

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "CallableOrigins")>]
type CallableOriginScheduleCases() =
    static member Programs: obj array seq =
        OriginSchedules.programs |> Seq.map (fun (name, _) -> [| box name |])

    [<Theory>]
    [<MemberData(nameof CallableOriginScheduleCases.Programs)>]
    member _.``The dependency worklist reaches exactly the whole-graph fixed point`` (name: string) =
        let graph = OriginSchedules.programs |> List.find (fst >> (=) name) |> OriginSchedules.graph
        for branchSelections in [false; true] do
            let reference = CallableOrigins.originFixedPoint CallableOrigins.WholeGraphPasses branchSelections graph
            let worklist = CallableOrigins.originFixedPoint CallableOrigins.DependencyWorklist branchSelections graph
            // Non-vacuous: the program has callable origins to propagate.
            Assert.NotEmpty reference.Facts
            Assert.Equal<Map<NodeId, Set<NodeId * int>>>(reference.Facts, worklist.Facts)
            Assert.Equal<Map<NodeId * string, Set<NodeId * int>>>(reference.Fields, worklist.Fields)
            Assert.Equal<Map<NodeId, (NodeId * NodeId) list>>(reference.Inputs, worklist.Inputs)
            Assert.Equal<Map<NodeId, CallableBranchObservation>>(reference.Branches, worklist.Branches)
            Assert.Equal<Map<NodeId, NodeId list>>(reference.TransportInputs, worklist.TransportInputs)
            // Work proportional to the changed facts: never more evaluations
            // than the passes it replaces.
            Assert.True(worklist.Evaluations <= reference.Evaluations,
                        sprintf "%s: worklist evaluated %d node transfers, the whole-graph passes %d" name worklist.Evaluations reference.Evaluations)

    [<Fact>]
    member _.``A field written after its first read reaches the reader's origins`` () =
        let graph = OriginSchedules.programs |> List.find (fst >> (=) "field-written-after-read") |> OriginSchedules.graph
        let worklist = CallableOrigins.originFixedPoint CallableOrigins.DependencyWorklist false graph
        // Both stored functions reach the read in `call`: the initial one and
        // the one written later in node order.
        let read =
            graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && match node.Kind with SemanticKind.FieldGet(_, "Run") -> true | _ -> false)
            |> Seq.map (fun node -> worklist.Facts.TryFind node.Id |> Option.defaultValue Set.empty)
            |> Seq.maxBy Set.count
        let lambdas =
            read |> Set.filter (fun (origin, offset) ->
                offset = 0 && match graph.Nodes[origin].Kind with SemanticKind.Lambda _ -> true | _ -> false)
        Assert.Equal(2, lambdas.Count)
        Assert.Equal<Set<NodeId * int>>(lambdas, read)

    [<Fact>]
    member _.``A new caller lights its latent extern while independent roots remain retained`` () =
        let source =
            String.concat "\n" [
                "module ShadowCone"
                "[<FidelityExtern(\"c\", \"latent\")>]"
                "let latent (value: int) : int = NativeDefault.zeroed ()"
                "let standingOne (value: int) = value"
                "let standingTwo (value: int) = value"
                "let helper (value: int) = value + 1"
                "let caller (value: int) = helper value"
                "let activate (value: int) = latent value"
            ]
        let graph =
            SourcePlatformFixture.check 64 "shadow-cone.clef" (source + "\n[<EntryPoint>]\nlet main _ = standingOne 1 + standingTwo 2 + caller 3\n")
        let binding name =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
            |> Assert.Single
        let first = binding "standingOne"
        let second = binding "standingTwo"
        let helper = binding "helper"
        let caller = binding "caller"
        let latent = binding "latent"
        let added = binding "activate"
        Assert.True(latent.Metadata.ContainsKey "FidelityExtern.Library")
        Assert.True(latent.Metadata.ContainsKey "FidelityExtern.Symbol")

        // Model the edit with stable identities: the old graph has the same
        // standing declarations, but does not contain the new binding root.
        let roots = [first.Id, DeclRoot.LibraryExport; second.Id, DeclRoot.LibraryExport; caller.Id, DeclRoot.LibraryExport]
        let rec subtree pending seen =
            match pending with
            | [] -> seen
            | id :: rest when Set.contains id seen -> subtree rest seen
            | id :: rest ->
                let children = graph.Nodes.TryFind id |> Option.map _.Children |> Option.defaultValue []
                subtree (children @ rest) (Set.add id seen)
        let addedSubtree = subtree [added.Id] Set.empty
        let latentSubtree = subtree [latent.Id] Set.empty
        let firstSubtree = subtree [first.Id] Set.empty
        let baselineNodes =
            graph.Nodes
            |> Map.filter (fun id _ -> not (Set.contains id addedSubtree))
            |> Map.map (fun _ node ->
                match node.Kind with
                | SemanticKind.ModuleDef(name, members) ->
                    { node with Kind = SemanticKind.ModuleDef(name, List.filter (fun id -> not (Set.contains id addedSubtree)) members)
                                Children = List.filter (fun id -> not (Set.contains id addedSubtree)) node.Children }
                | _ -> node)
        let baseline =
            { graph with Nodes = baselineNodes
                         Edges = graph.Edges |> List.filter (fun edge ->
                             not (Set.contains edge.Target addedSubtree) &&
                             not (edge.Sources |> List.exists (fun s -> Set.contains s addedSubtree)))
                         DeclarationRoots = roots }
            |> Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable
        let current =
            { graph with DeclarationRoots = roots @ [added.Id, DeclRoot.LibraryExport] }
            |> Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable
        Assert.False(baseline.Nodes[latent.Id].IsReachable)
        Assert.True(current.Nodes[latent.Id].IsReachable)
        let cone = Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.computeShadowCone baseline current
        let allReachable =
            current.Nodes
            |> Map.fold (fun acc id node -> if node.IsReachable then Set.add id acc else acc) Set.empty
        Assert.Equal<Set<NodeId>>(allReachable, Set.union cone.AffectedCone cone.RetainedReachable)
        Assert.Empty(Set.intersect cone.AffectedCone cone.RetainedReachable)
        Assert.Contains(added.Id, cone.SeedRoots)
        Assert.Contains(added.Id, cone.AffectedCone)
        Assert.Contains(added.Id, cone.NewlyLitNodes)
        Assert.Contains(latent.Id, cone.NewlyLitNodes)
        Assert.Empty(cone.ExtinguishedNodes)
        Assert.DoesNotContain(first.Id, cone.NewlyLitNodes)
        Assert.DoesNotContain(second.Id, cone.NewlyLitNodes)
        Assert.Equal<Set<NodeId>>(
            Set.intersect (Set.union addedSubtree latentSubtree) cone.AffectedCone,
            cone.NewlyLitNodes)
        Assert.Contains(latent.Id, cone.AffectedCone)
        Assert.Contains(first.Id, cone.RetainedReachable)
        Assert.Contains(second.Id, cone.RetainedReachable)
        Assert.Contains(helper.Id, cone.RetainedReachable)
        Assert.Contains(caller.Id, cone.RetainedReachable)

        let coneAfterRemoval = Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.computeShadowCone current baseline
        Assert.Empty(coneAfterRemoval.NewlyLitNodes)
        Assert.Equal<Set<NodeId>>(cone.NewlyLitNodes, coneAfterRemoval.ExtinguishedNodes)
        Assert.True(Set.isSubset coneAfterRemoval.ExtinguishedNodes coneAfterRemoval.SeedRoots)
        Assert.Contains(first.Id, coneAfterRemoval.RetainedReachable)
        Assert.Contains(second.Id, coneAfterRemoval.RetainedReachable)

        let coneAfterEdgeReorder =
            Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.computeShadowCone
                current
                { current with Edges = List.rev current.Edges }
        Assert.Empty(coneAfterEdgeReorder.AffectedCone)
        Assert.Equal<Set<NodeId>>(allReachable, coneAfterEdgeReorder.RetainedReachable)

        let currentWithTypeCascade =
            let oldHelper = current.Nodes[helper.Id]
            { current with
                Nodes = current.Nodes.Add(helper.Id, { oldHelper with Type = Clef.Compiler.NativeTypedTree.NativeTypes.Types.floatType }) }
        let coneAfterTypeCascade = Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.computeShadowCone current currentWithTypeCascade
        Assert.Contains(helper.Id, coneAfterTypeCascade.SeedRoots)
        Assert.Contains(helper.Id, coneAfterTypeCascade.AffectedCone)
        Assert.Contains(caller.Id, coneAfterTypeCascade.AffectedCone)
        Assert.Empty(coneAfterTypeCascade.NewlyLitNodes)
        Assert.Empty(coneAfterTypeCascade.ExtinguishedNodes)
        Assert.Contains(first.Id, coneAfterTypeCascade.RetainedReachable)
        Assert.Contains(second.Id, coneAfterTypeCascade.RetainedReachable)

        let sharedRepNode =
            current.Edges
            |> List.pick (fun edge ->
                match edge.Role with
                | EdgeRole.NumericCarrier carrier when Set.contains edge.Target firstSubtree ->
                    carrier.Declaration
                | _ -> None)
        let allRepConsumerSites =
            current.Edges
            |> List.choose (fun edge ->
                if List.contains sharedRepNode edge.Sources && Set.contains edge.Target allReachable then
                    Some edge.Target
                else
                    None)
            |> Set.ofList
        Assert.NotEmpty(allRepConsumerSites)
        let currentWithChangedRep =
            let oldRep = current.Nodes[sharedRepNode]
            { current with
                Nodes = current.Nodes.Add(sharedRepNode, { oldRep with Metadata = oldRep.Metadata.Add("PlatformEdit", MetadataValue.String "modified") }) }
        let coneAfterRepEdit = Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.computeShadowCone current currentWithChangedRep
        Assert.Contains(sharedRepNode, coneAfterRepEdit.SeedRoots)
        Assert.True(Set.isSubset allRepConsumerSites coneAfterRepEdit.AffectedCone)
        Assert.Empty(Set.intersect allRepConsumerSites coneAfterRepEdit.RetainedReachable)
        Assert.Empty(Set.intersect (Set.union latentSubtree addedSubtree) allRepConsumerSites)
        for consumerBinding in [first.Id; second.Id; helper.Id; caller.Id] do
            Assert.Contains(consumerBinding, coneAfterRepEdit.AffectedCone)
            Assert.DoesNotContain(consumerBinding, coneAfterRepEdit.RetainedReachable)
        for unreferencedBinding in [latent.Id; added.Id] do
            Assert.Contains(unreferencedBinding, coneAfterRepEdit.RetainedReachable)
            Assert.DoesNotContain(unreferencedBinding, coneAfterRepEdit.AffectedCone)

        let firstEnrichmentTarget =
            current.Edges
            |> List.pick (fun edge ->
                match edge.Role with
                | EdgeRole.EnrichedWith when List.exists (fun s -> Set.contains s firstSubtree) edge.Sources ->
                    Some edge.Target
                | _ -> None)
        let currentWithChangedFirstEnrichment =
            let oldTarget = current.Nodes[firstEnrichmentTarget]
            { current with
                Nodes = current.Nodes.Add(firstEnrichmentTarget, { oldTarget with Metadata = oldTarget.Metadata.Add("DomainEdit", MetadataValue.String "modified") }) }
        let coneAfterFirstEnrichmentEdit =
            Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.computeShadowCone
                current
                currentWithChangedFirstEnrichment
        Assert.Contains(firstEnrichmentTarget, coneAfterFirstEnrichmentEdit.SeedRoots)
        Assert.Contains(first.Id, coneAfterFirstEnrichmentEdit.AffectedCone)
        Assert.Contains(second.Id, coneAfterFirstEnrichmentEdit.RetainedReachable)

        // Transitive invalidation through a reachable, unchanged EnrichedWith target d:
        // EnrichedWith {u} -> d, p -> d, and d -> u, where only p.Metadata changes.
        let reachableEnrichmentNode =
            { current.Nodes[firstEnrichmentTarget] with IsReachable = true }
        let transitivePremiseToEnrichmentTarget =
            { Sources = [added.Id]
              Target = firstEnrichmentTarget
              Class = EdgeClass.Provenance
              Role = EdgeRole.Constrains
              Ordinal = 0 }
        let enrichmentTargetToConsumer =
            { Sources = [firstEnrichmentTarget]
              Target = first.Id
              Class = EdgeClass.Provenance
              Role = EdgeRole.Constrains
              Ordinal = 0 }
        let baselineWithTransitiveEnrichmentPremise =
            { current with
                Nodes = current.Nodes.Add(firstEnrichmentTarget, reachableEnrichmentNode)
                Edges = transitivePremiseToEnrichmentTarget :: enrichmentTargetToConsumer :: current.Edges }
        let currentWithChangedTransitivePremise =
            let oldAdded = baselineWithTransitiveEnrichmentPremise.Nodes[added.Id]
            { baselineWithTransitiveEnrichmentPremise with
                Nodes =
                    baselineWithTransitiveEnrichmentPremise.Nodes.Add(
                        added.Id,
                        { oldAdded with Metadata = oldAdded.Metadata.Add("PremiseEdit", MetadataValue.String "modified") }) }
        let coneThroughUnchangedEnrichmentTarget =
            Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.computeShadowCone
                baselineWithTransitiveEnrichmentPremise
                currentWithChangedTransitivePremise
        Assert.Contains(added.Id, coneThroughUnchangedEnrichmentTarget.SeedRoots)
        Assert.DoesNotContain(firstEnrichmentTarget, coneThroughUnchangedEnrichmentTarget.SeedRoots)
        Assert.DoesNotContain(first.Id, coneThroughUnchangedEnrichmentTarget.SeedRoots)
        Assert.Contains(firstEnrichmentTarget, coneThroughUnchangedEnrichmentTarget.AffectedCone)
        Assert.Contains(first.Id, coneThroughUnchangedEnrichmentTarget.AffectedCone)
        Assert.Contains(second.Id, coneThroughUnchangedEnrichmentTarget.RetainedReachable)

        let sharedNumericDomainEdge =
            current.Edges
            |> List.pick (fun edge ->
                match edge.Role with
                | EdgeRole.NumericDomain _ -> Some edge
                | _ -> None)
        let sharedNumericDomainTarget = sharedNumericDomainEdge.Target
        let currentWithChangedNumericDomain =
            let oldTarget = current.Nodes[sharedNumericDomainTarget]
            { current with
                Nodes = current.Nodes.Add(sharedNumericDomainTarget, { oldTarget with Metadata = oldTarget.Metadata.Add("DomainEdit", MetadataValue.String "modified") }) }
        let coneAfterNumericDomainEdit =
            Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.computeShadowCone
                current
                currentWithChangedNumericDomain
        Assert.Contains(sharedNumericDomainTarget, coneAfterNumericDomainEdit.SeedRoots)
        Assert.Contains(first.Id, coneAfterNumericDomainEdit.AffectedCone)
        Assert.Contains(second.Id, coneAfterNumericDomainEdit.AffectedCone)

        // Transitive invalidation along p -NumericDomain-> d -Constrains-> u and edge-delta seeding on EnrichedWith:
        let numericDomainPremiseToEnrichment =
            { Sources = [added.Id]
              Target = firstEnrichmentTarget
              Class = sharedNumericDomainEdge.Class
              Role = sharedNumericDomainEdge.Role
              Ordinal = 0 }
        let baselineWithNumericDomainHop =
            { current with
                Nodes = current.Nodes.Add(firstEnrichmentTarget, reachableEnrichmentNode)
                Edges = numericDomainPremiseToEnrichment :: enrichmentTargetToConsumer :: current.Edges }
        let currentWithChangedNumericDomainPremise =
            let oldAdded = baselineWithNumericDomainHop.Nodes[added.Id]
            { baselineWithNumericDomainHop with
                Nodes =
                    baselineWithNumericDomainHop.Nodes.Add(
                        added.Id,
                        { oldAdded with Metadata = oldAdded.Metadata.Add("NumericDomainPremiseEdit", MetadataValue.String "modified") }) }
        let coneThroughNumericDomainHop =
            Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.computeShadowCone
                baselineWithNumericDomainHop
                currentWithChangedNumericDomainPremise
        Assert.Contains(added.Id, coneThroughNumericDomainHop.SeedRoots)
        Assert.DoesNotContain(firstEnrichmentTarget, coneThroughNumericDomainHop.SeedRoots)
        Assert.Contains(firstEnrichmentTarget, coneThroughNumericDomainHop.AffectedCone)
        Assert.Contains(first.Id, coneThroughNumericDomainHop.AffectedCone)
        Assert.Contains(second.Id, coneThroughNumericDomainHop.RetainedReachable)

        let addedEnrichedWithEdgeToFirst =
            { Sources = [added.Id]
              Target = first.Id
              Class = EdgeClass.Provenance
              Role = EdgeRole.EnrichedWith
              Ordinal = 0 }
        let coneFromEnrichedWithEdgeDelta =
            Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.computeShadowCone
                current
                { current with Edges = addedEnrichedWithEdgeToFirst :: current.Edges }
        Assert.Contains(first.Id, coneFromEnrichedWithEdgeDelta.SeedRoots)
        Assert.Contains(first.Id, coneFromEnrichedWithEdgeDelta.AffectedCone)
        Assert.Contains(second.Id, coneFromEnrichedWithEdgeDelta.RetainedReachable)

        let extinguishedEdge =
            { Sources = [latent.Id]
              Target = first.Id
              Class = EdgeClass.Provenance
              Role = EdgeRole.Constrains
              Ordinal = 0 }
        let coneFromExtinguishedPremise =
            Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.computeShadowCone
                { current with Edges = extinguishedEdge :: current.Edges }
                { baseline with Edges = extinguishedEdge :: baseline.Edges }
        Assert.Contains(latent.Id, coneFromExtinguishedPremise.ExtinguishedNodes)
        Assert.DoesNotContain(first.Id, coneFromExtinguishedPremise.SeedRoots)
        Assert.Contains(first.Id, coneFromExtinguishedPremise.AffectedCone)
        Assert.Contains(second.Id, coneFromExtinguishedPremise.RetainedReachable)
