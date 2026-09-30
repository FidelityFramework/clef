namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module ElementRecipes = Clef.Compiler.Baker.Recipes.SequenceElementRecipes
module ElementOrigins = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceOrigins
module ElementCurrent = Clef.Compiler.Nanopass.SequenceCurrentAdmission
module ElementRanges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis

module private ElementRangeFixture =
    let check source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        result.Graph

    let isElement = function
        | EdgeRole.SequenceElementAdmission | EdgeRole.SequenceElementOwner
        | EdgeRole.SequenceElementPayload | EdgeRole.SequenceElementUnknown -> true
        | _ -> false

    let evidence (graph: SemanticGraph) =
        let graph = { graph with Edges = graph.Edges |> List.filter (fun edge -> not (isElement edge.Role) && edge.Role <> EdgeRole.IteratorCurrentAdmitted) }
        let _, certificates = ElementCurrent.certify graph
        let graph = { graph with Edges = graph.Edges @ certificates }
        let facts = ElementRecipes.elaborate graph
        { graph with Edges = graph.Edges @ facts }, certificates

    let ranged graph = ElementRanges.run None graph |> fst
    let ordinary () = check "[<EntryPoint>]\nlet main _ =\n    for value in seq { yield 7; yield 300 } do ignore value\n    0\n"
    let range expected (graph: SemanticGraph) id = Assert.Equal(Some expected, graph.Nodes[id].ValueRange)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceElementRange")>]
type SequenceElementRangeCases() =
    [<Fact>]
    member _.``Nested delegation joins exact source payload ranges in the same fixed point``() =
        let graph = ElementRangeFixture.check """
[<EntryPoint>]
let main _ =
    let inner = seq { yield 7<m>; yield 300<m> }
    let middle = seq { yield! inner }
    let outer = seq { yield! middle }
    for value in outer do ignore value
    0
"""
        let enriched, certificates = ElementRangeFixture.evidence graph
        Assert.Equal(3, certificates.Length)
        let ranged = ElementRangeFixture.ranged enriched
        for certificate in certificates do
            ElementRangeFixture.range (ValueRange.Bounded(7I, 300I)) ranged certificate.Target
            Assert.Contains(enriched.Edges, fun edge ->
                edge.Target = certificate.Target && edge.Role = EdgeRole.SequenceElementAdmission
                && edge.Sources = certificate.Sources)
        Assert.Same(graph.Nodes, enriched.Nodes)

    [<Fact>]
    member _.``Pre-Curry declaration and application chains retain the unique factory origin``() =
        let graph = ElementRangeFixture.check """
let make (first: int) (last: int) = seq { yield first; yield last }
[<EntryPoint>]
let main _ =
    for value in make 7 300 do ignore value
    0
"""
        let binding = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding("make", _, _, _) -> true | _ -> false) |> Assert.Single
        let lambda = graph.Nodes[Assert.Single binding.Children]
        // Reconstitute the declaration chain to exercise the earlier pass
        // seam, without relying on the public pipeline's later Curry coeffect.
        let parameters, body, captures, enclosing, context =
            match lambda.Kind with SemanticKind.Lambda(p, b, c, e, x) -> p, b, c, e, x | _ -> failwith "No factory lambda"
        Assert.Equal(2, parameters.Length)
        let _, lastType, lastId = parameters[1]
        let innerId = NodeId.fresh()
        let inner =
            { lambda with
                Id = innerId
                Kind = SemanticKind.Lambda([parameters[1]], body, [], enclosing, context)
                Type = NativeType.TFun(lastType, graph.Nodes[body].Type)
                Children = [lastId; body]
                Parent = None }
        let _, _, firstId = parameters.Head
        let outer = { lambda with Kind = SemanticKind.Lambda([parameters.Head], innerId, captures, enclosing, context); Children = [firstId; innerId] }
        let curry = { graph.Codata.Value.Curry with SaturatedCalls = Map.empty; PartialApplications = Map.empty; AbsorbedLambdas = Set.empty }
        let raw =
            { graph with
                Nodes = graph.Nodes |> Map.add lambda.Id outer |> Map.add innerId inner
                Codata = lazy { graph.Codata.Value with Curry = curry } }
        let unique, _ = ElementOrigins.settle raw curry
        let enriched, certificates = ElementRangeFixture.evidence raw
        let certificate = Assert.Single certificates
        let iterator = match raw.Nodes[certificate.Target].Kind with SemanticKind.Application(_, [value]) -> value | _ -> failwith "No current"
        Assert.Equal(body, unique[iterator])
        ElementRangeFixture.range (ValueRange.Bounded(7I, 300I)) (ElementRangeFixture.ranged enriched) certificate.Target

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Unknown input alternatives prevent narrowing even alongside a bounded owner`` mixed =
        let selected = if mixed then "if flag then seq { yield 7 } else input" else "input"
        let graph = ElementRangeFixture.check (
            "let consume (flag: bool) (input: seq<int>) =\n    let selected = " + selected +
            "\n    for value in selected do ignore value\n[<EntryPoint>]\nlet main _ = ignore consume; 0\n")
        let enriched, certificates = ElementRangeFixture.evidence graph
        let certificate = Assert.Single certificates
        Assert.Contains(enriched.Edges, fun edge -> edge.Target = certificate.Target && edge.Role = EdgeRole.SequenceElementUnknown)
        if mixed then Assert.Contains(enriched.Edges, fun edge -> edge.Target = certificate.Target && edge.Role = EdgeRole.SequenceElementOwner)
        ElementRangeFixture.range ValueRange.Unbounded (ElementRangeFixture.ranged enriched) certificate.Target

    [<Theory>]
    [<InlineData("admission")>]
    [<InlineData("dependency")>]
    [<InlineData("payload")>]
    member _.``Missing proof participants cannot leave a narrower stale range`` missing =
        let enriched, certificates = ElementRangeFixture.evidence (ElementRangeFixture.ordinary ())
        let certificate = Assert.Single certificates
        let removed = enriched.Edges |> List.find (fun edge ->
            edge.Target = certificate.Target && edge.Role =
                (match missing with "admission" -> EdgeRole.IteratorCurrentAdmitted | "dependency" -> EdgeRole.SequenceElementAdmission | _ -> EdgeRole.SequenceElementPayload))
        let without = { enriched with Edges = enriched.Edges |> List.filter (fun edge -> not (edge.Target = removed.Target && edge.Role = removed.Role && edge.Sources = removed.Sources && edge.Class = removed.Class && edge.Ordinal = removed.Ordinal)) }
        ElementRangeFixture.range ValueRange.Unbounded (ElementRangeFixture.ranged without) certificate.Target
        if missing = "admission" then Assert.Empty (ElementRecipes.elaborate without)

    [<Fact>]
    member _.``Known empty sequence has no possible current payload instead of an invented value``() =
        let graph = ElementRangeFixture.check "[<EntryPoint>]\nlet main _ =\n    let values: seq<int> = seq { () }\n    for value in values do ignore value\n    0\n"
        let enriched, certificates = ElementRangeFixture.evidence graph
        let certificate = Assert.Single certificates
        Assert.Contains(enriched.Edges, fun edge -> edge.Target = certificate.Target && edge.Role = EdgeRole.SequenceElementOwner)
        Assert.DoesNotContain(enriched.Edges, fun edge -> edge.Target = certificate.Target && edge.Role = EdgeRole.SequenceElementPayload)
        ElementRangeFixture.range ValueRange.Empty (ElementRangeFixture.ranged enriched) certificate.Target

module private SequenceAccumulationFixture =
    let check body =
        let source = SequenceProgramFixture.header + body
        let input =
            match parseStringWithDefaults source SequenceProgramFixture.file with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Expected the finite summation source to parse: %A" errors
        checkParsedInputsWithPlatform [input] (Some SequenceProgramFixture.context)

    let cells name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(actual, true, _, _) -> actual = name | _ -> false)
        |> Seq.toList

    let admitted body =
        let result = check body
        let errors = CheckResult.errors result
        let cells = cells "total" result.Graph |> List.map (fun node -> node.Id, node.ValueRange)
        Assert.True(errors.IsEmpty, sprintf "Source errors: %A\nLive accumulator ranges: %A" errors cells)
        result.Graph

    let bounded finalValue upper (graph: SemanticGraph) =
        let cell = cells "total" graph |> Assert.Single
        match cell.ValueRange with
        | Some(ValueRange.Bounded(actualLower, actualUpper)) ->
            Assert.True(actualLower <= 0I && actualUpper >= finalValue, sprintf "Seed/final value missing from %A" cell.ValueRange)
            Assert.True(actualLower >= 0I && actualUpper <= upper, sprintf "Finite pull enclosure missing: %A" cell.ValueRange)
        | _ -> Assert.Fail(sprintf "The source-owned accumulator range must be finite: %A" cell.ValueRange)
        cell

    let currentRange expected (graph: SemanticGraph) =
        let admitted = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.IteratorCurrentAdmitted) |> Assert.Single
        Assert.Equal(Some expected, graph.Nodes[admitted.Target].ValueRange)
        admitted

    let evidence expectedPulls (graph: SemanticGraph) (cell: SemanticNode) =
        let accumulation =
            graph.Edges |> List.filter (fun edge ->
                edge.Class = EdgeClass.Range && edge.Role = EdgeRole.SequenceAccumulation && edge.Target = cell.Id)
            |> Assert.Single
        let owner, loop, seed, store, update, delta, current =
            match accumulation.Sources with
            | owner :: loop :: seed :: store :: update :: delta :: current :: _ -> owner, loop, seed, store, update, delta, current
            | sources -> failwithf "Incomplete accumulator evidence: %A" sources
        match graph.Nodes[owner].Kind with
        | SemanticKind.Lambda(_, _, _, _, context) -> Assert.NotEqual(LambdaContext.SeqGenerator, context)
        | kind -> failwithf "The accumulation lost its ordinary callable owner: %A" kind
        Assert.Equal<NodeId list>([seed], cell.Children)
        match graph.Nodes[store].Kind with
        | SemanticKind.Set(target, value) ->
            Assert.Equal(update, value)
            match graph.Nodes[target].Kind with
            | SemanticKind.VarRef(_, Some binding) -> Assert.Equal(cell.Id, binding)
            | kind -> failwithf "The accumulation store lost its exact cell: %A" kind
        | kind -> failwithf "The accumulation lost its actual store: %A" kind
        let pull =
            graph.Edges |> List.filter (fun edge ->
                edge.Class = EdgeClass.Range && edge.Role = EdgeRole.SequencePullBound && edge.Target = current)
            |> Assert.Single
        let producer, generator, input, enumerator, acquisition, guard, consumingLoop =
            match pull.Sources with
            | producer :: generator :: input :: enumerator :: acquisition :: guard :: loop :: _ ->
                producer, generator, input, enumerator, acquisition, guard, loop
            | sources -> failwithf "Incomplete finite-pull evidence: %A" sources
        Assert.Equal(loop, consumingLoop)
        let successfulCurrent =
            graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.IteratorCurrentAdmitted && edge.Target = current)
            |> Assert.Single
        Assert.Equal<NodeId list>([enumerator; guard; loop], successfulCurrent.Sources)
        match graph.Nodes[producer].Kind with
        | SemanticKind.SeqExpr(actual, _) -> Assert.Equal(generator, actual)
        | kind -> failwithf "The finite-pull proof lost its source producer: %A" kind
        match graph.Nodes[acquisition].Kind with
        | SemanticKind.Application(callee, [argument]) ->
            Assert.Equal(input, argument)
            match graph.Nodes[callee].Kind with
            | SemanticKind.Intrinsic info ->
                Assert.Equal(IntrinsicModule.Seq, info.Module)
                Assert.Equal("getEnumerator", info.Operation)
            | kind -> failwithf "The finite-pull proof lost its acquisition operation: %A" kind
        | kind -> failwithf "The finite-pull proof lost its acquisition: %A" kind
        let proof kind =
            let node =
                graph.Nodes.Values |> Seq.filter (fun node ->
                    match node.Kind with SemanticKind.Obligation info -> info.Kind = kind | _ -> false)
                |> Assert.Single
            let info = match node.Kind with SemanticKind.Obligation info -> info | _ -> failwith "Expected an obligation"
            let support =
                graph.Edges |> List.filter (fun edge ->
                    edge.Class = EdgeClass.Obligation && edge.Role = EdgeRole.Constrains && edge.Target = node.Id)
                |> Assert.Single
            for participant in cell.Id :: current :: accumulation.Sources @ pull.Sources |> List.distinct do
                Assert.True(graph.Nodes.ContainsKey participant, sprintf "Missing source participant %A" participant)
                Assert.Contains(participant, support.Sources)
            for site in [cell.Id; current; store; update; delta] do
                match graph.Nodes[site].Metadata.TryFind ObligationMetadata.Anchors with
                | Some(MetadataValue.StringList anchors) -> Assert.Contains(info.Id, anchors)
                | _ -> failwithf "Source participant %A lost its proof anchor" site
            info
        match (proof "finite-sequence-pulls").Body with
        | ObligationBody.FiniteSequencePull model ->
            Assert.Equal(expectedPulls, model.MaximumPulls)
            Assert.NotEmpty model.Steps
            Assert.Contains(model.Steps, fun step -> step.Label = model.Entry)
        | body -> failwithf "Wrong successful-pull obligation: %A" body
        match (proof "sequence-additive-invariant").Body with
        | ObligationBody.AdditiveLoopInvariant model ->
            Assert.Equal(expectedPulls, model.MaximumIterations)
            Assert.Equal(Some(ValueRange.Bounded(model.InitialLower, model.InitialUpper)), graph.Nodes[seed].ValueRange)
            Assert.Equal(Some(ValueRange.Bounded(model.DeltaLower, model.DeltaUpper)), graph.Nodes[delta].ValueRange)
            match cell.ValueRange with
            | Some range -> Assert.True(ValueRange.contains (ValueRange.Bounded(model.Lower, model.Upper)) range)
            | None -> failwith "The proven accumulator lost its range"
        | body -> failwithf "Wrong accumulation obligation: %A" body

    let twoYields = """
let input = seq { yield 10; yield 20 }
let sum () =
    let mutable total = 0
    for value in input do
        total <- total + value
    total
[<EntryPoint>]
let main _ = if sum () = 30 then 0 else 1
"""

    let sourceGraph body =
        let result = DimensionalCases.check body
        DimensionalCases.noErrors result
        Assert.True(result.Graph.Platform.IsNone)
        result.Graph

    let rejected expectedSites body =
        let source = "module Dimensions\n[<Measure>] type m\n[<Measure>] type s\n" + body
        match parseAndCheck source "dimensions.clef" with
        | CheckFailure result ->
            let errors = CheckResult.errors result
            Assert.NotEmpty errors
            let sites = errors |> List.map (fun diagnostic ->
                Assert.Equal("CCS8011", diagnostic.Code)
                Assert.Equal("dimensions.clef", diagnostic.Range.File)
                Assert.Contains("cannot be observed", diagnostic.Message)
                Assert.Equal(diagnostic.Range.Start.Line, diagnostic.Range.End.Line)
                let node = result.Graph.Nodes[Assert.Single diagnostic.RelatedNodes]
                Assert.True(node.IsReachable)
                Assert.True((node.Range = diagnostic.Range), "The range refusal must identify its actual source node")
                Assert.True(node.ValueRange |> Option.exists (ValueRange.isObservable >> not), "The rejected source node must retain a nonobservable range")
                diagnostic.Range.Start.Line, diagnostic.Range.Start.Column, diagnostic.Range.End.Column)
            Assert.Equal<(int * int * int) list>(List.sort expectedSites, List.sort sites)
            Assert.True(result.Graph.Platform.IsNone)
            result.Graph
        | result -> failwithf "Expected the located numeric source refusals: %A" result

    let raw () =
        // With no platform, the actual source recipes run before a runtime
        // machine replaces the generator. No source history is reconstructed.
        let graph = sourceGraph twoYields
        let cell = bounded 30I 40I graph
        evidence 2I graph cell
        graph

    let rewrite id kind children (graph: SemanticGraph) =
        let changed = { graph.Nodes[id] with Kind = kind; Children = children }
        let incidence (edge: Hyperedge) = edge.Class = EdgeClass.Structural || edge.Role = EdgeRole.Definition
        let edges = graph.Edges |> List.filter (fun edge -> edge.Target <> id || not (incidence edge))
        let current = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence changed |> List.filter incidence
        { graph with Nodes = graph.Nodes.Add(id, changed); Edges = edges @ current }

    let proofNodes (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Obligation info when info.Kind = "finite-sequence-pulls" || info.Kind = "sequence-additive-invariant" -> Some(node.Id, info.Id)
            | _ -> None) |> Seq.toList

    let noCertificate (graph: SemanticGraph) =
        Assert.DoesNotContain(graph.Edges, fun edge -> edge.Role = EdgeRole.SequencePullBound || edge.Role = EdgeRole.SequenceAccumulation)
        Assert.Empty(proofNodes graph)

    let retracted (original: SemanticGraph) (changed: SemanticGraph) =
        let before = proofNodes original
        Assert.Equal(2, before.Length)
        // The mutation retains old evidence, so this tests retraction rather
        // than constructing an already-empty inventory or fabricated Inputs.
        Assert.Equal<(NodeId * string) list>(before, proofNodes changed)
        let ranged, _ = ElementRanges.run None changed
        noCertificate ranged
        let oldIds = before |> List.map fst |> Set.ofList
        let oldNames = before |> List.map snd |> Set.ofList
        for id in oldIds do Assert.False(ranged.Nodes.ContainsKey id)
        Assert.DoesNotContain(ranged.Edges, fun edge -> oldIds.Contains edge.Target || edge.Sources |> List.exists oldIds.Contains)
        for node in ranged.Nodes.Values do
            match node.Metadata.TryFind ObligationMetadata.Anchors with
            | Some(MetadataValue.StringList anchors) -> Assert.False(anchors |> List.exists oldNames.Contains)
            | _ -> ()
        let cell = cells "total" ranged |> Assert.Single
        match cell.ValueRange with
        | Some range -> Assert.False(ValueRange.isObservable range, sprintf "A withdrawn finite pull proof left a finite accumulator: %A" range)
        | None -> Assert.Fail("Retraction lost the numeric cell instead of retaining its residual range")

    let handoff (graph: SemanticGraph) =
        let controls =
            graph.Nodes.Values |> Seq.choose (fun owner ->
                match owner.Kind with
                | SemanticKind.SeqExpr _ when owner.IsReachable ->
                    match Clef.Compiler.Baker.Recipes.SequenceControlRecipes.forOwner graph owner with
                    | Ok control -> Some(owner.Id, control)
                    | Result.Error error -> failwithf "Source control must remain valid for this proof-inventory test: %A" error
                | _ -> None)
            |> Map.ofSeq
        let fresh = ElementRanges.sequenceAccumulationFacts graph
        Assert.True(fresh.IsSome, "The ordinary demand census must remain valid for this proof-inventory test")
        Clef.Compiler.Baker.Recipes.SequenceAccumulationRecipes.handoff graph controls fresh

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceAccumulation")>]
type SequenceAccumulationCases() =
    [<Fact>]
    member _.``Named summation over a finite program sequence has a bounded accumulator``() =
        let source = SequenceProgramFixture.header + """
let input = seq { yield 10; yield 20 }
let sum () =
    let mutable total = 0
    for value in input do
        total <- total + value
    total
[<EntryPoint>]
let main _ = if sum () = 30 then 0 else 1
"""
        let input =
            match parseStringWithDefaults source SequenceProgramFixture.file with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Expected the finite summation source to parse: %A" errors
        let result = checkParsedInputsWithPlatform [input] (Some SequenceProgramFixture.context)
        let graph = result.Graph
        let cells = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding("total", true, _, _) -> true | _ -> false) |> Seq.toList
        let currentReads =
            graph.Edges |> List.choose (fun edge ->
                if edge.Role = EdgeRole.IteratorCurrentAdmitted then graph.Nodes.TryFind edge.Target else None)
            |> List.distinctBy (fun node -> node.Id)
        let errors = result.Diagnostics |> List.filter (fun diagnostic ->
            Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)
        let describe (node: SemanticNode) =
            sprintf "%A: kind=%A type=%s range=%A heldWidth=%A representation=%A"
                node.Id node.Kind (formatType node.Type) node.ValueRange
                (ElementRanges.heldWidth graph node.Id) (ElementRanges.selectedRepresentation graph node.Id)
        let report =
            [ yield sprintf "Source errors: %d" errors.Length
              for diagnostic in errors do
                  yield sprintf "%s: %s at %A; related=%A" diagnostic.Code diagnostic.Message diagnostic.Range diagnostic.RelatedNodes
              yield sprintf "Live accumulator cells: %d" cells.Length
              yield! cells |> List.map describe
              yield sprintf "Admitted current reads: %d" currentReads.Length
              yield! currentReads |> List.map describe ]
            |> String.concat "\n"
        // Inspect the actual checked result: no graph mutation or independent
        // range rerun may supply facts missing from complete source admission.
        Assert.True(errors.IsEmpty, report)
        let cell = Assert.Single cells
        Assert.NotEmpty currentReads
        match cell.ValueRange with
        | Some(ValueRange.Bounded(lower, upper)) ->
            // Two successful pulls, each in [10,20], suffice for [0,40]. This
            // admits a tighter proof while retaining the seed and final value.
            Assert.True(lower <= 0I && upper >= 30I, report)
            Assert.True(lower >= 0I && upper <= 40I, report)
        | _ -> Assert.Fail("The source-owned accumulator range must be finite.\n" + report)
        SequenceAccumulationFixture.evidence 2I graph cell

    [<Fact>]
    member _.``An added suspension changes the pull bound without changing the payload range``() =
        let graph = SequenceAccumulationFixture.admitted """
let input = seq { yield 10; yield 20; yield 20 }
let sum () =
    let mutable total = 0
    for value in input do
        total <- total + value
    total
[<EntryPoint>]
let main _ = if sum () = 50 then 0 else 1
"""
        // Repeating 20 leaves the element range unchanged. A two-pull row
        // would cap total at 40 and fail this actual three-suspension case.
        SequenceAccumulationFixture.currentRange (ValueRange.Bounded(10I, 20I)) graph |> ignore
        let cell = SequenceAccumulationFixture.bounded 50I 60I graph
        SequenceAccumulationFixture.evidence 3I graph cell

    [<Fact>]
    member _.``Generator writes to a disjoint program counter preserve the accumulator proof``() =
        let graph = SequenceAccumulationFixture.admitted """
let mutable pulls = 0
let input = seq {
    pulls <- (pulls + 1) % 100
    yield 10
    pulls <- (pulls + 1) % 100
    yield 20
}
let sum () =
    let mutable total = 0
    for value in input do
        total <- total + value
    total
[<EntryPoint>]
let main _ = if sum () = 30 then 0 else 1
"""
        let total = SequenceAccumulationFixture.bounded 30I 40I graph
        let pulls = SequenceAccumulationFixture.cells "pulls" graph |> Assert.Single
        Assert.NotEqual(total.Id, pulls.Id)
        let current = SequenceAccumulationFixture.currentRange (ValueRange.Bounded(10I, 20I)) graph
        let guard =
            match current.Sources with
            | [_; guard; _] -> guard
            | sources -> failwithf "Incomplete successful-current evidence: %A" sources
        Assert.Contains(graph.Edges, fun edge -> edge.Target = guard && edge.Role = EdgeRole.SequencePullBody)
        Assert.DoesNotContain(graph.Edges, fun edge -> edge.Target = guard && edge.Role = EdgeRole.SequenceEffectUnknown)
        SequenceAccumulationFixture.evidence 2I graph total
        let pull = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequencePullBound && edge.Target = current.Target) |> Assert.Single
        let generator =
            match pull.Sources with
            | _producer :: generator :: _ -> generator
            | sources -> failwithf "Missing generator identity: %A" sources
        let runtimeBody =
            match graph.Nodes[generator].Kind with
            | SemanticKind.Lambda(_, body, _, _, LambdaContext.SeqGenerator) -> body
            | kind -> failwithf "Missing realized sequence generator: %A" kind
        let rec descendants seen id =
            if Set.contains id seen then seen
            else graph.Nodes[id].Children |> List.fold descendants (Set.add id seen)
        let runtimeNodes = descendants Set.empty runtimeBody
        // Identify generated assignments from the current machine body, not
        // historical reachability or the presence of the correspondence being
        // tested. A missing correspondence cannot hide a generated target.
        let externalTargets =
            runtimeNodes |> Set.toList |> List.choose (fun id ->
                let node = graph.Nodes[id]
                match node.Kind with
                | SemanticKind.Set(target, _) when node.IsReachable ->
                    match graph.Nodes[target] with
                    | { Kind = SemanticKind.VarRef(_, Some declaration); IsReachable = true } as reference when declaration = pulls.Id -> Some reference
                    | _ -> None
                | _ -> None)
        Assert.Equal(2, externalTargets.Length)
        for target in externalTargets do
            let correspondence =
                graph.Edges |> List.filter (fun edge ->
                    edge.Class = EdgeClass.Provenance && edge.Role = EdgeRole.ContinuationValue && edge.Target = target.Id)
                |> Assert.Single
            let source = graph.Nodes[Assert.Single correspondence.Sources]
            Assert.NotEqual(source.Id, target.Id)
            match source.Kind with
            | SemanticKind.VarRef(_, Some declaration) -> Assert.Equal(pulls.Id, declaration)
            | kind -> failwithf "Generated assignment target lost its source reference: %A" kind
            Assert.Contains(graph.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Set(reference, _) -> reference = source.Id | _ -> false)
            Assert.True(source.ValueRange.IsSome)
            Assert.Equal(pulls.ValueRange, source.ValueRange)
            Assert.Equal(source.ValueRange, target.ValueRange)
            Assert.Equal(source.Range, target.Range)

    [<Theory>]
    [<InlineData("repeated-store-occurrence")>]
    [<InlineData("shared-iterator-reference")>]
    [<InlineData("cyclic-producer")>]
    [<InlineData("missing-evaluation-flow")>]
    [<InlineData("changed-evaluation-flow")>]
    member _.``Changed complete source premises retract finite pull evidence and accumulator ranges`` scenario =
        let graph = SequenceAccumulationFixture.raw ()
        let accumulation = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequenceAccumulation) |> Assert.Single
        let owner, loop, current =
            match accumulation.Sources with
            | owner :: loop :: _seed :: _store :: _update :: _delta :: current :: _ -> owner, loop, current
            | sources -> failwithf "Incomplete original accumulation: %A" sources
        let pull = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequencePullBound) |> Assert.Single
        let producer, generator, guard =
            match pull.Sources with
            | producer :: generator :: _input :: _enumerator :: _acquisition :: guard :: _ -> producer, generator, guard
            | sources -> failwithf "Incomplete original pull bound: %A" sources
        let changed =
            match scenario with
            | "repeated-store-occurrence" ->
                let body = match graph.Nodes[loop].Kind with SemanticKind.WhileLoop(_, body) -> body | _ -> failwith "Missing loop"
                let binding, reference, action =
                    match graph.Nodes[body].Kind with
                    | SemanticKind.Sequential [binding; reference; action] -> binding, reference, action
                    | kind -> failwithf "Missing current prefix: %A" kind
                let wrapperId = NodeId.fresh()
                let wrapper =
                    { graph.Nodes[action] with
                        Id = wrapperId
                        Kind = SemanticKind.Sequential [action; action]
                        Children = [action; action]
                        Parent = Some body
                        Metadata = Map.empty }
                let changed =
                    { graph with Nodes = graph.Nodes.Add(wrapperId, wrapper).Add(action, { graph.Nodes[action] with Parent = Some wrapperId }) }
                    |> SequenceAccumulationFixture.rewrite wrapperId wrapper.Kind wrapper.Children
                SequenceAccumulationFixture.rewrite body (SemanticKind.Sequential [binding; reference; wrapperId]) [binding; reference; wrapperId] changed
            | "shared-iterator-reference" ->
                let argument = match graph.Nodes[guard].Kind with SemanticKind.Application(_, [argument]) -> argument | _ -> failwith "Missing guard argument"
                let body = match graph.Nodes[owner].Kind with SemanticKind.Lambda(_, body, _, _, _) -> body | _ -> failwith "Missing consumer lambda"
                match graph.Nodes[body].Kind with
                | SemanticKind.Sequential values ->
                    // A second occurrence of the existing VarRef leaves the
                    // enumerator's set of reference node IDs unchanged.
                    let prefix, last = List.take (values.Length - 1) values, List.last values
                    let values = prefix @ [argument; last]
                    SequenceAccumulationFixture.rewrite body (SemanticKind.Sequential values) values graph
                | kind -> failwithf "Missing ordinary consumer scope: %A" kind
            | "cyclic-producer" ->
                let parameters, body, captures, enclosing, context =
                    match graph.Nodes[generator].Kind with
                    | SemanticKind.Lambda(parameters, body, captures, enclosing, context) -> parameters, body, captures, enclosing, context
                    | kind -> failwithf "Missing source generator: %A" kind
                let loopId, conditionId = NodeId.fresh(), NodeId.fresh()
                let condition =
                    { graph.Nodes[body] with
                        Id = conditionId
                        Kind = SemanticKind.Literal(NativeLiteral.Bool true)
                        Type = Types.boolType
                        Children = []
                        Parent = Some loopId
                        ValueRange = Some ValueRange.boolean
                        Metadata = Map.empty }
                let repeated =
                    { graph.Nodes[body] with
                        Id = loopId
                        Kind = SemanticKind.WhileLoop(conditionId, body)
                        Type = Types.unitType
                        Children = [conditionId; body]
                        Parent = Some generator
                        ValueRange = None
                        Metadata = Map.empty }
                let changed =
                    { graph with Nodes = graph.Nodes.Add(conditionId, condition).Add(loopId, repeated).Add(body, { graph.Nodes[body] with Parent = Some loopId }) }
                    |> SequenceAccumulationFixture.rewrite loopId repeated.Kind repeated.Children
                    |> SequenceAccumulationFixture.rewrite generator
                        (SemanticKind.Lambda(parameters, loopId, captures, enclosing, context))
                        ((parameters |> List.map (fun (_, _, id) -> id)) @ [loopId])
                    |> Clef.Compiler.Nanopass.SequenceEvaluation.normalize
                // The source/evaluation correspondence is fresh; refusal must
                // cover a real control cycle rather than a missing edge.
                match Clef.Compiler.Baker.Recipes.SequenceControlRecipes.forOwner changed changed.Nodes[producer] with
                | Ok _ -> ()
                | Result.Error error -> failwithf "Expected a well-formed cyclic source control: %A" error
                changed
            | "missing-evaluation-flow" | "changed-evaluation-flow" ->
                let flow = graph.Edges |> List.find (fun edge ->
                    edge.Class = EdgeClass.Evaluation && List.tryHead edge.Sources = Some producer &&
                    edge.Role = EdgeRole.EvaluationFlow(EvaluationPort.Ready, EvaluationPort.Exit, EvaluationTransfer.Resume))
                let fields (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
                if scenario = "missing-evaluation-flow" then
                    { graph with Edges = graph.Edges |> List.filter (fun edge -> fields edge <> fields flow) }
                else
                    let edges =
                        graph.Edges |> List.map (fun edge ->
                            if fields edge = fields flow then
                                { edge with Role = EdgeRole.EvaluationFlow(EvaluationPort.Ready, EvaluationPort.Exit, EvaluationTransfer.Continue) }
                            else edge)
                    { graph with Edges = edges }
            | _ -> failwithf "Unknown mutation: %s" scenario
        let _, stillCurrent = ElementCurrent.certify changed
        Assert.Contains(stillCurrent, fun certificate -> certificate.Target = current)
        let changed =
            if scenario = "repeated-store-occurrence" then
                // Refresh the actual upstream demand owner after changing a
                // structural occurrence. Range analysis must see valid demand
                // evidence while the old sequence proofs remain to retract.
                let normalized = Clef.Compiler.Nanopass.OrdinaryDemand.normalize changed
                match Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.tryRead normalized with
                | Ok _ -> ()
                | Result.Error failures -> failwithf "The current demand census must validate before range retraction: %A" failures
                Assert.Equal<(NodeId * string) list>(SequenceAccumulationFixture.proofNodes changed, SequenceAccumulationFixture.proofNodes normalized)
                normalized
            else changed
        SequenceAccumulationFixture.retracted graph changed

    [<Fact>]
    member _.``An additional accumulator writer cannot retain the zero-seed one-store proof``() =
        SequenceAccumulationFixture.raw () |> ignore
        let graph = SequenceAccumulationFixture.rejected [(7, 16, 21); (10, 17, 30); (13, 16, 22)] """
let input = seq { yield 10; yield 20 }
let sum () =
    let mutable total = 0
    total <- 100
    for value in input do
        total <- total + value
    total
[<EntryPoint>]
let main _ = if sum () = 130 then 0 else 1
"""
        SequenceAccumulationFixture.currentRange (ValueRange.Bounded(10I, 20I)) graph |> ignore
        let cell = SequenceAccumulationFixture.cells "total" graph |> Assert.Single
        let stores =
            graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable &&
                (match node.Kind with
                 | SemanticKind.Set(target, _) ->
                     match graph.Nodes[target].Kind with SemanticKind.VarRef(_, Some binding) -> binding = cell.Id | _ -> false
                 | _ -> false))
            |> Seq.toList
        Assert.Equal(2, stores.Length)
        SequenceAccumulationFixture.noCertificate graph

    [<Fact>]
    member _.``An unresolved sequence origin supplies no finite pull count``() =
        SequenceAccumulationFixture.raw () |> ignore
        let graph = SequenceAccumulationFixture.rejected [(6, 16, 21); (8, 17, 30); (11, 20, 23); (7, 4, 4)] """
let sum (input: seq<int>) =
    let mutable total = 0
    for value in input do
        total <- total + value
    total
[<EntryPoint>]
let main _ = ignore sum; 0
"""
        // Keeping the callable as a value leaves its input unsupplied; this is
        // an unknown-origin test, not a claim that sum was demanded or run.
        let current = SequenceAccumulationFixture.currentRange ValueRange.Unbounded graph
        Assert.Contains(graph.Edges, fun edge -> edge.Target = current.Target && edge.Role = EdgeRole.SequenceElementUnknown)
        SequenceAccumulationFixture.noCertificate graph

    [<Theory>]
    [<InlineData("missing-additive-proof")>]
    [<InlineData("missing-paired-relations")>]
    [<InlineData("orphan-proof")>]
    [<InlineData("duplicate-additive-proof")>]
    member _.``Runtime handoff requires a complete proof pair for every live accumulation`` scenario =
        let graph = SequenceAccumulationFixture.sourceGraph """
let input = seq { yield 10; yield 20 }
let sum () =
    let mutable total = 0
    for value in input do
        total <- total + value
    total
let sumAgain () =
    let mutable other = 0
    for value in input do
        other <- other + value
    other
[<EntryPoint>]
let main _ = if sum () = 30 then (if sumAgain () = 30 then 0 else 1) else 1
"""
        let facts = ElementRanges.sequenceAccumulationFacts graph |> Option.defaultWith (fun () -> failwith "Missing current source accumulation facts")
        Assert.Equal(2, facts.Length)
        Assert.Equal(4, (SequenceAccumulationFixture.proofNodes graph).Length)
        let intact, failures = SequenceAccumulationFixture.handoff graph
        Assert.Empty failures
        Assert.Equal<(NodeId * string) list>(SequenceAccumulationFixture.proofNodes graph, SequenceAccumulationFixture.proofNodes intact)
        let cell = SequenceAccumulationFixture.bounded 30I 40I graph
        let item = facts |> List.filter (fun item -> item.Cell = cell.Id) |> Assert.Single
        let additive, support =
            graph.Edges |> List.choose (fun edge ->
                if edge.Class = EdgeClass.Obligation && edge.Role = EdgeRole.Constrains && List.truncate 2 edge.Sources = [item.Current; item.Cell] then
                    match graph.Nodes[edge.Target].Kind with
                    | SemanticKind.Obligation info when info.Kind = "sequence-additive-invariant" -> Some(graph.Nodes[edge.Target], edge)
                    | _ -> None
                else None)
            |> Assert.Single
        let changed =
            match scenario with
            | "missing-additive-proof" ->
                { graph with
                    Nodes = graph.Nodes.Remove additive.Id
                    Edges = graph.Edges |> List.filter (fun edge -> edge.Target <> additive.Id && not (List.contains additive.Id edge.Sources)) }
            | "missing-paired-relations" ->
                let edges =
                    graph.Edges |> List.filter (fun edge ->
                        not ((edge.Role = EdgeRole.SequencePullBound && edge.Target = item.Current) ||
                             (edge.Role = EdgeRole.SequenceAccumulation && edge.Target = item.Cell)))
                { graph with Edges = edges }
            | "orphan-proof" | "duplicate-additive-proof" ->
                let copyId = NodeId.fresh()
                let info = match additive.Kind with SemanticKind.Obligation info -> info | _ -> failwith "Missing additive proof"
                let copy = { additive with Id = copyId; Kind = SemanticKind.Obligation { info with Id = info.Id + "_extra" } }
                let edges =
                    if scenario = "duplicate-additive-proof" then graph.Edges @ [{ support with Target = copyId }]
                    else graph.Edges
                { graph with Nodes = graph.Nodes.Add(copyId, copy); Edges = edges }
            | _ -> failwithf "Unknown proof inventory mutation: %s" scenario
        // The second accumulation remains present: a nonempty global inventory
        // cannot excuse a missing, duplicated or unowned pair for the first.
        let others = changed.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequenceAccumulation && edge.Target <> item.Cell)
        Assert.Single others |> ignore
        let _, failures = SequenceAccumulationFixture.handoff changed
        Assert.NotEmpty failures
