namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeService
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module ValueEnvironments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments

module private ClosureValues =
    let check source =
        match parseAndCheck ("module ClosureValues\n" + source) "closure-values.clef" with
        | Success result | CheckFailure result ->
            DimensionalCases.noErrors result
            result
        | ParseFailure errors -> failwithf "Parse failed: %A" errors
    let bindingNamed name (result: CheckResult) =
        result.Graph.Nodes |> Map.values |> Seq.find (fun node ->
            node.IsReachable && match node.Kind with
                                | SemanticKind.Binding (bindingName, _, _, _) -> bindingName = name || bindingName.EndsWith("." + name)
                                | _ -> false)
    let rec valueNode (result: CheckResult) id =
        let node = result.Graph.Nodes[id]
        match node.Kind with
        | SemanticKind.TypeAnnotation (child, _) -> valueNode result child
        | _ -> node
    let assertAlias sourceName (result: CheckResult) =
        let saved = bindingNamed "saved" result
        let value = valueNode result saved.Children.Head
        match value.Kind with
        | SemanticKind.VarRef (name, Some _) -> Assert.True(name = sourceName || name.EndsWith("." + sourceName))
        | kind -> failwithf "A function alias must snapshot the referenced value, got %A" kind
        let promotedSource = ValueEnvironments.trySourceDeclaration result.Graph
        let sourceDefinition id =
            let occurrence = valueNode result id
            promotedSource occurrence.Id |> Option.orElseWith (fun () ->
                match occurrence.Kind with SemanticKind.VarRef (_, Some target) -> Some target | _ -> None)
        let source = sourceDefinition value.Id |> Option.get
        match result.Graph.Nodes[source].Kind with
        | SemanticKind.Binding (name, _, _, _) | SemanticKind.PatternBinding name ->
            Assert.True(name = sourceName || name.EndsWith("." + sourceName))
        | kind -> failwithf "Alias lost its source declaration: %A" kind
        let calls = result.Graph.Nodes |> Map.values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Application (funcId, args) when node.IsReachable && sourceDefinition funcId = Some saved.Id -> Some args
            | _ -> None) |> Seq.toList
        Assert.Single calls |> ignore
        Assert.Equal(2, calls.Head.Length)
    let expressionLambdas (result: CheckResult) =
        result.Graph.Nodes |> Map.values |> Seq.filter (fun node ->
            node.IsReachable && (node.Metadata |> Map.tryFind ClosureMetadata.LambdaExpression = Some (MetadataValue.Bool true))) |> Seq.toList
    let context: PlatformContext = {
            PlatformLoading = None
            PlatformId = "closure-test"; Dimensions = Map.ofList ["Pointer", 64; "Register", 64]
            Representations = Map.empty; EndpointReturns = Map.empty; PlatformLibraryPath = None
            PlatformDescription = None; PlatformArchitecture = None; PlatformOS = None
            PlatformSourcePaths = Set.empty
            Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
            AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None; ProjectMemoryPolicy = None }
    let assertPairs (result: CheckResult) =
        let layouts = Clef.Compiler.PSGSaturation.SemanticGraph.Placement.closures (Some context) result.Graph
        let lambdas = expressionLambdas result
        Assert.NotEmpty lambdas
        for node in lambdas do
            Assert.True(layouts.ContainsKey node.Id, $"Anonymous function {node.Id} has no closure placement")
            Assert.Equal(EscapeKind.EscapesViaReturn, result.Graph.Codata.Value.Escapes[node.Id])

    let plainCode name expectedArity (result: CheckResult) =
        let binding = bindingNamed name result
        let value = valueNode result (Assert.Single binding.Children)
        let implementation = ValueEnvironments.tryImplementation result.Graph value.Id |> Option.get
        let code = result.Graph.Nodes[implementation]
        Assert.Equal(None, ValueEnvironments.tryKnown result.Graph value.Id)
        Assert.Equal(Some (MetadataValue.Type binding.Type), code.Metadata.TryFind ClosureMetadata.SourceSignature)
        Assert.NotEqual(Some (MetadataValue.Bool true), code.Metadata.TryFind ClosureMetadata.RequiresClosurePair)
        Assert.NotEqual(Some (MetadataValue.Bool true), code.Metadata.TryFind ClosureMetadata.LambdaExpression)
        Assert.False(result.Graph.Codata.Value.Closures.ContainsKey code.Id)
        Assert.False(result.Graph.Codata.Value.Closures.ContainsKey value.Id)
        let declarations = ValueEnvironments.implementationBindings result.Graph
        Assert.Contains(code.Parent |> Option.get, declarations)
        match code.Kind with
        | SemanticKind.Lambda (parameters, body, [], _, _) ->
            Assert.Equal(expectedArity, parameters.Length)
            Assert.Equal<NodeId list>((parameters |> List.map (fun (_, _, id) -> id)) @ [body], code.Children)
            for _, ty, formal in parameters do
                Assert.Equal(Some code.Id, result.Graph.Nodes[formal].Parent)
                DimensionalCases.same ty result.Graph.Nodes[formal].Type
                Assert.Equal(None, ValueEnvironments.tryEnvironmentOwner result.Graph formal)
            code, parameters, body
        | kind -> failwithf "Expected a capture-free code declaration: %A" kind

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ClosureValues")>]
type ClosureValueTests() =
    [<Fact>]
    member _.``Refused integer storage does not publish a snapshot flow``() =
        // The write's result range is negative, so it selects the signed register
        // representation where the initializer's result selects the unsigned one.
        let source = """
module ClosureValues
let invoke (work: int -> int) value = work value
[<EntryPoint>]
let main _ =
    let mutable selected = fun (value: int) -> value + 1
    let saved = selected
    selected <- fun (value: int) -> value - 100
    invoke saved 7 + selected 7
"""
        let result = SourcePlatformFixture.checkResult 64 "refused-integer-snapshot.clef" source
        let graph = result.Graph
        let cell = ClosureValues.bindingNamed "selected" result
        let saved = ClosureValues.bindingNamed "saved" result
        let read = ClosureValues.valueNode result (Assert.Single saved.Children)
        let families, _ = Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.sourceFamilies graph
        Assert.True(families.ContainsKey cell.Id, "The control must retain the logical mutable family.")
        Assert.Contains(read.Id, families[cell.Id].Reads)
        let _, _, written = Assert.Single families[cell.Id].Writes
        Assert.True(graph.Codata.Value.CallableCarriers.ContainsKey families[cell.Id].Initial,
                    "The initializer must have an actual callable carrier.")
        Assert.True(graph.Codata.Value.CallableCarriers.ContainsKey written,
                    "The replacement must have an actual callable carrier.")
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.allowsOccurrence
                        (Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.analyze graph) read.Id,
                    "The exact read must be admitted before testing its absent physical flow.")
        Assert.Empty(result.Diagnostics |> List.filter (fun diagnostic ->
            diagnostic.Severity = NativeDiagnosticSeverity.Error && diagnostic.Code <> "CCS8403"))
        let initialResult = graph.Codata.Value.CallableCarriers[families[cell.Id].Initial].Result
        let writtenResult = graph.Codata.Value.CallableCarriers[written].Result
        let initialConvention = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention graph initialResult
        let writtenConvention = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention graph writtenResult
        Assert.True(initialConvention.IsSome && writtenConvention.IsSome,
                    "Both results select a convention; the write's negative range selects the signed register.")
        Assert.NotEqual(initialConvention, writtenConvention)
        let storage =
            Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.settle
                Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.sourceType
                Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.valueShape
                Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention
                graph.Codata.Value.CallableCarriers graph.Codata.Value.EnvironmentLayouts graph
        Assert.Contains(storage.Residuals, fun residual ->
            residual.Binding = cell.Id && residual.Reason.Contains("common parameter, result, and environment convention"))
        Assert.False(storage.Storage.ContainsKey cell.Id)
        Assert.False(storage.Joins.ContainsKey read.Id)
        Assert.False(graph.Codata.Value.CallableCarriers.ContainsKey read.Id)
        Assert.False(graph.Codata.Value.CallableJoins.ContainsKey read.Id,
                     "A refused storage contract must not publish a join for the read.")
        Assert.False(graph.Codata.Value.CallableFlows.ContainsKey read.Id,
                     "A refused storage contract must not publish a callable flow for the read.")
        Assert.False(graph.Codata.Value.CallableFlows.ContainsKey saved.Id,
                     "A refused storage contract must not publish a callable flow for the saved alias.")
        let flows, flowResiduals =
            Clef.Compiler.PSGSaturation.SemanticGraph.CallableFlows.settle
                { Carriers = graph.Codata.Value.CallableCarriers
                  Joins = storage.Joins
                  Layouts = graph.Codata.Value.EnvironmentLayouts
                  SequenceFlows = graph.Codata.Value.SequenceFlows
                  SequenceFamilies = graph.Codata.Value.SequenceFamilies } graph
        Assert.False(flows.ContainsKey read.Id)
        Assert.False(flows.ContainsKey saved.Id)
        Assert.DoesNotContain(flowResiduals, fun residual ->
            (residual.Occurrence = read.Id || residual.Occurrence = saved.Id) &&
            residual.Reason.Contains("Every callable alternative"))

    [<Fact>]
    member _.``Admitted integer family with distinct result ranges publishes its snapshot flow``() =
        // Every parameter and result row selects the same declared convention while
        // the two result ranges differ; each range keeps its own coverage obligation.
        let source = """
module ClosureValues
let invoke (work: int -> int) value = work value
[<EntryPoint>]
let main _ =
    let mutable selected = fun (value: int) -> value + 1
    let saved = selected
    selected <- fun (value: int) -> value + 2
    invoke saved 7 + selected 7
"""
        let result = SourcePlatformFixture.checkResult 64 "admitted-integer-snapshot.clef" source
        let graph = result.Graph
        let cell = ClosureValues.bindingNamed "selected" result
        let saved = ClosureValues.bindingNamed "saved" result
        let read = ClosureValues.valueNode result (Assert.Single saved.Children)
        Assert.Empty(result.Diagnostics |> List.filter (fun diagnostic -> diagnostic.Severity = NativeDiagnosticSeverity.Error))
        let families, _ = Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.sourceFamilies graph
        let _, _, written = Assert.Single families[cell.Id].Writes
        let initialResult = graph.Codata.Value.CallableCarriers[families[cell.Id].Initial].Result
        let writtenResult = graph.Codata.Value.CallableCarriers[written].Result
        Assert.True(graph.Nodes[initialResult].ValueRange.IsSome && graph.Nodes[writtenResult].ValueRange.IsSome)
        Assert.NotEqual(graph.Nodes[initialResult].ValueRange, graph.Nodes[writtenResult].ValueRange)
        let convention = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention graph
        Assert.True((convention initialResult).IsSome, "The initializer's result selects a convention.")
        Assert.Equal(convention initialResult, convention writtenResult)
        Assert.True(graph.Codata.Value.MutableCallableStorage.ContainsKey cell.Id, "The family is admitted.")
        Assert.True(graph.Codata.Value.CallableJoins.ContainsKey read.Id, "The snapshot read holds its join.")
        // The storage owner seeds a join at the read and forwards it through the immutable
        // alias binding and its references, keeping SourceType, Storage, Read and Alternatives
        // (MutableCallableStorage.fs:268-286); the flows owner excludes join keys from flow
        // rows (CallableFlows.fs:178-180). The alias therefore holds a forwarded join, not a flow.
        let storage = graph.Codata.Value.MutableCallableStorage[cell.Id]
        Assert.True((storage.Alternatives = [ families[cell.Id].Initial; written ]),
                    "The admitted storage row keeps the initializer and the write as its distinct alternatives.")
        let forwarded occurrence =
            match graph.Codata.Value.CallableJoins.TryFind occurrence with
            | Some join ->
                Assert.True((join.Occurrence = occurrence), "A forwarded join is keyed by its own occurrence.")
                Assert.True((join.SourceType = storage.SourceType), "A forwarded join keeps the cell's source type.")
                Assert.True((join.Storage = cell.Id), "A forwarded join names the admitted cell.")
                Assert.True((join.Read = read.Id), "A forwarded join keeps the exact read it forwards.")
                Assert.True((join.Alternatives = storage.Alternatives), "A forwarded join keeps the storage row's exact alternatives.")
                Assert.False(graph.Codata.Value.CallableFlows.ContainsKey occurrence, "A join key holds no flow row.")
                Assert.False(graph.Codata.Value.CallableCarriers.ContainsKey occurrence, "A join key holds no carrier row.")
            | None -> failwithf "No held join at %A." occurrence
        forwarded read.Id
        forwarded saved.Id
        // Logical closed ingress binds the alias's actual to the receiving formal through
        // the real call (CallableIngress.fs:16-37, 896-918); it is not itself a physical flow.
        let invoke = ClosureValues.bindingNamed "invoke" result
        let work =
            match (ClosureValues.valueNode result (Assert.Single invoke.Children)).Kind with
            | SemanticKind.Lambda(parameters, _, _, _, _) ->
                match parameters |> List.filter (fun (name, _, _) -> name = "work" || name.EndsWith(".work")) with
                | [ _, _, formal ] -> formal
                | formals -> failwithf "invoke declares one formal named work, found %A." formals
            | kind -> failwithf "invoke's value is not a lambda: %A." kind
        let resolution = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
        let reading = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.analyzeWith graph resolution
        let promotedSource = ValueEnvironments.trySourceDeclaration graph
        let sourceDefinition id =
            let occurrence = ClosureValues.valueNode result id
            promotedSource occurrence.Id |> Option.orElseWith (fun () ->
                match occurrence.Kind with SemanticKind.VarRef (_, Some target) -> Some target | _ -> None)
        let ingress =
            match Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.closedFormalInputs graph resolution reading work with
            | Some ingress -> ingress
            | None -> failwith "The work formal needs a closed ingress with its actual inputs."
        let site, actual =
            ingress.Inputs |> List.filter (fun (_, actual) -> sourceDefinition actual = Some saved.Id) |> Assert.Single
        Assert.True(ingress.Participants.Contains work && ingress.Participants.Contains site && ingress.Participants.Contains actual,
                    "The formal, its call site and the alias's actual are ingress participants.")
        Assert.Contains(ingress.Closure.Calls, fun call ->
            call.Site = site && call.Parameters.Length = call.Arguments.Length &&
            (List.zip call.Parameters call.Arguments |> List.contains (work, actual)))
        for occurrence in [ read.Id; saved.Id; actual; work ] do
            Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.allowsOccurrence reading occurrence,
                        sprintf "Ingress admits %A under the physical resolution." occurrence)
        forwarded actual
        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph with
        | Result.Ok publication ->
            // Occurrence representations are published for every participant and must be a
            // scalar slot here; a value row is not presumed, so both are required explicitly
            // and must carry that same slot (NumericPublication.fs:97-108).
            let scalar id =
                match publication.OccurrenceRepresentations.TryFind id with
                | Some (Result.Ok (ValueRepresentation.Scalar slot)) -> slot
                | other -> failwithf "Result %A needs a published scalar occurrence representation, got %A." id other
            Assert.Equal(scalar initialResult, scalar writtenResult)
            match publication.Values.TryFind initialResult, publication.Values.TryFind writtenResult with
            | Some initialValue, Some writtenValue ->
                Assert.Equal(scalar initialResult, initialValue.Slot)
                Assert.Equal(scalar writtenResult, writtenValue.Slot)
                // Bind each published row to its own selected convention: the row's
                // representation record is the selected declared record and its bits are
                // the selected width; NumericPublication.fs:98 ties those bits to the slot.
                // The obligation counts below are membership only, not proof discharge.
                let bound id (published: NumericRepresentation option) (slot: SettledSlot) =
                    match convention id, published with
                    | Some (representation, bits), Some record ->
                        Assert.Equal(representation, record)
                        Assert.Equal(bits, record.Bits)
                        // NumericCarrierRecipes.fs:359 publishes the slot as Integer(bits, Some representation.Name).
                        Assert.Equal(SettledSlot.Integer(record.Bits, Some record.Name), slot)
                    | selected, published ->
                        failwithf "Result %A needs a selected convention and a published representation record, got %A and %A." id selected published
                bound initialResult initialValue.Representation initialValue.Slot
                bound writtenResult writtenValue.Representation writtenValue.Slot
                Assert.Equal(1, initialValue.Obligations.Length)
                Assert.Equal(1, writtenValue.Obligations.Length)
                Assert.NotEqual(initialValue.Range, writtenValue.Range)
            | _ -> failwith "Both results need a published numeric value row for the range and obligation check."
        | Result.Error reason -> failwithf "%A" reason
        // Owner-level invariance at this one graph state only: the compared convention
        // gates admission and is recorded nowhere, so a uniformly shifted selection
        // settles to the same storage, joins and residuals. This is not a phase,
        // currentness or pipeline-acceptance claim.
        let settleWith predicate =
            Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.settle
                Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.sourceType
                Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.valueShape predicate
                graph.Codata.Value.CallableCarriers graph.Codata.Value.EnvironmentLayouts graph
        let shifted graph nodeId =
            Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention graph nodeId
            |> Option.map (fun (representation, bits) -> representation, bits + 1)
        let settled = settleWith Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention
        Assert.True(settled.Storage.ContainsKey cell.Id)
        Assert.Equal(settled, settleWith shifted)
        // Final-graph currentness on this fixture only: emission rederives carriers, storage,
        // joins and flows on this graph under the real selection and compares them with the
        // held tables (CallableEmission.fs:69-81), so the rows installed before numeric
        // settlement must be exactly what the final state rederives. This shows neither
        // that the pipeline invokes emission nor early/late equality of any selection; the
        // fourth member is its refusing counterpart.
        let ordinary =
            match Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.projectValidated graph with
            | Result.Ok ordinary -> ordinary
            | Result.Error reason -> failwithf "The control needs the ordinary demand projection: %A" reason
        match Clef.Compiler.PSGSaturation.SemanticGraph.CallableEmission.projectWithDemand graph ordinary with
        | Result.Ok _ -> ()
        | Result.Error failures -> failwithf "Emission refused held rows the final state should rederive: %A" failures

    [<Fact>]
    member _.``Proved-inactive integer result refuses mutable callable storage``() =
        // Owner re-evaluation on a mutated final graph, not an actual inactive program:
        // one result row is given the Empty range, the proved-inactive case heldWidth
        // refuses (RangeAnalysis.fs:3776-3777); selectedConvention then answers None and
        // the storage owner refuses the family that it admits with the real range.
        let source = """
module ClosureValues
let invoke (work: int -> int) value = work value
[<EntryPoint>]
let main _ =
    let mutable selected = fun (value: int) -> value + 1
    let saved = selected
    selected <- fun (value: int) -> value + 2
    invoke saved 7 + selected 7
"""
        let result = SourcePlatformFixture.checkResult 64 "inactive-integer-snapshot.clef" source
        let graph = result.Graph
        let cell = ClosureValues.bindingNamed "selected" result
        let families, _ = Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.sourceFamilies graph
        let _, _, written = Assert.Single families[cell.Id].Writes
        let writtenResult = graph.Codata.Value.CallableCarriers[written].Result
        let settleOn (graph: SemanticGraph) =
            Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.settle
                Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.sourceType
                Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.valueShape
                Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention
                graph.Codata.Value.CallableCarriers graph.Codata.Value.EnvironmentLayouts graph
        Assert.True((settleOn graph).Storage.ContainsKey cell.Id, "The real ranges admit the family.")
        let inactive =
            { graph with Nodes = graph.Nodes.Add(writtenResult, { graph.Nodes[writtenResult] with ValueRange = Some ValueRange.Empty }) }
        Assert.Equal(None, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention inactive writtenResult)
        Assert.Equal(None, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth inactive writtenResult)
        let refused = settleOn inactive
        Assert.False(refused.Storage.ContainsKey cell.Id, "A proved-inactive result is no agreement.")
        Assert.Contains(refused.Residuals, fun residual ->
            residual.Binding = cell.Id && residual.Reason.Contains("common parameter, result, and environment convention"))

    [<Fact>]
    member _.``Without a platform mutable callable storage keeps the source range agreement``() =
        // No platform means no physical selection (RangeAnalysis.fs:3707, 3749): the owner
        // compares the alternatives' integer result ranges as the pushed rule did. The
        // source ranges are asserted explicitly: distinct ranges are refused, equal ranges
        // are admitted.
        let check name write =
            let source =
                "module ClosureValues" + System.Environment.NewLine +
                "let invoke (work: int -> int) value = work value" + System.Environment.NewLine +
                "[<EntryPoint>]" + System.Environment.NewLine +
                "let main _ =" + System.Environment.NewLine +
                "    let mutable selected = fun (value: int) -> value + 1" + System.Environment.NewLine +
                "    let saved = selected" + System.Environment.NewLine +
                sprintf "    selected <- fun (value: int) -> value + %d" write + System.Environment.NewLine +
                "    invoke saved 7 + selected 7" + System.Environment.NewLine
            let result = SourcePlatformFixture.checkResult 64 name source
            let graph = result.Graph
            let cell = ClosureValues.bindingNamed "selected" result
            let families, _ = Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.sourceFamilies graph
            let _, _, written = Assert.Single families[cell.Id].Writes
            let initialRange = graph.Nodes[graph.Codata.Value.CallableCarriers[families[cell.Id].Initial].Result].ValueRange
            let writtenRange = graph.Nodes[graph.Codata.Value.CallableCarriers[written].Result].ValueRange
            Assert.True(initialRange.IsSome && writtenRange.IsSome, "Both result ranges are established.")
            let unplatformed = { graph with Platform = None }
            Assert.Equal(None, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention unplatformed (graph.Codata.Value.CallableCarriers[written].Result))
            let settled =
                Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.settle
                    Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.sourceType
                    Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.valueShape
                    Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention
                    unplatformed.Codata.Value.CallableCarriers unplatformed.Codata.Value.EnvironmentLayouts unplatformed
            cell.Id, initialRange, writtenRange, settled
        let distinctCell, distinctInitial, distinctWritten, distinct = check "unplatformed-distinct-ranges.clef" 2
        Assert.NotEqual(distinctInitial, distinctWritten)
        Assert.False(distinct.Storage.ContainsKey distinctCell, "Distinct result ranges are no agreement without a platform.")
        Assert.Contains(distinct.Residuals, fun residual ->
            residual.Binding = distinctCell && residual.Reason.Contains("common parameter, result, and environment convention"))
        let equalCell, equalInitial, equalWritten, equal = check "unplatformed-equal-ranges.clef" 1
        Assert.Equal(equalInitial, equalWritten)
        Assert.True(equal.Storage.ContainsKey equalCell, "Equal result ranges remain the agreement without a platform.")

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Mutable callable alternatives proved inactive refuse storage on their Empty rows`` (invoked: bool) =
        // Mirrors OrdinaryDemandCases.fs:637-668 on a mutable family: a callable payload that
        // `keep` receives and ignores is a current inactivity proof (OrdinaryDemand.fs:35-46,
        // 625-630) whose formals RangeAnalysis.fs:1322-1332 defers and the range owner leaves
        // Empty. Empty is the proved-inactive range; Unbounded is the full type range of a row
        // without observations and is not accepted here. Every premise is asserted through the
        // owner's reading before the storage conclusion. With invoked = true the same cell's
        // alternatives are applied instead: no proof lists them, their rows are Bounded, their
        // conventions are selected, and the family is admitted.
        let useText = if invoked then "saved 7 + selected 7" else "keep saved + keep selected"
        let source =
            "module ClosureValues\nlet keep (callback: int -> int) = 0\n[<EntryPoint>]\nlet main _ =\n" +
            "    let mutable selected = fun (value: int) -> value + 1\n    let saved = selected\n" +
            "    selected <- fun (value: int) -> value + 2\n    " + useText + "\n"
        let result = SourcePlatformFixture.checkResult 64 (if invoked then "active-alternatives.clef" else "inactive-alternatives.clef") source
        let graph = result.Graph
        let cell = ClosureValues.bindingNamed "selected" result
        let saved = ClosureValues.bindingNamed "saved" result
        let read = ClosureValues.valueNode result (Assert.Single saved.Children)
        let families, sourceResiduals = Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.sourceFamilies graph
        // The selection callback below covers the whole settle, so the graph must hold exactly
        // the intended family and no source residual: every query then belongs to this cell.
        Assert.Empty sourceResiduals
        Assert.True((families.Count = 1 && families.ContainsKey cell.Id), "The graph holds exactly the intended mutable family.")
        let _, _, written = Assert.Single families[cell.Id].Writes
        let carrierOf alternative =
            match graph.Codata.Value.CallableCarriers.TryFind alternative with
            | Some carrier -> carrier
            | None -> failwithf "Alternative %A needs a settled carrier for this control." alternative
        let carriers = [ carrierOf families[cell.Id].Initial; carrierOf written ]
        let formalsOf (carrier: CallableCarrier) = carrier.Parameters |> List.map (fun (_, _, formal) -> formal)
        let inactive =
            match Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.tryInactivity graph with
            | Result.Ok inactive -> inactive
            | Result.Error failures -> failwithf "The control needs the current inactivity reading: %A" failures
        // Owner-level instrumentation, test side only: the selection callback the storage owner
        // receives records every node it is asked about and the answer. The owner reaches a
        // formal's comparison only by querying it (MutableCallableStorage.fs sameShape), after
        // the source-type, environment and arity conjuncts of sameBoundary (222-226); a recorded
        // None on the formal is what ties the refusal below to that formal and not to an earlier
        // conjunct. Answers are the real ones; only the record is added.
        let queries = System.Collections.Generic.List<NodeId * (NumericRepresentation * int) option>()
        let recorded (graph: SemanticGraph) (nodeId: NodeId) =
            let answer = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention graph nodeId
            queries.Add((nodeId, answer))
            answer
        let settled =
            Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.settle
                Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.sourceType
                Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.valueShape
                recorded
                graph.Codata.Value.CallableCarriers graph.Codata.Value.EnvironmentLayouts graph
        if invoked then
            for carrier in carriers do
                Assert.False(inactive.Implementations.ContainsKey carrier.Implementation, "An applied alternative is not proved inactive.")
                Assert.Equal(1, (formalsOf carrier).Length)
                for row in formalsOf carrier @ [ carrier.Result ] do
                    Assert.True((match graph.Nodes[row].ValueRange with Some (ValueRange.Bounded _) -> true | _ -> false),
                                sprintf "Applied row %A must be Bounded, got %A." row graph.Nodes[row].ValueRange)
                    Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention graph row).IsSome, sprintf "Applied row %A selects a convention." row)
                Assert.True((carrier.ParameterShapes = [ CallableValueShape.Data (List.head (formalsOf carrier)) ]), "The unary formal is the carrier's data parameter shape.")
                Assert.True((carrier.ResultShape = CallableValueShape.Data carrier.Result), "The result is the carrier's data result shape.")
            for carrier in carriers do
                for row in formalsOf carrier @ [ carrier.Result ] do
                    Assert.Contains(queries, fun (queried, answer) -> queried = row && answer.IsSome)
            Assert.True((queries |> Seq.forall (fun (_, answer) -> answer.IsSome)), "Every queried row of the admitted family selects a convention.")
            Assert.True(settled.Storage.ContainsKey cell.Id, "Applied alternatives with equal conventions are admitted.")
            Assert.True(graph.Codata.Value.MutableCallableStorage.ContainsKey cell.Id, "The pipeline installed the admitted storage row.")
        else
            for carrier in carriers do
                let formals = formalsOf carrier
                Assert.Equal(1, formals.Length)
                let proof =
                    match inactive.Implementations.TryFind carrier.Implementation with
                    | Some proof -> proof
                    | None -> failwithf "Alternative implementation %A must be proved inactive for this control; proved implementations: %A." carrier.Implementation (inactive.Implementations |> Map.keys |> List.ofSeq)
                Assert.True((proof.Parameters = formals), "The proof names the alternative's formals in order.")
                Assert.True((proof.Body = carrier.Result), "The proof names the alternative's body, the carrier's result.")
                Assert.True((carrier.ParameterShapes = [ CallableValueShape.Data (List.head formals) ]), "The unary formal is the carrier's data parameter shape.")
                for formal in formals do
                    Assert.Contains(formal, inactive.Formals)
                    Assert.True((graph.Nodes[formal].ValueRange = Some ValueRange.Empty),
                                sprintf "Proved-inactive formal %A must be Empty, got %A." formal graph.Nodes[formal].ValueRange)
                // Only the proof's formals are owner-proven Empty (OrdinaryDemandCases.fs:659-661,
                // RangeAnalysis.fs:1327). An excluded body keeps whatever range the range owner
                // gives it, observed as Unbounded on this fixture, and is not asserted. The formal
                // rows alone force the refusal asserted below: parameter shapes are compared
                // before the result (MutableCallableStorage.fs:225-226).
                for row in formals do
                    Assert.Equal(None, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention graph row)
                    Assert.Equal(None, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth graph row)
            // The owner compares the first alternative against itself first (253) and stops at
            // the first disagreement, so the recorded None must be on the first alternative's
            // formal; the second alternative's formal is queried only if the first agreed.
            let firstFormal = List.head (formalsOf (List.head carriers))
            Assert.Contains(queries, fun (queried, answer) -> queried = firstFormal && answer.IsNone)
            Assert.True((queries |> Seq.forall (fun (_, answer) -> answer.IsNone)), "No queried row of the refused family selects a convention.")
            Assert.True((queries |> Seq.forall (fun (queried, _) -> carriers |> List.exists (fun carrier -> List.contains queried (formalsOf carrier) || queried = carrier.Result))),
                        "Only the family's own rows are queried.")
            Assert.False(settled.Storage.ContainsKey cell.Id, "Proved-inactive rows are no agreement.")
            Assert.Contains(settled.Residuals, fun residual ->
                residual.Binding = cell.Id && residual.Reason.Contains("common parameter, result, and environment convention"))
            Assert.False(graph.Codata.Value.MutableCallableStorage.ContainsKey cell.Id, "The pipeline installed no storage row for the refused family.")
            Assert.False(graph.Codata.Value.CallableJoins.ContainsKey read.Id, "No join is published for a read of the refused family.")

    [<Fact>]
    member _.``A platform declaring no integer representation refuses mutable callable storage``() =
        // Owner re-evaluation on a platform copy, not an actual platform fixture: the admitted
        // program's final graph is re-settled under its own context with Representations
        // emptied (NativeTypes.fs:951-954). selectedRepresentation answers None for a context
        // declaring no integer representation (RangeAnalysis.fs:3701-3702), so selectedConvention
        // is None and the storage owner refuses the family it admits on the real platform.
        let source = """
module ClosureValues
let invoke (work: int -> int) value = work value
[<EntryPoint>]
let main _ =
    let mutable selected = fun (value: int) -> value + 1
    let saved = selected
    selected <- fun (value: int) -> value + 2
    invoke saved 7 + selected 7
"""
        let result = SourcePlatformFixture.checkResult 64 "no-representation-snapshot.clef" source
        let graph = result.Graph
        let cell = ClosureValues.bindingNamed "selected" result
        let families, _ = Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.sourceFamilies graph
        let _, _, written = Assert.Single families[cell.Id].Writes
        let rows = [ graph.Codata.Value.CallableCarriers[families[cell.Id].Initial].Result; graph.Codata.Value.CallableCarriers[written].Result ]
        let context =
            match graph.Platform with
            | Some context -> context
            | None -> failwith "The fixture supplies a platform."
        let bare = { graph with Platform = Some { context with Representations = Map.empty } }
        let settleOn (graph: SemanticGraph) =
            Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.settle
                Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.sourceType
                Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.valueShape
                Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention
                graph.Codata.Value.CallableCarriers graph.Codata.Value.EnvironmentLayouts graph
        for row in rows do
            Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention graph row).IsSome, sprintf "The real platform selects a convention for %A." row)
            Assert.Equal(None, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention bare row)
        Assert.True((settleOn graph).Storage.ContainsKey cell.Id, "The real platform admits the family.")
        let refused = settleOn bare
        Assert.False(refused.Storage.ContainsKey cell.Id, "No declared representation is no agreement.")
        Assert.Contains(refused.Residuals, fun residual ->
            residual.Binding = cell.Id && residual.Reason.Contains("common parameter, result, and environment convention"))

    [<Fact>]
    member _.``Unavailable numeric selection refuses mutable callable storage``() =
        // An unavailable selection on one alternative is no agreement, whatever the
        // ranges say; the same graph is admitted under the real selection.
        let source = """
module ClosureValues
let invoke (work: int -> int) value = work value
[<EntryPoint>]
let main _ =
    let mutable selected = fun (value: int) -> value + 1
    let saved = selected
    selected <- fun (value: int) -> value + 2
    invoke saved 7 + selected 7
"""
        let result = SourcePlatformFixture.checkResult 64 "unavailable-integer-snapshot.clef" source
        let graph = result.Graph
        let cell = ClosureValues.bindingNamed "selected" result
        let families, _ = Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.sourceFamilies graph
        let _, _, written = Assert.Single families[cell.Id].Writes
        let writtenResult = graph.Codata.Value.CallableCarriers[written].Result
        let settleWith predicate =
            Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.settle
                Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.sourceType
                Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.valueShape predicate
                graph.Codata.Value.CallableCarriers graph.Codata.Value.EnvironmentLayouts graph
        let masked graph nodeId =
            if nodeId = writtenResult then None
            else Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention graph nodeId
        Assert.True((settleWith Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention).Storage.ContainsKey cell.Id,
                    "The real selection admits the family.")
        let refused = settleWith masked
        Assert.False(refused.Storage.ContainsKey cell.Id)
        Assert.Contains(refused.Residuals, fun residual ->
            residual.Binding = cell.Id && residual.Reason.Contains("common parameter, result, and environment convention"))

    [<Fact>]
    member _.``Emission refuses a held storage row its current selection does not rederive``() =
        // Divergent late case only: a family admitted under a selection answering one
        // convention for every row is installed into a codata copy, and the emission
        // owner, rederiving storage under the real selection, refuses the held row
        // and its join. Nothing here measures a uniform early-to-late change.
        let source = """
module ClosureValues
let invoke (work: int -> int) value = work value
[<EntryPoint>]
let main _ =
    let mutable selected = fun (value: int) -> value + 1
    let saved = selected
    selected <- fun (value: int) -> value - 100
    invoke saved 7 + selected 7
"""
        let result = SourcePlatformFixture.checkResult 64 "stale-integer-snapshot.clef" source
        let graph = result.Graph
        let cell = ClosureValues.bindingNamed "selected" result
        let saved = ClosureValues.bindingNamed "saved" result
        let read = ClosureValues.valueNode result (Assert.Single saved.Children)
        let families, _ = Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.sourceFamilies graph
        let anchor =
            Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention graph
                graph.Codata.Value.CallableCarriers[families[cell.Id].Initial].Result
        Assert.True(anchor.IsSome)
        let settleWith predicate =
            Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.settle
                Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.sourceType
                Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.valueShape predicate
                graph.Codata.Value.CallableCarriers graph.Codata.Value.EnvironmentLayouts graph
        Assert.False((settleWith Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedConvention).Storage.ContainsKey cell.Id)
        let admitted = settleWith (fun _ _ -> anchor)
        Assert.True(admitted.Storage.ContainsKey cell.Id, "The constant selection admits the family.")
        Assert.True(admitted.Joins.ContainsKey read.Id)
        let stale =
            { graph with Codata = lazy { graph.Codata.Value with MutableCallableStorage = admitted.Storage; CallableJoins = admitted.Joins } }
        let ordinary =
            match Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.projectValidated graph with
            | Ok ordinary -> ordinary
            | Result.Error reason -> failwithf "The control needs the ordinary demand projection: %A" reason
        match Clef.Compiler.PSGSaturation.SemanticGraph.CallableEmission.projectWithDemand stale ordinary with
        | Result.Error failures ->
            Assert.Contains(failures, fun failure ->
                failure.Occurrence = Some cell.Id && failure.Reason.StartsWith("Mutable callable storage at"))
            Assert.Contains(failures, fun failure ->
                failure.Occurrence = Some read.Id && failure.Reason.StartsWith("Callable join at"))
        | Ok _ -> failwith "Emission accepted a held storage row that its current selection does not rederive."

    [<Fact>]
    member _.``Module level mutable snapshot ingress needs a current startup plan``() =
        let result = SourcePlatformFixture.checkResult 64 "module-snapshot.clef" """
module ClosureValues
let mutable selected = fun (value: bool) -> value
let invoke (work: bool -> bool) value = work value
[<EntryPoint>]
let main _ =
    let saved = selected
    selected <- fun (value: bool) -> not value
    if invoke saved false then 0 else 1
"""
        let graph = result.Graph
        Assert.Empty(result.Diagnostics |> List.filter (fun diagnostic ->
            diagnostic.Severity = NativeDiagnosticSeverity.Error && diagnostic.Code <> "CCS8403"))
        let plan = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read graph
        Assert.True(plan.IsSome, "This control must contain the selected program startup plan.")
        let cell = ClosureValues.bindingNamed "selected" result
        let saved = ClosureValues.bindingNamed "saved" result
        let read = ClosureValues.valueNode result (Assert.Single saved.Children)
        let work =
            graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && match node.Kind with SemanticKind.PatternBinding "work" -> true | _ -> false)
            |> Assert.Single
        let families, _ = Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.sourceFamilies graph
        Assert.True(families.ContainsKey cell.Id, "The module cell must have a logical family.")
        Assert.Contains(read.Id, families[cell.Id].Reads)
        Assert.Single families[cell.Id].Writes |> ignore
        Assert.Contains((Option.get plan).Initializers, fun initial -> initial.Binding = cell.Id)
        let ingress graph = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.analyze graph
        let evidence = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.tryEvidence (ingress graph) work.Id
        Assert.True(evidence.IsSome, "The current graph admits this module-level snapshot.")
        Assert.Contains(read.Id, (Option.get evidence).Participants)
        Assert.Contains(cell.Id, (Option.get evidence).Participants)
        Assert.Equal(Some (Option.get plan).EntryLambda,
                     Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.tryExecutionOwner (ingress graph) cell.Id)
        let stale = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramInitialization) }
        Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read stale).IsNone)
        Assert.Equal(Some (Option.get plan).EntryLambda,
                     Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.tryExecutionOwner (ingress stale) cell.Id)
        Assert.False(Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.allowsOccurrence (ingress stale) work.Id,
                     "The admission must retract when the startup plan is missing.")
        let exportedKind =
            match cell.Kind with
            | SemanticKind.Binding(name, mutableBinding, recursiveBinding, _) ->
                SemanticKind.Binding(name, mutableBinding, recursiveBinding, Some DeclRoot.LibraryExport)
            | kind -> failwithf "Expected mutable binding, got %A" kind
        let externalRoots = [
            "declaration annotation", { graph with Nodes = graph.Nodes.Add(cell.Id, { cell with Kind = exportedKind }) }
            "root table", { graph with DeclarationRoots = (cell.Id, DeclRoot.LibraryExport) :: graph.DeclarationRoots }
        ]
        let admittedRoots = externalRoots |> List.choose (fun (description, externalGraph) ->
            if Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.allowsOccurrence (ingress externalGraph) work.Id
            then Some description else None)
        Assert.Empty admittedRoots

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Mutable callable snapshot ingress retains its exact read and complete source family``(annotated: bool) =
        let source = """
let invoke (work: bool -> bool) value = work value
let other (foreign: bool -> bool) value = foreign value
[<EntryPoint>]
let main _ =
    let mutable selected<INITIAL> = fun (value: bool) -> value
    let saved = selected
    selected <- <WRITE>
    let independent = other (fun value -> not value) false
    if invoke saved independent then 0 else 1
"""
        let source = source.Replace("<INITIAL>", if annotated then ": bool -> bool" else "")
                           .Replace("<WRITE>", if annotated then "((fun (value: bool) -> not value) : bool -> bool)" else "fun (value: bool) -> not value")
        let result = ClosureValues.check source
        let graph = result.Graph
        let cell = ClosureValues.bindingNamed "selected" result
        let saved = ClosureValues.bindingNamed "saved" result
        let read = ClosureValues.valueNode result (Assert.Single saved.Children)
        let work =
            graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && match node.Kind with SemanticKind.PatternBinding "work" -> true | _ -> false)
            |> Assert.Single
        let foreign =
            graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && match node.Kind with SemanticKind.PatternBinding "foreign" -> true | _ -> false)
            |> Assert.Single
        let actual =
            graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && match node.Kind with
                                    | SemanticKind.VarRef("saved", Some source) -> source = saved.Id
                                    | _ -> false) |> Assert.Single
        let families, residuals = Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.sourceFamilies graph
        Assert.Empty residuals
        let family = families[cell.Id]
        Assert.Contains(read.Id, family.Reads)
        Assert.Single family.Writes |> ignore
        let ingress graph = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.analyze graph
        let admitted = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.tryEvidence (ingress graph) work.Id
        Assert.True(admitted.IsSome, "The exact mutable snapshot must reach its closed callable formal.")
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.allowsOccurrence (ingress graph) foreign.Id,
                    "The separate callable formal must have a complete independent source.")
        let evidence = Option.get admitted
        Assert.Contains(read.Id, evidence.Participants)
        Assert.Contains(cell.Id, evidence.Participants)
        Assert.Contains(evidence.Calls, fun call -> List.contains actual.Id call.Arguments)
        let initial = graph.Nodes[family.Initial]
        let writer, target, value = Assert.Single family.Writes
        let isAnnotation id =
            match graph.Nodes[id].Kind with SemanticKind.TypeAnnotation _ -> true | _ -> false
        Assert.Equal(annotated, isAnnotation family.Initial)
        Assert.Equal(annotated, isAnnotation value)
        let written = graph.Nodes[writer]
        let opaque = { work with Id = NodeId.fresh(); Kind = SemanticKind.PatternBinding "unknown"; Parent = None; Children = [] }
        let opaqueWrite = SemanticKind.Set(target, opaque.Id)
        let updatedWrite = { written with Kind = opaqueWrite; Children = [target; opaque.Id] }
        let crossScopeWrite = SemanticKind.Set(target, work.Id)
        let crossScope = { written with Kind = crossScopeWrite; Children = [target; work.Id] }
        let resolvedCrossScopeWrite = SemanticKind.Set(target, foreign.Id)
        let resolvedCrossScope = { written with Kind = resolvedCrossScopeWrite; Children = [target; foreign.Id] }
        let currentEdges = graph.Edges |> List.filter (fun edge ->
            edge.Target <> writer || (edge.Class <> EdgeClass.Structural && edge.Class <> EdgeClass.Reference))
        let parent = graph.Nodes[Option.get written.Parent]
        let detachedParent =
            match parent.Kind with
            | SemanticKind.Sequential values ->
                let values = values |> List.filter ((<>) writer)
                { parent with Kind = SemanticKind.Sequential values; Children = values }
            | kind -> failwithf "Expected the write in a sequence, got %A" kind
        let detachedEdges = graph.Edges |> List.filter (fun edge ->
            edge.Target <> parent.Id || (edge.Class <> EdgeClass.Structural && edge.Class <> EdgeClass.Reference))
        let detached =
            { graph with Nodes = graph.Nodes.Add(parent.Id, detachedParent)
                         Edges = detachedEdges @ kindEdges parent.Id detachedParent.Kind }
        let detachedFamilies, _ = Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.sourceFamilies detached
        Assert.True(detachedFamilies.ContainsKey cell.Id, "The detached writer control must retain the logical family census.")
        let retyped = { graph with Nodes = graph.Nodes.Add(value, { graph.Nodes[value] with Type = NativeType.TFun(Types.boolType, Types.unitType) }) }
        if annotated then
            let changedFamilies, _ = Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.sourceFamilies retyped
            Assert.False(changedFamilies.ContainsKey cell.Id, "A retyped write annotation must retract its source family.")
        let invalid = [
            "missing read", { graph with Nodes = graph.Nodes.Remove read.Id }
            "redirected read", { graph with Nodes = graph.Nodes.Add(read.Id, { read with Kind = SemanticKind.VarRef("selected", None) }) }
            "changed read type", { graph with Nodes = graph.Nodes.Add(read.Id, { read with Type = Types.boolType }) }
            "opaque initializer", { graph with Nodes = graph.Nodes.Add(initial.Id, { initial with Kind = SemanticKind.PatternBinding "opaque"; Children = [] }) }
            "opaque write", { graph with Nodes = graph.Nodes.Add(writer, updatedWrite).Add(opaque.Id, opaque); Edges = currentEdges @ kindEdges writer opaqueWrite }
            "cross-activation write", { graph with Nodes = graph.Nodes.Add(writer, crossScope); Edges = currentEdges @ kindEdges writer crossScopeWrite }
            "resolved cross-activation write", { graph with Nodes = graph.Nodes.Add(writer, resolvedCrossScope); Edges = currentEdges @ kindEdges writer resolvedCrossScopeWrite }
            "detached writer", detached
            if annotated then
                "retyped write annotation", retyped
        ]
        for name, changed in invalid do
            Assert.False(Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.allowsOccurrence (ingress changed) work.Id,
                         $"The {name} must retract the mutable snapshot's ingress evidence.")

    [<Theory>]
    [<InlineData("")>]
    [<InlineData(": int -> int")>]
    member _.``Mutable callable initializers use the value boundary while direct bindings remain direct``(annotation: string) =
        let source = $"""
module ClosureValues
let direct (value: int) = value + 1
[<EntryPoint>]
let main _ =
    let mutable selected{annotation} = fun (value: int) -> value + 1
    let saved = selected
    selected <- fun (value: int) -> value + 2
    saved 7 + selected 7 + direct 7
"""
        let graph = SourcePlatformFixture.check 64 "mutable-value-boundary.clef" source
        let implementation name =
            let binding =
                graph.Nodes.Values |> Seq.filter (fun node ->
                    node.IsReachable && match node.Kind with
                                        | SemanticKind.Binding (actual, _, _, _) -> actual = name || actual.EndsWith("." + name)
                                        | _ -> false) |> Assert.Single
            let initial = Assert.Single binding.Children
            ValueEnvironments.tryImplementation graph initial |> Option.get
        let initial = implementation "selected"
        let direct = implementation "direct"
        let ranges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.escapes
        Assert.True((ranges graph initial).IsSome, "The mutable cell initializer must have the value-call boundary.")
        Assert.Equal(None, ranges graph direct)
        match graph.Nodes[initial].Kind with
        | SemanticKind.Lambda (parameters, body, _, _, _) ->
            for _, _, formal in parameters do
                Assert.Equal(Some 64, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedWidth graph formal)
            Assert.Equal(Some 64, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedWidth graph body)
        | kind -> failwithf "Expected the initial callable implementation, got %A" kind

    [<Fact>]
    member _.``Listener descriptors govern native callback entry scalar width and void result``() =
        let source = """
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Pointer of int | Float of int | Void
type PassBy = Value | Reference
type CallConv = | CDecl
type Transfer = | Borrowed
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type CallbackDescriptor = { Record: string; Field: string; Signature: FunctionDescriptor }
type Listener = { Done: FnPtr<CHandle<unit> -> int -> unit>; Marker: bool }
let mutable observed = 0
let onDone (_data: CHandle<unit>) (serial: int) : unit = observed <- serial
let DoneDescriptor: Expr<CallbackDescriptor> = <@ {
    Record = "Listener"; Field = "Done"
    Signature = { CName = "listener.done"
                  Parameters = [| { Name = "data"; Type = Pointer 64; PassBy = Value }
                                  { Name = "serial"; Type = Integer (Unsigned, 32); PassBy = Value } |]
                  ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Borrowed } } @>
[<EntryPoint>]
let main _ =
    let listener = { Done = FnPtr.ofFunction onDone; Marker = true }
    if listener.Marker then 0 else 1
"""
        let result = ClosureValues.check source
        let graph = { result.Graph with Platform = Some ClosureValues.context }
        let declarations = Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations.read graph
        Assert.Empty declarations.Findings
        let callback = Assert.Single declarations.Callbacks
        Assert.True callback.ReturnsVoid
        let serialId, serial = callback.Function.Parameters |> List.pick (fun (id, p) ->
            p |> Option.filter (fun p -> p.Name = "serial") |> Option.map (fun p -> id, p))
        Assert.Equal(32, serial.Bits)
        Assert.Equal(ValueRange.unsignedOf 32, serial.Range)
        Assert.Equal(Some serial.Range, result.Graph.Nodes[serialId].ValueRange)
        Assert.Equal(Some 32, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth graph serialId)
        let invalid = ClosureValues.check (source.Replace("ReturnType = Void", "ReturnType = Integer (Signed, 32)"))
        let invalidGraph = { invalid.Graph with Platform = Some ClosureValues.context }
        let invalidDeclarations = Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations.read invalidGraph
        Assert.Contains(invalidDeclarations.Findings, fun finding -> finding.Message.Contains("Void result"))
        let wrongPointer = ClosureValues.check (source.Replace("Type = Pointer 64", "Type = Float 64"))
        let wrongPointerGraph = { wrongPointer.Graph with Platform = Some ClosureValues.context }
        Assert.Contains((Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations.read wrongPointerGraph).Findings,
                        fun finding -> finding.Message.Contains("matching Pointer"))
        let otherPlatform = { graph with Platform = Some { ClosureValues.context with Dimensions = Map.ofList ["Pointer", 32; "Register", 64] } }
        Assert.Contains((Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations.read otherPlatform).Findings,
                        fun finding -> finding.Message.Contains("Pointer dimension"))

    [<Fact>]
    member _.``Declared callback ABI follows another address and its indirect scalar results``() =
        let source = """
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Pointer of int | Float of int | Void
type PassBy = Value | Reference
type CallConv = | CDecl
type Transfer = | Borrowed
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type CallbackDescriptor = { Record: string; Field: string; Signature: FunctionDescriptor }
type Listener = { Apply: FnPtr<int -> int> }
let identity (value: int) : int = value
let ApplyDescriptor: Expr<CallbackDescriptor> = <@ {
    Record = "Listener"; Field = "Apply"
    Signature = { CName = "listener.apply"
                  Parameters = [| { Name = "value"; Type = Integer (Signed, 32); PassBy = Value } |]
                  ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Borrowed } } @>
[<EntryPoint>]
let main _ =
    let listener = { Apply = FnPtr.ofFunction identity }
    let again = FnPtr.ofFunction identity
    let first = FnPtr.invoke listener.Apply -1
    let second = FnPtr.invoke again -2
    if first = -1 && second = -2 then 0 else 1
"""
        let result = ClosureValues.check source
        let graph = { result.Graph with Platform = Some ClosureValues.context }
        let callbacks = Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations.read graph
        Assert.Empty callbacks.Findings
        let calls = graph.Codata.Value.FunctionPointers |> Map.toList |> List.choose (function
            | call, FunctionPointerPlan.Invoke (pointer, _, _, _) -> Some (call, pointer)
            | _ -> None)
        Assert.Equal(2, calls.Length)
        for call, pointer in calls do
            Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations.forPointer graph pointer |> Option.isSome)
            Assert.Equal(Some (ValueRange.twosComplement 32), graph.Nodes[call].ValueRange)
            Assert.Equal(Some 32, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth graph call)
        let wrongResult = ClosureValues.check (source.Replace("ReturnType = Integer (Signed, 32)", "ReturnType = Float 32"))
        Assert.Contains((Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations.read wrongResult.Graph).Findings,
                        fun finding -> finding.Message.Contains("callback result needs a matching scalar"))

    [<Theory>]
    [<InlineData(32)>]
    [<InlineData(64)>]
    member _.``Aggregate function fields retain the entire settled view descriptor``(pointerBits: int) =
        let graph = SourcePlatformFixture.check pointerBits "closure-values.clef" """
module ClosureValues
type Holder = { Work: int -> int -> int; Tail: bool }
[<EntryPoint>]
let main _ =
    let holder = { Work = (fun a b -> a + b); Tail = true }
    if holder.Tail then holder.Work 1 2 else 0
"""
        let layout = graph.Layouts.Value |> Map.toSeq |> Seq.pick (fun (identity, layout) ->
            match identity with
            | TypeIdentity.Application(constructor, _) when constructor.Declaration.Name = "Holder" -> Some layout
            | _ -> None)
        match layout with
        | SettledLayout.Record ([work; tail], Some size, Some alignment) ->
            // Closure Representation §2.4: "A slot without an environment
            // and with one alternative occupies no component storage."
            Assert.Equal(SettledSlot.InlineBytes(0, 1), work.Slot)
            Assert.Equal(Some 0, work.Size)
            Assert.Equal(Some 0, tail.Offset)
            Assert.Equal(Some 1, tail.Size)
            Assert.Equal(1, size)
            Assert.Equal(1, alignment)
        | other -> failwithf "Expected a fully placed function/boolean record, got %A" other

    [<Fact>]
    member _.``Annotated zero-capture function values retain plain code and real arity``() =
        let result = ClosureValues.check """
let emptyWork: int -> int -> int = fun _lo _hi -> 0
let emptyRetirement: unit -> unit = fun () -> ()
[<EntryPoint>]
let main _ =
    emptyRetirement ()
    emptyWork 0 1
"""
        ClosureValues.plainCode "emptyWork" 2 result |> ignore
        ClosureValues.plainCode "emptyRetirement" 1 result |> ignore
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            node.IsReachable && match node.Kind with SemanticKind.ClosureValue _ | SemanticKind.EnvironmentCreate _ -> true | _ -> false)

    [<Fact>]
    member _.``Locally bound zero-capture values retain their promoted code boundary``() =
        let result = ClosureValues.check """
[<EntryPoint>]
let main _ =
    let failWork = fun (_lo: int) (_hi: int) -> 77
    failWork 0 1
"""
        let _, _, body = ClosureValues.plainCode "failWork" 2 result
        Assert.Equal(Some (ValueRange.point 77I), result.Graph.Nodes[body].ValueRange)
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            node.IsReachable && match node.Kind with SemanticKind.ClosureValue _ | SemanticKind.EnvironmentCreate _ -> true | _ -> false)

    [<Fact>]
    member _.``Returned zero-capture lambdas retain a live pair``() =
        let result = ClosureValues.check """
let make (choose: bool) =
    if choose then (fun (value: int) -> value)
    else (fun (value: int) -> value + 1)
[<EntryPoint>]
let main _ =
    let callback = make true
    callback 0
"""
        ClosureValues.assertPairs result

    [<Fact>]
    member _.``Returned unit closures retain their concrete generic record captures``() =
        let source = """type State<'a> = { Value: 'a; Ready: bool }
let make (state: State<'a>) = fun () -> state
[<EntryPoint>]
let main _ =
    let number = make { Value = 1000; Ready = true }
    let flag = make { Value = false; Ready = false }
    let numberState = number ()
    let flagState = flag ()
    if numberState.Value = 1000 && numberState.Ready && not flagState.Value && not flagState.Ready then 0 else 1
"""
        let result = ClosureValues.check source
        // As in assertPairs, supply the physical context directly to the placement stage;
        // a full platform check requires a source description declaring its dimensions.
        let placements = Clef.Compiler.PSGSaturation.SemanticGraph.Placement.closures (Some ClosureValues.context) result.Graph
        let closures = ClosureValues.expressionLambdas result
        Assert.Equal(2, closures.Length)
        for closure in closures do
            Assert.False(result.Graph.Codata.Value.Curry.AbsorbedLambdas.Contains closure.Id)
            Assert.True(placements.ContainsKey closure.Id)
            match closure.Kind with
            | SemanticKind.Lambda (parameters, _, captures, _, _) ->
                let _, parameterType, parameterId = Assert.Single parameters
                DimensionalCases.same Types.unitType parameterType
                Assert.Contains(parameterId, closure.Children)
                let capture = Assert.Single captures
                Assert.Equal("state", capture.Name)
                Assert.False(Clef.Compiler.NativeTypedTree.UnionFind.hasUnboundVars capture.Type)
            | kind -> failwithf "Returned function value ceased to be a lambda: %A" kind
            match closure.Parent |> Option.map (fun id -> result.Graph.Nodes[id]) with
            | Some { Kind = SemanticKind.Lambda (parameters, body, _, _, _) } ->
                Assert.Single parameters |> ignore
                Assert.Equal(closure.Id, body)
            | parent -> failwithf "Returned closure lost its enclosing callable: %A" parent

    [<Fact>]
    member _.``Ordinary curried declaration parameters still form one callable``() =
        let result = ClosureValues.check """
let add (left: int) (right: int) = left + right
[<EntryPoint>]
let main _ = add 20 22
"""
        let binding = ClosureValues.bindingNamed "add" result
        let lambda = ClosureValues.valueNode result binding.Children.Head
        match lambda.Kind with
        | SemanticKind.Lambda (parameters, body, _, _, _) ->
            Assert.Equal(2, parameters.Length)
            match result.Graph.Nodes[body].Kind with
            | SemanticKind.Lambda _ -> failwith "A formal parameter tail was left as a returned closure"
            | _ -> ()
        | kind -> failwithf "Named declaration ceased to be a callable: %A" kind

    [<Fact>]
    member _.``Range evidence keeps the closure factory separate from its returned callable``() =
        let result = ClosureValues.check """
[<Measure>] type m
let make (seed: int<m>) = fun (delta: int<m>) -> seed + delta
[<EntryPoint>]
let main _ =
    let work = make 1000<m>
    let actual = work 7<m>
    if actual = 1007<m> then 0 else 1
"""
        let factory = ClosureValues.bindingNamed "make" result
        let factoryLambda = ClosureValues.valueNode result factory.Children.Head
        match factoryLambda.Kind with
        | SemanticKind.Lambda (parameters, body, _, _, _) ->
            let _, _, seed = Assert.Single parameters
            Assert.Equal(Some (ValueRange.point 1000I), result.Graph.Nodes[seed].ValueRange)
            // Calling make supplies its complete parameter list. Its returned
            // function is the escaping value, rather than a partial call of make.
            Assert.Equal(None, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.escapes result.Graph factoryLambda.Id)
            let returned = result.Graph.Nodes[body]
            match returned.Kind with
            | SemanticKind.ClosureValue (implementation, environment) ->
                let code = result.Graph.Nodes[implementation]
                let returnedParameters =
                    match code.Kind with
                    | SemanticKind.Lambda (parameters, _, [], _, _) -> parameters
                    | kind -> failwithf "Returned value lost its physical implementation: %A" kind
                Assert.Equal(2, returnedParameters.Length)
                let _, _, formal = List.head returnedParameters
                Assert.Equal(Some returned.Id, ValueEnvironments.tryEnvironmentOwner result.Graph formal)
                Assert.Equal(Some returned.Id, ValueEnvironments.tryEnvironmentOwner result.Graph environment)
                Assert.Equal(Some (MetadataValue.Type returned.Type), code.Metadata.TryFind ClosureMetadata.SourceSignature)
                let _, deltaType, delta = Assert.Single (List.tail returnedParameters)
                Assert.Equal(Some (ValueRange.point 7I), result.Graph.Nodes[delta].ValueRange)
                let capture = ValueEnvironments.captures result.Graph returned.Id |> Assert.Single
                Assert.Equal(Some seed, capture.SourceNodeId)
                Assert.Equal(formatType deltaType, formatType capture.Type)
                Assert.False capture.IsMutable
                Assert.Equal<(NodeId * NodeId * bool) list>([(seed, seed, false)],
                    ValueEnvironments.capturedInitializers result.Graph returned.Id |> Option.get)
                let actual = ClosureValues.bindingNamed "actual" result
                let call = Assert.Single actual.Children
                let ordinal, actualEnvironment = ValueEnvironments.callEnvironments result.Graph |> Map.find call
                Assert.Equal(0, ordinal)
                Assert.Equal(Some returned.Id, ValueEnvironments.tryEnvironmentOwner result.Graph actualEnvironment)
            | kind -> failwithf "Factory result lost its callable boundary: %A" kind
        | kind -> failwithf "Expected a closure factory: %A" kind

    [<Fact>]
    member _.``One source fun keeps all formal parameters in its closure callable``() =
        let result = ClosureValues.check """
let mutable selected: int -> int -> int = fun left right -> left + right
let invoke (work: int -> int -> int) left right = work left right
[<EntryPoint>]
let main _ =
    let saved = selected
    selected <- fun left right -> left - right
    if invoke saved 7 3 = 10 && selected 7 3 = 4 then 0 else 1
"""
        let closures = ClosureValues.expressionLambdas result
        Assert.Equal(2, closures.Length)
        for closure in closures do
            match closure.Kind with
            | SemanticKind.Lambda (parameters, body, captures, _, _) ->
                Assert.Equal(2, parameters.Length)
                Assert.Empty captures
                match result.Graph.Nodes[body].Kind with
                | SemanticKind.Lambda _ -> failwith "A synthetic parameter group became a returned function value"
                | _ -> ()
            | kind -> failwithf "Function value ceased to be a lambda: %A" kind
        Assert.NotEmpty result.Graph.Codata.Value.Curry.AbsorbedLambdas
        for absorbed in result.Graph.Codata.Value.Curry.AbsorbedLambdas do
            let node = result.Graph.Nodes[absorbed]
            Assert.NotEqual(Some (MetadataValue.Bool true), Map.tryFind ClosureMetadata.LambdaExpression node.Metadata)

    [<Fact>]
    member _.``Named native callback declarations stay direct``() =
        let result = ClosureValues.check """
let identity (value: int) : int = value
[<EntryPoint>]
let main _ = FnPtr.invoke (FnPtr.ofFunction identity) 0
"""
        let symbol, lambda =
            result.Graph.Codata.Value.FunctionPointers |> Map.values |> Seq.pick (function FunctionPointerPlan.Address(symbol, lambda) -> Some(symbol, lambda) | _ -> None)
        Assert.Equal("ClosureValues.identity", symbol)
        Assert.False(result.Graph.Codata.Value.Closures.ContainsKey lambda)

    [<Fact>]
    member _.``A function parameter alias remains a value and receives all arguments together``() =
        let result = ClosureValues.check """
let apply (callback: int -> int -> int) (lo: int) (hi: int) =
    let saved = callback
    saved lo hi
[<EntryPoint>]
let main _ = apply (fun a b -> a + b) 40 2
"""
        ClosureValues.assertAlias "callback" result

    [<Fact>]
    member _.``A mutable function alias snapshots before subsequent assignment``() =
        let result = ClosureValues.check """
let add (a: int) (b: int) = a + b
let subtract (a: int) (b: int) = a - b
let mutable selected: int -> int -> int = add
[<EntryPoint>]
let main _ =
    let saved = selected
    selected <- subtract
    saved 40 2
"""
        ClosureValues.assertAlias "selected" result

    [<Fact>]
    member _.``An anonymous function alias reuses the existing closure value``() =
        let result = ClosureValues.check """
[<EntryPoint>]
let main _ =
    let callback = fun (a: int) (b: int) -> a + b
    let saved = callback
    saved 40 2
"""
        ClosureValues.assertAlias "callback" result

    [<Fact>]
    member _.``A named declaration alias retains plain code with a saturated direct call``() =
        let result = ClosureValues.check """
let add (a: int) (b: int) = a + b
[<EntryPoint>]
let main _ =
    let saved = add
    saved 40 2
"""
        let _, parameters, body = ClosureValues.plainCode "saved" 2 result
        let add = ClosureValues.bindingNamed "add" result
        match (ClosureValues.valueNode result body).Kind with
        | SemanticKind.Application (callee, arguments) ->
            match (ClosureValues.valueNode result callee).Kind with
            | SemanticKind.VarRef (_, Some declaration) -> Assert.Equal(add.Id, declaration)
            | kind -> failwithf "Expected the original declaration identity: %A" kind
            Assert.Equal(2, arguments.Length)
            List.zip parameters arguments |> List.iter (fun ((_, _, formal), argument) ->
                match result.Graph.Nodes[argument].Kind with
                | SemanticKind.VarRef (_, Some actual) -> Assert.Equal(formal, actual)
                | kind -> failwithf "Expected the original formal in source order: %A" kind)
        | kind -> failwithf "Expected saturated declaration call, got %A" kind

    [<Fact>]
    member _.``Indirect curried callbacks receive actual argument ranges through a mutable slot``() =
        let result = ClosureValues.check """
let mutable published: int -> int -> int = fun _lo _hi -> 0
let call () =
    let work = published
    work 224 257
let run (work: int -> int -> int) =
    published <- work
    call ()
[<EntryPoint>]
let main _ =
    let output: int array = Array.zeroCreate 258
    let work: int -> int -> int = fun lo hi ->
        let mutable index = lo
        while index < hi do
            Array.set output index 1
            index <- index + 1
        0
    let nested: int -> int -> int = fun lo hi -> work lo hi
    run work + run nested
"""
        let parameters = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.PatternBinding "lo" | SemanticKind.PatternBinding "hi" -> true | _ -> false) |> Seq.toList
        Assert.Equal(4, parameters.Length)
        for parameter in parameters do
            let expected = match parameter.Kind with SemanticKind.PatternBinding "lo" -> 224I | _ -> 257I
            Assert.Equal(Some (ValueRange.point expected), parameter.ValueRange)
        let index = ClosureValues.bindingNamed "index" result
        Assert.NotEqual(Some ValueRange.Empty, index.ValueRange)
        Assert.True(index.ValueRange |> Option.exists (fun range -> ValueRange.contains range (ValueRange.point 224I)))

    [<Fact>]
    member _.``An unobserved callback interior does not acquire a register width``() =
        let result = ClosureValues.check """
let keep (callback: int -> int -> int) = 0
[<EntryPoint>]
let main _ =
    let work: int -> int -> int = fun lo hi ->
        let saved = lo
        saved + hi
    keep work
"""
        let saved = ClosureValues.bindingNamed "saved" result
        // Width Inference §6: "A missing observation, an unreachable
        // computation, an inconsistent constraint, and a known range with no
        // covering representation are distinct states." This join is empty
        // because the current complete use census proves inactivity.
        let inactive =
            Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.tryInactivity result.Graph
            |> Result.defaultWith (fun failures -> failwithf "%A" failures)
        let proof = inactive.Implementations.Values |> Seq.filter (fun proof -> proof.Excluded.Contains saved.Id) |> Assert.Single
        Assert.All(proof.Parameters, fun formal ->
            Assert.Contains(formal, inactive.Formals)
            Assert.Equal(Some ValueRange.Empty, result.Graph.Nodes[formal].ValueRange))
        Assert.Equal(Some ValueRange.Empty, saved.ValueRange)
        let graph = { result.Graph with Platform = Some ClosureValues.context }
        Assert.Equal<int option>(None, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedWidthOf graph ValueRange.Empty)
        Assert.Equal<int option>(None, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth graph saved.Id)
        // The receiving signature retains its declared register convention;
        // a proved-inactive occurrence still has no physical held value.
        let core = { result.Graph with Platform = Some SourcePlatformFixture.platform }
        let formal = proof.Parameters.Head
        Assert.Equal<int option>(Some 64, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedWidth core formal)
        Assert.Equal<int option>(None, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth core formal)

    [<Fact>]
    member _.``Immutable binding adapts a uniform callback result before a narrow store``() =
        let result = ClosureValues.check """
let apply (callback: int -> int -> int) =
    let status = callback 0 1
    let mutable failure = 0
    failure <- status
    failure
[<EntryPoint>]
let main _ = apply (fun _lo _hi -> 0)
"""
        let representations = [
            { Name = "int8"; Capability = "native"; Family = "int"; Bits = 8
              MinMagnitude = "-128"; MaxMagnitude = "127"; Boundary = "wrap" }
            { Name = "int64"; Capability = "native"; Family = "int"; Bits = 64
              MinMagnitude = "-9223372036854775808"; MaxMagnitude = "9223372036854775807"; Boundary = "wrap" } ]
        let context = { ClosureValues.context with Representations = representations |> List.map (fun r -> r.Name, r) |> Map.ofList }
        let graph = { result.Graph with Platform = Some context }
        let status = ClosureValues.bindingNamed "status" result
        let call = ClosureValues.valueNode result status.Children.Head
        let width = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth graph
        Assert.Equal(Some 64, width call.Id)
        Assert.Equal(Some 8, width status.Id)
        let meets = Clef.Compiler.PSGSaturation.SemanticGraph.Meets.derive (Some context) graph result.Graph.Codata.Value.Curry
        Assert.True(meets.ContainsKey status.Id, "The immutable alias needs its ABI-to-binding representation meet")
        let conversion = Assert.Single meets[status.Id]
        Assert.Equal(call.Id, conversion.Operand)
        Assert.Equal(64, conversion.From)
        Assert.Equal(8, conversion.To)
        Assert.Equal(MeetKind.Truncate, conversion.Adapt)
