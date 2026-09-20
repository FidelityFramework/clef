namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Environments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments
module Residence = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence

module private EnvironmentFixture =
    let check source =
        match parseAndCheck ("module EnvironmentFixture\n" + source) "closure-environment.clef" with
        | Success result -> DimensionalCases.noErrors result; result.Graph
        | CheckFailure result -> failwithf "Expected admitted source: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed source: %A" errors

    let ordinary = """
[<EntryPoint>]
let main _ =
    let offset = 7
    let mutable calls = 0
    let mapper = fun value -> calls <- 1; value + offset
    let alias = mapper
    let mapped = Seq.map alias (seq { yield 2; yield 3 })
    for value in mapped do ignore value
    0
"""

    let callable (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && match node.Kind with SemanticKind.ClosureValue _ -> true | _ -> false) |> Assert.Single

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false) |> Assert.Single

    let preparedCollect () =
        let graph = check """
[<EntryPoint>]
let main _ =
    let mapper = fun (value: int) -> seq { yield value }
    let flattened = Seq.collect mapper (seq { yield 2; yield 3 })
    for value in flattened do ignore value
    0
"""
        let prepared = Clef.Compiler.Nanopass.SequenceFactoryResults.prepare graph graph.Codata.Value.Curry
        Assert.Empty prepared.Unresolved
        Assert.Single prepared.FactoryCalls |> ignore
        let graph = Clef.Compiler.Nanopass.SequenceEvaluation.normalize prepared.Graph
        graph, prepared

    let nestedCollect = """
[<EntryPoint>]
let main _ =
    let factor = 7
    let mutable effects = 0
    let mapper = fun (value: int) -> seq { effects <- 300; yield value * factor }
    let flattened = Seq.collect mapper (seq { yield 2; yield 3 })
    for value in flattened do ignore value
    0
"""

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ClosureEnvironments")>]
type ClosureEnvironmentCases() =
    [<Fact>]
    member _.``Known callback has a truthful env first implementation and keeps public source identity`` () =
        let graph = EnvironmentFixture.check EnvironmentFixture.ordinary
        let source = EnvironmentFixture.callable graph
        let implementation, environment = match source.Kind with SemanticKind.ClosureValue(code, storage) -> code, storage | _ -> failwith "No logical callable"
        let code = graph.Nodes[implementation]
        let formal, parameter =
            match code.Kind with
            | SemanticKind.Lambda([_, envType, formal; _, argumentType, parameter], _, [], _, _) ->
                DimensionalCases.same Environments.environmentType envType
                DimensionalCases.same (NativeType.TFun(argumentType, argumentType)) source.Type
                formal, parameter
            | kind -> failwithf "Expected actual environment and source parameter: %A" kind
        Assert.Equal(code.Range.Start, code.Range.End)
        Assert.Equal(MetadataValue.Type source.Type, code.Metadata[ClosureMetadata.SourceSignature])
        Assert.Equal(Some source.Id, graph.Codata.Value.EnvironmentOrigins.TryFind formal)
        Assert.Equal(Some implementation, graph.Codata.Value.KnownCallables.TryFind source.Id |> Option.map _.Implementation)
        Assert.NotEqual(formal, parameter)
        let mapper, alias = EnvironmentFixture.binding "mapper" graph, EnvironmentFixture.binding "alias" graph
        for value in [mapper; alias] do
            DimensionalCases.same source.Type value.Type
            Assert.Equal(Some { Implementation = implementation; EnvironmentOwner = source.Id }, Environments.tryKnown graph value.Id)
        match graph.Nodes[environment].Kind with
        | SemanticKind.EnvironmentCreate(owner, initializers) ->
            Assert.Equal(source.Id, owner)
            Assert.Equal(2, initializers.Length)
            Assert.All(initializers, fun (slot, value) -> Assert.Equal(slot, value))
        | kind -> failwithf "Missing source-time environment formation: %A" kind
        let calls = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with
            | SemanticKind.Application(_, first :: _) -> match graph.Nodes[first].Kind with SemanticKind.EnvironmentReference _ -> true | _ -> false
            | _ -> false) |> Seq.toList
        Assert.NotEmpty calls
        for call in calls do
            match call.Kind with
            | SemanticKind.Application(callee, [actual; _]) ->
                match graph.Nodes[callee].Kind with
                | SemanticKind.VarRef(_, Some binding) -> Assert.Equal<NodeId list>([implementation], graph.Nodes[binding].Children)
                | kind -> failwithf "Implementation callee is not a resolved real binding: %A" kind
                match graph.Nodes[actual].Kind with
                | SemanticKind.EnvironmentReference value -> Assert.Equal(Some source.Id, Environments.tryEnvironmentOwner graph value)
                | kind -> failwithf "Call lost its actual environment occurrence: %A" kind
            | kind -> failwithf "Call did not preserve ordinary explicit argument order: %A" kind
        for edge in graph.Edges do
            for participant in edge.Target :: edge.Sources do Assert.True(graph.Nodes.ContainsKey participant, sprintf "Missing graph participant %A" participant)

    [<Fact>]
    member _.``Environment capture mode and source cell identity survive body rewriting`` () =
        let graph = EnvironmentFixture.check EnvironmentFixture.ordinary
        let source = EnvironmentFixture.callable graph
        let offset, calls = EnvironmentFixture.binding "offset" graph, EnvironmentFixture.binding "calls" graph
        let captures = Environments.captures graph source.Id
        Assert.Contains(captures, fun capture -> capture.SourceNodeId = Some offset.Id && not capture.IsMutable)
        Assert.Contains(captures, fun capture -> capture.SourceNodeId = Some calls.Id && capture.IsMutable)
        Assert.Contains(graph.Nodes.Values, fun node -> node.IsReachable && match node.Kind with SemanticKind.EnvironmentRead(_, slot) -> slot = offset.Id | _ -> false)
        Assert.Contains(graph.Nodes.Values, fun node -> node.IsReachable && match node.Kind with SemanticKind.EnvironmentWrite(_, slot, _) -> slot = calls.Id | _ -> false)

    [<Fact>]
    member _.``Continuation control admits implementation code but still tracks actual environment initialization`` () =
        let graph = EnvironmentFixture.check EnvironmentFixture.ordinary
        let source = EnvironmentFixture.callable graph
        let environment = match source.Kind with SemanticKind.ClosureValue(_, storage) -> storage | _ -> failwith "No environment"
        let implementations = Environments.implementationBindings graph
        Assert.Single implementations |> ignore
        Assert.DoesNotContain(source.Id, implementations)
        Assert.DoesNotContain(environment, implementations)
        Assert.DoesNotContain((EnvironmentFixture.binding "alias" graph).Id, implementations)
        let owners = graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false) |> Seq.toList
        Assert.NotEmpty owners
        for owner in owners do
            match Clef.Compiler.Baker.Recipes.SequenceControlRecipes.forOwner graph owner with
            | Ok control ->
                Assert.True(Set.isSubset implementations control.AssignedAtEntry[control.Entry])
                Assert.DoesNotContain(environment, control.AssignedAtEntry[control.Entry])
            | Error pending -> failwithf "Known code declaration must not require runtime initialization: %A" pending

    [<Fact>]
    member _.``Bounded sequence consumption proves environment residence from graph incidence`` () =
        let original = EnvironmentFixture.check EnvironmentFixture.ordinary
        let graph = { original with Nodes = original.Nodes |> Map.map (fun _ node -> { node with Parent = None }) }
        let source = EnvironmentFixture.callable graph
        let environment = match source.Kind with SemanticKind.ClosureValue(_, storage) -> storage | _ -> failwith "No environment"
        let reading = Residence.analyzeEnvironments graph
        Assert.Empty reading.Unresolved
        Assert.Empty reading.Regions
        Assert.Equal(Some EscapeKind.StackScoped, reading.Sites.TryFind environment)
        let evidence = reading.Evidence |> List.filter (fun edge -> edge.Target = source.Id && edge.Role = EdgeRole.EnvironmentResidence) |> Assert.Single
        Assert.Contains(environment, evidence.Sources)
        Assert.Contains((EnvironmentFixture.binding "calls" graph).Id, evidence.Sources)

    [<Fact>]
    member _.``An opaque resident reference retracts environment scope admission at its exact consumer`` () =
        let graph = EnvironmentFixture.check EnvironmentFixture.ordinary
        let source, alias = EnvironmentFixture.callable graph, EnvironmentFixture.binding "alias" graph
        let environment = match source.Kind with SemanticKind.ClosureValue(_, storage) -> storage | _ -> failwith "No environment"
        // An ordinary value has no callable-consumption contract; introducing
        // a reference there must retract the environment's complete-use proof.
        let consumer = graph.Nodes.Values |> Seq.find (fun node -> node.IsReachable && match node.Kind with SemanticKind.Literal _ -> true | _ -> false)
        let opaque = Hyperedge.edge1 EdgeClass.Reference EdgeRole.Symbol 0 alias.Id consumer.Id
        let changed = { graph with Edges = opaque :: graph.Edges }
        let reading = Residence.analyzeEnvironments changed
        Assert.False(reading.Sites.ContainsKey environment)
        Assert.Contains(reading.Unresolved, fun pending -> pending.Site = environment && pending.Reason = Residence.ResidualReason.UnsupportedConsumer consumer.Id)
        Assert.Equal(Some EscapeKind.StackScoped, (Residence.analyzeEnvironments graph).Sites.TryFind environment)

    [<Fact>]
    member _.``Factory destination insertion preserves the exact callback environment formal and call argument`` () =
        let graph, prepared = EnvironmentFixture.preparedCollect ()
        let source = EnvironmentFixture.callable graph
        let implementation = match source.Kind with SemanticKind.ClosureValue(code, _) -> code | _ -> failwith "No callable"
        let relation = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.EnvironmentFormal && edge.Sources = [source.Id; implementation]) |> Assert.Single
        let destination = prepared.Destinations.Values |> Assert.Single
        let parameters = match graph.Nodes[implementation].Kind with SemanticKind.Lambda(parameters, _, [], _, _) -> parameters | _ -> failwith "No implementation"
        Assert.Equal(3, parameters.Length)
        let _, _, first = parameters[0]
        let _, _, second = parameters[1]
        Assert.Equal(destination, first)
        Assert.Equal(relation.Target, second)
        Assert.Equal(Some source.Id, Environments.tryEnvironmentOwner graph second)
        Assert.Equal(None, Environments.tryEnvironmentOwner graph first)
        Assert.Single(Environments.implementationBindings graph) |> ignore
        let call = prepared.FactoryCalls.Keys |> Assert.Single
        let arguments = match graph.Nodes[call].Kind with SemanticKind.Application(_, arguments) -> arguments | _ -> failwith "No prepared factory call"
        Assert.Equal(Some(1, arguments[1]), (Environments.callEnvironments graph).TryFind call)
        let residence = Residence.analyzeEnvironments graph
        Assert.Empty residence.Unresolved
        for owner in graph.Nodes.Values do
            match owner.Kind with
            | SemanticKind.SeqExpr _ when owner.IsReachable ->
                match Clef.Compiler.Baker.Recipes.SequenceControlRecipes.forOwner graph owner with
                | Ok _ -> ()
                | Error pending -> failwithf "Prepared callable code lost definite availability: %A" pending
            | _ -> ()

    [<Fact>]
    member _.``Environment call admission requires its exact formal relation and complete actual arity`` () =
        let graph, prepared = EnvironmentFixture.preparedCollect ()
        let call = prepared.FactoryCalls.Keys |> Assert.Single
        let node = graph.Nodes[call]
        let callee, arguments = match node.Kind with SemanticKind.Application(callee, arguments) -> callee, arguments | _ -> failwith "No prepared factory call"
        let short = { graph with Nodes = graph.Nodes.Add(call, { node with Kind = SemanticKind.Application(callee, List.tail arguments) }) }
        Assert.False((Environments.callEnvironments short).ContainsKey call)
        let destination = prepared.Destinations.Values |> Assert.Single
        let edges = graph.Edges |> List.map (fun edge -> if edge.Role = EdgeRole.EnvironmentFormal then { edge with Target = destination } else edge)
        let changed = { graph with Edges = edges }
        Assert.Empty(Environments.implementationBindings changed)
        Assert.False((Environments.callEnvironments changed).ContainsKey call)
        Assert.Equal(None, Environments.tryEnvironmentOwner changed destination)
        Assert.True((Environments.callEnvironments graph).ContainsKey call)

    [<Fact>]
    member _.``Returned child formation retains original slots and evaluates environment reads before construction`` () =
        let graph = EnvironmentFixture.check EnvironmentFixture.nestedCollect
        let formation = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequenceCaptureFormation) |> Assert.Single
        let child = graph.Nodes[formation.Target]
        let initializers = Environments.sequenceInitializers graph child |> Option.defaultWith (fun () -> failwith "Missing complete child initializers")
        let factor, effects = EnvironmentFixture.binding "factor" graph, EnvironmentFixture.binding "effects" graph
        let factorValue = initializers |> List.find (fst >> (=) factor.Id) |> snd
        let effectsValue = initializers |> List.find (fst >> (=) effects.Id) |> snd
        match graph.Nodes[factorValue].Kind, graph.Nodes[effectsValue].Kind with
        | SemanticKind.EnvironmentRead(_, actualFactor), SemanticKind.EnvironmentBorrow(_, actualEffects) ->
            Assert.Equal(factor.Id, actualFactor)
            Assert.Equal(effects.Id, actualEffects)
        | kinds -> failwithf "Expected typed snapshot and original-cell borrow: %A" kinds
        let generator, captures = match child.Kind with SemanticKind.SeqExpr(generator, captures) -> generator, captures | _ -> failwith "No child constructor"
        Assert.Contains(captures, fun capture -> capture.SourceNodeId = Some factor.Id && not capture.IsMutable)
        Assert.Contains(captures, fun capture -> capture.SourceNodeId = Some effects.Id && capture.IsMutable)
        let wrapper = graph.Nodes.Values |> Seq.filter (fun node -> match node.Kind with SemanticKind.Sequential values -> List.tryLast values = Some child.Id | _ -> false) |> Assert.Single
        let values = match wrapper.Kind with SemanticKind.Sequential values -> values | _ -> []
        Assert.True(List.findIndex ((=) factorValue) values < values.Length - 1)
        Assert.True(List.findIndex ((=) effectsValue) values < values.Length - 1)
        let generatorCaptures = match graph.Nodes[generator].Kind with SemanticKind.Lambda(_, _, captures, _, _) -> captures | _ -> []
        Assert.Contains(generatorCaptures, fun capture -> capture.SourceNodeId = Some effects.Id)
        for edge in graph.Edges |> List.filter (fun edge -> edge.Target = child.Id && match edge.Role with EdgeRole.SequenceCaptureFormation | EdgeRole.SequenceCaptureInitializer _ -> true | _ -> false) do
            Assert.All(edge.Sources, fun id -> Assert.True(graph.Nodes.ContainsKey id))

    [<Fact>]
    member _.``Returned mutable capture joins environment coverage to each actual caller destination`` () =
        let graph = EnvironmentFixture.check EnvironmentFixture.nestedCollect
        let prepared = Clef.Compiler.Nanopass.SequenceFactoryResults.prepare graph graph.Codata.Value.Curry
        Assert.Empty prepared.Unresolved
        let proof = prepared.Graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequenceEnvironmentBorrow) |> Assert.Single
        Assert.Contains((EnvironmentFixture.binding "effects" graph).Id, proof.Sources)
        Assert.Contains(prepared.Destinations[proof.Target], proof.Sources)
        for call, allocation in Map.toList prepared.FactoryCalls do
            Assert.Contains(call, proof.Sources)
            Assert.Contains(allocation, proof.Sources)
        Assert.All(proof.Sources, fun id -> Assert.True(prepared.Graph.Nodes.ContainsKey id))

    [<Fact>]
    member _.``Missing child initializer or escaped environment retracts borrowed factory admission`` () =
        let graph = EnvironmentFixture.check EnvironmentFixture.nestedCollect
        let effects = EnvironmentFixture.binding "effects" graph
        let formation = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.SequenceCaptureFormation) |> Assert.Single
        let changed = { graph with Edges = graph.Edges |> List.filter (fun edge -> not (edge.Target = formation.Target && edge.Role = EdgeRole.SequenceCaptureInitializer true)) }
        Assert.Equal(None, Environments.sequenceInitializers changed changed.Nodes[formation.Target])
        let missing = Clef.Compiler.Nanopass.SequenceFactoryResults.prepare changed changed.Codata.Value.Curry
        Assert.Contains(missing.Unresolved, fun pending -> pending.Reason.Contains("Reference capture") && pending.Reason.Contains("effects"))
        let mapper = EnvironmentFixture.binding "mapper" graph
        let literal = graph.Nodes.Values |> Seq.find (fun node -> node.IsReachable && match node.Kind with SemanticKind.Literal _ -> true | _ -> false)
        let escaped = { graph with Edges = Hyperedge.edge1 EdgeClass.Reference EdgeRole.Symbol 0 mapper.Id literal.Id :: graph.Edges }
        let residence = Residence.analyzeEnvironments escaped
        Assert.Contains(residence.Unresolved, fun pending -> pending.Reason = Residence.ResidualReason.UnsupportedConsumer literal.Id)
        let refused = Clef.Compiler.Nanopass.SequenceFactoryResults.prepare escaped escaped.Codata.Value.Curry
        Assert.Contains(refused.Unresolved, fun pending -> pending.Reason.Contains("Reference capture") && pending.Reason.Contains("effects"))
        Assert.True(Environments.sequenceInitializers graph graph.Nodes[formation.Target] |> Option.exists (List.exists (fst >> (=) effects.Id)))

    [<Fact>]
    member _.``Returning factory local mutable storage retains its exact lifetime residual`` () =
        let graph = EnvironmentFixture.check """
[<EntryPoint>]
let main _ =
    let mapper value =
        let mutable local = value
        seq { local <- 3; yield local }
    let flattened = Seq.collect mapper (seq { yield 2 })
    for value in flattened do ignore value
    0
"""
        let prepared = Clef.Compiler.Nanopass.SequenceFactoryResults.prepare graph graph.Codata.Value.Curry
        Assert.Contains(prepared.Unresolved, fun pending -> pending.Reason.Contains("Factory-local capture 'local'") && pending.Reason.Contains("returning activation"))
