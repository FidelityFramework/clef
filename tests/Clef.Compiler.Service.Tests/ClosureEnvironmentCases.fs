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
    let offset = 1
    let mapper = fun (value: int) -> seq { yield value + offset }
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
    member _.``Ordinary callbacks settle the same callable formation as deferred consumers`` () =
        let graph = EnvironmentFixture.check """
[<EntryPoint>]
let main _ =
    let mutable visited = 0
    let visit = fun value -> visited <- (visited + value) % 100
    Seq.iter visit (seq { yield 1; yield 2 })
    let folder = fun state value -> (state + value) % 100
    let folded = Seq.fold folder 0 (seq { yield 3; yield 4 })
    let observe = fun value -> visited + value
    observe folded
"""
        let known = Environments.knownCallables graph
        for name in ["visit"; "observe"] do
            let binding = EnvironmentFixture.binding name graph
            let callable = known.TryFind binding.Id |> Option.defaultWith (fun () -> failwithf "%s lacks ordinary environment formation" name)
            let captures = Environments.captures graph callable.EnvironmentOwner
            let captured = Assert.Single captures
            Assert.True(captured.IsMutable)
            Assert.Equal(Some (EnvironmentFixture.binding "visited" graph).Id, captured.SourceNodeId)
            match graph.Nodes[callable.Implementation].Kind with
            | SemanticKind.Lambda(parameters, _, [], _, _) ->
                let _, _, formal = List.head parameters
                Assert.Equal(Some callable.EnvironmentOwner, Environments.tryEnvironmentOwner graph formal)
            | kind -> failwithf "Unsettled captured implementation: %A" kind
        let folder = EnvironmentFixture.binding "folder" graph
        let implementation = Environments.tryImplementation graph folder.Id |> Option.get
        Assert.False(known.ContainsKey folder.Id)
        match graph.Nodes[implementation].Kind with
        | SemanticKind.Lambda(_, _, [], _, _) ->
            Assert.True(graph.Nodes[implementation].Metadata.ContainsKey ClosureMetadata.SourceSignature)
            Assert.False(graph.Nodes[implementation].Metadata.ContainsKey ClosureMetadata.RequiresClosurePair)
        | kind -> failwithf "Stateless eager callback is not plain code: %A" kind

    [<Fact>]
    member _.``Stateless promotion retains each source alias name and exact declaration`` () =
        let graph = EnvironmentFixture.check """
[<EntryPoint>]
let main _ =
    let mapper = fun (value: int) -> value
    let firstAlias = mapper
    let secondAlias = mapper
    let unrelated = fun (value: int) -> value + 1
    let first = Seq.map firstAlias (seq { yield 1 })
    let second = Seq.map secondAlias (seq { yield 2 })
    let third = Seq.map unrelated (seq { yield 3 })
    for value in first do ignore value
    for value in second do ignore value
    for value in third do ignore value
    0
"""
        let sourceDeclaration = Environments.trySourceDeclaration graph
        let implementation = Environments.tryImplementation graph
        let sharedCode = implementation (EnvironmentFixture.binding "mapper" graph).Id |> Option.get
        for name in ["mapper"; "firstAlias"; "secondAlias"] do
            let declaration = EnvironmentFixture.binding name graph
            let references = graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && match node.Kind with SemanticKind.VarRef(actual, _) -> actual = name | _ -> false) |> Seq.toList
            Assert.NotEmpty references
            for reference in references do
                Assert.Equal(Some declaration.Id, sourceDeclaration reference.Id)
                Assert.Equal(Some sharedCode, implementation reference.Id)
                let edge = graph.Edges |> List.filter (fun edge ->
                    edge.Target = reference.Id && edge.Role = EdgeRole.CallableReferenceOrigin) |> Assert.Single
                let missing = { graph with Edges = graph.Edges |> List.filter (fun row -> row.Target <> reference.Id || row.Role <> EdgeRole.CallableReferenceOrigin) }
                Assert.Equal(None, Environments.trySourceDeclaration missing reference.Id)
                let ambiguous = { graph with Edges = edge :: graph.Edges }
                Assert.Equal(None, Environments.trySourceDeclaration ambiguous reference.Id)
                let unrelated = EnvironmentFixture.binding "unrelated" graph
                let foreign = { edge with Sources = [unrelated.Id; edge.Sources[1]] }
                let malformed = { missing with Edges = foreign :: missing.Edges }
                Assert.Equal(None, Environments.trySourceDeclaration malformed reference.Id)

    [<Fact>]
    member _.``Stored callbacks preserve the shared identity of an effectful supplied computation`` () =
        let graph = EnvironmentFixture.check """
[<EntryPoint>]
let main _ =
    let mutable formations = 0
    let stored = Seq.map (formations <- 1; fun (value: int) -> value)
    let first = stored (seq { yield 2 })
    let second = stored (seq { yield 3 })
    for value in first do ignore value
    for value in second do ignore value
    formations
"""
        let stored = EnvironmentFixture.binding "stored" graph
        let retained = Environments.tryKnown graph stored.Id |> Option.defaultWith (fun () -> failwith "Effectful callback computation lost its retained identity")
        let implementation = retained.Implementation
        let captured = Environments.capturedInitializers graph retained.EnvironmentOwner |> Option.defaultWith (fun () -> failwith "Missing exact callback capture") |> Assert.Single
        let slot, initializer, mutableCell = captured
        Assert.False mutableCell
        Assert.Equal(slot, initializer)
        let supplied = graph.Nodes[slot]
        match supplied.Kind with
        | SemanticKind.Binding(_, false, _, _) -> ()
        | kind -> failwithf "The original supplied computation has no shared binding: %A" kind
        let formation = graph.Nodes[Assert.Single supplied.Children]
        match formation.Kind with
        | SemanticKind.Sequential [effect; callback] ->
            match graph.Nodes[effect].Kind with
            | SemanticKind.Set _ -> ()
            | kind -> failwithf "The original effect was erased: %A" kind
            let code = Environments.tryImplementation graph callback |> Option.defaultWith (fun () -> failwith "Callback lost its actual code")
            match graph.Nodes[code].Kind with
            | SemanticKind.Lambda(_, _, captures, _, _) -> Assert.Empty captures
            | kind -> failwithf "Callback is not stateless code: %A" kind
        | kind -> failwithf "Code identity erased the original supplied computation: %A" kind
        let reads = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && (match node.Kind with SemanticKind.EnvironmentRead(_, source) -> source = slot | _ -> false)) |> Seq.toList
        Assert.NotEmpty reads
        for read in reads do
            Assert.Equal(Environments.tryImplementation graph initializer, Environments.tryImplementation graph read.Id)
        match graph.Nodes[implementation].Kind with
        | SemanticKind.Lambda(_, _, captures, _, _) -> Assert.Empty captures
        | kind -> failwithf "Expected explicit environment implementation: %A" kind
        Assert.False(graph.Nodes[implementation].Metadata.ContainsKey ClosureMetadata.RequiresClosurePair)
        let declarations = Environments.implementationBindings graph
        let declaration = graph.Nodes[implementation].Parent.Value
        Assert.Contains(declaration, declarations)
        Assert.DoesNotContain(stored.Id, declarations)
        for owner in graph.Nodes.Values do
            match owner.Kind with
            | SemanticKind.SeqExpr _ when owner.IsReachable ->
                match Clef.Compiler.Baker.Recipes.SequenceControlRecipes.forOwner graph owner with
                | Ok control -> Assert.True(Set.isSubset declarations control.AssignedAtEntry[control.Entry])
                | Error pending -> failwithf "Stateless code must remain definitely available across suspension: %A" pending
            | _ -> ()
        let callbackImplementation = Environments.tryImplementation graph formation.Children[1] |> Option.get
        let code = graph.Nodes[callbackImplementation]
        let unprepared = { code with Metadata = code.Metadata.Add(ClosureMetadata.RequiresClosurePair, MetadataValue.Bool true) }
        let changed = { graph with Nodes = graph.Nodes.Add(callbackImplementation, unprepared) }
        Assert.DoesNotContain(code.Parent.Value, Environments.implementationBindings changed)
        let writes = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && (match node.Kind with SemanticKind.Set _ -> true | _ -> false)) |> Seq.toList
        let write = Assert.Single writes
        Assert.Equal(write.Id, formation.Children.Head)
        // This graph contract preserves one shared source computation. Its
        // body is demanded according to ordinary call-by-need; retaining its
        // capture is not permission to execute the effect at formation.
        let main = EnvironmentFixture.binding "main" graph
        let mainLambda = Assert.Single main.Children
        let rec contains seen id =
            if Set.contains id seen then false
            elif id = write.Id then true
            else
                match graph.Nodes[id].Kind with
                | SemanticKind.Lambda _ | SemanticKind.SeqExpr _ | SemanticKind.LazyExpr _ -> false
                | _ -> graph.Nodes[id].Children |> List.exists (contains (Set.add id seen))
        for node in graph.Nodes.Values do
            match node.Kind with
            | SemanticKind.Lambda(_, body, _, _, _) when node.IsReachable ->
                Assert.Equal(node.Id = mainLambda, contains Set.empty body)
            | _ -> ()

    [<Fact>]
    member _.``Stored sequence operation reads the retained callable environment rather than replaying its callback`` () =
        let graph = EnvironmentFixture.check """
[<EntryPoint>]
let main _ =
    let offset = 7
    let callback = fun value -> value + offset
    let stored = Seq.map callback
    let mapped = stored (seq { yield 2; yield 3 })
    for value in mapped do ignore value
    0
"""
        let callback = EnvironmentFixture.binding "callback" graph
        let stored = EnvironmentFixture.binding "stored" graph
        let original = Environments.tryKnown graph callback.Id |> Option.defaultWith (fun () -> failwith "Callback has no retained environment")
        let residual = Environments.tryKnown graph stored.Id |> Option.defaultWith (fun () -> failwith "Stored operation has no retained environment")
        Assert.NotEqual(original.EnvironmentOwner, residual.EnvironmentOwner)
        let held = Environments.capturedInitializers graph residual.EnvironmentOwner |> Option.defaultWith (fun () -> failwith "Missing formation incidence")
        let slot, _, mutableCell = held |> List.filter (fun (_, value, _) -> Environments.tryKnown graph value = Some original) |> Assert.Single
        Assert.False mutableCell
        let reads = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && (match node.Kind with SemanticKind.EnvironmentRead(_, source) -> source = slot | _ -> false)) |> Seq.toList
        Assert.NotEmpty reads
        for read in reads do Assert.Equal(Some original, Environments.tryKnown graph read.Id)
        let environment = match graph.Nodes[residual.EnvironmentOwner].Kind with SemanticKind.ClosureValue(_, environment) -> environment | _ -> failwith "No closure value"
        let missingEdges = graph.Edges |> List.filter (fun edge ->
            not (edge.Target = environment && edge.Role = EdgeRole.EnvironmentCapture false))
        let missing = { graph with Edges = missingEdges }
        Assert.Equal(None, Environments.capturedInitializers missing residual.EnvironmentOwner)
        for read in reads do Assert.Equal(None, Environments.tryKnown missing read.Id)

    [<Fact>]
    member _.``Stored consumer captures its callback value while callback writes retain one original mutable cell`` () =
        let graph = EnvironmentFixture.check """
[<EntryPoint>]
let main _ =
    let mutable total = 0
    let action = fun value -> total <- value
    let stored = Seq.iter action
    stored (seq { yield 2 })
    total
"""
        let total = EnvironmentFixture.binding "total" graph
        let action = EnvironmentFixture.binding "action" graph
        let stored = EnvironmentFixture.binding "stored" graph
        let actionOwner = Environments.tryKnown graph action.Id |> Option.defaultWith (fun () -> failwith "Missing action environment")
        let residual = Environments.tryKnown graph stored.Id |> Option.defaultWith (fun () -> failwith "Missing consumer environment")
        Assert.Contains(Environments.captures graph actionOwner.EnvironmentOwner, fun capture -> capture.SourceNodeId = Some total.Id && capture.IsMutable)
        Assert.DoesNotContain(Environments.captures graph residual.EnvironmentOwner, fun capture -> capture.SourceNodeId = Some total.Id)
        Assert.Contains(Environments.capturedInitializers graph residual.EnvironmentOwner |> Option.get, fun (_, value, mutableCell) ->
            not mutableCell && Environments.tryKnown graph value = Some actionOwner)
        let writes = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && (match node.Kind with SemanticKind.EnvironmentWrite(_, slot, _) -> slot = total.Id | _ -> false)) |> Seq.toList
        Assert.Single writes |> ignore

    [<Fact>]
    member _.``Returned callback formation forwards its enclosing environment cell by identity`` () =
        let graph = EnvironmentFixture.check """
[<EntryPoint>]
let main _ =
    let mutable effects = 0
    let make = fun (offset: int) -> fun value -> effects <- value; value + offset
    let callback = make 7
    let mapped = Seq.map callback (seq { yield 2 })
    for value in mapped do ignore value
    0
"""
        let effects = EnvironmentFixture.binding "effects" graph
        let make = EnvironmentFixture.binding "make" graph
        let callback = EnvironmentFixture.binding "callback" graph
        let parent = Environments.tryKnown graph make.Id |> Option.defaultWith (fun () -> failwith "Missing factory environment")
        let child = Environments.tryKnown graph callback.Id |> Option.defaultWith (fun () -> failwith "Missing returned environment")
        let slot, initializer, mutableCell = Environments.capturedInitializers graph child.EnvironmentOwner |> Option.get
                                            |> List.filter (fun (slot, _, _) -> slot = effects.Id) |> Assert.Single
        Assert.True mutableCell
        Assert.Equal(effects.Id, slot)
        match graph.Nodes[initializer].Kind with
        | SemanticKind.EnvironmentBorrow(environment, source) ->
            Assert.Equal(effects.Id, source)
            Assert.Equal(Some parent.EnvironmentOwner, Environments.tryEnvironmentOwner graph environment)
        | kind -> failwithf "Returned closure did not retain the actual outer cell: %A" kind
        let environment = match graph.Nodes[child.EnvironmentOwner].Kind with SemanticKind.ClosureValue(_, environment) -> environment | _ -> failwith "No returned closure"
        Assert.Contains(initializer, graph.Nodes[environment].Children)

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
    member _.``Complete higher order invocation borrows the actual environment across all callable alternatives`` () =
        let graph = EnvironmentFixture.check """
let twice (f: int -> int) (value: int) = f (f value)
[<EntryPoint>]
let main _ =
    let offset = 7
    let addOffset = fun (value: int) -> value + offset
    let direct = addOffset 1
    let captured = twice addOffset direct
    let plain = twice (fun (value: int) -> value * 2) 3
    captured + plain
"""
        let owner = EnvironmentFixture.callable graph
        let environment = match owner.Kind with SemanticKind.ClosureValue(_, environment) -> environment | _ -> failwith "Missing environment"
        let origins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
        let calls = origins.Calls |> Map.toList |> List.filter (fun (_, call) -> call.Targets.Length = 2)
        Assert.Equal(2, calls.Length)
        let reading = Residence.analyzeEnvironments graph
        Assert.Empty reading.Unresolved
        Assert.Equal(Some EscapeKind.StackScoped, reading.Sites.TryFind environment)
        for call, targets in calls do
            Assert.True targets.Complete
            let evidence = reading.Evidence |> List.filter (fun edge ->
                edge.Role = EdgeRole.CallableInvocationBorrow && edge.Target = call) |> Assert.Single
            Assert.Contains(environment, evidence.Sources)
            for target in targets.Targets do
                Assert.Contains(target.Lambda, evidence.Sources)
                Assert.Contains(target.Body, evidence.Sources)
                for _, _, formal in target.Parameters do Assert.Contains(formal, evidence.Sources)
                for actual in target.Arguments do Assert.Contains(actual, evidence.Sources)
        // A complete invocation cannot be inferred from the other known
        // alternative after one input becomes opaque.
        let plain = EnvironmentFixture.binding "plain" graph
        let plainCall = graph.Nodes[Assert.Single plain.Children]
        let actual = match plainCall.Kind with SemanticKind.Application(_, argument :: _) -> argument | kind -> failwithf "Missing plain actual: %A" kind
        let opaque = { graph.Nodes[actual] with Kind = SemanticKind.VarRef("opaque", None); Children = [] }
        let changed = { graph with Nodes = graph.Nodes.Add(actual, opaque); Edges = graph.Edges |> List.filter (fun edge -> edge.Target <> actual) }
        let refused = Residence.analyzeEnvironments changed
        Assert.False(refused.Sites.ContainsKey environment)
        Assert.Contains(refused.Unresolved, fun pending ->
            pending.Site = environment && (calls |> List.exists (fun (call, _) -> pending.Reason = Residence.ResidualReason.UnsupportedConsumer call)))
        // Removing an actual makes this occurrence a retained partial value;
        // it must lose the consumption proof even though all code is known.
        let call, _ = List.head calls
        let node = graph.Nodes[call]
        let callee = match node.Kind with SemanticKind.Application(callee, _) -> callee | _ -> failwith "Missing invocation"
        let partial = { node with Kind = SemanticKind.Application(callee, []); Children = [callee] }
        let changed = { graph with Nodes = graph.Nodes.Add(call, partial) }
        let refused = Residence.analyzeEnvironments changed
        Assert.False(refused.Sites.ContainsKey environment)
        Assert.Contains(refused.Unresolved, fun pending -> pending.Site = environment && pending.Reason = Residence.ResidualReason.UnsupportedConsumer call)

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
        Assert.Equal(relation.Target, first)
        Assert.Equal(destination, second)
        Assert.Equal(Some source.Id, Environments.tryEnvironmentOwner graph first)
        Assert.Equal(None, Environments.tryEnvironmentOwner graph second)
        Assert.Single(Environments.implementationBindings graph) |> ignore
        let call = prepared.FactoryCalls.Keys |> Assert.Single
        let arguments = match graph.Nodes[call].Kind with SemanticKind.Application(_, arguments) -> arguments | _ -> failwith "No prepared factory call"
        Assert.Equal(Some(0, arguments[0]), (Environments.callEnvironments graph).TryFind call)
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

    [<Fact>]
    member _.``Captured source references retain exact occurrence authority and retract malformed projections`` () =
        let graph = EnvironmentFixture.check EnvironmentFixture.ordinary
        let rows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.CaptureReferenceOrigin)
        Assert.NotEmpty rows
        let read = Environments.tryCapturedSourceReference graph
        for row in rows do Assert.Equal(Some row.Sources[1], read row.Target)
        let row = rows.Head
        let source = graph.Nodes[row.Target]
        let environment, slot =
            match source.Kind with
            | SemanticKind.EnvironmentRead(environment, slot) -> environment, slot
            | kind -> failwithf "Source reference was not materialized: %A" kind
        let without = graph.Edges |> List.filter (fun edge -> not (edge.Target = row.Target && edge.Role = EdgeRole.CaptureReferenceOrigin))
        let withoutCapture =
            graph.Edges |> List.filter (fun edge ->
                match edge.Role, edge.Sources with
                | EdgeRole.EnvironmentCapture _, [owner; declaration; _] -> owner <> row.Sources.Head || declaration <> slot
                | _ -> true)
        let environmentNode = graph.Nodes[environment]
        let malformed =
            [ "missing source occurrence", { graph with Edges = without }
              "duplicate source occurrence", { graph with Edges = row :: graph.Edges }
              "wrong source owner", { graph with Edges = { row with Sources = [slot; slot] } :: without }
              "missing actual child", { graph with Nodes = graph.Nodes.Add(source.Id, { source with Children = [] }) }
              "changed source type", { graph with Nodes = graph.Nodes.Add(source.Id, { source with Type = Types.unitType }) }
              "missing captured slot authority", { graph with Edges = withoutCapture }
              "unrelated environment reference", { graph with Nodes = graph.Nodes.Add(environment, { environmentNode with Kind = SemanticKind.VarRef("unrelated", Some slot) }) } ]
        for name, changed in malformed do
            Assert.True((Environments.tryCapturedSourceReference changed row.Target).IsNone, "Source reference did not retract: " + name)
        // Navigation needs exact value identity, not the physical ABI marker.
        // Complete actuals still identify the same environment when that
        // redundant formal-to-owner relation is absent.
        let withoutFormal = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.EnvironmentFormal) }
        Assert.Equal(Some row.Sources.Head, Environments.tryEnvironmentOwner withoutFormal environment)
        Assert.Equal(Some slot, Environments.tryCapturedSourceReference withoutFormal row.Target)
        // Matching range, slot and environment do not invent source identity
        // for a new compiler-generated read with no occurrence relation.
        let generated = { source with Id = NodeId.fresh(); Kind = SemanticKind.EnvironmentRead(environment, slot) }
        let additional = { graph with Nodes = graph.Nodes.Add(generated.Id, generated) }
        Assert.Equal(None, Environments.tryCapturedSourceReference additional generated.Id)
        Assert.Equal(Some slot, read row.Target)
