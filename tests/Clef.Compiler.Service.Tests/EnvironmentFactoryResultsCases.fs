namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module EnvironmentResults = Clef.Compiler.Nanopass.EnvironmentFactoryResults
module EnvironmentValues = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments
module EnvironmentIncidence = Clef.Compiler.Baker.Ingredients.Closures

module private EnvironmentFactories =
    let check source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        Assert.True result.Graph.Platform.IsNone
        result.Graph

    let bareSource = """
[<EntryPoint>]
let main _ =
    let offset = 10
    let mutable formations = 0
    let callback = fun (value: int) -> value + offset
    let bareMap: (int -> int) -> seq<int> -> seq<int> = Seq.map
    let first = bareMap (formations <- formations + 1; callback)
    let second = bareMap (formations <- formations + 2; callback)
    let firstValues = first (seq { yield 3 })
    let secondValues = second (seq { yield 4 })
    for value in firstValues do ignore value
    for value in secondValues do ignore value
    formations
"""

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && (match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false))
        |> Assert.Single

    let implementation name graph =
        EnvironmentValues.tryImplementation graph (binding name graph).Id
        |> Option.defaultWith (fun () -> failwith "Factory lost its actual implementation")

    let prepare (graph: SemanticGraph) = EnvironmentResults.prepare graph graph.Codata.Value.Curry

    let relations role (graph: SemanticGraph) = graph.Edges |> List.filter (fun edge -> edge.Role = role)

    let sourceSignature (node: SemanticNode) =
        match node.Metadata.TryFind ClosureMetadata.SourceSignature with
        | Some (MetadataValue.Type ty) -> ty
        | _ -> node.Type

    let calls implementation (graph: SemanticGraph) =
        let resolved = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
        resolved.Calls |> Map.toList |> List.choose (fun (id, call) ->
            match call.Targets, graph.Nodes[id].Kind with
            | [target], SemanticKind.Application(callee, arguments) when call.Complete && not call.Unknown && target.Lambda = implementation ->
                Some(graph.Nodes[id], callee, arguments)
            | _ -> None)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "EnvironmentFactoryResults")>]
type EnvironmentFactoryResultsCases() =
    [<Fact>]
    member _.``Returned string captures retain actual declared backing and distinct caller storage`` () =
        let source = """
module StringFactories
let make (prefix: string) = fun (value: string) -> if prefix = value then 1 else 0
let first = make "Hello"
let second = make "World"
[<EntryPoint>]
let main _ =
    ignore (first "Hello")
    ignore (second "World")
    0
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let reading = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence.analyzeEnvironments graph
        Assert.Empty reading.Unresolved
        let calls = EnvironmentFactories.relations EdgeRole.EnvironmentResultCall graph
        Assert.Equal(2, calls.Length)
        Assert.Equal(2, calls |> List.map (fun row -> row.Sources[3]) |> Set.ofList |> Set.count)
        let pool = graph.StaticStringPool |> Option.get
        for call in calls do
            let allocation = call.Sources[3]
            Assert.True(reading.Sites.ContainsKey allocation)
            let evidence = reading.Evidence |> List.filter (fun row ->
                row.Role = EdgeRole.EnvironmentResidence && List.contains allocation row.Sources)
            Assert.Contains(evidence, fun row -> List.contains pool.DeclarationNode row.Sources)
            Assert.Contains(evidence, fun row -> List.contains call.Target row.Sources)
        // Storage declarations and actual pooled bytes are independent premises.
        // Keeping stale codata/edges must not preserve residence after either changes.
        for changed in [
            { graph with StaticStringPool = None }
            { graph with StaticStringPool = Some { pool with Bytes = 255uy :: List.tail pool.Bytes } }
            { graph with Nodes = graph.Nodes.Remove pool.DeclarationNode }
        ] do
            let retracted = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence.analyzeEnvironments changed
            for call in calls do Assert.False(retracted.Sites.ContainsKey call.Sources[3])
            Assert.NotEmpty retracted.Unresolved
        Assert.Empty((Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence.analyzeEnvironments graph).Unresolved)

    [<Fact>]
    member _.``Direct immutable string capture requires backing rather than descriptor layout alone`` () =
        let source = """
module StringLocal
[<EntryPoint>]
let main _ =
    let prefix = "retained"
    let callback = fun (value: string) -> if prefix = value then 1 else 0
    callback "retained"
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let reading = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence.analyzeEnvironments graph
        Assert.Empty reading.Unresolved
        let owner = EnvironmentValues.tryKnown graph (EnvironmentFactories.binding "callback" graph).Id |> Option.get
        let environment =
            match graph.Nodes[owner.EnvironmentOwner].Kind with
            | SemanticKind.ClosureValue(_, environment) -> environment
            | kind -> failwithf "No canonical string capture environment: %A" kind
        Assert.True(reading.Sites.ContainsKey environment)
        Assert.Contains(reading.Evidence, fun row ->
            row.Role = EdgeRole.EnvironmentResidence && row.Target = owner.EnvironmentOwner &&
            List.contains graph.StaticStringPool.Value.DeclarationNode row.Sources)
        let prefix = EnvironmentFactories.binding "prefix" graph
        let mutablePrefix =
            match prefix.Kind with
            | SemanticKind.Binding(name, _, recursive, exported) ->
                { prefix with Kind = SemanticKind.Binding(name, true, recursive, exported) }
            | _ -> failwith "No immutable prefix binding"
        let changed = { graph with Nodes = graph.Nodes.Add(prefix.Id, mutablePrefix) }
        let retracted = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence.analyzeEnvironments changed
        Assert.False(retracted.Sites.ContainsKey environment)
        Assert.NotEmpty retracted.Unresolved

    [<Fact>]
    member _.``String factory residence keeps exact aliases formals and actual call premises`` () =
        let source = """
module StringAliasFactory
let make (prefix: string) =
    let held = (prefix: string)
    fun (value: string) -> if held = value then 1 else 0
let callback = make "held"
[<EntryPoint>]
let main _ = callback "held"
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let read graph = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence.analyzeEnvironments graph
        let baseline = read graph
        Assert.Empty baseline.Unresolved
        let call = EnvironmentFactories.relations EdgeRole.EnvironmentResultCall graph |> Assert.Single
        let implementation, destinationFormal, allocation = call.Sources[0], call.Sources[2], call.Sources[3]
        let held = EnvironmentFactories.binding "held" graph
        let annotation = graph.Nodes[Assert.Single held.Children]
        let reference =
            match annotation.Kind with
            | SemanticKind.TypeAnnotation(value, _) -> graph.Nodes[value]
            | kind -> failwithf "Expected the retained source annotation, found %A" kind
        let formal =
            match reference.Kind with
            | SemanticKind.VarRef(_, Some formal) -> formal
            | kind -> failwithf "Expected the retained formal reference, found %A" kind
        let evidence = baseline.Evidence |> List.filter (fun row ->
            row.Role = EdgeRole.EnvironmentResidence && List.contains allocation row.Sources)
        for participant in [implementation; destinationFormal; call.Target; held.Id; annotation.Id; reference.Id; formal] do
            Assert.Contains(evidence, fun row -> List.contains participant row.Sources)
        let malformedAnnotation = { annotation with Kind = SemanticKind.TypeAnnotation(reference.Id, Types.intType) }
        let malformedReference = { reference with Type = Types.intType }
        let malformedCall = { graph.Nodes[call.Target] with Children = [] }
        let contradictoryDefinition =
            { Class = EdgeClass.Reference; Role = EdgeRole.Definition; Ordinal = 0
              Sources = [held.Id]; Target = reference.Id }
        let inconsistentDefinition = { graph with Edges = contradictoryDefinition :: graph.Edges }
        for changed in [
            { graph with Nodes = graph.Nodes.Add(annotation.Id, malformedAnnotation) }
            { graph with Nodes = graph.Nodes.Add(reference.Id, malformedReference) }
            { graph with Nodes = graph.Nodes.Add(call.Target, malformedCall) }
            inconsistentDefinition
        ] do
            let retracted = read changed
            Assert.False(retracted.Sites.ContainsKey allocation)
            Assert.NotEmpty retracted.Unresolved
        Assert.True((read graph).Sites.ContainsKey allocation)

    [<Fact>]
    member _.``Nested string capture reads the actual scoped environment formal`` () =
        let source = """
module StringNestedCapture
[<EntryPoint>]
let main _ =
    let prefix = "held"
    let outer = fun (expected: string) ->
        let callback = fun (value: string) -> if prefix = value then 1 else 0
        callback expected
    outer "held"
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let read graph = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence.analyzeEnvironments graph
        let baseline = read graph
        Assert.Empty baseline.Unresolved
        let constructor, access =
            graph.Nodes.Values |> Seq.collect (fun node ->
                match node.Kind with
                | SemanticKind.EnvironmentCreate(_, initializers) ->
                    initializers |> List.choose (fun (_, value) ->
                        match graph.Nodes[value].Kind with
                        | SemanticKind.EnvironmentRead _ -> Some(node, graph.Nodes[value])
                        | _ -> None)
                | _ -> []) |> Assert.Single
        let environment, slot =
            match access.Kind with
            | SemanticKind.EnvironmentRead(environment, slot) -> environment, slot
            | _ -> failwith "Expected a nested immutable capture read"
        let formal =
            match graph.Nodes[environment].Kind with
            | SemanticKind.VarRef(_, Some formal) -> formal
            | kind -> failwithf "Expected the actual environment formal reference, found %A" kind
        let relation = graph.Edges |> List.filter (fun row ->
            row.Role = EdgeRole.EnvironmentFormal && row.Target = formal) |> Assert.Single
        let schemaFormation =
            match graph.Nodes[relation.Sources[0]].Kind with
            | SemanticKind.ClosureValue(_, formation) -> formation
            | _ -> failwith "Expected the actual closure formation"
        Assert.True(baseline.Sites.ContainsKey constructor.Id)
        for participant in environment :: formal :: slot :: schemaFormation :: relation.Sources do
            Assert.Contains(baseline.Evidence, fun row ->
                row.Role = EdgeRole.EnvironmentResidence && List.contains constructor.Id row.Sources &&
                List.contains participant row.Sources)
        let wrongInstance =
            { access with Kind = SemanticKind.EnvironmentRead(schemaFormation, slot); Children = [schemaFormation] }
        let missingChildren = { access with Children = [] }
        let retainedFormals =
            graph.Edges |> List.filter (fun row ->
                row.Role <> EdgeRole.EnvironmentFormal || row.Target <> formal)
        let malformedRelation = { graph with Edges = retainedFormals }
        for changed in [
            { graph with Nodes = graph.Nodes.Add(access.Id, wrongInstance) }
            { graph with Nodes = graph.Nodes.Add(access.Id, missingChildren) }
            malformedRelation
        ] do
            let retracted = read changed
            Assert.False(retracted.Sites.ContainsKey constructor.Id)
            Assert.NotEmpty retracted.Unresolved
        Assert.True((read graph).Sites.ContainsKey constructor.Id)

    [<Fact>]
    member _.``Program callable instances retain distinct factory destinations and shared aliases`` () =
        let source = """
module ProgramCallableInstances
let make (prefix: string) = fun (value: string) -> if prefix = value then 1 else 0
let first = make "first"
let second = make "second"
let alias = first
let direct =
    let prefix = "direct"
    fun (value: string) -> if prefix = value then 1 else 0
[<EntryPoint>]
let main _ = first "first" + second "second" + alias "first" + direct "direct"
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let read graph name =
            Clef.Compiler.Nanopass.ClosureEnvironmentSettlement.programInstance graph (EnvironmentFactories.binding name graph).Id
        let first, second, alias, direct = read graph "first" |> Option.get, read graph "second" |> Option.get, read graph "alias" |> Option.get, read graph "direct" |> Option.get
        Assert.Equal(first.Carrier.Implementation, second.Carrier.Implementation)
        Assert.NotEqual(first.Allocation, second.Allocation)
        Assert.Equal(first.Allocation, alias.Allocation)
        Assert.NotEqual(first.Allocation, direct.Allocation)
        for value in [first; second; alias; direct] do
            let allocation = value.Allocation |> Option.get
            Assert.Equal(Some EscapeKind.StaticLifetime, graph.Codata.Value.Escapes.TryFind allocation)
            Assert.Contains(allocation, value.Participants)
            let authority = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.tryValueAuthority graph value.Carrier.Occurrence |> Option.get
            for participant in authority.Evidence.Sources do Assert.Contains(participant, value.Participants)

    [<Fact>]
    member _.``Program callable authority retracts stale startup destination layout and capacity facts`` () =
        let source = """
module ProgramCallableRetraction
let make (prefix: string) = fun (value: string) -> if prefix = value then 1 else 0
let first = make "first"
let second = make "second"
[<EntryPoint>]
let main _ = first "first" + second "second"
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let first = EnvironmentFactories.binding "first" graph
        let read graph = Clef.Compiler.Nanopass.ClosureEnvironmentSettlement.programInstance graph first.Id
        let contract = read graph |> Option.get
        let allocation = contract.Allocation |> Option.get
        let calls = EnvironmentFactories.relations EdgeRole.EnvironmentResultCall graph
        let call = calls |> List.filter (fun row -> row.Sources[3] = allocation) |> Assert.Single
        let other = calls |> List.filter (fun row -> row.Sources[3] <> allocation) |> Assert.Single
        let changedCall =
            let node = graph.Nodes[call.Target]
            match node.Kind with
            | SemanticKind.Application(callee, arguments) ->
                let arguments = arguments |> List.map (fun value -> if value = call.Sources[4] then other.Sources[4] else value)
                { node with Kind = SemanticKind.Application(callee, arguments); Children = callee :: arguments }
            | _ -> failwith "Expected exact factory call"
        let layout = graph.Codata.Value.EnvironmentLayouts[contract.Carrier.Environment.Value.Owner]
        let changedLayouts = graph.Codata.Value.EnvironmentLayouts.Add(layout.Owner, { layout with Bytes = layout.Bytes + 1 })
        let changedFacts = { graph.Codata.Value with EnvironmentLayouts = changedLayouts }
        let authority = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.tryValueAuthority graph first.Id |> Option.get
        let capacity =
            match graph.Nodes[authority.Space.Node].Kind with
            | SemanticKind.RecordExpr(fields, _) -> fields |> List.find (fst >> (=) "Capacity") |> snd
            | _ -> failwith "Expected actual space declaration"
        let capacityNode = graph.Nodes[capacity]
        let reducedCapacity =
            match capacityNode.Kind with
            | SemanticKind.Literal(NativeLiteral.Int(_, kind)) -> { capacityNode with Kind = SemanticKind.Literal(NativeLiteral.Int(1L, kind)) }
            | _ -> failwith "Expected source capacity literal"
        Assert.Contains(capacity, contract.Participants)
        let withoutRole role target =
            let edges = graph.Edges |> List.filter (fun row -> row.Role <> role || not (target row.Target))
            { graph with Edges = edges }
        let changed = [
            withoutRole EdgeRole.ProgramInitialization (fun _ -> true)
            withoutRole EdgeRole.ProgramValue ((=) first.Id)
            withoutRole EdgeRole.EnvironmentResultCall ((=) call.Target)
            { graph with Nodes = graph.Nodes.Add(call.Target, changedCall) }
            { graph with Codata = lazy changedFacts }
            { graph with Nodes = graph.Nodes.Remove layout.Obligations.Head }
            { graph with Nodes = graph.Nodes.Add(capacity, reducedCapacity) }
        ]
        for stale in changed do Assert.True((read stale).IsNone)
        Assert.Equal(Some allocation, (read graph |> Option.get).Allocation)

    [<Fact>]
    member _.``Writable inventory accounts exact instances once and keeps the held scalar type`` () =
        let source = """
module ProgramInventory
[<Measure>] type m
let make (prefix: string) = fun (value: string) -> if prefix = value then 1 else 0
let first = make "first"
let second = make "second"
let alias = first
let mutable distance = 3<m>
[<EntryPoint>]
let main _ =
    if distance = 3<m> then first "first" + second "second" + alias "first" else 1
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let reading = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorage.read graph |> Option.get
        Assert.Empty reading.Unresolved
        Assert.Equal(3, reading.Entries.Count)
        let sourceBinding = EnvironmentFactories.binding "distance" graph
        let scalar = reading.Entries[ProgramStorageIdentity.BindingSlot sourceBinding.Id]
        Assert.Equal(Clef.Compiler.NativeTypedTree.UnionFind.applySubst sourceBinding.Type, scalar.SourceType)
        match scalar.Shape with
        | ProgramStorageShape.Scalar(SettledSlot.Integer(_, Some _)) -> ()
        | shape -> failwithf "Expected the source-selected measured scalar representation, got %A" shape
        let first = EnvironmentFactories.binding "first" graph
        let second = EnvironmentFactories.binding "second" graph
        let alias = EnvironmentFactories.binding "alias" graph
        let instance (binding: SemanticNode) = Clef.Compiler.Nanopass.ClosureEnvironmentSettlement.programInstance graph binding.Id |> Option.get
        let firstInstance, secondInstance, aliasInstance = instance first, instance second, instance alias
        Assert.Equal(firstInstance.Allocation, aliasInstance.Allocation)
        Assert.NotEqual(firstInstance.Allocation, secondInstance.Allocation)
        for value in [firstInstance; secondInstance] do
            let entry = reading.Entries[ProgramStorageIdentity.Allocation value.Allocation.Value]
            Assert.True(Set.isSubset value.Participants entry.Participants)
        let reservation = reading.Reservations.Values |> Assert.Single
        Assert.Equal(3, reservation.Requests.Length)
        Assert.Equal(reading.Entries.Values |> Seq.sumBy (fun value -> int64 value.Bytes), reservation.PayloadSize)
        // Source inventory deliberately contains no target section or guessed
        // placement offset. A backend must separately commit actual storage.
        Assert.Equal("data", reservation.Space.Kind)

    [<Fact>]
    member _.``Writable inventory retracts stale premises and rejects aggregate overflow`` () =
        let source = """
module ProgramInventoryRetraction
let make (prefix: string) = fun (value: string) -> if prefix = value then 1 else 0
let first = make "first"
let second = make "second"
[<EntryPoint>]
let main _ = first "first" + second "second"
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let read = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorage.read
        let inventory = read graph |> Option.get
        Assert.Empty inventory.Unresolved
        let first = EnvironmentFactories.binding "first" graph
        let authority = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.tryValueAuthority graph first.Id |> Option.get
        let capacity =
            match graph.Nodes[authority.Space.Node].Kind with
            | SemanticKind.RecordExpr(fields, _) -> fields |> List.find (fst >> (=) "Capacity") |> snd
            | _ -> failwith "Expected declared mutable-space record"
        let largest = inventory.Entries.Values |> Seq.map _.Bytes |> Seq.max
        let total = inventory.Entries.Values |> Seq.sumBy _.Bytes
        Assert.True(largest > 0 && total > largest, "This fixture requires multiple positive reservations.")
        // Each request fits independently, but their combined payload cannot.
        let insufficient = total - 1
        Assert.True(largest <= insufficient && insufficient < total)
        let capacityNode = graph.Nodes[capacity]
        let smaller =
            match capacityNode.Kind with
            | SemanticKind.Literal(NativeLiteral.Int(_, kind)) ->
                { capacityNode with Kind = SemanticKind.Literal(NativeLiteral.Int(int64 insufficient, kind)) }
            | _ -> failwith "Expected declared capacity literal"
        let changed = { graph with Nodes = graph.Nodes.Add(capacity, smaller) }
        Assert.True((read changed).IsNone)
        let pending = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorage.settle changed
        // A raw declaration mutation invalidates each retained per-allocation
        // reservation proof before the aggregate reservation can be attempted.
        Assert.Empty pending.Entries
        Assert.Equal(2, pending.Unresolved.Count)
        Assert.Empty pending.Reservations
        Assert.Equal<Set<ProgramStorageIdentity>>(inventory.Entries |> Map.keys |> Set.ofSeq, pending.Unresolved |> Map.keys |> Set.ofSeq)
        Assert.All(pending.Unresolved.Values, fun reason -> Assert.Contains("not jointly established", reason))
        // Fresh source compilation must establish current individual proofs,
        // then refuse the combined inventory. No stale codata is restamped.
        let overfullResult = LazyResidenceFixture.checkProgramWithCapacity insufficient (Some source)
        let errors = overfullResult.Diagnostics |> List.filter (fun value -> value.Severity = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.NativeDiagnosticSeverity.Error)
        Assert.Equal(2, errors.Length)
        Assert.All(errors, fun error ->
            Assert.Equal("CCS8403", error.Code)
            Assert.Contains("capacity-exceeded", error.Message)
            Assert.Equal("lazy-program.clef", error.Range.File))
        Assert.Equal<Set<int>>(Set.ofList [4; 5], errors |> List.map (fun error -> error.Range.Start.Line) |> Set.ofList)
        let overfullGraph = overfullResult.Graph
        let overfull = read overfullGraph |> Option.get
        Assert.Equal(2, overfull.Entries.Count)
        Assert.Equal(total, overfull.Entries.Values |> Seq.sumBy _.Bytes)
        Assert.All(overfull.Entries.Values, fun entry ->
            Assert.Equal(int64 insufficient, entry.Space.Capacity)
            Assert.True(int64 entry.Bytes <= entry.Space.Capacity))
        Assert.Equal(2, overfull.Unresolved.Count)
        for identity in overfull.Unresolved.Keys do
            let site = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorage.sourceOf identity
            Assert.Single(errors |> List.filter (fun error -> List.contains site error.RelatedNodes)) |> ignore
        Assert.Empty overfull.Reservations
        Assert.All(overfull.Unresolved.Values, fun reason -> Assert.Contains("capacity-exceeded", reason))
        let fitting = LazyResidenceFixture.programWithCapacity total (Some source) |> read |> Option.get
        Assert.Equal(2, fitting.Entries.Count)
        Assert.Empty fitting.Unresolved
        Assert.Equal(int64 total, (Assert.Single fitting.Reservations.Values).PayloadSize)
        let withoutStartup =
            let edges = graph.Edges |> List.filter (fun row -> row.Role <> EdgeRole.ProgramInitialization)
            { graph with Edges = edges }
        Assert.True((read withoutStartup).IsNone)
        let withoutCall =
            let row = EnvironmentFactories.relations EdgeRole.EnvironmentResultCall graph |> List.head
            let edges = graph.Edges |> List.filter (fun edge -> edge.Role <> row.Role || edge.Target <> row.Target)
            { graph with Edges = edges }
        Assert.True((read withoutCall).IsNone)
        Assert.Equal(inventory, read graph |> Option.get)

    [<Theory>]
    [<InlineData(true, false)>]
    [<InlineData(false, true)>]
    [<InlineData(true, true)>]
    member _.``Explicit eager factory boundaries retain their marker identity and caller residence`` (eagerResult: bool, eagerCallee: bool) =
        let result = if eagerResult then "eager (fun value -> value + seed)" else "fun value -> value + seed"
        let callee = if eagerCallee then "(eager make)" else "make"
        let template = """
let make (seed: int) = __RESULT__
[<EntryPoint>]
let main _ =
    let first = __CALLEE__ (eager 7)
    let second = __CALLEE__ 8
    ignore (first 1)
    ignore (second 2)
    0
"""
        let source = template.Replace("__RESULT__", result).Replace("__CALLEE__", callee)
        let original = EnvironmentFactories.check source
        let implementation = EnvironmentFactories.implementation "make" original
        let originalCalls = EnvironmentFactories.calls implementation original
        Assert.Equal(2, originalCalls.Length)
        let markers = original.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && match node.Kind with SemanticKind.EagerExpr _ -> true | _ -> false) |> Seq.toList
        Assert.NotEmpty markers
        let prepared, _ = EnvironmentFactories.prepare original
        let calls = EnvironmentFactories.relations EdgeRole.EnvironmentResultCall prepared
        Assert.Equal(2, calls.Length)
        Assert.Equal(2, calls |> List.map (fun row -> row.Sources[3]) |> List.distinct |> List.length)
        for marker in markers do
            Assert.Equal(marker.Kind, prepared.Nodes[marker.Id].Kind)
            Assert.Equal<NodeId list>(marker.Children, prepared.Nodes[marker.Id].Children)
        for call, callee, arguments in originalCalls do
            let invocation =
                match prepared.Nodes[call.Id].Kind with
                | SemanticKind.Sequential [_; actual] -> prepared.Nodes[actual]
                | kind -> failwithf "Expected destination-only factory prefix, got %A" kind
            match invocation.Kind with
            | SemanticKind.Application(actualCallee, _ :: actuals) ->
                Assert.Equal(callee, actualCallee)
                Assert.Equal<NodeId list>(arguments, actuals)
            | kind -> failwithf "Expected preserved factory invocation, got %A" kind
        let reading = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence.analyzeEnvironments prepared
        Assert.Empty reading.Unresolved
        for row in calls do Assert.True(reading.Sites.ContainsKey row.Sources[3])
        if eagerResult then
            let marker = markers |> List.find (fun marker ->
                match marker.Kind with
                | SemanticKind.EagerExpr value -> match original.Nodes[value].Kind with SemanticKind.ClosureValue _ -> true | _ -> false
                | _ -> false)
            for row in calls do
                Assert.Contains(reading.Evidence, fun proof ->
                    proof.Role = EdgeRole.EnvironmentResidence && List.contains row.Sources[3] proof.Sources && List.contains marker.Id proof.Sources)
            let malformed = { prepared with Nodes = prepared.Nodes.Add(marker.Id, { prepared.Nodes[marker.Id] with Children = [] }) }
            let retracted = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence.analyzeEnvironments malformed
            for row in calls do Assert.False(retracted.Sites.ContainsKey row.Sources[3])
            Assert.NotEmpty retracted.Unresolved
        if eagerCallee then
            let marker = markers |> List.find (fun marker ->
                originalCalls |> List.exists (fun (_, callee, _) -> callee = marker.Id))
            let malformed = { original with Nodes = original.Nodes.Add(marker.Id, { marker with Children = [] }) }
            let retracted, _ = EnvironmentFactories.prepare malformed
            Assert.Empty(EnvironmentFactories.relations EdgeRole.EnvironmentResultDestination retracted)

    [<Fact>]
    member _.``Bare map front gives each captured callback result distinct caller storage and exact formation incidence`` () =
        let original = EnvironmentFactories.check EnvironmentFactories.bareSource
        let implementation = EnvironmentFactories.implementation "bareMap" original
        let graph, curry = EnvironmentFactories.prepare original
        let destination = EnvironmentFactories.relations EdgeRole.EnvironmentResultDestination graph |> Assert.Single
        Assert.Equal(EdgeClass.Provenance, destination.Class)
        let owner, formal =
            match destination.Sources with
            | [actual; owner; formal] -> Assert.Equal(implementation, actual); owner, formal
            | participants -> failwithf "Incomplete result destination: %A" participants
        match graph.Nodes[owner].Kind, graph.Nodes[destination.Target].Kind with
        | SemanticKind.ClosureValue(_, environment), SemanticKind.EnvironmentCreate(actual, _) ->
            Assert.Equal(destination.Target, environment)
            Assert.Equal(owner, actual)
        | kinds -> failwithf "Destination lost the exact returned closure constructor: %A" kinds
        let calls = EnvironmentFactories.relations EdgeRole.EnvironmentResultCall graph
        Assert.Equal(2, calls.Length)
        let allocations = calls |> List.map (fun edge ->
            Assert.Equal(EdgeClass.Provenance, edge.Class)
            match edge.Sources, graph.Nodes[edge.Target].Kind with
            | [actual; constructor; resultFormal; allocation; supplied], SemanticKind.Application(_, arguments) ->
                Assert.Equal(implementation, actual)
                Assert.Equal(destination.Target, constructor)
                Assert.Equal(formal, resultFormal)
                Assert.Equal(supplied, arguments.Head)
                Assert.Equal<NodeId list>(arguments, curry.SaturatedCalls[edge.Target].AllArgNodes)
                match graph.Nodes[allocation].Kind, graph.Nodes[supplied].Kind with
                | SemanticKind.EnvironmentAllocate actualOwner, SemanticKind.VarRef(_, Some held) ->
                    Assert.Equal(owner, actualOwner)
                    Assert.Equal(allocation, Assert.Single graph.Nodes[held].Children)
                | kinds -> failwithf "Result storage lacks its actual allocation and value: %A" kinds
                allocation
            | evidence -> failwithf "Incomplete exact result call: %A" evidence)
        Assert.Equal(2, allocations |> Set.ofList |> Set.count)
        // Representation preparation does not assert a storage lifetime.
        Assert.DoesNotContain(graph.Edges, fun edge -> edge.Role = EdgeRole.EnvironmentResidence)

    [<Fact>]
    member _.``Environment factory preparation inserts only result storage and retains ordinary argument demand frontiers`` () =
        let original = EnvironmentFactories.check EnvironmentFactories.bareSource
        let implementation = EnvironmentFactories.implementation "bareMap" original
        let calls = EnvironmentFactories.calls implementation original
        Assert.Equal(2, calls.Length)
        let graph, _ = EnvironmentFactories.prepare original
        for call, callee, arguments in calls do
            let ordered =
                match graph.Nodes[call.Id].Kind with SemanticKind.Sequential values -> values | kind -> failwithf "Missing destination preparation: %A" kind
            Assert.Equal(2, ordered.Length)
            match graph.Nodes[ordered.Head].Kind, graph.Nodes[Assert.Single graph.Nodes[ordered.Head].Children].Kind with
            | SemanticKind.Binding(_, false, false, None), SemanticKind.EnvironmentAllocate _ -> ()
            | kinds -> failwithf "Preparation added something other than caller result storage: %A" kinds
            let actuals =
                match graph.Nodes[List.last ordered].Kind with SemanticKind.Application(_, supplied) -> supplied.Tail | kind -> failwithf "Missing invocation: %A" kind
            Assert.Equal<NodeId list>(arguments, actuals)
            for argument in arguments do
                let evaluations = graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && List.contains argument node.Children)
                Assert.Single evaluations |> ignore
            for id in [implementation; callee] do
                Assert.Equal(formatType (EnvironmentFactories.sourceSignature original.Nodes[id]),
                             formatType (EnvironmentFactories.sourceSignature graph.Nodes[id]))
                Assert.True(graph.Nodes[id].Metadata.ContainsKey ClosureMetadata.SourceSignature)
            Assert.Equal(call.Range, graph.Nodes[call.Id].Range)
        let writes graph = graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && (match node.Kind with SemanticKind.Set _ -> true | _ -> false)) |> Seq.map _.Id |> Set.ofSeq
        Assert.Equal<Set<NodeId>>(writes original, writes graph)

    [<Fact>]
    member _.``A stored factory alias preserves its formation and original callee while receiving distinct result storage`` () =
        let original = EnvironmentFactories.check """
let mutable formations = 0
[<EntryPoint>]
let main _ =
    let stored = (formations <- formations + 1; fun (offset: int) -> fun value -> value + offset)
    let first = stored 3
    let second = stored 4
    if first 5 = second 4 then formations else 1
"""
        let stored = EnvironmentFactories.binding "stored" original
        let formation = original.Nodes[Assert.Single stored.Children]
        match formation.Kind with
        | SemanticKind.Sequential values -> Assert.Equal(2, values.Length)
        | kind -> failwithf "Expected the original deferred formation: %A" kind
        let implementation = EnvironmentFactories.implementation "stored" original
        let calls = EnvironmentFactories.calls implementation original
        Assert.Equal(2, calls.Length)
        let graph, _ = EnvironmentFactories.prepare original
        let destinations = EnvironmentFactories.relations EdgeRole.EnvironmentResultCall graph
        Assert.Equal(2, destinations.Length)
        Assert.Equal(2, destinations |> List.map (fun row -> row.Sources[3]) |> Set.ofList |> Set.count)
        Assert.Equal<NodeId list>(stored.Children, graph.Nodes[stored.Id].Children)
        Assert.Equal<NodeId list>(formation.Children, graph.Nodes[formation.Id].Children)
        for call, callee, arguments in calls do
            let invocation =
                match graph.Nodes[call.Id].Kind with
                | SemanticKind.Sequential [storage; invocation] ->
                    match graph.Nodes[Assert.Single graph.Nodes[storage].Children].Kind with
                    | SemanticKind.EnvironmentAllocate _ -> ()
                    | kind -> failwithf "Unexpected preparation operand: %A" kind
                    graph.Nodes[invocation]
                | kind -> failwithf "Factory alias lost destination-only preparation: %A" kind
            match invocation.Kind with
            | SemanticKind.Application(actualCallee, actualArguments) ->
                Assert.Equal(callee, actualCallee)
                Assert.Equal<NodeId list>(arguments, actualArguments.Tail)
                match graph.Nodes[callee].Kind with
                | SemanticKind.VarRef(_, Some declaration) -> Assert.Equal(stored.Id, declaration)
                | kind -> failwithf "Alias demand identity changed: %A" kind
            | kind -> failwithf "Missing original invocation: %A" kind

    [<Fact>]
    member _.``A capturing factory keeps its own environment first and inserts result storage before source arguments`` () =
        let original = EnvironmentFactories.check """
[<EntryPoint>]
let main _ =
    let mutable effects = 0
    let mutable formations = 0
    let make = fun (offset: int) -> fun value -> effects <- value; value + offset
    let callback = make (formations <- 1; 7)
    let mapped = Seq.map callback (seq { yield 2 })
    for value in mapped do ignore value
    formations
"""
        let implementation = EnvironmentFactories.implementation "make" original
        let environment = EnvironmentFactories.relations EdgeRole.EnvironmentFormal original |> List.filter (fun edge -> List.tryLast edge.Sources = Some implementation) |> Assert.Single
        let call, _, originalArguments = EnvironmentFactories.calls implementation original |> Assert.Single
        let graph, _ = EnvironmentFactories.prepare original
        let destination = EnvironmentFactories.relations EdgeRole.EnvironmentResultDestination graph |> Assert.Single
        let resultFormal = List.last destination.Sources
        match graph.Nodes[implementation].Kind with
        | SemanticKind.Lambda((_, _, first) :: (_, _, second) :: _, _, [], _, _) ->
            Assert.Equal(environment.Target, first)
            Assert.Equal(resultFormal, second)
        | kind -> failwithf "Factory lost environment-first order: %A" kind
        let invocation = EnvironmentFactories.relations EdgeRole.EnvironmentResultCall graph |> Assert.Single
        let supplied =
            match graph.Nodes[invocation.Target].Kind with SemanticKind.Application(_, arguments) -> arguments | _ -> failwith "Missing prepared call"
        Assert.Equal(List.last invocation.Sources, supplied[1])
        let ordered = match graph.Nodes[call.Id].Kind with SemanticKind.Sequential values -> values | _ -> failwith "Missing frontier"
        Assert.Equal(2, ordered.Length)
        Assert.Equal<NodeId list>(originalArguments, supplied.Head :: List.skip 2 supplied)
        Assert.Equal(Some(0, supplied[0]), (EnvironmentValues.callEnvironments graph).TryFind invocation.Target)
        Assert.Equal(formatType (EnvironmentFactories.sourceSignature original.Nodes[implementation]),
                     formatType (EnvironmentFactories.sourceSignature graph.Nodes[implementation]))

    [<Fact>]
    member _.``An opaque extra use retracts all destination preparation for the otherwise closed factory`` () =
        let original = EnvironmentFactories.check EnvironmentFactories.bareSource
        let implementation = EnvironmentFactories.implementation "bareMap" original
        let _, callee, _ = EnvironmentFactories.calls implementation original |> List.head
        let consumer = original.Nodes.Values |> Seq.find (fun node -> node.IsReachable && (match node.Kind with SemanticKind.Literal _ -> true | _ -> false))
        let opaque = Hyperedge.edge1 EdgeClass.Reference EdgeRole.Symbol 0 callee consumer.Id
        let changed = { original with Edges = opaque :: original.Edges }
        let prepared, _ = EnvironmentFactories.prepare changed
        Assert.Empty(EnvironmentFactories.relations EdgeRole.EnvironmentResultDestination prepared)
        Assert.Empty(EnvironmentFactories.relations EdgeRole.EnvironmentResultCall prepared)
        let control, _ = EnvironmentFactories.prepare original
        Assert.Single(EnvironmentFactories.relations EdgeRole.EnvironmentResultDestination control) |> ignore

    [<Fact>]
    member _.``A mixed known and opaque callable alternative cannot acquire one factory destination`` () =
        let original = EnvironmentFactories.check EnvironmentFactories.bareSource
        let implementation = EnvironmentFactories.implementation "bareMap" original
        let _, callee, _ = EnvironmentFactories.calls implementation original |> List.head
        let source = original.Nodes[callee]
        let known = { source with Id = NodeId.fresh(); Parent = Some callee }
        let opaque = { source with Id = NodeId.fresh(); Kind = SemanticKind.PatternBinding "opaque"; Children = []; Parent = Some callee }
        let condition = { source with Id = NodeId.fresh(); Kind = SemanticKind.Literal(NativeLiteral.Bool true); Type = Types.boolType; Children = []; Parent = Some callee }
        let chosen = { source with Kind = SemanticKind.IfThenElse(condition.Id, known.Id, Some opaque.Id); Children = [condition.Id; known.Id; opaque.Id] }
        let added = [known; opaque; condition; chosen]
        let graph =
            { original with Nodes = added |> List.fold (fun nodes node -> Map.add node.Id node nodes) original.Nodes
                            Edges = (original.Edges |> List.filter (fun edge -> edge.Target <> callee)) @ (added |> List.collect EnvironmentIncidence.structuralIncidence) }
        let prepared, _ = EnvironmentFactories.prepare graph
        Assert.Empty(EnvironmentFactories.relations EdgeRole.EnvironmentResultDestination prepared)
        Assert.Empty(EnvironmentFactories.relations EdgeRole.EnvironmentResultCall prepared)

    [<Fact>]
    member _.``Stored partial factory application retains its earlier supplied effect without destination preparation`` () =
        let original = EnvironmentFactories.check """
let make (left: int) (right: int) = fun value -> left + right + value
[<EntryPoint>]
let main _ =
    let mutable formations = 0
    let partial = make (formations <- 1; 3)
    let callback = partial 4
    let values = Seq.map callback (seq { yield 2 })
    for value in values do ignore value
    formations
"""
        Assert.NotEmpty original.Codata.Value.Curry.PartialApplications
        let prepared, _ = EnvironmentFactories.prepare original
        Assert.Empty(EnvironmentFactories.relations EdgeRole.EnvironmentResultDestination prepared)
        Assert.Empty(EnvironmentFactories.relations EdgeRole.EnvironmentResultCall prepared)
        let partial = EnvironmentFactories.binding "partial" original
        Assert.Equal<NodeId list>(partial.Children, prepared.Nodes[partial.Id].Children)

module private CapturedStringOriginFixture =
    module Origin = Clef.Compiler.Baker.Recipes.StringComparisonRecipes
    module Flow = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
    module Boundary = Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission
    module Demand = Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand

    let constructions = Origin.constructions
    let lengthConstructions = Origin.lengthConstructions
    let validLengthStructure = Origin.validLengthStructure
    let project = Boundary.project

    type Capture = {
        Read: SemanticNode
        Environment: NodeId
        Formal: NodeId
        Owner: NodeId
        Implementation: NodeId
        Constructor: NodeId
        Slot: NodeId
        Initializer: NodeId
        FormalRow: Hyperedge
        CaptureRow: Hyperedge
        OriginRow: Hyperedge
    }

    let source text =
        sprintf "module CapturedUtf8\nlet make (prefix: string) = fun (value: string) -> if prefix = value then 1 else 0\nlet first = make %A\nlet second = make \"World\"\n[<EntryPoint>]\nlet main _ =\n    ignore (first \"probe\")\n    ignore (second \"probe\")\n    0\n" text

    let check text = LazyResidenceFixture.programWith (Some(source text))

    let literal text (graph: SemanticGraph) =
        graph.Nodes.Values
        |> Seq.filter (fun node -> node.IsReachable && node.Kind = SemanticKind.Literal(NativeLiteral.String text))
        |> Assert.Single
        |> _.Id

    let capturedRead (graph: SemanticGraph) =
        graph.Nodes.Values
        |> Seq.filter (fun node ->
            node.IsReachable && Types.isStringType node.Type &&
            match node.Kind with SemanticKind.EnvironmentRead _ -> true | _ -> false)
        |> Assert.Single

    let requireOrigin (graph: SemanticGraph) site =
        match Origin.stringOrigin graph (Flow.resolve graph) site site with
        | Ok(Some fact) -> fact
        | result -> failwithf "Missing complete captured source-string origin: %A" result

    let capture (graph: SemanticGraph) =
        let read = capturedRead graph
        let environment, slot =
            match read.Kind with
            | SemanticKind.EnvironmentRead(environment, slot) -> environment, slot
            | _ -> failwith "Missing captured string read"
        Assert.Equal<NodeId list>([environment], read.Children)
        let formal =
            match graph.Nodes[environment].Kind with
            | SemanticKind.VarRef(_, Some formal) -> formal
            | kind -> failwithf "Missing environment formal reference: %A" kind
        let formalRow =
            graph.Edges
            |> List.filter (fun row -> row.Role = EdgeRole.EnvironmentFormal && row.Target = formal)
            |> Assert.Single
        let owner, implementation =
            match formalRow.Class, formalRow.Ordinal, formalRow.Sources with
            | EdgeClass.Provenance, 0, [owner; implementation] -> owner, implementation
            | _ -> failwith "Lost exact environment formal authority"
        let constructor =
            match graph.Nodes[owner].Kind with
            | SemanticKind.ClosureValue(actual, constructor) when actual = implementation -> constructor
            | kind -> failwithf "Lost matching closure owner: %A" kind
        let captureRow =
            graph.Edges
            |> List.filter (fun row ->
                row.Target = constructor &&
                match row.Role, row.Sources with
                | EdgeRole.EnvironmentCapture _, [_; actual; _] -> actual = slot
                | _ -> false)
            |> Assert.Single
        let initializer =
            match captureRow.Class, captureRow.Role, captureRow.Sources with
            | EdgeClass.Provenance, EdgeRole.EnvironmentCapture false, [actual; declaration; value]
                when actual = owner && declaration = slot -> value
            | _ -> failwith "Lost exact immutable initializer authority"
        let originRow =
            graph.Edges
            |> List.filter (fun row -> row.Role = EdgeRole.CaptureReferenceOrigin && row.Target = read.Id)
            |> Assert.Single
        Assert.Equal<NodeId list>([owner; slot], originRow.Sources)
        { Read = read; Environment = environment; Formal = formal; Owner = owner
          Implementation = implementation; Constructor = constructor; Slot = slot
          Initializer = initializer; FormalRow = formalRow; CaptureRow = captureRow; OriginRow = originRow }

    let projection graph =
        match Boundary.project graph with
        | Ok projection -> projection
        | Error failures -> failwithf "Missing current string boundary: %A" failures

    let private key (row: Hyperedge) = row.Class, row.Role, row.Ordinal, row.Sources, row.Target
    let replaceRow (before: Hyperedge) (after: Hyperedge option) (graph: SemanticGraph) =
        { graph with
            Edges =
                graph.Edges
                |> List.collect (fun row -> if key row = key before then Option.toList after else [row]) }

    let refreshDemand (graph: SemanticGraph) =
        let refreshed =
            match Demand.tryRead graph with
            | Ok _ -> graph
            | Error failures ->
                Assert.NotEmpty failures
                Clef.Compiler.Nanopass.OrdinaryDemand.normalize graph
        match Demand.tryRead refreshed with
        | Ok _ -> refreshed
        | Error failures -> failwithf "Owning ordinary-demand refresh failed: %A" failures

    let refused graph site =
        let current = refreshDemand graph
        match Origin.stringOrigin current (Flow.resolve current) site site with
        | Ok(Some value) -> failwithf "Malformed captured origin was retained: %A" value
        | Ok None | Error _ -> ()

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "CapturedStringOrigin")>]
type CapturedStringOriginCases() =
    [<Theory>]
    [<InlineData("é", 2)>]
    [<InlineData("", 0)>]
    member _.``Captured factory strings retain exact UTF8 alternatives and distinct destinations``(text: string, bytes: int) =
        let graph = CapturedStringOriginFixture.check text
        let capture = CapturedStringOriginFixture.capture graph
        let expected =
            Map.ofList [CapturedStringOriginFixture.literal text graph, bigint bytes
                        CapturedStringOriginFixture.literal "World" graph, 5I]
        let identity, origins, participants = CapturedStringOriginFixture.requireOrigin graph capture.Read.Id
        Assert.Equal(capture.Read.Id, identity)
        Assert.Equal<Map<NodeId, bigint>>(expected, origins)
        for origin in expected.Keys do
            Assert.Contains(participants, fun participant -> participant.Node = origin && participant.Role = ParticipantRole.Origin)
        for id in [capture.Read.Id; capture.Environment; capture.Formal; capture.Owner; capture.Implementation
                   capture.Constructor; capture.Slot; capture.Initializer] do
            Assert.Contains(participants, fun participant -> participant.Node = id)
        let projection = CapturedStringOriginFixture.projection graph
        let extentSites =
            (CapturedStringOriginFixture.constructions graph
             |> List.choose (fun construction ->
                 if construction.Left = capture.Read.Id then Some(construction.LeftSource, construction.LeftLength)
                 elif construction.Right = capture.Read.Id then Some(construction.RightSource, construction.RightLength)
                 else None))
            @ (CapturedStringOriginFixture.lengthConstructions graph
               |> List.choose (fun construction ->
                   if construction.Left = capture.Read.Id then Some(construction.LeftSource, construction.LeftLength)
                   elif construction.Right = capture.Read.Id then Some(construction.RightSource, construction.RightLength)
                   else None))
        Assert.NotEmpty extentSites
        for source, site in extentSites do
            let extent = projection.StringExtents[site]
            Assert.Equal(source, extent.Source)
            Assert.Equal<Map<NodeId, bigint>>(expected, extent.StaticOrigins)
            Assert.Equal<ValueRange option>(Some(ValueRange.bounded (bigint bytes) 5I), graph.Nodes[extent.Site].ValueRange)
        let calls = EnvironmentFactories.relations EdgeRole.EnvironmentResultCall graph
        Assert.Equal(2, calls.Length)
        Assert.Equal(2, calls |> List.map (fun row -> row.Sources[3]) |> Set.ofList |> Set.count)

    [<Theory>]
    [<InlineData("mutable-capture")>]
    [<InlineData("missing-formal")>]
    [<InlineData("duplicate-formal")>]
    [<InlineData("missing-capture")>]
    [<InlineData("capture-ordinal")>]
    [<InlineData("missing-source-origin")>]
    [<InlineData("duplicate-source-origin")>]
    [<InlineData("schema-environment")>]
    member _.``Captured string authority mutations retract stored and freshly read origins``(defect: string) =
        let graph = CapturedStringOriginFixture.check "é"
        let capture = CapturedStringOriginFixture.capture graph
        CapturedStringOriginFixture.requireOrigin graph capture.Read.Id |> ignore
        CapturedStringOriginFixture.projection graph |> ignore
        let changed =
            match defect with
            | "mutable-capture" ->
                CapturedStringOriginFixture.replaceRow capture.CaptureRow
                    (Some { capture.CaptureRow with Role = EdgeRole.EnvironmentCapture true }) graph
            | "missing-formal" -> CapturedStringOriginFixture.replaceRow capture.FormalRow None graph
            | "duplicate-formal" -> { graph with Edges = capture.FormalRow :: graph.Edges }
            | "missing-capture" -> CapturedStringOriginFixture.replaceRow capture.CaptureRow None graph
            | "capture-ordinal" ->
                CapturedStringOriginFixture.replaceRow capture.CaptureRow
                    (Some { capture.CaptureRow with Ordinal = capture.CaptureRow.Ordinal + 1 }) graph
            | "missing-source-origin" -> CapturedStringOriginFixture.replaceRow capture.OriginRow None graph
            | "duplicate-source-origin" -> { graph with Edges = capture.OriginRow :: graph.Edges }
            | "schema-environment" ->
                let changedRead =
                    { capture.Read with Kind = SemanticKind.EnvironmentRead(capture.Constructor, capture.Slot)
                                        Children = [capture.Constructor] }
                { graph with Nodes = graph.Nodes.Add(capture.Read.Id, changedRead) }
            | other -> failwithf "Unknown capture defect: %s" other
        if defect <> "schema-environment" then Assert.Same(graph.Nodes, changed.Nodes)
        Assert.True(CapturedStringOriginFixture.project changed |> Result.isError)
        CapturedStringOriginFixture.refused changed capture.Read.Id
        CapturedStringOriginFixture.requireOrigin graph capture.Read.Id |> ignore

    [<Fact>]
    member _.``Captured literal text changes withdraw old extent without claiming new backing``() =
        let graph = CapturedStringOriginFixture.check "é"
        let capture = CapturedStringOriginFixture.capture graph
        let origin = CapturedStringOriginFixture.literal "é" graph
        let _, before, _ = CapturedStringOriginFixture.requireOrigin graph capture.Read.Id
        Assert.Equal(2I, before[origin])
        CapturedStringOriginFixture.projection graph |> ignore
        let changedLiteral = { graph.Nodes[origin] with Kind = SemanticKind.Literal(NativeLiteral.String "plane") }
        let changed = { graph with Nodes = graph.Nodes.Add(origin, changedLiteral) }
        // The old pool and derived rows remain. Only fresh logical source
        // observation may succeed; this does not authorize their physical use.
        Assert.True(CapturedStringOriginFixture.project changed |> Result.isError)
        let current = CapturedStringOriginFixture.refreshDemand changed
        let _, after, _ = CapturedStringOriginFixture.requireOrigin current capture.Read.Id
        Assert.Equal<Map<NodeId, bigint>>(before.Add(origin, 5I), after)

    [<Fact>]
    member _.``An unknown supplied string prevents a partial captured origin map``() =
        let graph = CapturedStringOriginFixture.check "é"
        let capture = CapturedStringOriginFixture.capture graph
        let unknown = CapturedStringOriginFixture.literal "é" graph
        let retained = CapturedStringOriginFixture.literal "World" graph
        let _, before, _ = CapturedStringOriginFixture.requireOrigin graph capture.Read.Id
        Assert.True(before.ContainsKey unknown && before.ContainsKey retained)
        CapturedStringOriginFixture.projection graph |> ignore
        let opaque = { graph.Nodes[unknown] with Kind = SemanticKind.PatternBinding "unknown_string"; Children = [] }
        let changed = { graph with Nodes = graph.Nodes.Add(unknown, opaque) }
        Assert.Equal(graph.Nodes[retained].Kind, changed.Nodes[retained].Kind)
        Assert.True(CapturedStringOriginFixture.project changed |> Result.isError)
        CapturedStringOriginFixture.refused changed capture.Read.Id

    [<Fact>]
    member _.``Generated immutable forwarding reads need no fabricated source reference row``() =
        let source =
            "module CapturedForwarding\n[<EntryPoint>]\nlet main _ =\n    let prefix = \"é\"\n    let outer = fun (expected: string) ->\n        let callback = fun (value: string) -> if prefix = value then 1 else 0\n        callback expected\n    outer \"probe\"\n"
        let graph = LazyResidenceFixture.programWith (Some source)
        let access =
            graph.Nodes.Values
            |> Seq.collect (fun node ->
                match node.Kind with
                | SemanticKind.EnvironmentCreate(_, initializers) ->
                    initializers
                    |> List.choose (fun (_, value) ->
                        match graph.Nodes[value].Kind with
                        | SemanticKind.EnvironmentRead _ when Types.isStringType graph.Nodes[value].Type -> Some graph.Nodes[value]
                        | _ -> None)
                | _ -> [])
            |> Assert.Single
        Assert.DoesNotContain(graph.Edges, fun row -> row.Role = EdgeRole.CaptureReferenceOrigin && row.Target = access.Id)
        let _, origins, _ = CapturedStringOriginFixture.requireOrigin graph access.Id
        Assert.Equal<Map<NodeId, bigint>>(Map.ofList [CapturedStringOriginFixture.literal "é" graph, 2I], origins)
        CapturedStringOriginFixture.projection graph |> ignore

    [<Fact>]
    member _.``Captured empty comparison retains length-only authority and withdraws stale emptiness``() =
        let source =
            "module CapturedEmpty\nlet make (prefix: string) = fun (value: string) -> if prefix = value then 1 else 0\nlet callback = make \"\"\n[<EntryPoint>]\nlet main _ = callback \"probe\"\n"
        let graph = LazyResidenceFixture.programWith (Some source)
        let capture = CapturedStringOriginFixture.capture graph
        let empty = CapturedStringOriginFixture.literal "" graph
        let identity, origins, _ = CapturedStringOriginFixture.requireOrigin graph capture.Read.Id
        Assert.Equal(capture.Read.Id, identity)
        Assert.Equal<Map<NodeId, bigint>>(Map.ofList [empty, 0I], origins)
        let construction =
            CapturedStringOriginFixture.lengthConstructions graph
            |> List.filter (fun construction -> construction.Left = capture.Read.Id || construction.Right = capture.Read.Id)
            |> Assert.Single
        Assert.DoesNotContain(CapturedStringOriginFixture.constructions graph, fun current -> current.Site = construction.Site)
        match CapturedStringOriginFixture.validLengthStructure graph construction with
        | Ok true -> ()
        | other -> failwithf "Missing current empty-comparison authority: %A" other
        let projection = CapturedStringOriginFixture.projection graph
        let site = if construction.Left = capture.Read.Id then construction.LeftLength else construction.RightLength
        Assert.Equal<Map<NodeId, bigint>>(origins, projection.StringExtents[site].StaticOrigins)
        for changed in [
            CapturedStringOriginFixture.replaceRow capture.OriginRow None graph
            { graph with Edges = capture.FormalRow :: graph.Edges }
        ] do
            Assert.Same(graph.Nodes, changed.Nodes)
            Assert.True(CapturedStringOriginFixture.project changed |> Result.isError)
            CapturedStringOriginFixture.refused changed capture.Read.Id
        let changedLiteral = { graph.Nodes[empty] with Kind = SemanticKind.Literal(NativeLiteral.String "é") }
        let changed = { graph with Nodes = graph.Nodes.Add(empty, changedLiteral) }
        Assert.True(CapturedStringOriginFixture.project changed |> Result.isError)
        let current = CapturedStringOriginFixture.refreshDemand changed
        let _, revised, _ = CapturedStringOriginFixture.requireOrigin current capture.Read.Id
        Assert.Equal<Map<NodeId, bigint>>(Map.ofList [empty, 2I], revised)
        match CapturedStringOriginFixture.validLengthStructure current construction with
        | Ok false -> ()
        | other -> failwithf "A nonempty capture retained the empty-comparison shortcut: %A" other

        // A fresh empty source is insufficient to repair an already-stale
        // proof. Transfer must require the prior construction's exact evidence.
        let row =
            graph.Edges
            |> List.filter (fun row ->
                row.Target = construction.Site &&
                match row.Role with EdgeRole.StringLengthComparison _ -> true | _ -> false)
            |> Assert.Single
        Assert.True(row.Sources.Length > 11)
        let malformedRow = { row with Sources = List.take 11 row.Sources }
        let malformed = CapturedStringOriginFixture.replaceRow row (Some malformedRow) graph
        let _, stillEmpty, _ = CapturedStringOriginFixture.requireOrigin malformed capture.Read.Id
        Assert.Equal<Map<NodeId, bigint>>(origins, stillEmpty)
        let malformedConstruction =
            CapturedStringOriginFixture.lengthConstructions malformed
            |> List.filter (fun current -> current.Site = construction.Site)
            |> Assert.Single
        Assert.Empty malformedConstruction.Evidence
        match CapturedStringOriginFixture.validLengthStructure malformed malformedConstruction with
        | Ok false -> ()
        | other -> failwithf "Missing evidence did not invalidate the old construction: %A" other
        let transferred =
            Clef.Compiler.Baker.Recipes.StringComparisonRecipes.transferLengthAfterFactoryRewrite malformed malformed
        let retainedRow =
            transferred.Edges
            |> List.filter (fun row ->
                row.Target = construction.Site &&
                match row.Role with EdgeRole.StringLengthComparison _ -> true | _ -> false)
            |> Assert.Single
        Assert.Equal<EdgeClass>(malformedRow.Class, retainedRow.Class)
        Assert.Equal<EdgeRole>(malformedRow.Role, retainedRow.Role)
        Assert.Equal(malformedRow.Ordinal, retainedRow.Ordinal)
        Assert.Equal(malformedRow.Target, retainedRow.Target)
        Assert.Equal<NodeId list>(malformedRow.Sources, retainedRow.Sources)
        match CapturedStringOriginFixture.validLengthStructure transferred malformedConstruction with
        | Ok false -> ()
        | other -> failwithf "Factory transfer repaired a stale prior proof: %A" other
        Assert.True(CapturedStringOriginFixture.project transferred |> Result.isError)

    [<Fact>]
    member _.``Immutable capture reader rejects an additional environment convention``() =
        let graph = CapturedStringOriginFixture.check "é"
        let capture = CapturedStringOriginFixture.capture graph
        let read = Clef.Compiler.Baker.Ingredients.CapturedStrings.reader
        Assert.True(read graph capture.Read.Id |> Option.isSome)
        let extra = { capture.FormalRow with Target = capture.Slot }
        Assert.NotEqual(capture.Formal, extra.Target)
        let changed = { graph with Edges = extra :: graph.Edges }
        Assert.Same(graph.Nodes, changed.Nodes)
        Assert.True(CapturedStringOriginFixture.project changed |> Result.isError)
        Assert.True(read changed capture.Read.Id |> Option.isNone)
        CapturedStringOriginFixture.refused changed capture.Read.Id

type ProgramInstanceDemandCases() =
    [<Theory>]
    [<InlineData("missing")>]
    [<InlineData("ordinal")>]
    [<InlineData("class")>]
    [<InlineData("sources")>]
    member _.``Stale ordinary demand makes a program instance unavailable without erasing its diagnostic`` defect =
        let source = "module ProgramInstanceDemand\nlet make (prefix: string) = fun (value: string) -> if prefix = value then 1 else 0\nlet first = make \"first\"\nlet second = make \"second\"\n[<EntryPoint>]\nlet main _ = first \"first\" + second \"second\"\n"
        let graph = LazyResidenceFixture.programWith (Some source)
        let first = EnvironmentFactories.binding "first" graph
        let read current =
            Clef.Compiler.Nanopass.ClosureEnvironmentSettlement.programInstance current first.Id
        let original = read graph |> Option.get
        let demand =
            graph.Edges
            |> List.find (fun edge -> edge.Role = EdgeRole.OrdinaryUnusedActual)
        let changedRows =
            graph.Edges
            |> List.choose (fun edge ->
                if not (obj.ReferenceEquals(edge, demand)) then Some edge
                else
                    match defect with
                    | "missing" -> None
                    | "ordinal" -> Some { edge with Ordinal = edge.Ordinal + 1 }
                    | "class" -> Some { edge with Class = EdgeClass.Provenance }
                    | "sources" -> Some { edge with Sources = edge.Sources @ [edge.Target] }
                    | _ -> failwithf "Unknown demand mutation %s" defect)
        let changed = { graph with Edges = changedRows }
        // The owning source diagnostic remains available. The optional instance
        // reader must refuse this prerequisite, not throw or settle a new row.
        match Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.projectValidated changed with
        | Result.Error failures -> Assert.NotEmpty failures
        | Result.Ok _ -> failwith "Changed demand was accepted before instance validation."
        Assert.True((read changed).IsNone)
        match Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.projectValidated changed with
        | Result.Error failures -> Assert.NotEmpty failures
        | Result.Ok _ -> failwith "Instance reading erased or refreshed the demand failure."
        let unavailableCodata = lazy (failwith "Stale demand must refuse before reading codata.")
        let guarded = { changed with Codata = unavailableCodata }
        Assert.True((read guarded).IsNone)
        Assert.False(unavailableCodata.IsValueCreated)
        Assert.Equal(original.Allocation, (read graph |> Option.get).Allocation)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "FiniteCellAuthority")>]
type FiniteCellAuthorityCases() =
    [<Fact>]
    member _.``Identical numeric results with changed finite support require new downstream proofs`` () =
        let source = """module FiniteSupportRenewal
let mutable state = 0
let record digit = state <- state + digit
[<EntryPoint>]
let main _ =
    record 1
    record 2
    state
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let finite = Clef.Compiler.PSGSaturation.SemanticGraph.FiniteCellRanges.recognize graph |> Assert.Single
        let project source =
            match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project source with
            | Result.Ok projection -> projection
            | Result.Error failures -> failwithf "Missing numeric projection: %A" failures
        let domainEntry (source: SemanticGraph) =
            source.Edges |> List.choose (fun edge ->
                match edge.Role with EdgeRole.NumericDomain domain -> Some(edge.Target, domain) | _ -> None) |> Assert.Single
        let previous = project graph
        let originalAnchor, originalDomain = domainEntry graph
        let changed, annotation = FiniteCellRepresentationFixture.annotateInitializer graph
        let initializer = graph.Nodes[Assert.Single (graph.Nodes[finite.Cell].Children)]
        let transported = { changed.Nodes[annotation] with ValueRange = initializer.ValueRange }
        let changed = { changed with Nodes = changed.Nodes.Add(annotation, transported) }
        Assert.False(Clef.Compiler.PSGSaturation.SemanticGraph.FiniteCellRanges.evidenceCurrent changed)
        let preserved = Clef.Compiler.Nanopass.RepresentationRanges.preserve graph changed
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.FiniteCellRanges.evidenceCurrent preserved)
        for KeyValue(id, node) in graph.Nodes do Assert.Equal(node.ValueRange, preserved.Nodes[id].ValueRange)
        let finiteProof = Assert.Single originalDomain.FiniteCellObligations |> fst
        Assert.Same(graph.Nodes[finiteProof], preserved.Nodes[finiteProof])
        Assert.Contains(preserved.Edges, fun edge ->
            edge.Role = EdgeRole.Constrains && edge.Target = finiteProof && List.contains annotation edge.Sources)
        // The added numeric participant needs its own claim even when its range
        // is unchanged: the completeness census names the missing claim before
        // the owner renews proofs. Publication checks currentness first (clef
        // #120, lead ruling), so the stale finite-cell premise is its one refusal
        // and the census is not consulted on this stale graph.
        Assert.Equal(None, Clef.Compiler.Baker.Ingredients.Obligations.sourceClaimId "numeric-carrier-coverage" preserved.Nodes[annotation])
        let claim = $"numeric_carrier_{NodeId.value annotation}"
        Assert.Contains(Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.completeness preserved, fun (site, reason) ->
            site = annotation && reason = "Numeric obligation completeness: missing or duplicate claim " + claim)
        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project preserved with
        | Result.Error failures ->
            let failure = Assert.Single failures
            Assert.Equal(WitnessProjectionFailureKind.Settlement, failure.Kind)
            Assert.Equal(Some originalAnchor, failure.Occurrence)
            Assert.Equal("NumericPublication: finite-cell relation premises changed; source numeric settlement is required.", failure.Reason)
        | Result.Ok _ -> failwith "The old numeric proof survived a change of finite support."
        let staleDemand =
            { preserved with
                Edges =
                    { Class = EdgeClass.Demand
                      Role = EdgeRole.OrdinaryUnusedFormal
                      Ordinal = 0
                      Sources = [annotation]
                      Target = annotation } :: preserved.Edges }
        Assert.True(Result.isError (Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.tryRead staleDemand))
        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project staleDemand with
        | Result.Error failures ->
            let failure = Assert.Single failures
            Assert.Equal(WitnessProjectionFailureKind.Settlement, failure.Kind)
            Assert.Equal(Some originalAnchor, failure.Occurrence)
            Assert.Equal("NumericPublication: finite-cell relation premises changed; source numeric settlement is required.", failure.Reason)
        | Result.Ok _ -> failwith "Stale ordinary demand and finite support crossed numeric publication."
        let renewed = Clef.Compiler.Nanopass.NumericSettlement.normalize preserved
        let renewedAnchor, renewedDomain = domainEntry renewed
        let current = project renewed
        let staleDomainOnly =
            { renewed with
                Edges =
                    renewed.Edges
                    |> List.map (fun edge ->
                        match edge.Role with
                        | EdgeRole.NumericDomain _ -> { edge with Role = EdgeRole.NumericDomain originalDomain }
                        | _ -> edge) }
        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project staleDomainOnly with
        | Result.Error failures ->
            let failure = Assert.Single failures
            Assert.Equal(WitnessProjectionFailureKind.Settlement, failure.Kind)
            Assert.Equal(Some renewedAnchor, failure.Occurrence)
            Assert.Equal("NumericPublication: finite-cell relation premises changed; source numeric settlement is required.", failure.Reason)
        | Result.Ok _ -> failwith "Stale finite-cell relation premises on a settled claim graph crossed numeric publication."
        let claimNodeId = Assert.Single current.Values[annotation].Obligations
        let missingClaimOnly = { renewed with Nodes = renewed.Nodes.Remove claimNodeId }
        // Claim-only deletion: the census names the withdrawn claim, and
        // publication refuses once, for the inconsistent ledger, without
        // consulting completeness (clef #120 lead ruling; the same control as
        // NUMERIC-STRICT-COMPLETENESS-UNREACHED in NumericPublicationCases).
        Assert.Contains(Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.completeness missingClaimOnly, fun (site, reason) ->
            site = annotation && reason = "Numeric obligation completeness: missing or duplicate claim " + claim)
        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project missingClaimOnly with
        | Result.Error failures ->
            let failure = Assert.Single failures
            Assert.Equal(WitnessProjectionFailureKind.Settlement, failure.Kind)
            Assert.Equal(Some renewedAnchor, failure.Occurrence)
            Assert.Equal("NumericPublication: The numeric carrier, joint premises, rewrite record or checked coverage obligation is inconsistent.", failure.Reason)
        | Result.Ok _ -> failwith "Withdrawn carrier claim citizen crossed numeric publication."
        let claimNode = renewed.Nodes[claimNodeId]
        let missingClaimIdentity =
            match claimNode.Kind with
            | SemanticKind.Obligation info ->
                { renewed with Nodes = renewed.Nodes.Add(claimNodeId, { claimNode with Kind = SemanticKind.Obligation { info with Id = "stale_" + claim } }) }
            | _ -> failwith "Expected carrier coverage obligation node."
        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project missingClaimIdentity with
        | Result.Error failures ->
            Assert.Equal(2, failures.Length)
            Assert.Contains(failures, fun failure ->
                failure.Kind = WitnessProjectionFailureKind.Settlement &&
                failure.Occurrence = Some annotation &&
                failure.Reason = "Numeric obligation completeness: missing or duplicate claim " + claim)
            Assert.Contains(failures, fun failure ->
                failure.Kind = WitnessProjectionFailureKind.Settlement &&
                failure.Occurrence = Some claimNodeId &&
                failure.Reason = "Numeric obligation completeness: unexpected claim stale_" + claim)
        | Result.Ok _ -> failwith "Corrupted carrier claim identity crossed numeric publication."
        Assert.Equal(previous.Values[finite.Cell].Slot, current.Values[finite.Cell].Slot)
        Assert.Equal(graph.Nodes[finite.Cell].ValueRange, renewed.Nodes[finite.Cell].ValueRange)
        Assert.NotEqual(originalDomain.FiniteCellRelations, renewedDomain.FiniteCellRelations)
        Assert.Contains(renewedDomain.FiniteCellRelations |> Option.get, fun relation -> List.contains annotation relation.Sources)
        Assert.NotEmpty(previous.Values[finite.Cell].Obligations)
        for obligation in previous.Values[finite.Cell].Obligations do
            Assert.False(renewed.Nodes.ContainsKey obligation, "Changed support requires new downstream numeric proof citizens.")
        let parseForeign source path =
            match Clef.Compiler.NativeService.parseStringWithDefaults source path with
            | Clef.Compiler.NativeService.ParseSuccess input -> input
            | Clef.Compiler.NativeService.ParseError errors -> failwithf "%A" errors
        let foreignAuthority = SourcePlatformFixture.authority.Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")
        let foreignSource = """module Foreign
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Pointer of int | Void
type PassBy = Value | Reference
type CallConv = | CDecl
type Transfer = | Borrowed
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
[<FidelityExtern("c", "native_read")>]
let read (count: int) : int = NativeDefault.zeroed ()
let readDescriptor: Expr<FunctionDescriptor> = <@ {
    CName="native_read"; Parameters=[| {Name="count";Type=Integer(Unsigned,32);PassBy=Value} |]
    ReturnType=Integer(Signed,64); CallingConvention=CDecl; OwnershipTransfer=Borrowed } @>
[<EntryPoint>]
let main _ = if read 4 = 0 then 0 else 1
"""
        let settledForeign =
            Clef.Compiler.NativeService.checkParsedInputsWithPlatform
                [parseForeign foreignAuthority "write-authority.clef"; parseForeign foreignSource "foreign.clef"]
                (Some SourcePlatformFixture.platform)
            |> fun result ->
                DimensionalCases.noErrors result
                result.Graph
        project settledForeign |> ignore
        let foreignAnchor, foreignDomain = domainEntry settledForeign
        let foreignUse = Assert.Single foreignDomain.ForeignResultUses
        let foreignRole, abiClaimNodeId = Assert.Single foreignUse.Claims
        Assert.Equal(ForeignResultProofRole.AbiNarrowing, foreignRole)
        Assert.Empty(Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.completeness settledForeign)
        let abiClaimId =
            match settledForeign.Nodes[abiClaimNodeId].Kind with
            | SemanticKind.Obligation info -> info.Id
            | _ -> failwith "Expected foreign result coverage obligation node."
        let foreignWithStaleValues =
            { settledForeign with
                Edges =
                    settledForeign.Edges
                    |> List.map (fun edge ->
                        match edge.Role with
                        | EdgeRole.NumericDomain _ -> { edge with Role = EdgeRole.NumericDomain { foreignDomain with Values = [] } }
                        | _ -> edge) }
        let abiSuffix = "31333A6162692D6E6172726F77696E67"
        let logicalSuffix = "31363A6C6F676963616C2D636F766572616765"
        Assert.EndsWith(abiSuffix, abiClaimId)
        let logicalClaimId = abiClaimId.Substring(0, abiClaimId.Length - abiSuffix.Length) + logicalSuffix
        let staleValueCompleteness = Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.completeness foreignWithStaleValues
        let staleValueSite, staleValueReason = Assert.Single staleValueCompleteness
        Assert.Equal(foreignUse.Application.Call, staleValueSite)
        Assert.Equal("Numeric obligation completeness: missing or duplicate claim " + logicalClaimId, staleValueReason)
        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project foreignWithStaleValues with
        | Result.Error failures ->
            let failure = Assert.Single failures
            Assert.Equal(WitnessProjectionFailureKind.Settlement, failure.Kind)
            Assert.Equal(Some foreignAnchor, failure.Occurrence)
            Assert.Equal("NumericPublication: A required source scalar carrier is absent or duplicated.", failure.Reason)
        | Result.Ok _ -> failwith "Stale foreign carrier domain crossed numeric publication."
        let callCarrier =
            foreignDomain.Values
            |> List.filter (fun value -> value.Site = foreignUse.Application.Call)
            |> Assert.Single
        Assert.Equal(SettledSlot.Integer(64, Some "signed64"), callCarrier.Slot)
        let narrowCarrier =
            foreignDomain.Values
            |> List.find (fun value ->
                match value.Slot, value.Representation, value.Declaration with
                | SettledSlot.Integer(bits, Some _), Some rep, Some _ -> bits > 0 && bits < 64 && rep.Bits = bits
                | _ -> false)
        let stalePositiveSlot = narrowCarrier.Slot
        let stalePositiveCarrier =
            { callCarrier with
                Slot = stalePositiveSlot
                Representation = narrowCarrier.Representation
                Declaration = narrowCarrier.Declaration
                Participants =
                    match narrowCarrier.Declaration with
                    | Some decl -> callCarrier.Participants |> Set.add decl
                    | None -> callCarrier.Participants }
        let foreignWithStalePositiveCarrier =
            { settledForeign with
                Edges =
                    settledForeign.Edges
                    |> List.map (fun edge ->
                        match edge.Role with
                        | EdgeRole.NumericDomain _ ->
                            { edge with
                                Role =
                                    EdgeRole.NumericDomain
                                        { foreignDomain with
                                            Values =
                                                foreignDomain.Values
                                                |> List.map (fun value ->
                                                    if value.Site = foreignUse.Application.Call then stalePositiveCarrier else value)
                                            OccurrenceRepresentations =
                                                foreignDomain.OccurrenceRepresentations.Add(
                                                    foreignUse.Application.Call,
                                                    Ok(ValueRepresentation.Scalar stalePositiveSlot)) } }
                        | _ -> edge) }
        let stalePositiveCompleteness = Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.completeness foreignWithStalePositiveCarrier
        let stalePositiveSite, stalePositiveReason = Assert.Single stalePositiveCompleteness
        Assert.Equal(foreignUse.Application.Call, stalePositiveSite)
        Assert.Equal("Numeric obligation completeness: missing or duplicate claim " + logicalClaimId, stalePositiveReason)
        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project foreignWithStalePositiveCarrier with
        | Result.Error failures ->
            let failure = Assert.Single failures
            Assert.Equal(WitnessProjectionFailureKind.Settlement, failure.Kind)
            Assert.Equal(Some foreignAnchor, failure.Occurrence)
            Assert.Equal("NumericPublication: The numeric carrier, joint premises, rewrite record or checked coverage obligation is inconsistent.", failure.Reason)
        | Result.Ok _ -> failwith "Stale positive-width foreign carrier crossed numeric publication."
        let foreignWithStaleFiniteCellsAndMissingAbiNarrowing =
            { settledForeign with
                Nodes = settledForeign.Nodes.Remove abiClaimNodeId
                Edges =
                    settledForeign.Edges
                    |> List.filter (fun edge -> edge.Target <> abiClaimNodeId && not (List.contains abiClaimNodeId edge.Sources))
                    |> List.map (fun edge ->
                        match edge.Role with
                        | EdgeRole.NumericDomain _ ->
                            { edge with Role = EdgeRole.NumericDomain { foreignDomain with FiniteCellRelations = Some [] } }
                        | _ -> edge) }
        // The census still names the withdrawn ABI-narrowing claim, but the
        // stale finite-cell premise is publication's one refusal: completeness
        // is not consulted on a stale graph (clef #120, lead ruling).
        Assert.Contains(Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.completeness foreignWithStaleFiniteCellsAndMissingAbiNarrowing, fun (site, reason) ->
            site = foreignUse.Application.Call && reason = "Numeric obligation completeness: missing or duplicate claim " + abiClaimId)
        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project foreignWithStaleFiniteCellsAndMissingAbiNarrowing with
        | Result.Error failures ->
            let failure = Assert.Single failures
            Assert.Equal(WitnessProjectionFailureKind.Settlement, failure.Kind)
            Assert.Equal(Some foreignAnchor, failure.Occurrence)
            Assert.Equal("NumericPublication: finite-cell relation premises changed; source numeric settlement is required.", failure.Reason)
        | Result.Ok _ -> failwith "Stale finite-cell relations and missing foreign ABI-narrowing claim crossed numeric publication."

    [<Theory>]
    [<InlineData(false, "startup")>]
    [<InlineData(false, "reference")>]
    [<InlineData(true, "startup")>]
    [<InlineData(true, "reference")>]
    member _.``Numeric publication retracts finite cell authority on relation only changes`` local defect =
        let body =
            if local then """[<EntryPoint>]
let main _ =
    let mutable state = 0
    state <- state + 1
    state <- state + 2
    state
"""
            else """let mutable state = 0
let record digit = state <- state + digit
[<EntryPoint>]
let main _ =
    record 1
    record 2
    state
"""
        let graph = LazyResidenceFixture.programWith (Some("module FiniteCellAuthority\n" + body))
        let bound = Clef.Compiler.PSGSaturation.SemanticGraph.FiniteCellRanges.recognize graph |> Assert.Single
        let project = Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project
        match project graph with
        | Result.Ok _ -> ()
        | Result.Error failures -> failwithf "Missing original numeric authority: %A" failures
        let changed =
            if defect = "startup" then
                { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramInitialization) }
            else
                let reference = graph.Nodes.Values |> Seq.find (fun node ->
                    node.IsReachable && match node.Kind with SemanticKind.VarRef(_, Some cell) -> cell = bound.Cell | _ -> false)
                let row = { Class = EdgeClass.Reference; Role = EdgeRole.Definition; Ordinal = 0
                            Sources = [bound.Writes.Head.Value]; Target = reference.Id }
                { graph with Edges = row :: graph.Edges }
        Assert.Same(graph.Nodes, changed.Nodes)
        Assert.Empty(Clef.Compiler.PSGSaturation.SemanticGraph.FiniteCellRanges.recognize changed)
        Assert.Same(changed, Clef.Compiler.Nanopass.RepresentationRanges.preserve graph changed)
        // Query the old numeric domain directly: no range pass or normalization
        // may refresh the authority before this refusal.
        match project changed with
        | Result.Error failures ->
            Assert.Contains(failures, fun failure -> failure.Reason.Contains("finite-cell relation premises changed"))
        | Result.Ok _ -> failwith "Stale finite-cell ranges crossed numeric publication."
        match project graph with
        | Result.Ok _ -> ()
        | Result.Error failures -> failwithf "The original immutable revision lost authority: %A" failures

    [<Theory>]
    [<InlineData("certificate")>]
    [<InlineData("constraint")>]
    member _.``Numeric renewal cannot bless an altered finite recurrence certificate`` defect =
        let source = """module FiniteCertificateAuthority
let mutable state = 0
let record digit = state <- state + digit
[<EntryPoint>]
let main _ =
    record 1
    record 2
    state
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let project = Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project
        let admitted source =
            match project source with
            | Result.Ok _ -> ()
            | Result.Error failures -> failwithf "Missing original numeric authority: %A" failures
        admitted graph
        admitted (Clef.Compiler.Nanopass.NumericSettlement.normalize graph)
        let proof = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Obligation info -> info.Kind = "finite-cell-effects" | _ -> false) |> Assert.Single
        let changed =
            if defect = "certificate" then
                let kind =
                    match proof.Kind with
                    | SemanticKind.Obligation info ->
                        match info.Body with
                        | ObligationBody.FiniteLinearRecurrence model ->
                            SemanticKind.Obligation { info with Body = ObligationBody.FiniteLinearRecurrence { model with MaximumIterations = model.MaximumIterations + 1I } }
                        | _ -> failwith "Missing finite recurrence model"
                    | _ -> failwith "Missing source obligation"
                { graph with Nodes = graph.Nodes.Add(proof.Id, { proof with Kind = kind }) }
            else
                let edges = graph.Edges |> List.map (fun edge ->
                    if edge.Role = EdgeRole.Constrains && edge.Target = proof.Id then { edge with Ordinal = edge.Ordinal + 1 } else edge)
                { graph with Edges = edges }
        for KeyValue(id, node) in graph.Nodes do Assert.Equal(node.ValueRange, changed.Nodes[id].ValueRange)
        Assert.Same(changed, Clef.Compiler.Nanopass.RepresentationRanges.preserve graph changed)
        match project changed with
        | Result.Error failures -> Assert.Contains(failures, fun failure -> failure.Reason.Contains("finite-cell relation premises changed"))
        | Result.Ok _ -> failwith "An altered finite certificate crossed numeric publication."
        // Refreshing only the carrier domain cannot repair the source proof.
        let renewed = Clef.Compiler.Nanopass.NumericSettlement.normalize changed
        match project renewed with
        | Result.Error failures -> Assert.NotEmpty failures
        | Result.Ok _ -> failwith "Numeric renewal silently blessed an altered source certificate."
        admitted graph

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Repeated numeric renewal cannot forget wholly withdrawn finite cell evidence`` local =
        let body =
            if local then """[<EntryPoint>]
let main _ =
    let mutable state = 0
    state <- state + 1
    state <- state + 2
    state
"""
            else """let mutable state = 0
let record digit = state <- state + digit
[<EntryPoint>]
let main _ =
    record 1
    record 2
    state
"""
        let graph = LazyResidenceFixture.programWith (Some("module WithdrawnFiniteCellEvidence\n" + body))
        let project = Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project
        let admitted source =
            match project source with
            | Result.Ok _ -> ()
            | Result.Error failures -> failwithf "Missing original numeric authority: %A" failures
        admitted graph
        admitted (Clef.Compiler.Nanopass.NumericSettlement.normalize graph)
        let proofs =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.Obligation info when info.Kind = "finite-cell-effects" -> Some node.Id
                | _ -> None)
            |> Set.ofSeq
        Assert.Single proofs |> ignore
        let oldDomain =
            graph.Edges
            |> List.choose (fun edge -> match edge.Role with EdgeRole.NumericDomain domain -> Some domain | _ -> None)
            |> Assert.Single
        Assert.True(oldDomain.FiniteCellRelations.IsSome)
        Assert.Single oldDomain.FiniteCellObligations |> ignore
        let nodes = graph.Nodes |> Map.filter (fun id _ -> not (proofs.Contains id))
        // Keep the historical numeric domain until its real owner renews it.
        // Remove every finite certificate and all its current range/proof rows.
        let edges = graph.Edges |> List.filter (fun edge ->
            edge.Role <> EdgeRole.FiniteCellRange && not (proofs.Contains edge.Target))
        let changed = { graph with Nodes = nodes; Edges = edges }
        for KeyValue(id, node) in changed.Nodes do Assert.Equal(graph.Nodes[id].ValueRange, node.ValueRange)
        Assert.DoesNotContain(changed.Edges, fun edge -> edge.Role = EdgeRole.FiniteCellRange)
        Assert.DoesNotContain(changed.Nodes.Values, fun node ->
            match node.Kind with SemanticKind.Obligation info -> info.Kind = "finite-cell-effects" | _ -> false)
        // The source transitions remain recognizable, but their independently
        // required proof inventory is absent. Held range annotations cannot replace it.
        Assert.Single(Clef.Compiler.PSGSaturation.SemanticGraph.FiniteCellRanges.recognize changed) |> ignore
        Assert.False(Clef.Compiler.PSGSaturation.SemanticGraph.FiniteCellRanges.evidenceCurrent changed)
        Assert.Same(changed, Clef.Compiler.Nanopass.RepresentationRanges.preserve graph changed)
        match project changed with
        | Result.Error failures -> Assert.Contains(failures, fun failure -> failure.Reason.Contains("finite-cell relation premises changed"))
        | Result.Ok _ -> failwith "Deleting finite source evidence crossed numeric publication."
        let refused source =
            match project source with
            | Result.Error failures -> Assert.Contains(failures, fun failure -> failure.Reason.Contains("finite-cell relation premises changed", System.StringComparison.OrdinalIgnoreCase))
            | Result.Ok _ -> failwith "Numeric renewal forgot the withdrawn finite-cell proof requirement."
        let once = Clef.Compiler.Nanopass.NumericSettlement.normalize changed
        refused once
        let twice = Clef.Compiler.Nanopass.NumericSettlement.normalize once
        refused twice
        // The owning recurrence recipe can restore current evidence. Failed
        // numeric renewals must not permanently taint a subsequently valid graph.
        let restored =
            Clef.Compiler.PSGSaturation.SemanticGraph.FiniteCellRanges.settle
                (Clef.Compiler.PSGSaturation.SemanticGraph.FiniteCellRanges.recognize twice) twice
            |> Clef.Compiler.Nanopass.NumericSettlement.normalize
        admitted restored
        admitted graph
