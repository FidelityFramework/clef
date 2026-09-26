namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module LazyValues = Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues
module LazyElaboration = Clef.Compiler.Nanopass.LazyElaboration

module private LazyFixture =
    let platform pointerBits : PlatformContext =
        { PlatformId = "lazy-placement-test"
          Dimensions = Map.ofList ["Pointer", pointerBits; "Register", 64]
          Representations = Map.empty; EndpointReturns = Map.empty
          PlatformLibraryPath = None; PlatformDescription = None; PlatformArchitecture = None; PlatformOS = None
          PlatformSourcePaths = Set.empty; Predicates = Map.empty; FreestandingStartup = None
          SubstrateKind = None; RuntimeModel = None; AvailableMemorySpaces = []; DefaultMemorySpace = None
          ClockFrequencyMhz = None; NsPerWeightUnit = None }

    let source = """
module LazyFixture
let make value = lazy value
[<EntryPoint>]
let main _ =
    let mutable cell = 3
    let delayed = lazy (cell <- 7; cell)
    let alias = delayed
    let first = Lazy.force alias
    cell <- 9
    let second = Lazy.force delayed
    first + second
"""

    let check source =
        match parseAndCheck source "lazy-values.clef" with
        | Success result -> DimensionalCases.noErrors result; result.Graph
        | CheckFailure result -> failwithf "Expected checked lazy source: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed lazy source: %A" errors

    let checkedSource () = check source
    let normalized () = checkedSource () |> LazyElaboration.normalize
    let protocols graph =
        graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LazyMemoization)
        |> List.map (fun edge -> LazyValues.force graph edge.Target |> Option.defaultWith (fun () -> failwithf "Invalid force %A" edge.Target))
    let binding name graph =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false) |> Assert.Single
    let modify id transform graph = { graph with Nodes = graph.Nodes.Add(id, transform graph.Nodes[id]) }

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "LazyValues")>]
type LazyValueCases() =
    [<Fact>]
    member _.``Baker makes the real guarded cache read and result before publication sequence`` () =
        let graph = LazyFixture.normalized ()
        Assert.Empty((LazyValues.settle graph).Residuals)
        let forces = LazyFixture.protocols graph
        Assert.Equal(2, forces.Length)
        for force in forces do
            let contract = LazyValues.instance graph force.Formation |> Option.get
            match graph.Nodes[force.UncachedBranch].Kind with
            | SemanticKind.Sequential [result; store; publish; yielded] ->
                Assert.Equal(force.ResultBinding, result)
                Assert.Equal(force.ResultStore, store)
                Assert.Equal(force.Publication, publish)
                match graph.Nodes[yielded].Kind with
                | SemanticKind.VarRef(_, Some actual) -> Assert.Equal(result, actual)
                | kind -> failwithf "The branch must return the computed value, got %A" kind
            | kind -> failwithf "Missing store-before-publication spine: %A" kind
            Assert.Equal(Types.intType, contract.ElementType)
            Assert.Empty(graph.Nodes[contract.Cached].Children)
            match graph.Nodes[contract.Environment].Kind with
            | SemanticKind.LazyEnvironment(owner, initializers) ->
                Assert.Equal(force.Formation, owner)
                Assert.Equal((contract.Computed, contract.InitialComputed), List.head initializers)
                Assert.DoesNotContain(initializers, fun (slot, _) -> slot = contract.Cached)
            | kind -> failwithf "Missing lazy environment: %A" kind

    [<Fact>]
    member _.``Aliases retain the actual instance operand and the original mutable captured cell`` () =
        let graph = LazyFixture.normalized ()
        let forces = LazyFixture.protocols graph
        let formation = forces |> List.map _.Formation |> List.distinct |> Assert.Single
        let contract = LazyValues.instance graph formation |> Option.get
        let cell = LazyFixture.binding "cell" graph
        Assert.Equal((cell.Id, cell.Id, true), Assert.Single contract.Captured)
        Assert.Equal(2, forces |> List.map _.Operand |> List.distinct |> List.length)
        let ownerOf = LazyValues.tryOwner graph
        for name in ["alias"; "delayed"] do Assert.Equal(Some formation, ownerOf (LazyFixture.binding name graph).Id)
        for force in forces do
            let reference = Assert.Single graph.Nodes[force.EnvironmentBinding].Children
            match graph.Nodes[reference].Kind with
            | SemanticKind.LazyEnvironmentReference actual -> Assert.Equal(force.Operand, actual)
            | kind -> failwithf "Force lost its actual runtime instance: %A" kind
        match graph.Nodes[contract.Thunk].Kind with
        | SemanticKind.Lambda([_, formalType, formal], body, [], _, LambdaContext.LazyThunk) ->
            Assert.Equal(LazyValues.environmentType, formalType)
            Assert.Equal(contract.Formal, formal)
            Assert.Equal(contract.ThunkBody, body)
        | kind -> failwithf "Lazy code must use its actual environment: %A" kind
        Assert.Contains(graph.Nodes.Values, fun node ->
            match node.Kind with SemanticKind.LazyWrite(_, slot, _) -> slot = cell.Id | _ -> false)

    [<Theory>]
    [<InlineData("publish-first")>]
    [<InlineData("unguarded-cache")>]
    [<InlineData("duplicated-cache-occurrence")>]
    [<InlineData("changed-instance")>]
    [<InlineData("changed-cache-type")>]
    member _.``A memoization relation cannot admit a changed guard order or instance`` defect =
        let original = LazyFixture.normalized ()
        let force = LazyFixture.protocols original |> List.head
        let graph =
            match defect with
            | "publish-first" ->
                original |> LazyFixture.modify force.UncachedBranch (fun node ->
                    match node.Kind with
                    | SemanticKind.Sequential [result; store; publish; yielded] ->
                        let actions = [result; publish; store; yielded]
                        { node with Kind = SemanticKind.Sequential actions; Children = actions }
                    | _ -> failwith "Fixture lost its cold branch")
            | "unguarded-cache" ->
                original |> LazyFixture.modify force.Conditional (fun node ->
                    { node with Kind = SemanticKind.IfThenElse(force.Condition, force.UncachedBranch, Some force.CachedRead)
                                Children = [force.Condition; force.UncachedBranch; force.CachedRead] })
            | "duplicated-cache-occurrence" ->
                let node = original.Nodes[force.Site]
                let id = NodeId.fresh()
                let duplicate = { node with Id = id; Kind = SemanticKind.Sequential [force.CachedRead]; Children = [force.CachedRead] }
                { original with Nodes = original.Nodes.Add(id, duplicate) }
            | "changed-cache-type" ->
                original |> LazyFixture.modify force.CachedRead (fun node -> { node with Type = Types.boolType })
            | _ ->
                let reference = Assert.Single original.Nodes[force.EnvironmentBinding].Children
                original |> LazyFixture.modify reference (fun node -> { node with Kind = SemanticKind.LazyEnvironmentReference force.Site })
        Assert.Equal(None, LazyValues.force graph force.Site)

    [<Theory>]
    [<InlineData("read")>]
    [<InlineData("publish")>]
    member _.``A valid force does not authorize another cache access outside its source guard`` operation =
        let original = LazyFixture.normalized ()
        let force = LazyFixture.protocols original |> List.head
        let source = original.Nodes[if operation = "read" then force.CachedRead else force.Publication]
        let id = NodeId.fresh()
        let graph = { original with Nodes = original.Nodes.Add(id, { source with Id = id; Parent = None }) }
        Assert.True((LazyValues.force graph force.Site).IsSome)
        let result = LazyValues.settle graph
        Assert.Contains(result.Residuals, fun pending -> pending.Site = id)

    [<Theory>]
    [<InlineData("cache-default")>]
    [<InlineData("capture-mode")>]
    [<InlineData("duplicate-relation")>]
    [<InlineData("unrelated-byref")>]
    member _.``Formation never gains an invented cache value or loses its mutable capture identity`` defect =
        let original = LazyFixture.normalized ()
        let force = LazyFixture.protocols original |> List.head
        let contract = LazyValues.instance original force.Formation |> Option.get
        let graph =
            match defect with
            | "cache-default" ->
                original |> LazyFixture.modify contract.Environment (fun node ->
                    match node.Kind with
                    | SemanticKind.LazyEnvironment(owner, initializers) ->
                        { node with Kind = SemanticKind.LazyEnvironment(owner, initializers @ [contract.Cached, contract.InitialComputed]) }
                    | _ -> failwith "Fixture lost its environment")
            | "capture-mode" ->
                let edges = original.Edges |> List.map (fun edge ->
                    if edge.Target = contract.Environment && edge.Role = EdgeRole.LazyCapture true then
                        { edge with Role = EdgeRole.LazyCapture false } else edge)
                { original with Edges = edges }
            | "unrelated-byref" ->
                let slot, _, _ = Assert.Single contract.Captured
                let id = NodeId.fresh()
                let unrelated =
                    { original.Nodes[slot] with
                        Id = id
                        Kind = SemanticKind.PatternBinding "unrelated_cell"
                        Type = NativeType.TByref(original.Nodes[slot].Type, ByrefKind.InOut)
                        Children = []
                        Parent = None }
                let environment = original.Nodes[contract.Environment]
                let initializers = [contract.Computed, contract.InitialComputed; slot, id]
                let environment = { environment with Kind = SemanticKind.LazyEnvironment(contract.Formation, initializers) }
                let edges = original.Edges |> List.map (fun edge ->
                    if edge.Target = contract.Environment && edge.Role = EdgeRole.LazyCapture true then
                        { edge with Sources = [contract.Formation; slot; id] } else edge)
                { original with Nodes = original.Nodes.Add(id, unrelated).Add(environment.Id, environment); Edges = edges }
            | _ ->
                let edge = original.Edges |> List.find (fun edge -> edge.Role = EdgeRole.LazyInstance && edge.Target = contract.Formation)
                { original with Edges = edge :: original.Edges }
        Assert.Equal(None, LazyValues.instance graph contract.Formation)
        Assert.Equal(None, LazyValues.force graph force.Site)

    [<Fact>]
    member _.``Two factory results share code origin without sharing the force environment operand`` () =
        let source = """
module LazyFactories
let make value = lazy value
[<EntryPoint>]
let main _ =
    let first = make 3
    let second = make 7
    Lazy.force first + Lazy.force second
"""
        let graph = LazyFixture.check source |> LazyElaboration.normalize
        let forces = LazyFixture.protocols graph
        Assert.Equal(2, forces.Length)
        Assert.Single(forces |> List.map _.Formation |> List.distinct) |> ignore
        Assert.Equal(2, forces |> List.map _.Operand |> List.distinct |> List.length)
        Assert.Equal(2, forces |> List.map _.EnvironmentBinding |> List.distinct |> List.length)
        for force in forces do
            let reference = Assert.Single graph.Nodes[force.EnvironmentBinding].Children
            match graph.Nodes[reference].Kind with
            | SemanticKind.LazyEnvironmentReference operand -> Assert.Equal(force.Operand, operand)
            | kind -> failwithf "Factory instance was replaced by its code origin: %A" kind

    [<Theory>]
    [<InlineData("true")>]
    [<InlineData("()")>]
    [<InlineData("42<m>")>]
    member _.``Cached declaration keeps the body's exact source result type`` expression =
        let source = "module LazyTypes\n[<Measure>] type m\n[<EntryPoint>]\nlet main _ =\n    let value = lazy " + expression + "\n    ignore (Lazy.force value)\n    0\n"
        let graph = LazyFixture.check source |> LazyElaboration.normalize
        let force = LazyFixture.protocols graph |> Assert.Single
        let contract = LazyValues.instance graph force.Formation |> Option.get
        Assert.Equal(graph.Nodes[contract.ThunkBody].Type, graph.Nodes[contract.Cached].Type)
        Assert.Equal(graph.Nodes[contract.Cached].Type, graph.Nodes[force.Invocation].Type)
        Assert.Equal(graph.Nodes[force.Invocation].Type, graph.Nodes[force.CachedRead].Type)

    [<Theory>]
    [<InlineData(32)>]
    [<InlineData(64)>]
    member _.``Typed lazy storage contains a bool prefix and original cell descriptor with no code field`` pointerBits =
        let source = """
module LazyStorage
[<EntryPoint>]
let main _ =
    let mutable cell = true
    let value = lazy (cell <- false; cell)
    ignore (Lazy.force value)
    0
"""
        let raw = LazyFixture.check source |> LazyElaboration.normalize
        let graph = { raw with Platform = Some(LazyFixture.platform pointerBits) }
        let owner, contract = LazyValues.instances graph |> Map.toList |> Assert.Single
        match Clef.Compiler.PSGSaturation.SemanticGraph.Placement.placeLazyEnvironment graph owner with
        | Ok (SettledLayout.Record(fields, Some bytes, Some alignment), descriptors) ->
            let pointerBytes = pointerBits / 8
            Assert.Equal(3, fields.Length)
            Assert.Equal(6 * pointerBytes, bytes)
            Assert.Equal(pointerBytes, alignment)
            Assert.Equal<int option list>([Some 0; Some 1; Some pointerBytes], fields |> List.map _.Offset)
            Assert.Equal<int option list>([Some 1; Some 1; Some(5 * pointerBytes)], fields |> List.map _.Size)
            Assert.Equal(SettledSlot.Bool, fields[0].Slot)
            Assert.Equal(SettledSlot.Bool, fields[1].Slot)
            Assert.Equal(contract.Computed, descriptors[0].Source)
            Assert.Equal(contract.Cached, descriptors[1].Source)
            Assert.Equal(CaptureSlotKind.CellView Types.boolType, descriptors[2].Holds)
            Assert.Empty(graph.Nodes[contract.Cached].Children)
        | result -> failwithf "Expected source-typed memoization layout: %A" result

    [<Fact>]
    member _.``Callable results cannot acquire a code address data slot by type-only placement`` () =
        let source = """
module LazyCallable
[<EntryPoint>]
let main _ =
    let value = lazy (fun flag -> not flag)
    let predicate = Lazy.force value
    if predicate false then 0 else 1
"""
        let raw = LazyFixture.check source |> LazyElaboration.normalize
        let graph = { raw with Platform = Some(LazyFixture.platform 64) }
        let owner, contract = LazyValues.instances graph |> Map.toList |> Assert.Single
        match Clef.Compiler.PSGSaturation.SemanticGraph.Placement.placeLazyEnvironment graph owner with
        | Error (Clef.Compiler.PSGSaturation.SemanticGraph.Placement.ContinuationPlacementError.UnsupportedField(actual, _)) ->
            Assert.Equal(contract.Cached, actual)
        | result -> failwithf "A separate callable storage protocol is required: %A" result

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Reachability retains lazy declarations without fabricating a cached value or force`` force =
        let body = if force then "ignore (Lazy.force delayed)" else "ignore delayed"
        let source =
            "module LazyDeclarationLiveness\n[<EntryPoint>]\nlet main _ =\n    let delayed = lazy true\n    " + body + "\n    0\n"
        let graph = LazyFixture.check source |> LazyElaboration.normalize
        let owner, contract = LazyValues.instances graph |> Map.toList |> Assert.Single
        let before = LazyValues.settle graph
        let refreshed = Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable graph
        Assert.True(refreshed.Nodes[owner].IsReachable)
        Assert.True(refreshed.Nodes[contract.Computed].IsReachable)
        Assert.True(refreshed.Nodes[contract.Cached].IsReachable)
        Assert.Empty refreshed.Nodes[contract.Cached].Children
        let after = LazyValues.settle refreshed
        Assert.Empty after.Residuals
        Assert.Equal(before.Forces.Count, after.Forces.Count)
        Assert.Equal((if force then 1 else 0), after.Forces.Count)
        match refreshed.Nodes[contract.Environment].Kind with
        | SemanticKind.LazyEnvironment(_, initializers) ->
            Assert.DoesNotContain(initializers, fun (slot, _) -> slot = contract.Cached)
        | kind -> failwithf "Expected source environment: %A" kind

    [<Fact>]
    member _.``Lazy write replacement retires the old assignment target without losing its original cell`` () =
        let graph =
            LazyFixture.check "module LazyRetiredTarget\n[<EntryPoint>]\nlet main _ =\n    let mutable cell = false\n    let delayed = lazy (cell <- true; cell)\n    if Lazy.force delayed then 0 else 1\n"
            |> LazyElaboration.normalize
        let _, contract = LazyValues.instances graph |> Map.toList |> Assert.Single
        let cell, initializer, mutableCell = Assert.Single contract.Captured
        Assert.True mutableCell
        Assert.Equal(cell, initializer)
        Assert.True graph.Nodes[cell].IsReachable
        let targets =
            graph.Nodes.Values |> Seq.filter (fun node ->
                match node.Kind, node.Parent |> Option.bind graph.Nodes.TryFind with
                | SemanticKind.VarRef(_, Some original), Some { Kind = SemanticKind.LazyWrite(_, destination, _) } ->
                    original = cell && destination = cell
                | _ -> false)
        let target = Assert.Single targets
        Assert.False target.IsReachable
        let proof = LazyValues.settle graph
        Assert.Empty proof.Residuals
        Assert.Single proof.Forces |> ignore

    [<Theory>]
    [<InlineData("immutable")>]
    [<InlineData("eager")>]
    [<InlineData("mutable")>]
    [<InlineData("opaque")>]
    [<InlineData("detached")>]
    [<InlineData("annotation-type")>]
    member _.``Capture environment aliases require exact formal identity and their own thunk scope`` mode =
        let original = LazyFixture.normalized ()
        let owner, contract = LazyValues.instances original |> Map.toList |> Assert.Single
        let slot, _, _ = Assert.Single contract.Captured
        let read, environment =
            original.Nodes.Values |> Seq.pick (fun node ->
                match node.Kind with
                | SemanticKind.LazyRead(environment, actual) when actual = slot -> Some(node, environment)
                | _ -> None)
        let bindingId, referenceId, annotationId = NodeId.fresh(), NodeId.fresh(), NodeId.fresh()
        let template = original.Nodes[environment]
        let binding =
            { template with Id = bindingId
                            Kind = (if mode = "opaque" then SemanticKind.Application(NodeId.fresh(), [])
                                    else SemanticKind.Binding("environment_alias", (mode = "mutable"), false, None))
                            Children = (if mode = "opaque" then [] else [environment]) }
        let declared = if mode = "annotation-type" then Types.boolType else LazyValues.environmentType
        let annotationKind = if mode = "eager" then SemanticKind.EagerExpr bindingId else SemanticKind.TypeAnnotation(bindingId, declared)
        let annotation = { template with Id = annotationId; Kind = annotationKind; Children = [bindingId] }
        let reference = { template with Id = referenceId; Kind = SemanticKind.VarRef("environment_alias", Some annotationId); Children = [] }
        let body = original.Nodes[contract.ThunkBody]
        let body =
            match body.Kind with
            | SemanticKind.Sequential actions when mode <> "detached" ->
                { body with Kind = SemanticKind.Sequential(annotationId :: actions); Children = annotationId :: actions }
            | _ -> body
        let graph =
            { original with Nodes = original.Nodes.Add(bindingId, binding).Add(referenceId, reference).Add(annotationId, annotation)
                                        .Add(body.Id, body).Add(read.Id, { read with Kind = SemanticKind.LazyRead(referenceId, slot); Children = [referenceId] }) }
        let settled = LazyValues.settle graph
        if mode = "immutable" || mode = "eager" then
            Assert.Empty settled.Residuals
            for participant in [read.Id; environment; bindingId; referenceId; annotationId; contract.Formal; contract.ThunkBody; contract.Thunk] do
                Assert.Contains(participant, settled.CaptureUses[owner])
            if mode = "eager" then
                let demanded = Clef.Compiler.Nanopass.EagerDemand.normalize graph
                Assert.Equal(SemanticKind.EagerExpr bindingId, demanded.Nodes[annotationId].Kind)
                Assert.Contains(demanded.Edges, fun edge ->
                    edge.Target = annotationId && edge.Role = EdgeRole.EagerDemand EagerFrontier.Expression && edge.Sources = [annotationId; bindingId])
        else
            Assert.Contains(settled.Residuals, fun residual -> residual.Site = read.Id)

    [<Theory>]
    [<InlineData("formation-instance")>]
    [<InlineData("detached-read")>]
    [<InlineData("detached-write")>]
    [<InlineData("detached-borrow")>]
    [<InlineData("shared-lambda")>]
    [<InlineData("cycle")>]
    member _.``Capture slot and schema cannot authorize another actual instance or structural occurrence`` defect =
        let original = LazyFixture.normalized ()
        let owner, contract = LazyValues.instances original |> Map.toList |> Assert.Single
        let slot, _, _ = Assert.Single contract.Captured
        let access, environment =
            original.Nodes.Values |> Seq.pick (fun node ->
                match node.Kind with
                | SemanticKind.LazyRead(environment, actual) when actual = slot && defect <> "detached-write" -> Some(node, environment)
                | SemanticKind.LazyWrite(environment, actual, _) when actual = slot && defect = "detached-write" -> Some(node, environment)
                | _ -> None)
        let graph, rejected =
            match defect with
            | "formation-instance" ->
                let reference = original.Nodes[environment]
                let graph = { original with Nodes = original.Nodes.Add(environment, { reference with Kind = SemanticKind.VarRef("other_instance", Some contract.Environment); Children = [] }) }
                Assert.Equal(Some owner, LazyValues.tryOwner graph environment)
                graph, access.Id
            | "detached-read" | "detached-write" | "detached-borrow" ->
                let duplicate = NodeId.fresh()
                let copied =
                    if defect = "detached-borrow" then
                        { access with Kind = SemanticKind.LazyBorrow(environment, slot)
                                      Type = NativeType.TByref(original.Nodes[slot].Type, ByrefKind.InOut) }
                    else access
                // Keeping the old Parent deliberately tests actual incidence.
                { original with Nodes = original.Nodes.Add(duplicate, { copied with Id = duplicate }) }, duplicate
            | "shared-lambda" ->
                let id, formal = NodeId.fresh(), NodeId.fresh()
                let parameter = { original.Nodes[contract.Formal] with Id = formal }
                let lambda =
                    { original.Nodes[contract.Thunk] with
                        Id = id
                        Parent = None
                        Kind = SemanticKind.Lambda(["other", parameter.Type, formal], access.Id, [], None, LambdaContext.RegularClosure)
                        Children = [formal; access.Id] }
                { original with Nodes = original.Nodes.Add(formal, parameter).Add(id, lambda) }, access.Id
            | _ ->
                { original with Nodes = original.Nodes.Add(access.Id, { access with Children = access.Id :: access.Children }) }, access.Id
        Assert.True((LazyValues.instance graph owner).IsSome)
        Assert.Contains((LazyValues.settle graph).Residuals, fun residual -> residual.Site = rejected)

    [<Fact>]
    member _.``Lazy captured source references retain exact provenance while memoization reads stay internal`` () =
        let graph = LazyFixture.normalized ()
        let formations = LazyValues.instances graph
        let rows =
            graph.Edges |> List.filter (fun edge ->
                edge.Role = EdgeRole.CaptureReferenceOrigin &&
                (List.tryHead edge.Sources |> Option.exists formations.ContainsKey))
        Assert.NotEmpty rows
        let read = LazyValues.tryCapturedSourceReference graph
        for row in rows do Assert.Equal(Some row.Sources[1], read row.Target)
        let row = rows.Head
        let contract = formations[row.Sources.Head]
        let reference = graph.Nodes[row.Target]
        let environment, slot = match reference.Kind with SemanticKind.LazyRead(environment, slot) -> environment, slot | _ -> failwith "Expected lazy capture read"
        let without = graph.Edges |> List.filter (fun edge -> not (edge.Target = row.Target && edge.Role = EdgeRole.CaptureReferenceOrigin))
        let missingCapture =
            graph.Edges |> List.filter (fun edge ->
                match edge.Role, edge.Sources with
                | EdgeRole.LazyCapture _, [owner; declaration; _] -> owner <> contract.Formation || declaration <> slot
                | _ -> true)
        let malformed =
            [ "missing occurrence", { graph with Edges = without }
              "duplicate occurrence", { graph with Edges = row :: graph.Edges }
              "missing capture authority", { graph with Edges = missingCapture }
              "wrong capture type", { graph with Nodes = graph.Nodes.Add(reference.Id, { reference with Type = Types.unitType }) }
              "different environment instance", { graph with Nodes = graph.Nodes.Add(reference.Id, { reference with Kind = SemanticKind.LazyRead(contract.Environment, slot); Children = [contract.Environment] }) } ]
        for name, changed in malformed do
            Assert.True((LazyValues.tryCapturedSourceReference changed row.Target).IsNone, "Source reference did not retract: " + name)
        let internalReads =
            graph.Nodes.Values |> Seq.filter (fun node ->
                match node.Kind with
                | SemanticKind.LazyRead(_, field) -> field = contract.Computed || field = contract.Cached
                | _ -> false) |> Seq.toList
        Assert.NotEmpty internalReads
        for node in internalReads do Assert.Equal(None, read node.Id)
        let generated = { reference with Id = NodeId.fresh(); Kind = SemanticKind.LazyRead(environment, slot) }
        let additional = { graph with Nodes = graph.Nodes.Add(generated.Id, generated) }
        Assert.Equal(None, LazyValues.tryCapturedSourceReference additional generated.Id)
        Assert.Equal(Some slot, read row.Target)
