namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module MutableStorage = Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage
module MutableCarriers = Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers

module private MutableCallableFixture =
    type Fixture = {
        Graph: SemanticGraph
        Carriers: Map<NodeId, CallableCarrier>
        Initial: NodeId
        Replacement: NodeId
        Cell: NodeId
        Read: NodeId
        Saved: NodeId
        SavedRead: NodeId
        Later: NodeId
        Write: NodeId
        Target: NodeId
        Capturing: NodeId
        Opaque: NodeId
    }

    let create () =
        let builder = NodeBuilder()
        let ty = NativeType.TFun(Types.boolType, Types.boolType)
        let named name value =
            let parameter = builder.Create(SemanticKind.PatternBinding "argument", Types.boolType, dummyRange)
            let body = builder.Create(SemanticKind.Literal(NativeLiteral.Bool value), Types.boolType, dummyRange)
            let lambda = builder.Create(SemanticKind.Lambda(["argument", Types.boolType, parameter.Id], body.Id, [], None,
                                                          LambdaContext.RegularClosure), ty, dummyRange)
            let binding = builder.Create(SemanticKind.Binding(name, false, false, None), ty, dummyRange, children = [lambda.Id])
            builder.Create(SemanticKind.VarRef(name, Some binding.Id), ty, dummyRange)
        let initial, replacement = named "first" false, named "second" true
        let cell = builder.Create(SemanticKind.Binding("selected", true, false, None), ty, dummyRange, children = [initial.Id])
        let read = builder.Create(SemanticKind.VarRef("selected", Some cell.Id), ty, dummyRange)
        let saved = builder.Create(SemanticKind.Binding("saved", false, false, None), ty, dummyRange, children = [read.Id])
        let target = builder.Create(SemanticKind.VarRef("selected", Some cell.Id), ty, dummyRange)
        let write = builder.Create(SemanticKind.Set(target.Id, replacement.Id), Types.unitType, dummyRange)
        let later = builder.Create(SemanticKind.VarRef("selected", Some cell.Id), ty, dummyRange)
        let savedRead = builder.Create(SemanticKind.VarRef("saved", Some saved.Id), ty, dummyRange)
        let capturedRead = builder.Create(SemanticKind.VarRef("selected", Some cell.Id), ty, dummyRange)
        let capture = { Name = "selected"; Type = ty; IsMutable = true; SourceNodeId = Some cell.Id }
        let parameter = builder.Create(SemanticKind.PatternBinding "_", Types.unitType, dummyRange)
        let capturing = builder.Create(SemanticKind.Lambda(["_", Types.unitType, parameter.Id], capturedRead.Id,
                                                          [capture], None, LambdaContext.RegularClosure),
                                       NativeType.TFun(Types.unitType, ty), dummyRange)
        let opaque = builder.Create(SemanticKind.PatternBinding "unknown", ty, dummyRange)
        let raw = builder.Build []
        let carriers, _ = MutableCarriers.settle { Layouts = Map.empty; Origins = Map.empty; Known = Map.empty } raw
        let settled = MutableStorage.settle carriers Map.empty raw
        let codata =
            { raw.Codata.Value with
                CallableCarriers = carriers
                CallableJoins = settled.Joins
                MutableCallableStorage = settled.Storage }
        let graph = { raw with Codata = lazy codata }
        { Graph = graph; Carriers = carriers; Initial = initial.Id; Replacement = replacement.Id; Cell = cell.Id
          Read = read.Id; Saved = saved.Id; SavedRead = savedRead.Id; Later = later.Id; Write = write.Id
          Target = target.Id; Capturing = capturing.Id; Opaque = opaque.Id }

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "MutableCallableStorage")>]
type MutableCallableStorageCases() =
    [<Fact>]
    member _.``Finite cell retains all writes and snapshots the exact read frontier`` () =
        let f = MutableCallableFixture.create ()
        let cell = f.Graph.Codata.Value.MutableCallableStorage[f.Cell]
        Assert.Equal<NodeId list>([f.Initial; f.Replacement], cell.Alternatives)
        Assert.Equal<NodeId list>(cell.Alternatives, cell.AlternativeCarriers |> List.map _.Occurrence)
        Assert.Equal(0, cell.Initializer.Alternative)
        let write = Assert.Single cell.Writes
        Assert.Equal(f.Write, write.Site)
        Assert.Equal(f.Target, write.Destination)
        Assert.Equal(f.Replacement, write.Value)
        Assert.Equal(1, write.Alternative)
        Assert.Contains(f.Capturing, cell.Captures)
        Assert.Equal(None, cell.EnvironmentBytes)
        for occurrence in [f.Read; f.Saved; f.SavedRead] do
            let join = f.Graph.Codata.Value.CallableJoins[occurrence]
            Assert.Equal(occurrence, join.Occurrence)
            Assert.Equal(f.Read, join.Read)
            Assert.Equal(f.Cell, join.Storage)
            Assert.Equal<NodeId list>(cell.Alternatives, join.Alternatives)
        Assert.Equal(f.Later, f.Graph.Codata.Value.CallableJoins[f.Later].Read)
        Assert.False(f.Graph.Codata.Value.CallableJoins.ContainsKey f.Target)
        Assert.True(MutableStorage.validate f.Graph cell)

    [<Theory>]
    [<InlineData("opaque-write")>]
    [<InlineData("changed-capture-mode")>]
    [<InlineData("escaping-cell")>]
    member _.``Unaccounted writes references or capture changes retract the complete protocol`` defect =
        let f = MutableCallableFixture.create ()
        let graph =
            match defect with
            | "opaque-write" ->
                let node = f.Graph.Nodes[f.Write]
                { f.Graph with Nodes = f.Graph.Nodes.Add(node.Id, { node with Kind = SemanticKind.Set(f.Target, f.Opaque) }) }
            | "changed-capture-mode" ->
                let node = f.Graph.Nodes[f.Capturing]
                match node.Kind with
                | SemanticKind.Lambda(parameters, body, captures, enclosing, context) ->
                    let captures = captures |> List.map (fun held -> { held with IsMutable = false })
                    let changed = { node with Kind = SemanticKind.Lambda(parameters, body, captures, enclosing, context) }
                    { f.Graph with Nodes = f.Graph.Nodes.Add(node.Id, changed) }
                | _ -> failwith "Fixture lost its captured cell"
            | _ ->
                let node = f.Graph.Nodes[f.Opaque]
                { f.Graph with Nodes = f.Graph.Nodes.Add(node.Id, { node with Kind = SemanticKind.AddressOf(f.Cell, false) }) }
        let result = MutableStorage.settle f.Carriers Map.empty graph
        Assert.False(result.Storage.ContainsKey f.Cell)
        Assert.NotEmpty(result.Residuals)
        Assert.False(MutableStorage.validate graph f.Graph.Codata.Value.MutableCallableStorage[f.Cell])
        Assert.False(MutableStorage.validateJoin graph f.Graph.Codata.Value.CallableJoins[f.SavedRead])

    [<Fact>]
    member _.``A saved callable is a value snapshot and is never treated as a shared cell alias`` () =
        let f = MutableCallableFixture.create ()
        let target = f.Graph.Nodes[f.Target]
        let graph = { f.Graph with Nodes = f.Graph.Nodes.Add(target.Id, { target with Kind = SemanticKind.VarRef("saved", Some f.Saved) }) }
        let result = MutableStorage.settle f.Carriers Map.empty graph
        Assert.Empty(result.Storage[f.Cell].Writes)
        Assert.False(MutableStorage.validate graph f.Graph.Codata.Value.MutableCallableStorage[f.Cell])
        Assert.Equal(f.Read, result.Joins[f.SavedRead].Read)

    [<Fact>]
    member _.``An independent reference or redirected implementation invalidates retained protocol evidence`` () =
        let f = MutableCallableFixture.create ()
        let edge = { Class = EdgeClass.Reference; Role = EdgeRole.Argument; Sources = [f.Cell]; Target = f.Opaque; Ordinal = 0 }
        let opaque = { f.Graph with Edges = edge :: f.Graph.Edges }
        Assert.False(MutableStorage.validate opaque f.Graph.Codata.Value.MutableCallableStorage[f.Cell])
        let replacement = f.Graph.Nodes[f.Replacement]
        let changed = { replacement with Kind = SemanticKind.VarRef("unknown", Some f.Opaque) }
        let redirected = { f.Graph with Nodes = f.Graph.Nodes.Add(replacement.Id, changed) }
        Assert.False(MutableStorage.validate redirected f.Graph.Codata.Value.MutableCallableStorage[f.Cell])
        Assert.False(MutableStorage.validateJoin redirected f.Graph.Codata.Value.CallableJoins[f.SavedRead])

    [<Fact>]
    member _.``Captured protocol aliases must terminate at the original cell instead of a borrow cycle`` () =
        let f = MutableCallableFixture.create ()
        let first = f.Graph.Nodes.Keys |> Seq.map NodeId.value |> Seq.max |> (+) 1
        let owner, environment, borrow = NodeId first, NodeId(first + 1), NodeId(first + 2)
        let prototype = f.Graph.Nodes[f.Opaque]
        let node id kind ty =
            { prototype with Id = id; Kind = kind; Type = ty; Parent = None; Children = []; Metadata = Map.empty }
        let makeGraph initial =
            let ownerNode = node owner (SemanticKind.ClosureValue(f.Capturing, environment)) prototype.Type
            let environmentNode = node environment (SemanticKind.EnvironmentCreate(owner, [f.Cell, initial]))
                                           Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments.environmentType
            let borrowNode = node borrow (SemanticKind.EnvironmentBorrow(environment, f.Cell)) prototype.Type
            let capture = { Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentCapture true
                            Sources = [owner; f.Cell; initial]; Target = environment; Ordinal = 0 }
            { f.Graph with
                Nodes = f.Graph.Nodes.Add(owner, ownerNode).Add(environment, environmentNode).Add(borrow, borrowNode)
                Edges = capture :: f.Graph.Edges }
        let rooted = MutableStorage.settle f.Carriers Map.empty (makeGraph f.Cell)
        Assert.True(rooted.Storage.ContainsKey f.Cell)
        Assert.Contains(borrow, rooted.Storage[f.Cell].Borrows)
        let cyclic = MutableStorage.settle f.Carriers Map.empty (makeGraph borrow)
        Assert.False(cyclic.Storage.ContainsKey f.Cell)
        Assert.Contains(cyclic.Residuals, fun residual -> residual.Binding = f.Cell)
