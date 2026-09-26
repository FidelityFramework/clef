namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module ContinuationIngress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress

module private ContinuationIngressFixture =
    type Fixture = {
        Graph: SemanticGraph
        Owner: NodeId
        Generator: NodeId
        Formal: NodeId
        Storage: NodeId
        Source: NodeId
        Original: NodeId
        Persistent: NodeId
        Scratch: NodeId
        Writer: NodeId
        Body: NodeId
    }

    /// Typed source access contracts supplied by the continuation recipe. This
    /// tests callable identity only; it claims no frame layout or residence.
    let create () =
        let builder = NodeBuilder()
        let callable = NativeType.TFun(Types.boolType, Types.boolType)
        let input = builder.Create(SemanticKind.PatternBinding "input", Types.boolType, dummyRange)
        let code = builder.Create(SemanticKind.Lambda(["input", Types.boolType, input.Id], input.Id, [], None, LambdaContext.RegularClosure), callable, dummyRange)
        let source = builder.Create(SemanticKind.Binding("callback", false, false, None), callable, dummyRange, children = [code.Id])
        let original = builder.Create(SemanticKind.VarRef("callback", Some source.Id), callable, dummyRange)
        let owner = builder.Create(SemanticKind.PatternBinding "owner", NativeType.TSeq Types.boolType, dummyRange)
        let environmentType = NativeType.TSeqEnumerator Types.boolType
        let formal = builder.Create(SemanticKind.PatternBinding "environment", environmentType, dummyRange)
        let environment = builder.Create(SemanticKind.VarRef("environment", Some formal.Id), environmentType, dummyRange)
        let persistent = builder.Create(SemanticKind.FrameRead(environment.Id, source.Id), callable, dummyRange)
        let storageType = Types.mkArrayType Types.uint8Type
        let storage = builder.Create(SemanticKind.ContinuationStorage owner.Id, storageType, dummyRange)
        let stored = builder.Create(SemanticKind.Binding("storage", false, false, None), storageType, dummyRange, children = [storage.Id])
        let scratchEnvironment = builder.Create(SemanticKind.VarRef("storage", Some stored.Id), storageType, dummyRange)
        let writer = builder.Create(SemanticKind.FrameWrite(scratchEnvironment.Id, original.Id, persistent.Id), Types.unitType, dummyRange)
        let scratch = builder.Create(SemanticKind.FrameRead(scratchEnvironment.Id, original.Id), callable, dummyRange)
        let doneValue = builder.Create(SemanticKind.Literal(NativeLiteral.Bool false), Types.boolType, dummyRange)
        let body = builder.Create(SemanticKind.Sequential [stored.Id; writer.Id; scratch.Id; doneValue.Id], Types.boolType, dummyRange)
        let generator = builder.Create(SemanticKind.Lambda(["environment", environmentType, formal.Id], body.Id, [], None, LambdaContext.SeqGenerator),
                                       NativeType.TFun(environmentType, Types.boolType), dummyRange)
        let capture = { Name = "callback"; Type = callable; IsMutable = false; SourceNodeId = Some source.Id }
        builder.CompleteNode(owner.Id, SemanticKind.SeqExpr(generator.Id, [capture]), [generator.Id]) |> ignore
        let raw = builder.Build []
        let edges = [
            { Sources = [source.Id]; Target = persistent.Id; Class = EdgeClass.Provenance; Role = EdgeRole.ContinuationValue; Ordinal = 0 }
            { Sources = [owner.Id; generator.Id; formal.Id; source.Id]; Target = persistent.Id
              Class = EdgeClass.Provenance; Role = EdgeRole.ContinuationSlotAccess; Ordinal = 0 }
            { Sources = [original.Id]; Target = scratch.Id; Class = EdgeClass.Provenance; Role = EdgeRole.ContinuationValue; Ordinal = 0 }
            { Sources = [owner.Id; generator.Id; storage.Id; original.Id; writer.Id; persistent.Id]; Target = scratch.Id
              Class = EdgeClass.Provenance; Role = EdgeRole.ContinuationSlotAccess; Ordinal = 0 }
        ]
        let graph = { raw with Nodes = raw.Nodes.Add(original.Id, { original with IsReachable = false })
                               Edges = raw.Edges @ edges; Codata = lazy (failwith "Ingress forced final continuation codata") }
        { Graph = graph; Owner = owner.Id; Generator = generator.Id; Formal = formal.Id; Storage = storage.Id
          Source = source.Id; Original = original.Id; Persistent = persistent.Id; Scratch = scratch.Id
          Writer = writer.Id; Body = body.Id }

    let append (fixture: Fixture) (newNodes: SemanticNode list) operation (graph: SemanticGraph) =
        let body = graph.Nodes[fixture.Body]
        let values = match body.Kind with SemanticKind.Sequential values -> values | _ -> failwith "Missing continuation block"
        let values = (values |> List.take (values.Length - 1)) @ [operation; List.last values]
        let nodes = newNodes |> List.fold (fun nodes node -> Map.add node.Id node nodes) graph.Nodes
        { graph with Nodes = nodes.Add(body.Id, { body with Kind = SemanticKind.Sequential values }) }

    let writers target values (graph: SemanticGraph) =
        let edges =
            graph.Edges |> List.map (fun edge ->
                if edge.Target = target && edge.Role = EdgeRole.ContinuationSlotAccess then
                    { edge with Sources = List.take 4 edge.Sources @ (values |> List.collect (fun (writer, value) -> [writer; value])) }
                else edge)
        { graph with Edges = edges }

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "CallableIngress")>]
type ContinuationIngressCases() =
    [<Fact>]
    member _.``Exact persistent and scratch reads retain callable identity without reviving the retired original occurrence`` () =
        let fixture = ContinuationIngressFixture.create ()
        let reading = ContinuationIngress.analyze fixture.Graph
        for occurrence in [fixture.Persistent; fixture.Scratch] do
            let proof = ContinuationIngress.tryEvidence reading occurrence |> Option.get
            Assert.Contains(fixture.Owner, proof.Participants)
            Assert.Contains(fixture.Generator, proof.Participants)
            Assert.Contains(fixture.Source, proof.Participants)
        Assert.False(ContinuationIngress.allowsOccurrence reading fixture.Original)
        let scratch = ContinuationIngress.tryEvidence reading fixture.Scratch |> Option.get
        Assert.Contains(fixture.Original, scratch.Participants)
        Assert.Contains(fixture.Writer, scratch.Participants)
        Assert.Contains(fixture.Persistent, scratch.Participants)

    [<Theory>]
    [<InlineData("missing-access")>]
    [<InlineData("missing-original")>]
    [<InlineData("conflicting-access")>]
    [<InlineData("wrong-source")>]
    [<InlineData("wrong-owner")>]
    [<InlineData("wrong-generator")>]
    [<InlineData("wrong-storage")>]
    [<InlineData("read-type")>]
    [<InlineData("source-type")>]
    [<InlineData("storage-type")>]
    member _.``Changed continuation access participants retract the retained original value`` defect =
        let fixture = ContinuationIngressFixture.create ()
        let graph = fixture.Graph
        let change id transform = { graph with Nodes = graph.Nodes.Add(id, transform graph.Nodes[id]) }
        let changed =
            match defect with
            | "read-type" -> change fixture.Scratch (fun node -> { node with Type = NativeType.TFun(Types.unitType, Types.boolType) })
            | "source-type" -> change fixture.Original (fun node -> { node with Type = NativeType.TFun(Types.unitType, Types.boolType) })
            | "storage-type" -> change fixture.Storage (fun node -> { node with Type = Types.mkArrayType Types.boolType })
            | "missing-access" | "missing-original" ->
                let role = if defect = "missing-access" then EdgeRole.ContinuationSlotAccess else EdgeRole.ContinuationValue
                { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Target <> fixture.Scratch || edge.Role <> role) }
            | _ ->
                let original = graph.Edges |> List.find (fun edge -> edge.Target = fixture.Scratch && edge.Role = EdgeRole.ContinuationSlotAccess)
                let parts = original.Sources |> List.mapi (fun ordinal source ->
                    match defect, ordinal with
                    | "wrong-source", 3 | "conflicting-access", 3 -> fixture.Source
                    | "wrong-owner", 0 -> fixture.Source
                    | "wrong-generator", 1 -> fixture.Source
                    | "wrong-storage", 2 -> fixture.Formal
                    | _ -> source)
                let edges = if defect = "conflicting-access" then graph.Edges else graph.Edges |> List.filter (fun edge -> edge.Target <> fixture.Scratch || edge.Role <> EdgeRole.ContinuationSlotAccess)
                { graph with Edges = { original with Sources = parts } :: edges }
        Assert.False(ContinuationIngress.allowsOccurrence (ContinuationIngress.analyze changed) fixture.Scratch)
        Assert.True(ContinuationIngress.allowsOccurrence (ContinuationIngress.analyze graph) fixture.Scratch)

    [<Theory>]
    [<InlineData("capture-mode")>]
    [<InlineData("capture-slot")>]
    [<InlineData("capture-type")>]
    [<InlineData("mutable-source")>]
    member _.``Persistent callable reads require the original immutable capture contract`` defect =
        let fixture = ContinuationIngressFixture.create ()
        let graph = fixture.Graph
        let changed =
            if defect = "mutable-source" then
                let source = graph.Nodes[fixture.Source]
                { graph with Nodes = graph.Nodes.Add(source.Id, { source with Kind = SemanticKind.Binding("callback", true, false, None) }) }
            else
                let owner = graph.Nodes[fixture.Owner]
                match owner.Kind with
                | SemanticKind.SeqExpr(generator, [capture]) ->
                    let capture =
                        match defect with
                        | "capture-mode" -> { capture with IsMutable = true }
                        | "capture-slot" -> { capture with SourceNodeId = Some fixture.Original }
                        | _ -> { capture with Type = NativeType.TFun(Types.unitType, Types.boolType) }
                    { graph with Nodes = graph.Nodes.Add(owner.Id, { owner with Kind = SemanticKind.SeqExpr(generator, [capture]) }) }
                | _ -> failwith "Missing source capture"
        Assert.False(ContinuationIngress.allowsOccurrence (ContinuationIngress.analyze changed) fixture.Persistent)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Changing a writer value retracts identity even when its participant row is rewritten`` rewriteRow =
        let fixture = ContinuationIngressFixture.create ()
        let graph = fixture.Graph
        let code = graph.Nodes[fixture.Source].Children |> List.exactlyOne |> fun id -> graph.Nodes[id]
        let other = { code with Id = NodeId.fresh() }
        let writer = graph.Nodes[fixture.Writer]
        let frame, slot = match writer.Kind with SemanticKind.FrameWrite(frame, slot, _) -> frame, slot | _ -> failwith "Missing writer"
        let changed = { graph with Nodes = graph.Nodes.Add(other.Id, other).Add(writer.Id, { writer with Kind = SemanticKind.FrameWrite(frame, slot, other.Id) }) }
        let changed = if rewriteRow then ContinuationIngressFixture.writers fixture.Scratch [writer.Id, other.Id] changed else changed
        Assert.False(ContinuationIngress.allowsOccurrence (ContinuationIngress.analyze changed) fixture.Scratch)
        Assert.True(ContinuationIngress.allowsOccurrence (ContinuationIngress.analyze graph) fixture.Scratch)

    [<Theory>]
    [<InlineData("missing-writer")>]
    [<InlineData("missing-value")>]
    [<InlineData("writer-type")>]
    [<InlineData("writer-slot")>]
    [<InlineData("writer-storage")>]
    [<InlineData("duplicated-writer")>]
    [<InlineData("no-initialization")>]
    member _.``The exact writer initializer and complete writer incidence are required`` defect =
        let fixture = ContinuationIngressFixture.create ()
        let graph = fixture.Graph
        let writer = graph.Nodes[fixture.Writer]
        let frame, slot, value = match writer.Kind with SemanticKind.FrameWrite(frame, slot, value) -> frame, slot, value | _ -> failwith "Missing writer"
        let changed =
            match defect with
            | "missing-writer" -> ContinuationIngressFixture.writers fixture.Scratch [] graph
            | "missing-value" ->
                let edges =
                    graph.Edges |> List.map (fun edge ->
                        if edge.Target = fixture.Scratch && edge.Role = EdgeRole.ContinuationSlotAccess then
                            { edge with Sources = List.take 5 edge.Sources }
                        else edge)
                { graph with Edges = edges }
            | "duplicated-writer" -> ContinuationIngressFixture.writers fixture.Scratch [writer.Id, value; writer.Id, value] graph
            | "writer-type" -> { graph with Nodes = graph.Nodes.Add(writer.Id, { writer with Type = Types.boolType }) }
            | "writer-slot" -> { graph with Nodes = graph.Nodes.Add(writer.Id, { writer with Kind = SemanticKind.FrameWrite(frame, fixture.Source, value) }) }
            | "writer-storage" -> { graph with Nodes = graph.Nodes.Add(writer.Id, { writer with Kind = SemanticKind.FrameWrite(fixture.Formal, slot, value) }) }
            | _ ->
                let changed = { graph with Nodes = graph.Nodes.Add(writer.Id, { writer with Kind = SemanticKind.Literal NativeLiteral.Unit; Children = [] }) }
                ContinuationIngressFixture.writers fixture.Scratch [] changed
        Assert.False(ContinuationIngress.allowsOccurrence (ContinuationIngress.analyze changed) fixture.Scratch)
        Assert.True(ContinuationIngress.allowsOccurrence (ContinuationIngress.analyze graph) fixture.Scratch)

    [<Fact>]
    member _.``Every additional lawful writer must be present and retraction follows each graph revision`` () =
        let fixture = ContinuationIngressFixture.create ()
        let graph = fixture.Graph
        let writer = { graph.Nodes[fixture.Writer] with Id = NodeId.fresh() }
        let added = ContinuationIngressFixture.append fixture [writer] writer.Id graph
        Assert.False(ContinuationIngress.allowsOccurrence (ContinuationIngress.analyze added) fixture.Scratch)
        let covered = ContinuationIngressFixture.writers fixture.Scratch [fixture.Writer, fixture.Persistent; writer.Id, fixture.Persistent] added
        let proof = ContinuationIngress.tryEvidence (ContinuationIngress.analyze covered) fixture.Scratch |> Option.get
        Assert.Contains(writer.Id, proof.Participants)
        Assert.Contains(fixture.Writer, proof.Participants)
        Assert.True(ContinuationIngress.allowsOccurrence (ContinuationIngress.analyze graph) fixture.Scratch)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Immutable persistent captures refuse writes even with a matching all-writers row`` coverWriter =
        let fixture = ContinuationIngressFixture.create ()
        let graph = fixture.Graph
        let frame = match graph.Nodes[fixture.Persistent].Kind with SemanticKind.FrameRead(frame, _) -> frame | _ -> failwith "Missing persistent read"
        let writer = { graph.Nodes[fixture.Writer] with Id = NodeId.fresh(); Kind = SemanticKind.FrameWrite(frame, fixture.Source, fixture.Source) }
        let changed = ContinuationIngressFixture.append fixture [writer] writer.Id graph
        let changed = if coverWriter then ContinuationIngressFixture.writers fixture.Persistent [writer.Id, fixture.Source] changed else changed
        let reading = ContinuationIngress.analyze changed
        Assert.False(ContinuationIngress.allowsOccurrence reading fixture.Persistent)
        Assert.False(ContinuationIngress.allowsOccurrence reading fixture.Scratch)
        Assert.True(ContinuationIngress.allowsOccurrence (ContinuationIngress.analyze graph) fixture.Persistent)

    [<Theory>]
    [<InlineData("scratch-borrow")>]
    [<InlineData("capture-borrow")>]
    [<InlineData("opaque-storage-use")>]
    member _.``Unknown storage consumption and indirect callable slot mutation retract identity`` defect =
        let fixture = ContinuationIngressFixture.create ()
        let graph = fixture.Graph
        let read = if defect = "capture-borrow" then fixture.Persistent else fixture.Scratch
        let frame, slot = match graph.Nodes[read].Kind with SemanticKind.FrameRead(frame, slot) -> frame, slot | _ -> failwith "Missing read"
        let operation =
            { graph.Nodes[fixture.Writer] with
                Id = NodeId.fresh()
                Kind = if defect = "opaque-storage-use" then SemanticKind.Application(frame, []) else SemanticKind.FrameBorrow(frame, slot)
                Type = if defect = "opaque-storage-use" then Types.unitType else NativeType.TByref(graph.Nodes[read].Type, ByrefKind.InOut) }
        let changed = ContinuationIngressFixture.append fixture [operation] operation.Id graph
        Assert.False(ContinuationIngress.allowsOccurrence (ContinuationIngress.analyze changed) fixture.Scratch)
        Assert.True(ContinuationIngress.allowsOccurrence (ContinuationIngress.analyze graph) fixture.Scratch)
