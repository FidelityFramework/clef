namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module private RepresentationRangeFixture =
    module Ranges = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis
    module Settlement = Clef.Compiler.Nanopass.NumericSettlement
    module Publication = Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication
    let sourceFacts = Ranges.sourceFacts
    let normalize = Settlement.normalize

    let expected = ValueRange.Bounded(0I, 99I)
    let source = """
let mutable pulls = 0
let values = seq {
    pulls <- (pulls + 1) % 100
    let saved = (pulls + 7) % 100
    yield saved
    pulls <- (pulls + 1) % 100
    yield (saved + 1) % 100
}
[<EntryPoint>]
let main _ =
    for value in values do ignore value
    for value in values do ignore value
    0
"""
    let original = lazy (SequenceProgramFixture.check source)

    // Locate generated reads from their semantic operands, independently of
    // the correspondence rows whose absence or alteration these tests check.
    let reads (graph: SemanticGraph) =
        let found =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.FrameRead(_, source) when node.IsReachable ->
                    match graph.Nodes[source] with
                    | { Kind = SemanticKind.Application _; ValueRange = Some range } when range = expected -> Some node
                    | _ -> None
                | _ -> None)
            |> Seq.toList
        Assert.NotEmpty found
        found

    let relation role target (graph: SemanticGraph) =
        graph.Edges |> List.filter (fun edge -> edge.Role = role && edge.Target = target) |> Assert.Single

    let edgeKey (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target

    let admitted graph =
        match Publication.project graph with
        | Result.Ok _ -> ()
        | Result.Error failures -> failwithf "Missing current representation range authority: %A" failures

    let altered defect read (graph: SemanticGraph) =
        let value = relation EdgeRole.ContinuationValue read.Id graph
        let access = relation EdgeRole.ContinuationSlotAccess read.Id graph
        Assert.True(access.Sources.Length >= 6, "The fixture needs an actual scalar slot writer and operand.")
        let source = match read.Kind with SemanticKind.FrameRead(_, source) -> source | _ -> failwith "Missing frame read"
        let otherSource =
            reads graph
            |> List.pick (fun candidate ->
                match candidate.Kind with SemanticKind.FrameRead(_, other) when other <> source -> Some other | _ -> None)
        let replace original changed =
            { graph with Edges = graph.Edges |> List.map (fun edge -> if edgeKey edge = edgeKey original then changed else edge) }
        let alterAccess ordinal replacement =
            replace access { access with Sources = access.Sources |> List.mapi (fun index id -> if index = ordinal then replacement else id) }
        match defect with
        | "missing-value" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> edgeKey edge <> edgeKey value) }
        | "duplicate-value" -> { graph with Edges = value :: graph.Edges }
        | "wrong-value-source" -> replace value { value with Sources = [otherSource] }
        | "wrong-value-ordinal" -> replace value { value with Ordinal = 1 }
        | "missing-access" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> edgeKey edge <> edgeKey access) }
        | "duplicate-access" -> { graph with Edges = access :: graph.Edges }
        | "wrong-access-source" -> alterAccess 3 otherSource
        | "wrong-owner" -> alterAccess 0 access.Sources[1]
        | "wrong-generator" -> alterAccess 1 access.Sources[0]
        | "wrong-storage" -> alterAccess 2 access.Sources[0]
        | "wrong-access-ordinal" -> replace access { access with Ordinal = 1 }
        | "missing-writer" -> replace access { access with Sources = List.take 4 access.Sources }
        | "wrong-writer-value" -> alterAccess 5 otherSource
        | _ -> failwithf "Unknown representation correspondence defect: %s" defect

    let refused graph =
        match Publication.project graph with
        | Result.Error failures -> Assert.NotEmpty failures
        | Result.Ok _ -> failwith "Invalid continuation correspondence crossed numeric publication."

module private RepresentationStorageFixture =
    module Current = Clef.Compiler.PSGSaturation.SemanticGraph.ContinuationCurrentInputs
    module Ingress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress
    module Incidence = Clef.Compiler.Baker.Ingredients.Closures

    let frameAndProtocol (graph: SemanticGraph) =
        graph.Codata.Value.ContinuationFrames.Values
        |> Seq.choose (fun frame -> Current.forOwner graph frame.Owner |> Option.map (fun protocol -> frame, protocol))
        |> Seq.find (fun (frame, _) ->
            graph.Nodes.Values |> Seq.exists (fun node ->
                node.IsReachable && match node.Kind with SemanticKind.FrameRead(_, slot) -> slot = frame.State | _ -> false))

    let stateRead (frame: ContinuationFrame) (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.FrameRead(_, slot) -> slot = frame.State | _ -> false)

    let currentRead owner (graph: SemanticGraph) =
        graph.Edges |> List.pick (fun edge ->
            match edge.Role, edge.Sources, graph.Nodes.TryFind edge.Target with
            | EdgeRole.SequenceElementPayload, [actual; _], Some node when actual = owner && node.IsReachable -> Some node
            | _ -> None)

    let replaceRow before after (graph: SemanticGraph) =
        let edges = graph.Edges |> List.map (fun edge ->
            if RepresentationRangeFixture.edgeKey edge = RepresentationRangeFixture.edgeKey before then after else edge)
        { graph with Edges = edges }

    let removeRow row (graph: SemanticGraph) =
        let edges = graph.Edges |> List.filter (fun edge ->
            RepresentationRangeFixture.edgeKey edge <> RepresentationRangeFixture.edgeKey row)
        { graph with Edges = edges }

    // Change an actual writer and keep its exact structural incidence current.
    // Correspondence proof rows and every held scalar range remain unchanged.
    let replaceWriterValue writer value (graph: SemanticGraph) =
        let node = graph.Nodes[writer]
        let kind =
            match node.Kind with
            | SemanticKind.FrameWrite(frame, slot, _) -> SemanticKind.FrameWrite(frame, slot, value)
            | other -> failwithf "Missing actual storage writer: %A" other
        let children = kindEdges writer kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources
        let changed = { node with Kind = kind; Children = children }
        let retained = graph.Edges |> List.filter (fun edge ->
            edge.Target <> writer || (edge.Class <> EdgeClass.Structural && edge.Class <> EdgeClass.Reference))
        { graph with Nodes = graph.Nodes.Add(writer, changed)
                     Edges = retained @ Incidence.structuralIncidence changed }

    let changedState defect (graph: SemanticGraph) =
        let frame, protocol = frameAndProtocol graph
        let read = stateRead frame graph
        let changed =
            match defect with
            | "initial-entry" ->
                let row = graph.Edges |> List.filter (fun edge ->
                    edge.Role = EdgeRole.SuspensionResume 0 && edge.Sources = [frame.Owner; frame.Generator]) |> Assert.Single
                removeRow row graph
            | "initial-proof-support" ->
                let row = graph.Edges |> List.filter (fun edge ->
                    edge.Role = EdgeRole.Constrains && edge.Sources = [frame.Owner; frame.Generator; frame.State; protocol.InitialEntry]) |> Assert.Single
                replaceRow row { row with Sources = [frame.Owner; frame.Generator; frame.State; read.Id] } graph
            | "writer-support" ->
                let row = RepresentationRangeFixture.relation EdgeRole.ContinuationSlotAccess read.Id graph
                Assert.True(row.Sources.Length > 4)
                replaceRow row { row with Sources = List.take 4 row.Sources } graph
            | "actual-writer" ->
                let writer, value = List.head protocol.StateWrites
                let literal id =
                    match graph.Nodes[id].Kind with
                    | SemanticKind.Literal(NativeLiteral.Int(value, _)) -> Some(bigint value)
                    | SemanticKind.Literal(NativeLiteral.UInt(value, _)) -> Some(bigint value)
                    | _ -> None
                let alternative = protocol.StateWrites |> List.pick (fun (_, candidate) ->
                    if candidate <> value && graph.Nodes[candidate].Type = graph.Nodes[value].Type &&
                       literal candidate <> literal value then Some candidate else None)
                replaceWriterValue writer alternative graph
            | other -> failwithf "Unknown state support defect: %s" other
        Assert.True((Ingress.tryStorageAccess (Ingress.analyze graph) read.Id).IsSome)
        Assert.True((Ingress.tryStorageAccess (Ingress.analyze changed) read.Id).IsNone)
        changed, read

    let changedCurrent defect (graph: SemanticGraph) =
        let frame, protocol = frameAndProtocol graph
        let cut = List.head protocol.Cuts
        let other = protocol.Cuts |> List.find (fun candidate -> candidate.Yield <> cut.Yield)
        let writerRow = RepresentationRangeFixture.relation EdgeRole.ContinuationValue cut.Writer graph
        let cutRow = graph.Edges |> List.filter (fun edge ->
            edge.Target = cut.Yield && edge.Role = EdgeRole.SuspensionCut cut.State) |> Assert.Single
        let changed =
            match defect with
            | "missing-writer-proof" -> removeRow writerRow graph
            | "wrong-writer-proof" -> replaceRow writerRow { writerRow with Sources = [other.Yield] } graph
            | "cut-payload" -> replaceRow cutRow { cutRow with Sources = [frame.Owner; frame.Generator; other.Payload] } graph
            | "actual-writer" ->
                Assert.Equal(graph.Nodes[cut.Value].Type, graph.Nodes[other.Value].Type)
                replaceWriterValue cut.Writer other.Value graph
            | other -> failwithf "Unknown current support defect: %s" other
        Assert.True((Current.forOwner changed frame.Owner).IsNone)
        changed, currentRead frame.Owner graph

    let refusesWithoutChangingCachedRanges (original: SemanticGraph) (changed: SemanticGraph) (read: SemanticNode) =
        RepresentationRangeFixture.admitted original
        for KeyValue(id, node) in original.Nodes do Assert.Equal(node.ValueRange, changed.Nodes[id].ValueRange)
        Assert.True(read.ValueRange |> Option.exists ValueRange.isObservable)
        let before = RepresentationRangeFixture.sourceFacts original
        Assert.True(before.TryFind read.Id |> Option.exists ValueRange.isObservable)
        let current = RepresentationRangeFixture.sourceFacts changed
        Assert.False(current.TryFind read.Id |> Option.exists ValueRange.isObservable)
        RepresentationRangeFixture.refused changed
        let once = RepresentationRangeFixture.normalize changed
        RepresentationRangeFixture.refused once
        let twice = RepresentationRangeFixture.normalize once
        RepresentationRangeFixture.refused twice
        RepresentationRangeFixture.admitted original

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "RepresentationRange")>]
type RepresentationRangeCases() =
    [<Theory>]
    [<InlineData("initial-entry")>]
    [<InlineData("initial-proof-support")>]
    [<InlineData("writer-support")>]
    [<InlineData("actual-writer")>]
    member _.``State ranges retract when initial or live writer support changes despite identical cached ranges`` defect =
        let original = RepresentationRangeFixture.original.Value
        let changed, read = RepresentationStorageFixture.changedState defect original
        RepresentationStorageFixture.refusesWithoutChangingCachedRanges original changed read

    [<Theory>]
    [<InlineData("missing-writer-proof")>]
    [<InlineData("wrong-writer-proof")>]
    [<InlineData("cut-payload")>]
    [<InlineData("actual-writer")>]
    member _.``Sequence current ranges retract when cut or actual write support changes despite identical cached ranges`` defect =
        let original = RepresentationRangeFixture.original.Value
        let changed, read = RepresentationStorageFixture.changedCurrent defect original
        RepresentationStorageFixture.refusesWithoutChangingCachedRanges original changed read

    [<Fact>]
    member _.``Module sequence frame reads preserve the bounded source arithmetic after representation rewriting`` () =
        let graph = RepresentationRangeFixture.original.Value
        let fresh = RepresentationRangeFixture.sourceFacts graph
        for read in RepresentationRangeFixture.reads graph do
            let source = match read.Kind with SemanticKind.FrameRead(_, source) -> source | _ -> failwith "Missing frame read"
            let value = RepresentationRangeFixture.relation EdgeRole.ContinuationValue read.Id graph
            let access = RepresentationRangeFixture.relation EdgeRole.ContinuationSlotAccess read.Id graph
            Assert.Equal(EdgeClass.Provenance, value.Class)
            Assert.Equal(0, value.Ordinal)
            Assert.Equal<NodeId list>([source], value.Sources)
            Assert.Equal(EdgeClass.Provenance, access.Class)
            Assert.Equal(0, access.Ordinal)
            Assert.True(access.Sources.Length >= 4)
            Assert.Equal(source, access.Sources[3])
            Assert.Equal(Some RepresentationRangeFixture.expected, read.ValueRange)
            Assert.Equal(Some RepresentationRangeFixture.expected, fresh.TryFind read.Id)
        RepresentationRangeFixture.admitted graph

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Fresh frame read ranges do not use their cached scalar annotations`` poisoned =
        let graph = RepresentationRangeFixture.original.Value
        let reads = RepresentationRangeFixture.reads graph
        let nodes =
            reads |> List.fold (fun nodes read ->
                let range = if poisoned then Some(ValueRange.point 777I) else None
                Map.add read.Id { read with ValueRange = range } nodes) graph.Nodes
        let changed = { graph with Nodes = nodes }
        let fresh = RepresentationRangeFixture.sourceFacts changed
        for read in reads do
            Assert.Equal(Some RepresentationRangeFixture.expected, fresh.TryFind read.Id)
        RepresentationRangeFixture.admitted graph

    [<Fact>]
    member _.``Repeated numeric settlement preserves current module sequence frame read authority`` () =
        let graph = RepresentationRangeFixture.original.Value
        RepresentationRangeFixture.admitted graph
        let once = RepresentationRangeFixture.normalize graph
        RepresentationRangeFixture.admitted once
        let twice = RepresentationRangeFixture.normalize once
        RepresentationRangeFixture.admitted twice
        for read in RepresentationRangeFixture.reads graph do
            Assert.Equal(Some RepresentationRangeFixture.expected, (RepresentationRangeFixture.sourceFacts twice).TryFind read.Id)

    [<Theory>]
    [<InlineData("missing-value")>]
    [<InlineData("duplicate-value")>]
    [<InlineData("wrong-value-source")>]
    [<InlineData("wrong-value-ordinal")>]
    [<InlineData("missing-access")>]
    [<InlineData("duplicate-access")>]
    [<InlineData("wrong-access-source")>]
    [<InlineData("wrong-owner")>]
    [<InlineData("wrong-generator")>]
    [<InlineData("wrong-storage")>]
    [<InlineData("wrong-access-ordinal")>]
    [<InlineData("missing-writer")>]
    [<InlineData("wrong-writer-value")>]
    member _.``Invalid continuation correspondence cannot retain a bounded read or acquire renewed numeric authority`` defect =
        let graph = RepresentationRangeFixture.original.Value
        let read =
            RepresentationRangeFixture.reads graph
            |> List.find (fun read ->
                (RepresentationRangeFixture.relation EdgeRole.ContinuationSlotAccess read.Id graph).Sources.Length >= 6)
        let changed = RepresentationRangeFixture.altered defect read graph
        Assert.Same(graph.Nodes, changed.Nodes)
        Assert.Equal(Some RepresentationRangeFixture.expected, changed.Nodes[read.Id].ValueRange)
        let fresh = RepresentationRangeFixture.sourceFacts changed
        Assert.Equal(Some ValueRange.Unbounded, fresh.TryFind read.Id)
        RepresentationRangeFixture.refused changed
        let once = RepresentationRangeFixture.normalize changed
        RepresentationRangeFixture.refused once
        let twice = RepresentationRangeFixture.normalize once
        RepresentationRangeFixture.refused twice
        RepresentationRangeFixture.admitted graph

module private MappedRepresentationFixture =
    let source = """
[<EntryPoint>]
let main _ =
    let scale = 2
    let mutable calls = 0
    let mapper = fun value -> calls <- (calls + 1) % 100; value * scale
    let mapped = Seq.map mapper (seq { yield 3<m>; yield 4<m> })
    for value in mapped do ignore value
    calls
"""
    let original = lazy (SequenceProgramFixture.check source)

    let current (graph: SemanticGraph) =
        graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.IteratorCurrentAdmitted && edge.Sources.Length > 3 &&
            graph.Nodes[edge.Target].IsReachable) |> Assert.Single

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "RepresentationRange")>]
type MappedRepresentationRangeCases() =
    [<Fact>]
    member _.``Withdrawing iterator storage evidence retracts both its origin and the pull effect summary`` () =
        let graph = MappedRepresentationFixture.original.Value
        let call, iterator =
            graph.Nodes.Values |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.Application(callee, [iterator]) when node.IsReachable ->
                    match graph.Nodes[callee].Kind, graph.Nodes[iterator].Kind with
                    | SemanticKind.Intrinsic { Module = IntrinsicModule.SeqEnumerator; Operation = "moveNext" }, SemanticKind.FrameRead _ -> Some(node.Id, iterator)
                    | _ -> None
                | _ -> None)
            |> Assert.Single
        let access = RepresentationRangeFixture.relation EdgeRole.ContinuationSlotAccess iterator graph
        let _, originalOrigins = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceOrigins.settle graph graph.Codata.Value.Curry
        Assert.All(originalOrigins[iterator], fun origin ->
            Assert.True(match origin with Clef.Compiler.PSGSaturation.SemanticGraph.SequenceOrigins.Origin.Known _ -> true | _ -> false))
        Assert.NotEmpty(originalOrigins[iterator])
        Assert.Contains(graph.Edges, fun edge -> edge.Target = call && edge.Role = EdgeRole.SequencePullBody)
        Assert.DoesNotContain(graph.Edges, fun edge -> edge.Target = call && edge.Role = EdgeRole.SequenceEffectUnknown)
        let changed = RepresentationStorageFixture.removeRow access graph
        let _, origins = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceOrigins.settle changed changed.Codata.Value.Curry
        Assert.True(origins[iterator] |> Set.exists (function Clef.Compiler.PSGSaturation.SemanticGraph.SequenceOrigins.Origin.Unknown _ -> true | _ -> false))
        let refreshed = Clef.Compiler.Nanopass.SequenceEffects.normalize changed
        Assert.Contains(refreshed.Edges, fun edge -> edge.Target = call && edge.Role = EdgeRole.SequenceEffectUnknown)
        Assert.DoesNotContain(refreshed.Edges, fun edge -> edge.Target = call && edge.Role = EdgeRole.SequencePullBody)
        RepresentationRangeFixture.refused refreshed

    [<Fact>]
    member _.``A generated current on the failed pull branch cannot reuse the successful source guard`` () =
        let graph = MappedRepresentationFixture.original.Value
        let lifted = MappedRepresentationFixture.current graph
        let ingress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.analyze graph
        let branch = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.IfThenElse(condition, _, Some _) ->
                (Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.tryCorrespondence ingress lifted.Sources[2] condition).IsSome
            | _ -> false) |> Assert.Single
        let kind =
            match branch.Kind with
            | SemanticKind.IfThenElse(condition, yes, Some no) -> SemanticKind.IfThenElse(condition, no, Some yes)
            | _ -> failwith "Missing realized guard branch"
        let replacement =
            { branch with Kind = kind
                          Children = kindEdges branch.Id kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources }
        let retained = graph.Edges |> List.filter (fun edge ->
            edge.Target <> branch.Id || (edge.Class <> EdgeClass.Structural && edge.Class <> EdgeClass.Reference))
        let changed =
            { graph with Nodes = graph.Nodes.Add(branch.Id, replacement)
                         Edges = retained @ Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence replacement }
        let owner = graph.Codata.Value.ContinuationFrames.Keys |> Seq.find (fun owner ->
            Clef.Compiler.PSGSaturation.SemanticGraph.ContinuationCurrentInputs.forOwner graph owner
            |> Option.exists (fun protocol -> protocol.Participants.Contains lifted.Target))
        Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.ContinuationCurrentInputs.forOwner changed owner).IsSome,
                    "The cut and storage protocol stays current; the successful-pull branch must be checked separately.")
        Assert.Equal<Map<NodeId, ValueRange option>>(graph.Nodes |> Map.map (fun _ node -> node.ValueRange), changed.Nodes |> Map.map (fun _ node -> node.ValueRange))
        Assert.Equal(Some ValueRange.Unbounded, (RepresentationRangeFixture.sourceFacts changed).TryFind lifted.Target)
        RepresentationRangeFixture.refused changed
        RepresentationRangeFixture.refused (RepresentationRangeFixture.normalize changed)

    [<Fact>]
    member _.``A mapped sequence keeps the source element bound at its generated current and mapper formal`` () =
        let graph = MappedRepresentationFixture.original.Value
        let current = MappedRepresentationFixture.current graph
        let formal = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && node.Kind = SemanticKind.PatternBinding "value") |> Assert.Single
        let fresh = RepresentationRangeFixture.sourceFacts graph
        Assert.Equal(Some(ValueRange.Bounded(3I, 4I)), fresh.TryFind current.Target)
        Assert.Equal(Some(ValueRange.Bounded(3I, 4I)), fresh.TryFind formal.Id)
        RepresentationRangeFixture.admitted graph

    [<Theory>]
    [<InlineData("missing-source-admission")>]
    [<InlineData("missing-lifted-admission")>]
    [<InlineData("duplicate-lifted-admission")>]
    [<InlineData("wrong-source")>]
    [<InlineData("wrong-actual")>]
    member _.``Generated current cannot keep numeric authority after its guarded source correspondence changes`` defect =
        let graph = MappedRepresentationFixture.original.Value
        let lifted = MappedRepresentationFixture.current graph
        let source = RepresentationRangeFixture.relation EdgeRole.IteratorCurrentAdmitted lifted.Sources.Head graph
        let changed =
            match defect with
            | "missing-source-admission" -> RepresentationStorageFixture.removeRow source graph
            | "missing-lifted-admission" -> RepresentationStorageFixture.removeRow lifted graph
            | "duplicate-lifted-admission" -> { graph with Edges = lifted :: graph.Edges }
            | "wrong-source" -> RepresentationStorageFixture.replaceRow lifted { lifted with Sources = lifted.Target :: lifted.Sources.Tail } graph
            | "wrong-actual" ->
                let sources = lifted.Sources |> List.mapi (fun index id -> if index = lifted.Sources.Length - 1 then source.Target else id)
                RepresentationStorageFixture.replaceRow lifted { lifted with Sources = sources } graph
            | _ -> failwithf "Unknown current correspondence defect: %s" defect
        Assert.Same(graph.Nodes, changed.Nodes)
        Assert.Equal(Some(ValueRange.Bounded(3I, 4I)), changed.Nodes[lifted.Target].ValueRange)
        Assert.Equal(Some ValueRange.Unbounded, (RepresentationRangeFixture.sourceFacts changed).TryFind lifted.Target)
        RepresentationRangeFixture.refused changed
        RepresentationRangeFixture.refused (RepresentationRangeFixture.normalize changed)
        RepresentationRangeFixture.admitted graph

module private SequenceProofOwnershipFixture =
    let source = """
let input = seq { yield 10; yield 20 }
let sum () =
    let mutable total = 0
    for value in input do total <- total + value
    total
[<EntryPoint>]
let main _ = if sum () = 30 then 0 else 1
"""

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "RepresentationRange")>]
type SequenceProofOwnershipRepresentationRangeCases() =
    [<Fact>]
    member _.``Loop recognition preserves the sequence owned additive proof and its current dependency account`` () =
        let graph = SequenceProgramFixture.check SequenceProofOwnershipFixture.source
        let proof = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with
            | SemanticKind.Obligation { Kind = "sequence-additive-invariant"; Body = ObligationBody.AdditiveLoopInvariant _ } -> true
            | _ -> false) |> Assert.Single
        let account = graph.SequenceRangeProvenance |> Option.get
        let inputs: Clef.Compiler.Baker.Recipes.LoopRangeRecipes.Inputs =
            { Operators = Map.empty; Assignments = Map.empty; Effects = Map.empty }
        let changed, _ = Clef.Compiler.Nanopass.LoopRanges.recognize inputs graph
        Assert.True(changed.Nodes.ContainsKey proof.Id)
        Assert.Same(proof, changed.Nodes[proof.Id])
        Assert.True(Clef.Compiler.Baker.Ingredients.NumericValues.sequenceRangeCurrent changed account,
                    "Retiring a loop recipe's claims must preserve current sequence-owned evidence.")
        RepresentationRangeFixture.admitted changed

module private SharedMutableRepresentationFixture =
    module Ingress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress

    let expected = ValueRange.Bounded(0I, 7I)
    let source = """
[<EntryPoint>]
let main _ =
    let mutable shared = 0
    let writer = seq {
        shared <- 7
        yield 1
    }
    let reader = seq { yield shared }
    for value in writer do ignore value
    for value in reader do ignore value
    0
"""
    let original = lazy (SequenceProgramFixture.check source)

    let parts (graph: SemanticGraph) =
        let cell = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with SemanticKind.Binding("shared", true, _, _) -> true | _ -> false) |> Assert.Single
        let owners = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.SeqExpr(_, captures) ->
                captures |> List.exists (fun capture -> capture.IsMutable && capture.SourceNodeId = Some cell.Id)
            | _ -> false) |> Seq.toList
        Assert.Equal(2, owners.Length)
        let ingress = Ingress.analyze graph
        let accesses = owners |> List.map (fun owner ->
            let access = Ingress.trySlotAccess ingress owner.Id cell.Id |> Option.defaultWith (fun () ->
                failwithf "Missing checked shared cell access for owner %A" owner.Id)
            Assert.Equal(Some cell.Id, access.SharedCell)
            owner, access)
        let writer, writerAccess = accesses |> List.filter (fun (_, access) -> not access.Inputs.IsEmpty) |> Assert.Single
        let reader, readerAccess = accesses |> List.filter (fun (_, access) -> access.Inputs.IsEmpty) |> Assert.Single
        let read = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.FrameRead(_, slot) when slot = cell.Id ->
                let access = RepresentationRangeFixture.relation EdgeRole.ContinuationSlotAccess node.Id graph
                access.Sources.Head = reader.Id
            | _ -> false) |> Assert.Single
        // This owner must be accounted for without discovering a cell read.
        Assert.DoesNotContain(graph.Edges, fun edge ->
            edge.Role = EdgeRole.ContinuationSlotAccess && edge.Sources.Length >= 4 &&
            edge.Sources.Head = writer.Id && edge.Sources[3] = cell.Id)
        cell, writer, writerAccess, readerAccess, read

    let withdraw defect cell (writer: SemanticNode) (graph: SemanticGraph) =
        let kind =
            match writer.Kind with
            | SemanticKind.SeqExpr(generator, captures) ->
                let changed =
                    match defect with
                    | "missing-capture" -> captures |> List.filter (fun capture -> capture.SourceNodeId <> Some cell)
                    | "wrong-capture-source" ->
                        let initializer = graph.Nodes[cell].Children |> Assert.Single
                        captures |> List.map (fun capture ->
                            if capture.SourceNodeId = Some cell then { capture with SourceNodeId = Some initializer } else capture)
                    | _ -> failwithf "Unknown shared cell support defect: %s" defect
                SemanticKind.SeqExpr(generator, changed)
            | _ -> failwith "Missing actual writer sequence owner"
        let replacement =
            { writer with Kind = kind
                          Children = kindEdges writer.Id kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources }
        let retained = graph.Edges |> List.filter (fun edge ->
            edge.Target <> writer.Id || (edge.Class <> EdgeClass.Structural && edge.Class <> EdgeClass.Reference))
        { graph with Nodes = graph.Nodes.Add(writer.Id, replacement)
                     Edges = retained @ Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence replacement }

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "RepresentationRange")>]
type SharedMutableRepresentationRangeCases() =
    [<Theory>]
    [<InlineData("cell-address")>]
    [<InlineData("unknown-lazy-store")>]
    member _.``Unsupported writable cell exposures withdraw shared read authority without changing the known stores`` defect =
        let graph = SharedMutableRepresentationFixture.original.Value
        let cell, writer, writerAccess, _, read = SharedMutableRepresentationFixture.parts graph
        let borrowerId = NodeId((graph.Nodes.Keys |> Seq.map NodeId.value |> Seq.max) + 1)
        let kind, valueType =
            match defect with
            | "cell-address" -> SemanticKind.CellAddress cell.Id, NativeType.TByref(cell.Type, ByrefKind.InOut)
            | "unknown-lazy-store" ->
                // This operand has no lazy environment/instance authority. The
                // typed logical slot alone must not license an unseen store.
                let environment = cell.Children |> Assert.Single
                let _, value = writerAccess.Inputs |> Assert.Single
                SemanticKind.LazyWrite(environment, cell.Id, value), Types.unitType
            | _ -> failwithf "Unknown shared cell writable exposure: %s" defect
        let borrower =
            { read with Id = borrowerId; Kind = kind; Type = valueType
                        Children = kindEdges borrowerId kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources
                        Parent = None; ValueRange = None }
        let changed =
            { graph with Nodes = graph.Nodes.Add(borrowerId, borrower)
                         Edges = graph.Edges @ Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence borrower }
        // The outside writable exposure does not remove or corrupt any of the
        // actual known stores or the reader's correspondence rows.
        for KeyValue(id, node) in graph.Nodes do Assert.Same(node, changed.Nodes[id])
        for (store, value) in writerAccess.Inputs do
            Assert.Same(graph.Nodes[store], changed.Nodes[store])
            Assert.Same(graph.Nodes[value], changed.Nodes[value])
        let ingress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.analyze changed
        let unsupportedBorrow = defect = "cell-address"
        Assert.Equal(unsupportedBorrow, (Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.trySlotAccess ingress writer.Id cell.Id).IsNone)
        Assert.Equal(unsupportedBorrow, (Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.tryStorageAccess ingress read.Id).IsNone)
        Assert.Equal(Some SharedMutableRepresentationFixture.expected, (RepresentationRangeFixture.sourceFacts graph).TryFind read.Id)
        Assert.Equal(Some ValueRange.Unbounded, (RepresentationRangeFixture.sourceFacts changed).TryFind read.Id)
        RepresentationRangeFixture.refused changed
        RepresentationRangeFixture.refused (RepresentationRangeFixture.normalize changed)

    [<Fact>]
    member _.``Shared cell reads include stores from a second sequence owner that never reads the cell`` () =
        let graph = SharedMutableRepresentationFixture.original.Value
        let cell, _, writer, reader, read = SharedMutableRepresentationFixture.parts graph
        Assert.NotEmpty writer.Inputs
        Assert.Empty reader.Inputs
        let access = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.tryStorageAccess
                         (Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.analyze graph) read.Id |> Option.get
        Assert.Equal(Some cell.Id, access.SharedCell)
        Assert.Empty access.Inputs
        Assert.Equal(None, access.InitialState)
        let fresh = RepresentationRangeFixture.sourceFacts graph
        Assert.Equal(Some SharedMutableRepresentationFixture.expected, fresh.TryFind cell.Id)
        Assert.Equal(Some SharedMutableRepresentationFixture.expected, fresh.TryFind read.Id)
        let poisoned = { graph with Nodes = graph.Nodes.Add(read.Id, { read with ValueRange = Some(ValueRange.point 777I) }) }
        Assert.Equal(Some SharedMutableRepresentationFixture.expected, (RepresentationRangeFixture.sourceFacts poisoned).TryFind read.Id)
        RepresentationRangeFixture.admitted graph

    [<Theory>]
    [<InlineData("missing-capture")>]
    [<InlineData("wrong-capture-source")>]
    member _.``Shared cell range authority withdraws when a write only owner loses its checked storage identity`` defect =
        let graph = SharedMutableRepresentationFixture.original.Value
        let cell, writer, _, _, read = SharedMutableRepresentationFixture.parts graph
        let changed = SharedMutableRepresentationFixture.withdraw defect cell.Id writer graph
        for KeyValue(id, node) in graph.Nodes do Assert.Equal(node.ValueRange, changed.Nodes[id].ValueRange)
        let ingress = Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.analyze changed
        Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.trySlotAccess ingress writer.Id cell.Id).IsNone)
        Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.CallableIngress.tryStorageAccess ingress read.Id).IsSome,
                    "The reader's own correspondence remains valid; complete shared store coverage must still withdraw its range.")
        Assert.Equal(Some SharedMutableRepresentationFixture.expected, (RepresentationRangeFixture.sourceFacts graph).TryFind read.Id)
        Assert.Equal(Some ValueRange.Unbounded, (RepresentationRangeFixture.sourceFacts changed).TryFind read.Id)
        RepresentationRangeFixture.refused changed
        RepresentationRangeFixture.refused (RepresentationRangeFixture.normalize changed)
        RepresentationRangeFixture.admitted graph
[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "RepresentationRange")>]
type ContinuationGuardRangeCases() =
    static let source = """
[<EntryPoint>]
let main _ =
    let values = seq { for value in 1..10 do yield value }
    let limited = Seq.take 2 values
    for value in limited do ignore value
    0
"""
    static let original = lazy (SequenceProgramFixture.check source)
    static let guards graph =
        Clef.Compiler.Baker.Recipes.ContinuationGuardRecipes.forGraph graph (fun _ -> Set.empty, true)
    static let family prefix (graph: SemanticGraph) =
        guards graph |> List.filter (fun fact ->
            match graph.Nodes[fact.Cell].Kind with
            | SemanticKind.Binding(name, true, _, _) -> name.StartsWith(prefix, System.StringComparison.Ordinal)
            | _ -> false)

    [<Theory>]
    [<InlineData("__for_counter", 10)>]
    [<InlineData("__seq_remaining", 2)>]
    member _.``Generated guarded reads derive finite counted and take bounds without cached ranges`` (prefix: string, upper: int) =
        let graph = original.Value
        let facts = family prefix graph
        Assert.NotEmpty facts
        let fresh = RepresentationRangeFixture.sourceFacts graph
        let expected = ValueRange.Bounded(1I, bigint upper)
        let fact = facts |> List.find (fun fact -> fresh.TryFind fact.Read = Some expected)
        let changed =
            { graph with
                Nodes = graph.Nodes |> Map.map (fun id node ->
                    if id = fact.Read then { node with ValueRange = Some(ValueRange.point 777I) } else node) }
        Assert.Equal(Some expected, (RepresentationRangeFixture.sourceFacts changed).TryFind fact.Read)
        RepresentationRangeFixture.admitted graph

    [<Fact>]
    member _.``Swapping a generated counted branch retracts guard authority despite unchanged cached bounds`` () =
        let graph = original.Value
        let fact = family "__for_counter" graph |> List.head
        let sourceGuard = RepresentationRangeFixture.relation EdgeRole.ContinuationValue fact.Guard graph |> fun row -> Assert.Single row.Sources
        let branch = graph.Nodes.Values |> Seq.filter (fun value ->
            value.IsReachable &&
            match value.Kind with
            | SemanticKind.IfThenElse(condition, _, Some _) ->
                match graph.Nodes[condition].Kind with SemanticKind.FrameRead(_, source) -> source = sourceGuard | _ -> false
            | _ -> false) |> Assert.Single
        let kind =
            match branch.Kind with
            | SemanticKind.IfThenElse(condition, yes, Some no) -> SemanticKind.IfThenElse(condition, no, Some yes)
            | _ -> failwith "Missing counted continuation branch"
        let replacement =
            { branch with Kind = kind
                          Children = kindEdges branch.Id kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources }
        let edges = graph.Edges |> List.filter (fun edge ->
            edge.Target <> branch.Id || (edge.Class <> EdgeClass.Structural && edge.Class <> EdgeClass.Reference))
        let changed =
            { graph with Nodes = graph.Nodes.Add(branch.Id, replacement)
                         Edges = edges @ Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence replacement }
        Assert.Equal<Map<NodeId, ValueRange option>>(graph.Nodes |> Map.map (fun _ node -> node.ValueRange), changed.Nodes |> Map.map (fun _ node -> node.ValueRange))
        Assert.DoesNotContain(guards changed, fun candidate -> candidate.Cell = fact.Cell)
        RepresentationRangeFixture.refused changed
        RepresentationRangeFixture.refused (RepresentationRangeFixture.normalize changed)
