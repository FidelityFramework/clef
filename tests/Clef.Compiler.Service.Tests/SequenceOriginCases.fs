namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module SequenceOrigins = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceOrigins
module EnvironmentOrigins = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments

module private SequenceOriginFixture =
    let check source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        result.Graph

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Binding(actual, _, _, _) -> actual = name || actual.StartsWith(name + "__mono")
            | _ -> false) |> Assert.Single

    let origins graph = SequenceOrigins.settle graph graph.Codata.Value.Curry

/// These source/analysis gates establish origin identity and retained unknown
/// alternatives. They do not grant frame layout, caller-result storage or a
/// covering allocation lifetime to a sequence passed through a callable.
[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceOrigins")>]
type SequenceOriginCases() =
    [<Fact>]
    member _.``Eager sequence origins require the actual well typed reachable operand and retract on edits``() =
        let graph = SequenceOriginFixture.check """
[<EntryPoint>]
let main _ =
    let input = eager (seq { yield 1<m> })
    let alias = input
    ignore alias
    0
"""
        let marker, operand =
            graph.Nodes.Values |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.EagerExpr value when node.IsReachable -> Some(node, graph.Nodes[value])
                | _ -> None) |> Assert.Single
        let alias = SequenceOriginFixture.binding "alias" graph
        let checkOriginal () =
            let unique, _ = SequenceOriginFixture.origins graph
            Assert.Equal(operand.Id, unique[marker.Id])
            Assert.Equal(operand.Id, unique[alias.Id])
        checkOriginal ()
        let malformed =
            [ { graph with Nodes = graph.Nodes.Add(marker.Id, { marker with Children = [] }) }
              { graph with Nodes = graph.Nodes.Add(marker.Id, { marker with Type = NativeType.TSeq Types.boolType }) }
              { graph with Nodes = graph.Nodes.Add(operand.Id, { operand with IsReachable = false }) } ]
        for changed in malformed do
            let unique, facts = SequenceOriginFixture.origins changed
            for id in [marker.Id; alias.Id] do
                Assert.False(unique.ContainsKey id)
                Assert.DoesNotContain(SequenceOrigins.Origin.Known operand.Id, facts[id])
                Assert.Contains(SequenceOrigins.Origin.Unknown marker.Id, facts[id])
        // A different immutable snapshot must not poison the original reading.
        checkOriginal ()

    [<Fact>]
    member _.``Raw sequence storage classification retracts across immutable graph revisions``() =
        let builder = NodeBuilder()
        let ty = NativeType.TSeq Types.boolType
        let owner = builder.Create(SemanticKind.PatternBinding "owner", ty, dummyRange)
        let allocation = builder.Create(SemanticKind.ContinuationAllocate owner.Id, ty, dummyRange)
        let alias = builder.Create(SemanticKind.Binding("storage", false, false, None), ty, dummyRange, children = [allocation.Id])
        let read = builder.Create(SemanticKind.VarRef("storage", Some alias.Id), ty, dummyRange)
        let graph = builder.Build []
        let shape = Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers.valueShape
        Assert.Equal(CallableValueShape.Data read.Id, shape graph read)
        let replacement = { graph.Nodes[allocation.Id] with Kind = SemanticKind.PatternBinding "sourceSequence" }
        let changed = { graph with Nodes = graph.Nodes.Add(allocation.Id, replacement) }
        Assert.Equal(CallableValueShape.Sequence read.Id, shape changed read)
        Assert.Equal(CallableValueShape.Data read.Id, shape graph read)

    [<Fact>]
    member _.``One consumer formal retains populated and empty origins through its aliases``() =
        let graph = SequenceOriginFixture.check """
let inspect (items: seq<int<m>>) =
    let forwarded = items
    Seq.tryHead forwarded
[<EntryPoint>]
let main _ =
    let input = seq { yield 1<m> }
    let empty: seq<int<m>> = seq { () }
    ignore (inspect input)
    ignore (inspect empty)
    0
"""
        let unique, _ = SequenceOriginFixture.origins graph
        let input, empty = SequenceOriginFixture.binding "input" graph, SequenceOriginFixture.binding "empty" graph
        let expected = Set.ofList [unique[input.Id]; unique[empty.Id]]
        Assert.Equal(2, expected.Count)
        let formal = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && node.Kind = SemanticKind.PatternBinding "items") |> Assert.Single
        let forwarded = SequenceOriginFixture.binding "forwarded" graph
        for participant in [formal; forwarded] do
            Assert.False(unique.ContainsKey participant.Id)
            let flow = graph.Codata.Value.SequenceFlows[participant.Id]
            Assert.Equal(participant.Id, flow.Occurrence)
            Assert.False(flow.IsEnumerator)
            Assert.Equal<Set<NodeId>>(expected, flow.Owners)
            Assert.Empty(flow.Unknown)
            match participant.Type with
            | NativeType.TSeq element -> DimensionalCases.same element flow.ElementType
            | ty -> failwithf "Lost sequence participant type: %A" ty
        let iterators = graph.Codata.Value.SequenceFlows.Values |> Seq.filter (fun flow ->
            flow.IsEnumerator && flow.Owners = expected) |> Seq.toList
        Assert.NotEmpty(iterators)
        for iterator in iterators do Assert.Empty(iterator.Unknown)

    [<Fact>]
    member _.``Constructor-free reference cycles remain unknown flow instead of an empty admitted family``() =
        let builder = NodeBuilder()
        let ty = NativeType.TSeq Types.boolType
        let first = builder.Create(SemanticKind.PatternBinding "first", ty, dummyRange)
        let second = builder.Create(SemanticKind.VarRef("first", Some first.Id), ty, dummyRange)
        let raw = builder.Build []
        let first = { first with Kind = SemanticKind.VarRef("second", Some second.Id) }
        let graph = { raw with Nodes = raw.Nodes.Add(first.Id, first) }
        let flows = SequenceOrigins.settleFlows graph graph.Codata.Value.Curry
        for participant in [first.Id; second.Id] do
            Assert.Empty(flows[participant].Owners)
            Assert.Equal<Set<NodeId>>(Set.singleton participant, flows[participant].Unknown)

    [<Fact>]
    member _.``Stored returned callable carries the supplied sequence to its own result boundary``() =
        let graph = SequenceOriginFixture.check """
[<EntryPoint>]
let main _ =
    let input = seq { yield 1<m> }
    let factory = fun () -> fun (items: seq<int<m>>) -> items
    let stored = factory ()
    let observed = stored input
    ignore observed
    0
"""
        let unique, facts = SequenceOriginFixture.origins graph
        let input, observed = SequenceOriginFixture.binding "input" graph, SequenceOriginFixture.binding "observed" graph
        let owner = unique[input.Id]
        Assert.Equal(owner, unique[observed.Id])
        Assert.Equal<Set<SequenceOrigins.Origin>>(Set.singleton (SequenceOrigins.Origin.Known owner), facts[observed.Id])

    [<Fact>]
    member _.``Stored producer result retains its own constructor and the input origin at its formal``() =
        let graph = SequenceOriginFixture.check """
[<EntryPoint>]
let main _ =
    let input = seq { yield 1<m> }
    let stored = Seq.map (fun (value: int<m>) -> value)
    let observed = stored input
    ignore observed
    0
"""
        let unique, _ = SequenceOriginFixture.origins graph
        let input, observed = SequenceOriginFixture.binding "input" graph, SequenceOriginFixture.binding "observed" graph
        let inputOwner, resultOwner = unique[input.Id], unique[observed.Id]
        Assert.NotEqual(inputOwner, resultOwner)
        match graph.Nodes[resultOwner].Kind with SemanticKind.SeqExpr _ -> () | kind -> failwithf "Result origin is not its constructor: %A" kind
        let calls = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
        let target = calls.Calls.Values |> Seq.collect _.Targets |> Seq.filter (fun target ->
            List.contains input.Id target.Arguments ||
            target.Arguments |> List.exists (fun argument -> unique.TryFind argument = Some inputOwner)) |> Assert.Single
        let formal = target.Parameters |> List.choose (fun (_, ty, id) -> match ty with NativeType.TSeq _ -> Some id | _ -> None) |> Assert.Single
        Assert.Equal(inputOwner, unique[formal])

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Alternative callable results retain every constructor and any opaque alternative`` opaque =
        let alternative = if opaque then "opaque" else "(fun () -> seq { yield 2<m> })"
        let graph = SequenceOriginFixture.check $"""
let inspect (choose: bool) (opaque: unit -> seq<int<m>>) =
    let selected = if choose then (fun () -> seq {{ yield 1<m> }}) else {alternative}
    let observed = selected ()
    ignore observed
[<EntryPoint>]
let main _ = ignore inspect; 0
"""
        let unique, facts = SequenceOriginFixture.origins graph
        let observed = SequenceOriginFixture.binding "observed" graph
        Assert.False(unique.ContainsKey observed.Id)
        let known, unknown = facts[observed.Id] |> Set.toList |> List.partition (function SequenceOrigins.Origin.Known _ -> true | _ -> false)
        Assert.Equal((if opaque then 1 else 2), known.Length)
        Assert.Equal(opaque, not unknown.IsEmpty)
        let flow = graph.Codata.Value.SequenceFlows[observed.Id]
        Assert.Equal(observed.Id, flow.Occurrence)
        Assert.Equal(known.Length, flow.Owners.Count)
        Assert.Equal(unknown.Length, flow.Unknown.Count)
        Assert.False(flow.IsEnumerator)
        for origin in known do
            match origin with
            | SequenceOrigins.Origin.Known owner ->
                match graph.Nodes[owner].Kind with SemanticKind.SeqExpr _ -> () | kind -> failwithf "Not a sequence constructor: %A" kind
            | _ -> failwith "Unexpected unknown in known partition"

    [<Theory>]
    [<InlineData("valid")>]
    [<InlineData("missing")>]
    [<InlineData("mutable")>]
    [<InlineData("foreign-environment")>]
    member _.``Sequence capture origin requires its exact immutable environment initializer`` variant =
        let builder = NodeBuilder()
        let sequenceType = NativeType.TSeq Types.boolType
        let unitBody = builder.Create(SemanticKind.Literal NativeLiteral.Unit, Types.unitType, dummyRange)
        let parameter = builder.Create(SemanticKind.PatternBinding "frame", NativeType.TNativePtr sequenceType, dummyRange)
        let generator = builder.Create(SemanticKind.Lambda(["frame", parameter.Type, parameter.Id], unitBody.Id,
            [], None, LambdaContext.SeqGenerator), NativeType.TFun(parameter.Type, Types.boolType), dummyRange)
        let sequence = builder.Create(SemanticKind.SeqExpr(generator.Id, []), sequenceType, dummyRange)
        let slot = builder.Create(SemanticKind.Binding("captured", false, false, None), sequenceType,
                                  dummyRange, children = [sequence.Id])
        let owner = builder.Create(SemanticKind.PatternBinding "owner", Types.unitType, dummyRange)
        let environment = builder.Create(SemanticKind.EnvironmentCreate(owner.Id, [slot.Id, sequence.Id]),
                                         EnvironmentOrigins.environmentType, dummyRange)
        let foreign = builder.Create(SemanticKind.PatternBinding "foreign", EnvironmentOrigins.environmentType, dummyRange)
        let selected = if variant = "foreign-environment" then foreign.Id else environment.Id
        let read = builder.Create(SemanticKind.EnvironmentRead(selected, slot.Id), sequenceType, dummyRange)
        let raw = builder.Build []
        let edge = { Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentCapture (variant = "mutable")
                     Sources = [owner.Id; slot.Id; sequence.Id]; Target = environment.Id; Ordinal = 0 }
        let graph = { raw with Edges = if variant = "missing" then [] else [edge] }
        let unique, facts = SequenceOriginFixture.origins graph
        if variant = "valid" then
            Assert.Equal(sequence.Id, unique[read.Id])
            Assert.Equal<Set<SequenceOrigins.Origin>>(Set.singleton (SequenceOrigins.Origin.Known sequence.Id), facts[read.Id])
        else
            Assert.False(unique.ContainsKey read.Id)
            Assert.Equal<Set<SequenceOrigins.Origin>>(Set.singleton (SequenceOrigins.Origin.Unknown read.Id), facts[read.Id])
