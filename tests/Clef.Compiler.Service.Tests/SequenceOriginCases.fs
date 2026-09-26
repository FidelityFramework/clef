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
