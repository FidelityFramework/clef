namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module EmittedCallables = Clef.Compiler.PSGSaturation.SemanticGraph.CallableEmission
module EmittedCarriers = Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers

module internal CallableEmissionFixture =
    let checkedProgram () =
        let source = """
module CallableEmissionFixture
let make (offset: int) =
    ((fun (value: int) -> value + offset): int -> int)
let first = make 3
let second = make 7
[<EntryPoint>]
let main _ = if first 1 + second 2 = 13 then 0 else 1
"""
        LazyResidenceFixture.programWith (Some source)

    let project graph =
        match EmittedCallables.project graph with
        | Result.Ok projection -> projection
        | Result.Error failures -> failwithf "Source callable publication failed: %A" failures

    let componentGraph () =
        let builder = NodeBuilder()
        let formal name ty = builder.Create(SemanticKind.PatternBinding name, ty, dummyRange)
        let unused = formal "unused" Types.boolType
        let sequence = formal "sequence" (NativeType.TSeq Types.boolType)
        let delayed = formal "delayed" (NativeType.TLazy Types.boolType)
        let used = formal "used" Types.boolType
        let result = builder.Create(SemanticKind.VarRef("used", Some used.Id), Types.boolType, dummyRange)
        let make parameters =
            let signature = parameters |> List.foldBack (fun (_, ty, _) result -> NativeType.TFun(ty, result)) <| Types.boolType
            builder.Create(SemanticKind.Lambda(parameters, result.Id, [], None, LambdaContext.RegularClosure), signature, dummyRange,
                           children = (parameters |> List.map (fun (_, _, id) -> id)) @ [result.Id])
        let first = make ["unused", unused.Type, unused.Id; "sequence", sequence.Type, sequence.Id
                          "delayed", delayed.Type, delayed.Id; "used", used.Type, used.Id]
        let second = make ["used", used.Type, used.Id]
        // A single Parent cannot describe the deliberately shared formal.
        builder.SetParent(used.Id, first.Id)
        let raw = builder.Build []
        let inputs: EmittedCarriers.Inputs = { Layouts = Map.empty; Origins = Map.empty; Known = Map.empty }
        let carriers, residuals = EmittedCarriers.settle inputs raw
        Assert.Empty residuals
        let graph = { raw with Codata = lazy { raw.Codata.Value with CallableCarriers = carriers } }
        graph, first.Id, second.Id, unused.Id, sequence.Id, delayed.Id, used.Id

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "CallableEmission")>]
type CallableEmissionCases() =
    [<Fact>]
    member _.``Returned closure occurrence admits identity without admitting another factory call`` () =
        let graph = CallableEmissionFixture.checkedProgram ()
        let projection = CallableEmissionFixture.project graph
        let closures = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && (match node.Kind with SemanticKind.ClosureValue _ -> true | _ -> false)) |> Seq.toList
        Assert.NotEmpty closures
        for closure in closures do
            Assert.Contains(closure.Id, projection.Transports[closure.Id])
        let calls = projection.Carriers.Values |> Seq.filter (fun carrier ->
            carrier.Environment.IsSome && (match graph.Nodes[carrier.Occurrence].Kind with SemanticKind.Application _ -> true | _ -> false)) |> Seq.toList
        Assert.True(calls.Length >= 2)
        let first, second = calls[0], calls[1]
        Assert.Equal(first.Implementation, second.Implementation)
        Assert.Equal(first.Environment, second.Environment)
        Assert.DoesNotContain(first.Occurrence, projection.Transports[second.Occurrence])
        Assert.DoesNotContain(second.Occurrence, projection.Transports[first.Occurrence])

    [<Fact>]
    member _.``Transparent result path keeps every source participant and retracts changed children`` () =
        let graph = CallableEmissionFixture.checkedProgram ()
        let closure = graph.Nodes.Values |> Seq.find (fun node -> node.IsReachable && (match node.Kind with SemanticKind.ClosureValue _ -> true | _ -> false))
        let wrapper kind children = { closure with Id = NodeId.fresh(); Kind = kind; Children = children; Parent = None }
        let inner = wrapper (SemanticKind.TypeAnnotation(closure.Id, closure.Type)) [closure.Id]
        let outer = wrapper (SemanticKind.Sequential [inner.Id]) [inner.Id]
        let graph = { graph with Nodes = graph.Nodes.Add(inner.Id, inner).Add(outer.Id, outer) }
        let inputs: EmittedCarriers.Inputs =
            { Layouts = graph.Codata.Value.EnvironmentLayouts
              Origins = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments.origins graph
              Known = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments.knownCallables graph }
        let carriers, _ = EmittedCarriers.settle inputs graph
        let graph = { graph with Codata = lazy { graph.Codata.Value with CallableCarriers = carriers } }
        let projection = CallableEmissionFixture.project graph
        Assert.Contains(closure.Id, projection.Transports[outer.Id])
        Assert.Contains(inner.Id, projection.Supports[outer.Id])
        Assert.Contains(closure.Id, projection.Supports[outer.Id])
        let changed = { graph with Nodes = graph.Nodes.Add(outer.Id, { outer with Children = [] }) }
        match EmittedCallables.project changed with
        | Result.Error _ -> ()
        | Result.Ok projection ->
            Assert.False(projection.Transports.TryFind outer.Id |> Option.exists (Set.contains closure.Id))

    [<Fact>]
    member _.``Physical formal components retain each component and per-owner positions`` () =
        let graph, first, second, unused, sequence, delayed, used = CallableEmissionFixture.componentGraph ()
        let projection = CallableEmissionFixture.project graph
        Assert.Equal<int list>([0], projection.Arguments[first][unused])
        Assert.Equal<int list>([1; 2], projection.Arguments[first][sequence])
        Assert.Equal<int list>([3; 4], projection.Arguments[first][delayed])
        Assert.Equal<int list>([5], projection.Arguments[first][used])
        Assert.Equal<int list>([0], projection.Arguments[second][used])
        Assert.Contains(first, projection.Supports[first])
        Assert.Contains(used, projection.Supports[first])

    [<Fact>]
    member _.``Physical omission uses current source demand rather than stale held mask`` () =
        let source = """
module CallableOmission
let choose (unused: bool) (used: bool) = used
[<EntryPoint>]
let main _ = if choose false true then 0 else 1
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let projection = CallableEmissionFixture.project graph
        let declaration = projection.Declarations.Values |> Seq.filter (fun value ->
            value.Lookup = value.Implementation &&
            (value.Parameters |> List.map (fun (name, _, _) -> name)) = ["unused"; "used"]) |> Assert.Single
        let formal name = declaration.Parameters |> List.find (fun (actual, _, _) -> actual = name) |> fun (_, _, id) -> id
        Assert.Empty(projection.Arguments[declaration.Implementation][formal "unused"])
        Assert.Equal<int list>([0], projection.Arguments[declaration.Implementation][formal "used"])
        let changed = { graph with Codata = lazy { graph.Codata.Value with OrdinaryDemand = OrdinaryDemandProjection.empty } }
        match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.admit changed with
        | Result.Error _ -> ()
        | Result.Ok _ -> failwith "Stale held omission mask was admitted."
        let prepared =
            match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare changed with
            | Result.Ok value -> value
            | Result.Error failures -> failwithf "Current source demand could not be republished: %A" failures
        Assert.Empty(prepared.Codata.Value.CallableEmission.Arguments[declaration.Implementation][formal "unused"])
        Assert.Equal<int list>([0], prepared.Codata.Value.CallableEmission.Arguments[declaration.Implementation][formal "used"])
