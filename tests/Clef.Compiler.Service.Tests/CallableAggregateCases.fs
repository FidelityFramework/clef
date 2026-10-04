namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module AggregateAccounts = Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts
module AggregatePublication = Clef.Compiler.PSGSaturation.Publication.RevisionPublication

module private CallableAggregateFixture =
    let check body =
        let tag : NumericRepresentation =
            { Name = "int8"; Capability = "native"; Family = "int"; Bits = 8
              MinMagnitude = "-128"; MaxMagnitude = "127"; Boundary = "wrap" }
        let platform =
            { IntrinsicWriteFixture.platform with
                Representations = IntrinsicWriteFixture.platform.Representations.Add(tag.Name, tag) }
        let authority = IntrinsicWriteFixture.authority.Replace(
            "Representations = [| ",
            "Representations = [| { Name = \"int8\"; Capability = \"native\"; Family = \"int\"; Bits = 8; MinMagnitude = \"-128\"; MaxMagnitude = \"127\"; Boundary = \"wrap\" }; ")
        let parse source path =
            match Clef.Compiler.NativeService.parseStringWithDefaults source path with
            | Clef.Compiler.NativeService.ParseSuccess parsed -> parsed
            | Clef.Compiler.NativeService.ParseError errors -> failwithf "%A" errors
        let result = Clef.Compiler.NativeService.checkParsedInputsWithPlatform
                        [parse authority "write-authority.clef"; parse body "callable-aggregate.clef"] (Some platform)
        DimensionalCases.noErrors result
        result.Graph

    let source record =
        if record then
            "module StoredCallable\ntype Holder = { Apply: bool -> bool }\nlet first (value: bool) = value\n[<EntryPoint>]\nlet main _ =\n    let holder = { Apply = first }\n    if holder.Apply true then 0 else 1\n"
        else
            "module StoredCallable\nlet first (value: bool) = value\nlet fallback (value: bool) = false\nlet input () : Result<bool -> bool, bool> = Ok first\n[<EntryPoint>]\nlet main _ = if Result.defaultValue fallback (input ()) true then 0 else 1\n"

type CallableAggregateCases() =
    [<Theory>]
    [<InlineData(true)>]
    [<InlineData(false)>]
    member _.``Closed callable aggregate publishes paired formation and current source accounts`` record =
        let graph = CallableAggregateFixture.check (CallableAggregateFixture.source record)
        let facts = graph.Codata.Value
        Assert.NotEmpty facts.CallableAggregateValues
        for KeyValue(site, values) in facts.CallableAggregateValues do
            Assert.True(AggregateAccounts.current graph site |> Result.isOk)
            for value in values do
                Assert.Equal(0, value.Bytes)
                for alternative in value.Alternatives do
                    let carrier = facts.CallableCarriers[alternative.Carrier]
                    Assert.Equal(carrier.Formation, alternative.Formation)
                    Assert.Equal(carrier.EnvironmentValue, alternative.EnvironmentValue)
                    Assert.Equal(Ok alternative.Contract, carrier.Contract)
        match AggregatePublication.publish graph with
        | Error failures -> failwithf "Callable aggregate publication refused: %A" failures
        | Ok revision ->
            Assert.NotEmpty revision.Codata.CallableAggregateDependencies
            Assert.Equal<Map<Fidelity.PSG.NodeId, Fidelity.PSG.CallableAggregateValue list>>(
                revision.Codata.CallableAggregateValues, revision.Emission.Callable.AggregateValues)

    [<Fact>]
    member _.``Changing a nominal declaration at the same identity withdraws its aggregate account`` () =
        let graph = CallableAggregateFixture.check (CallableAggregateFixture.source true)
        let facts = graph.Codata.Value
        let slot = facts.CallableAggregateSlots.Values |> Seq.find (fun slot -> slot.Declaration.IsSome)
        let declaration = graph.Nodes[slot.Declaration.Value]
        let changedKind =
            match declaration.Kind with
            | SemanticKind.TypeDef(name, TypeDefKind.RecordDef fields, members) ->
                SemanticKind.TypeDef(name, TypeDefKind.RecordDef(fields @ ["Changed", Types.boolType]), members)
            | kind -> failwithf "Expected a nominal record declaration: %A" kind
        let changed = { graph with Nodes = graph.Nodes.Add(declaration.Id, { declaration with Kind = changedKind }) }
        let sites = facts.CallableAggregateValues |> Map.toList |> List.choose (fun (site, rows) ->
            if rows |> List.exists (fun row -> row.Slot = slot.Identity) then Some site else None)
        Assert.NotEmpty sites
        for site in sites do
            Assert.True(AggregateAccounts.current graph site |> Result.isOk)
            Assert.True(AggregateAccounts.current changed site |> Result.isError)
        Assert.True(AggregatePublication.publish changed |> Result.isError)

    [<Fact>]
    member _.``Changed numeric source support preserves results but withdraws the published aggregate account`` () =
        let graph = CallableAggregateFixture.check """
module NumericCallable
type Holder = { Apply: int -> int }
let first (value: int) = value + 1
[<EntryPoint>]
let main _ =
    let holder = { Apply = first }
    if holder.Apply 2 = 3 then 0 else 1
"""
        let publish graph =
            match AggregatePublication.publish graph with
            | Ok revision -> revision
            | Error failures -> failwithf "Publication refused: %A" failures
        let before = publish graph
        Assert.Empty(Fidelity.PSG.Integrity.callableAggregates before)
        let site, account =
            graph.Codata.Value.CallableAggregateDependencies |> Map.toSeq
            |> Seq.find (fun (_, account) -> account.Contracts |> List.exists (fun contract ->
                contract.SourcePremises |> Map.exists (fun id _ ->
                    not graph.Nodes[id].IsReachable &&
                    not (Clef.Compiler.Baker.Ingredients.NumericValues.owned graph.Nodes[id]))))
        let support =
            account.Contracts |> List.collect (fun contract -> contract.SourcePremises.Keys |> Seq.toList)
            |> List.find (fun id ->
                not graph.Nodes[id].IsReachable &&
                not (Clef.Compiler.Baker.Ingredients.NumericValues.owned graph.Nodes[id]))
        let original = graph.Nodes[support]
        let changedNode = {original with Metadata = original.Metadata.Add("CallableAggregate.SupportControl", MetadataValue.String "changed")}
        let changed = {graph with Nodes = graph.Nodes.Add(support, changedNode)}
        Assert.Equal(original.Kind, changedNode.Kind)
        Assert.Equal(original.ValueRange, changedNode.ValueRange)
        Assert.True(AggregateAccounts.current graph site |> Result.isOk)
        Assert.True(AggregateAccounts.current changed site |> Result.isError)
        Assert.True(AggregatePublication.publish changed |> Result.isError)
        // Renew the owners affected by the changed premise in their production
        // order. Numeric results stay equal; current proof identities do not.
        let callable, carrierFailures, flowFailures =
            changed |> Clef.Compiler.Nanopass.NumericSettlement.normalize
            |> Clef.Compiler.Nanopass.CallableBranchSettlement.normalize
        Assert.Empty carrierFailures
        Assert.Empty flowFailures
        let aggregate, aggregateFailures = Clef.Compiler.Nanopass.CallableAggregateSettlement.normalize callable
        let storage = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorage.settle aggregate
        let aggregate = {aggregate with Codata = lazy {aggregate.Codata.Value with ProgramStorage = storage}}
        let settled =
            aggregate |> Clef.Compiler.Nanopass.MemorySettlement.normalize
            |> Clef.Compiler.Nanopass.SpatialSettlement.normalize
            |> Clef.Compiler.Nanopass.BoundarySettlement.normalize
        let renewed, accountFailures = Clef.Compiler.Nanopass.CallableAggregateSettlement.renewAccounts settled
        let prepared =
            match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare renewed with
            | Ok value -> value
            | Error failures -> failwithf "Renewed source preparation refused: %A" failures
        // Closure Representation §2.4: "Unsupported families or storage forms
        // SHALL be diagnosed at commitment". Match NativeService's commitment
        // scope: a declaration's aggregate type is not an executable value.
        // Every excluded residual must have explicit scope/demand evidence.
        let demanded = prepared.Codata.Value.WitnessLiveScope.Value.Occurrences |> Map.keys |> Set.ofSeq
        let deferred =
            match Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.projectValidated prepared with
            | Ok demand -> demand.DeferredOnly
            | Error failures -> failwithf "Renewed demand refused: %A" failures
        let failures = aggregateFailures @ accountFailures |> List.distinct
        let required, excluded = failures |> List.partition (fun failure ->
            demanded.Contains failure.Occurrence && not (deferred.Contains failure.Occurrence))
        Assert.Empty required
        for failure in excluded do
            Assert.True(not (demanded.Contains failure.Occurrence) || deferred.Contains failure.Occurrence)
        let after = publish prepared
        Assert.Empty(Fidelity.PSG.Integrity.callableAggregates after)
        let numericResults (revision: Fidelity.PSG.Revision) =
            revision.Emission.Numeric.Values |> Map.map (fun _ value -> value.Slot, value.Range)
        Assert.Equal<Map<_, _>>(numericResults before, numericResults after)
        let publishedSite = let (NodeId value) = site in Fidelity.PSG.NodeId value
        let oldAccount = before.Emission.Callable.AggregateDependencies[publishedSite]
        let nextAccount = after.Emission.Callable.AggregateDependencies[publishedSite]
        Assert.NotEqual<Fidelity.PSG.CallableAggregateDependencyAccount>(oldAccount, nextAccount)
        let oldClaims = oldAccount.Claims |> List.map fst |> Set.ofList
        Assert.NotEmpty oldClaims
        Assert.Empty(Set.intersect oldClaims (after.CurrentClaims.Keys |> Set.ofSeq))
        let replayed =
            let callable =
                { after.Emission.Callable with
                    AggregateDependencies = after.Emission.Callable.AggregateDependencies.Add(publishedSite, oldAccount) }
            { after with Emission = { after.Emission with Callable = callable } }
        Assert.Contains(Fidelity.PSG.Integrity.callableAggregates replayed, fun violation -> violation.Part.EndsWith ".I6")
        let replayedSource =
            let facts =
                { prepared.Codata.Value with
                    CallableAggregateDependencies = prepared.Codata.Value.CallableAggregateDependencies.Add(site, account) }
            { prepared with Codata = lazy facts }
        Assert.True(AggregateAccounts.current replayedSource site |> Result.isError)
        Assert.True(AggregatePublication.publish replayedSource |> Result.isError)

    [<Fact>]
    member _.``Contract admission refuses missing or misfiled rows without authoring replacements`` () =
        let graph = CallableAggregateFixture.check (CallableAggregateFixture.source true)
        let facts = graph.Codata.Value
        let validate contracts =
            Clef.Compiler.Baker.Ingredients.CallableContracts.validate graph facts.EnvironmentLayouts contracts facts.CallableCarriers
        Assert.Empty(validate facts.CallableContracts)
        let identity, contract = facts.CallableContracts |> Map.toSeq |> Seq.head
        let missing = facts.CallableContracts.Remove identity
        Assert.NotEmpty(validate missing)
        Assert.False(missing.ContainsKey identity)
        let wrongIdentity = facts.CallableCarriers |> Map.keys |> Seq.head
        let misfiled = facts.CallableContracts.Add(identity, {contract with Identity = wrongIdentity})
        Assert.NotEmpty(validate misfiled)
        Assert.Equal(wrongIdentity, misfiled[identity].Identity)

    [<Theory>]
    [<InlineData(true)>]
    [<InlineData(false)>]
    member _.``Spatial declaration shells do not hide unresolved ordinary aggregate uses`` hardware =
        let graph = CallableAggregateFixture.check (CallableAggregateFixture.source true)
        let declaration = graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.Binding("holder", _, _, _) -> true | _ -> false)
        let references = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with SemanticKind.VarRef(_, Some source) -> source = declaration.Id | _ -> false) |> Seq.toList
        Assert.NotEmpty references
        let before = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolveCallableBranches graph
        Assert.True(before.Aggregates.ContainsKey declaration.Id)
        let descriptor = graph.Nodes[Assert.Single declaration.Children]
        let root = if hardware then DeclRoot.HardwareModule else DeclRoot.KernelModule
        let kind =
            match declaration.Kind with
            | SemanticKind.Binding(name, mutableBinding, recursiveBinding, _) ->
                SemanticKind.Binding(name, mutableBinding, recursiveBinding, Some root)
            | _ -> failwith "The source fixture lost its immutable holder declaration."
        // Reachability.hardwareDesignReferences retains the spatial shell and
        // its executable Step, leaving the descriptor as source metadata.
        // WitnessLiveRows.valueFacts gives that shell no runtime value demand.
        // Model that residence here, while retaining real ordinary references
        // as the negative control. This does not manufacture a spatial plan.
        let changed =
            { graph with
                Nodes = graph.Nodes.Add(declaration.Id, { declaration with Kind = kind })
                                   .Add(descriptor.Id, { descriptor with IsReachable = false }) }
        let resolution = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolveCallableBranches changed
        Assert.False(resolution.Aggregates.ContainsKey declaration.Id)
        for reference in references do
            Assert.NotEmpty resolution.Aggregates[reference.Id].UnknownOrigins
        let facts = changed.Codata.Value
        let settled = Clef.Compiler.Baker.Recipes.CallableAggregateRecipes.settle resolution
                        { Carriers = facts.CallableCarriers; Contracts = facts.CallableContracts
                          Flows = facts.CallableFlows; Joins = facts.CallableJoins
                          PreviousSlots = facts.CallableAggregateSlots } changed
        Assert.DoesNotContain(settled.Residuals, fun failure -> failure.Occurrence = declaration.Id)
        // Closure Representation §2.4: "Unsupported families or storage forms
        // SHALL be diagnosed at commitment". Only the declaration shell is
        // exempt; an ordinary value occurrence still needs its formation.
        for reference in references do
            Assert.Contains(settled.Residuals, fun failure ->
                failure.Occurrence = reference.Id && failure.Code = "CCS8414")
