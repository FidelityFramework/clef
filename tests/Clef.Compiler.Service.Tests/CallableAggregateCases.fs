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
