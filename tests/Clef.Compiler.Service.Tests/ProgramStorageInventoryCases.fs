namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module WritableInventory = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorage
module WritableProjection = Clef.Compiler.PSGSaturation.SemanticGraph.StorageWitness

module private ProgramInventoryFixture =
    let closureSource = """
module ProgramInventory
let make (flag: bool) = fun (value: bool) -> if flag then value else not value
let first = make true
let second = make false
[<EntryPoint>]
let main _ = if first true && second false then 0 else 1
"""

    let graph family =
        match family with
        | "lazy" -> LazyResidenceFixture.programWith None
        | _ -> LazyResidenceFixture.programWith (Some closureSource)

    let allocations (graph: SemanticGraph) =
        graph.Codata.Value.ProgramStorage.Entries.Keys |> Seq.choose (function
            | ProgramStorageIdentity.Allocation id -> Some id | _ -> None) |> Set.ofSeq

    let withoutAuthority (graph: SemanticGraph) =
        { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramValue) }

    let requirePending (sites: Set<NodeId>) (inventory: ProgramStorageInventory) =
        Assert.NotEmpty sites
        for site in sites do
            let identity = ProgramStorageIdentity.Allocation site
            Assert.True(inventory.Unresolved.ContainsKey identity, sprintf "Static allocation %A disappeared" site)
            Assert.False(inventory.Entries.ContainsKey identity, "Missing authority retained an accepted allocation")
        Assert.Empty inventory.Reservations

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ProgramStorageInventory")>]
type ProgramStorageInventoryCases() =
    [<Theory>]
    [<InlineData("closure")>]
    [<InlineData("lazy")>]
    member _.``Lost writable authority retains every static allocation as unresolved`` family =
        let original = ProgramInventoryFixture.graph family
        let sites = ProgramInventoryFixture.allocations original
        let changed = ProgramInventoryFixture.withoutAuthority original
        let current = WritableInventory.settle changed
        ProgramInventoryFixture.requirePending sites current
        Assert.True((WritableInventory.read changed).IsNone)
        let retained = { changed with Codata = lazy { changed.Codata.Value with ProgramStorage = current } }
        Assert.Equal(Some current, WritableInventory.read retained)
        Assert.Equal(Some original.Codata.Value.ProgramStorage, WritableInventory.read original)

    [<Theory>]
    [<InlineData("closure")>]
    [<InlineData("lazy")>]
    member _.``Missing startup cannot turn retained static allocations into an empty inventory`` family =
        let original = ProgramInventoryFixture.graph family
        let changed = { original with Edges = original.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramInitialization) }
        ProgramInventoryFixture.requirePending (ProgramInventoryFixture.allocations original) (WritableInventory.settle changed)

    [<Theory>]
    [<InlineData("closure")>]
    [<InlineData("lazy")>]
    member _.``An empty copied inventory cannot validate after all authorities disappear`` family =
        let original = ProgramInventoryFixture.graph family
        let changed = ProgramInventoryFixture.withoutAuthority original
        let omitted = { changed with Codata = lazy { changed.Codata.Value with ProgramStorage = ProgramStorageInventory.empty } }
        Assert.True((WritableInventory.read omitted).IsNone, "Missing allocations validated as an empty inventory")

    [<Theory>]
    [<InlineData("closure")>]
    [<InlineData("lazy")>]
    member _.``Source storage failures locate current allocations absent from copied inventory`` family =
        let original = ProgramInventoryFixture.graph family
        let changed = ProgramInventoryFixture.withoutAuthority original
        let omitted = { changed with Codata = lazy { changed.Codata.Value with ProgramStorage = ProgramStorageInventory.empty } }
        match WritableProjection.project omitted with
        | Ok _ -> failwith "Missing writable allocation authority was published"
        | Error failures ->
            for site in ProgramInventoryFixture.allocations original do
                Assert.Contains(failures, fun failure ->
                    failure.Occurrence = Some site && failure.Participants.Contains site
                    && failure.Reason.Contains("Writable program inventory"))

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Nonstatic and retired occurrences do not acquire unresolved program storage`` retired =
        let original = ProgramInventoryFixture.graph "closure"
        let sites = ProgramInventoryFixture.allocations original
        let changed = ProgramInventoryFixture.withoutAuthority original
        let excluded =
            if retired then
                { changed with Nodes = changed.Nodes |> Map.map (fun id node -> if sites.Contains id then { node with IsReachable = false } else node) }
            else
                { changed with Codata = lazy { changed.Codata.Value with Escapes = changed.Codata.Value.Escapes |> Map.map (fun id kind -> if sites.Contains id then EscapeKind.StackScoped else kind) } }
        let inventory = WritableInventory.settle excluded
        for site in sites do
            Assert.False(inventory.Unresolved.ContainsKey (ProgramStorageIdentity.Allocation site))
            Assert.False(inventory.Entries.ContainsKey (ProgramStorageIdentity.Allocation site))
