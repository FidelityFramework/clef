namespace Clef.Compiler.Service.Tests

open System
open System.IO
open Fidelity.Data.JSON
open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.Infrastructure
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module PendingDischarge = Clef.Compiler.Nanopass.ObligationDischarge

[<CollectionDefinition("Pending obligation artifact emission", DisableParallelization = true)>]
type PendingObligationCollection() = class end

[<Collection("Pending obligation artifact emission")>]
type PendingObligationCases() =
    let obligation body : ObligationInfo =
        { Id = "pending_order"; Kind = "program-initialization-order"; Logic = "QF_LIA"
          Statement = "initialization before every read"; Source = "pending.clef:4:2"; Refs = []; Body = body }
    let reasons = ["read occurrence has no settled use scope"; "initializer phase is unavailable"]
    let graph body =
        let checkedGraph = DimensionalCases.check "[<EntryPoint>]\nlet main _ = 0\n" |> _.Graph
        let template = checkedGraph.Nodes.Values |> Seq.head
        let node = { template with Id = NodeId.fresh (); Kind = SemanticKind.Obligation(obligation body)
                                   IsReachable = true; Children = []; Parent = None; Metadata = Map.empty }
        node.Id, { checkedGraph with Nodes = checkedGraph.Nodes.Add(node.Id, node) }

    [<Fact>]
    member _.``Pending rows stay in the inventory but cannot produce any solver query`` () =
        let pending = obligation (ObligationBody.Pending reasons)
        let ready = obligation (ObligationBody.ProgramInitializationOrder(0, 1, [1]))
        let ready = { ready with Id = "ready_order" }
        match PendingDischarge.trySmtLib [ready; pending] with
        | Ok query -> failwithf "Incomplete inventory produced a query: %s" query
        | Error unavailable ->
            let item = Assert.Single unavailable
            Assert.Equal(pending.Id, item.Anchor)
            Assert.Equal(pending.Source, item.Source)
            Assert.True(item.MissingPremises = reasons)
        Assert.Throws<InvalidOperationException>(fun () -> PendingDischarge.smtLib [pending] |> ignore) |> ignore
        let id, retained = graph pending.Body
        Assert.Contains(PendingDischarge.ofGraph retained, fun item -> item.Id = pending.Id && item.Body = pending.Body)
        let ledger = ArtifactJson.parse(PendingDischarge.ledgerJson [ready; pending])
        let rows = (ledger |> ArtifactJson.field "obligations" |> ArtifactJson.items) |> Seq.toList
        Assert.Equal("ready", (rows[0] |> ArtifactJson.field "state" |> ArtifactJson.text))
        Assert.Equal("pending", (rows[1] |> ArtifactJson.field "state" |> ArtifactJson.text))
        Assert.Equal(2, (rows[1] |> ArtifactJson.field "missingPremises" |> ArtifactJson.count))
        // Baker owns the unavailable proof account. The copy-only publisher
        // refuses an unprepared graph without forcing its source computations.
        let dispatch = Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.materialize retained |> Result.defaultWith (sprintf "%A" >> failwith)
        match dispatch.Query with
        | Error unavailable ->
            let occurrence, missing = Assert.Single unavailable
            Assert.Equal(id, occurrence)
            Assert.Equal<string list>(reasons, missing)
        | Ok query -> failwithf "Pending source premises produced a dispatch: %s" query
        let blocked = { retained with Codata = lazy (failwith "Pending publication forced semantic analysis") }
        match Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish blocked with
        | Ok _ -> failwith "A pending obligation was published"
        | Error failures ->
            let failure = Assert.Single failures
            Assert.Contains("Source emission admission", failure.Reason)
            Assert.False(blocked.Codata.IsValueCreated)
        Assert.Throws<InvalidOperationException>(fun () ->
            Clef.Compiler.Baker.Ingredients.PublishedFactRows.mapObligationInfo pending |> ignore) |> ignore

    [<Fact>]
    member _.``Pending emission removes stale solver text and settling removes unavailable evidence`` () =
        let _, pending = graph (ObligationBody.Pending reasons)
        let _, ready = graph (ObligationBody.ProgramInitializationOrder(0, 1, [1]))
        let directory = Path.Combine(Path.GetTempPath(), "clef-pending-obligation-" + Guid.NewGuid().ToString("N"))
        let previous = PhaseConfig.getConfig ()
        Directory.CreateDirectory directory |> ignore
        let queryPath = Path.Combine(directory, "06b_obligations.smt2")
        let unavailablePath = Path.Combine(directory, "06b_obligations.unavailable.json")
        try
            PhaseConfig.enableArtifacts directory [6]
            File.WriteAllText(queryPath, "(assert false)\n(check-sat)\n")
            PendingDischarge.emit pending
            Assert.False(File.Exists queryPath)
            let unavailable = ArtifactJson.parse(File.ReadAllText unavailablePath)
            Assert.Equal("pending_order", (unavailable |> ArtifactJson.at 0 |> ArtifactJson.field "Anchor" |> ArtifactJson.text))
            PendingDischarge.emit ready
            Assert.False(File.Exists unavailablePath)
            Assert.Equal(PendingDischarge.smtLib (PendingDischarge.ofGraph ready) + "\n", File.ReadAllText queryPath)
        finally
            PhaseConfig.setConfig previous
            Directory.Delete(directory, true)
