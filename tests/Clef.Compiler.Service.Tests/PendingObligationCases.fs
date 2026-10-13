namespace Clef.Compiler.Service.Tests

open System
open System.IO
open Fidelity.Data.JSON
open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.Infrastructure
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module PendingDischarge = Clef.Compiler.Nanopass.ObligationDischarge
module PendingElaboration = Clef.Compiler.Nanopass.ObligationElaboration
module PendingPlatform = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

[<CollectionDefinition("Pending obligation artifact emission", DisableParallelization = true)>]
type PendingObligationCollection() = class end

[<Collection("Pending obligation artifact emission")>]
type PendingObligationCases() =
    let obligation body : ObligationInfo =
        { Id = "pending_order"; Kind = "program-initialization-order"; Logic = "QF_LIA"
          Statement = "initialization before every read"; Source = "pending.clef:4:2"; Refs = []; Body = body }
    let reasons = ["read occurrence has no settled use scope"; "initializer phase is unavailable"]
    let graphOn (checkedGraph: SemanticGraph) body =
        let template = checkedGraph.Nodes.Values |> Seq.head
        let node = { template with Id = NodeId.fresh (); Kind = SemanticKind.Obligation(obligation body)
                                   IsReachable = true; Children = []; Parent = None; Metadata = Map.empty }
        node.Id, { checkedGraph with Nodes = checkedGraph.Nodes.Add(node.Id, node) }
    let graph body =
        graphOn (DimensionalCases.check "[<EntryPoint>]\nlet main _ = 0\n" |> _.Graph) body
    let pendingClaims graph =
        PendingDischarge.ofGraph graph |> List.choose (fun claim ->
            match claim.Body with
            | ObligationBody.Pending missing -> Some(claim, missing)
            | _ -> None)
    let emit graph =
        let inventory =
            match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.completeness graph with
            | [] -> Ok(PendingDischarge.ofGraph graph)
            | failures -> Error(failures |> List.map _.Reason)
        PendingDischarge.emit inventory

    // Extend the existing source authority to exercise the owning declaration
    // reader and source-site elaboration, including declaration withdrawal.
    let readlineAuthority =
        SourcePlatformFixture.authority
            .Replace("type PlatformDescription =", "type BufferSchema = { Name: string; Capacity: int; Space: string; Framing: string; TrimDelimiter: bool }\ntype PlatformDescription =")
            .Replace("Surfaces: BoundarySurface array }", "Surfaces: BoundarySurface array; Buffers: BufferSchema array }")
            .Replace("let description =", "let scratch = { Name = \"scratch\"; Kind = \"ram\"; Capacity = 4096; Alignment = 16; Granularity = 16; Growth = \"fixed\"; Access = \"rw\"; Base = None }\nlet consoleReadln = { Name = \"consoleReadln\"; Capacity = 1024; Space = \"scratch\"; Framing = \"line\"; TrimDelimiter = true }\nlet description =")
            .Replace("Spaces = [| rodata |]", "Spaces = [| rodata; scratch |]")
            .Replace("Surfaces = [| { Endpoints = [| write |] } |]", "Surfaces = [| { Endpoints = [| write |] } |]; Buffers = [| consoleReadln |]")
    let readlineSource = "module PendingInput\n[<EntryPoint>]\nlet main _ = if Sys.readline 0 = \"\" then 0 else 1\n"
    let checkReadline authority source =
        let parse text path =
            match parseStringWithDefaults text path with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Readline fixture parse failed: %A" errors
        let inputs = (authority |> Option.map (fun text -> parse text "write-authority.clef") |> Option.toList) @ [parse source "pending-input.clef"]
        checkParsedInputsWithPlatform inputs (authority |> Option.map (fun _ -> SourcePlatformFixture.platform))
    let inputClaims (enrichment: Clef.Compiler.Baker.Ingredients.Obligations.Enrichment) =
        enrichment.NewNodes |> List.choose (fun node ->
            match node.Kind with
            | SemanticKind.Obligation info when List.contains info.Kind ["buffer-capacity"; "input-buffer-bound"; "input-copy-bound"] -> Some(node, info)
            | _ -> None)
    let readlineSite (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Application(callee, _) ->
                match graph.Nodes[callee].Kind with
                | SemanticKind.Intrinsic info -> info.Module = IntrinsicModule.Sys && info.Operation = "readline"
                | _ -> false
            | _ -> false) |> Assert.Single
    let assertPendingInput (graph: SemanticGraph) reason =
        let enrichment = PendingElaboration.elaborate graph
        let node, info = inputClaims enrichment |> Assert.Single
        let site = readlineSite graph
        Assert.Equal("input_bound_consolereadln", info.Id)
        Assert.Equal(ObligationBody.Pending [reason], info.Body)
        Assert.Equal(site.Range, node.Range)
        Assert.Equal(Clef.Compiler.Baker.Ingredients.Obligations.fmtRange site.Range, info.Source)
        let edge = enrichment.NewEdges |> List.filter (fun edge -> edge.Target = node.Id) |> Assert.Single
        Assert.Equal(EdgeClass.Obligation, edge.Class)
        Assert.Equal(EdgeRole.Constrains, edge.Role)
        let expectedSources = site.Id :: (PendingPlatform.resolve graph |> Option.map _.Node |> Option.toList)
        Assert.Equal<NodeId list>(expectedSources, edge.Sources)
        Assert.Empty(enrichment.Annotated |> List.filter (fun node -> node.Id = site.Id))
        match PendingDischarge.trySmtLib [info] with
        | Ok query -> failwithf "Missing readline premises produced a solver query: %s" query
        | Error unavailable -> Assert.Equal<string list>([reason], (Assert.Single unavailable).MissingPremises)

    [<Fact>]
    member _.``Readline generates declared buffer obligations while physical admission stays refused`` () =
        let checkedGraph = checkReadline (Some readlineAuthority) readlineSource
        let refusal = checkedGraph.Diagnostics |> List.filter (fun diagnostic -> diagnostic.Severity = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.NativeDiagnosticSeverity.Error) |> Assert.Single
        Assert.Equal("CCS8403", refusal.Code)
        Assert.Equal("Source settlement is required before witnessing: BoundaryEmission: Intrinsic/system boundary Sys.readline requires CCS/Baker intrinsic boundary settlement (Layer 1); its source-owned operand and ABI contract is unsettled, and runtime or startup defaults cannot supply it.", refusal.Message)
        let graph = checkedGraph.Graph
        let platform = PendingPlatform.resolve graph |> Option.get
        let buffer = PendingPlatform.bufferNamed "consoleReadln" platform |> Option.get
        let space = PendingPlatform.spaceNamed "scratch" platform |> Option.get
        let site = readlineSite graph
        Assert.Equal(site.Range, refusal.Range)
        Assert.Contains(site.Id, refusal.RelatedNodes)
        let enrichment = PendingElaboration.elaborate graph
        let claims = inputClaims enrichment |> List.map (fun (node, info) -> info.Id, (node, info)) |> Map.ofList
        Assert.Equal(4, claims.Count)
        for anchor, body, sources in
            [ "capacity_positive_consolereadln", ObligationBody.CapacityPositive 1024L, [buffer.Node; space.Node]
              "capacity_consolereadln", ObligationBody.CapacityFits(1024L, 4096L), [buffer.Node; space.Node]
              "input_bound_consolereadln", ObligationBody.InputBufferBound(1024L, 1024L), [site.Id; buffer.Node]
              "input_copy_bound_consolereadln", ObligationBody.InputCopyBound(1024L, 1023L), [site.Id; buffer.Node] ] do
            let node, info = claims[anchor]
            Assert.Equal(body, info.Body)
            let edge = enrichment.NewEdges |> List.filter (fun edge -> edge.Target = node.Id) |> Assert.Single
            Assert.Equal<NodeId list>(sources, edge.Sources)
        let annotated = enrichment.Annotated |> List.filter (fun node -> node.Id = site.Id) |> Assert.Single
        Assert.Equal(MetadataValue.Int64 1024L, annotated.Metadata[BufferMetadata.Capacity])

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Readline retains a source Pending row when its buffer contract is absent`` (hasPlatform: bool) =
        let authority = if hasPlatform then Some(readlineAuthority.Replace("Buffers = [| consoleReadln |]", "Buffers = [||]")) else None
        let reason =
            if hasPlatform then "Sys.readline requires buffer 'consoleReadln', which is not declared in platform 'intrinsic-write-test'."
            else "Sys.readline requires buffer 'consoleReadln', but no source platform declaration is available."
        let graph = (checkReadline authority readlineSource).Graph
        assertPendingInput graph reason

    [<Fact>]
    member _.``An absent readline declaration creates no obligation without a readline use`` () =
        let checkedGraph = checkReadline (Some SourcePlatformFixture.authority) "module PendingInput\n[<EntryPoint>]\nlet main _ = 0\n"
        DimensionalCases.noErrors checkedGraph
        Assert.Empty(PendingElaboration.elaborate checkedGraph.Graph |> inputClaims)

    [<Fact>]
    member _.``Withdrawing the readline declaration retains the source obligation as Pending`` () =
        let graph = (checkReadline (Some readlineAuthority) readlineSource).Graph
        Assert.Equal(4, (PendingElaboration.elaborate graph |> inputClaims).Length)
        let withdrawnAuthority = readlineAuthority.Replace("Buffers = [| consoleReadln |]", "Buffers = [||]")
        let withdrawn = (checkReadline (Some withdrawnAuthority) readlineSource).Graph
        assertPendingInput withdrawn "Sys.readline requires buffer 'consoleReadln', which is not declared in platform 'intrinsic-write-test'."

    [<Fact>]
    member _.``An undeclared readline space retains known facts and a Pending capacity claim`` () =
        let authority = readlineAuthority.Replace("Spaces = [| rodata; scratch |]", "Spaces = [| rodata |]")
        let graph = (checkReadline (Some authority) readlineSource).Graph
        let platform = PendingPlatform.resolve graph |> Option.get
        let buffer = PendingPlatform.bufferNamed "consoleReadln" platform |> Option.get
        let site = readlineSite graph
        let enrichment = PendingElaboration.elaborate graph
        let claims = inputClaims enrichment
        Assert.Equal(4, claims.Length)
        let pendingNode, pending = claims |> List.filter (fun (_, info) -> info.Id = "capacity_consolereadln") |> Assert.Single
        let reason = "The space 'scratch' required by buffer 'consoleReadln' is not declared in platform 'intrinsic-write-test'."
        Assert.Equal(ObligationBody.Pending [reason], pending.Body)
        let edge = enrichment.NewEdges |> List.filter (fun edge -> edge.Target = pendingNode.Id) |> Assert.Single
        Assert.Equal<NodeId list>([site.Id; buffer.Node; platform.Node], edge.Sources)
        for anchor, body in
            [ "capacity_positive_consolereadln", ObligationBody.CapacityPositive 1024L
              "input_bound_consolereadln", ObligationBody.InputBufferBound(1024L, 1024L)
              "input_copy_bound_consolereadln", ObligationBody.InputCopyBound(1024L, 1023L) ] do
            let _, info = claims |> List.filter (fun (_, info) -> info.Id = anchor) |> Assert.Single
            Assert.Equal(body, info.Body)
        match PendingDischarge.trySmtLib (claims |> List.map snd) with
        | Ok query -> failwithf "Unknown space capacity produced a solver query: %s" query
        | Error unavailable -> Assert.Equal<string list>([reason], (Assert.Single unavailable).MissingPremises)

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
        let allPending = pendingClaims retained
        Assert.NotEmpty allPending
        for claim, missing in allPending do
            match PendingDischarge.trySmtLib [claim] with
            | Ok query -> failwithf "Pending claim %s produced a query: %s" claim.Id query
            | Error unavailable ->
                let item = Assert.Single unavailable
                Assert.Equal(claim.Id, item.Anchor)
                Assert.Equal<string list>(missing, item.MissingPremises)
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
            let occurrence, missing =
                unavailable |> List.filter (fst >> (=) id) |> Assert.Single
            Assert.Equal(id, occurrence)
            Assert.Equal<string list>(reasons, missing)
            let expected = allPending |> List.map (fun (claim, missing) ->
                let node = retained.Nodes.Values |> Seq.filter (fun node ->
                    match node.Kind with SemanticKind.Obligation info -> info.Id = claim.Id | _ -> false) |> Assert.Single
                node.Id, missing)
            Assert.Equal(expected.Length, unavailable.Length)
            Assert.Equal<Map<NodeId, string list>>(Map.ofList expected, Map.ofList unavailable)
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
        let _, settled =
            graphOn
                (SourcePlatformFixture.check 64 "pending-emission.clef" "module PendingEmission\n[<EntryPoint>]\nlet main _ = 0\n")
                (ObligationBody.ProgramInitializationOrder(0, 1, [ 1 ]))
        let directory = Path.Combine(Path.GetTempPath(), "clef-pending-obligation-" + Guid.NewGuid().ToString("N"))
        let previous = PhaseConfig.getConfig ()
        Directory.CreateDirectory directory |> ignore
        let queryPath = Path.Combine(directory, "06b_obligations.smt2")
        let unavailablePath = Path.Combine(directory, "06b_obligations.unavailable.json")
        try
            PhaseConfig.enableArtifacts directory [6]
            File.WriteAllText(queryPath, "(assert false)\n(check-sat)\n")
            emit pending
            Assert.False(File.Exists queryPath)
            let unavailable = ArtifactJson.parse(File.ReadAllText unavailablePath)
            let anchors = unavailable |> ArtifactJson.items |> Seq.map (ArtifactJson.field "Anchor" >> ArtifactJson.text) |> Seq.toList
            Assert.Contains("pending_order", anchors)
            Assert.Equal<string list>(pendingClaims pending |> List.map (fun (claim, _) -> claim.Id) |> List.sort, List.sort anchors)
            // Settling the fixture alone cannot erase other generated Pending
            // claims whose platform premises are still absent.
            emit ready
            Assert.False(File.Exists queryPath)
            let remaining = ArtifactJson.parse(File.ReadAllText unavailablePath) |> ArtifactJson.items
                            |> Seq.map (ArtifactJson.field "Anchor" >> ArtifactJson.text) |> Seq.toList
            Assert.NotEmpty remaining
            Assert.DoesNotContain("pending_order", remaining)
            Assert.Equal<string list>(pendingClaims ready |> List.map (fun (claim, _) -> claim.Id) |> List.sort, List.sort remaining)
            // The existing source authority supplies those actual premises;
            // only the fully ready inventory replaces unavailable evidence.
            Assert.Empty(pendingClaims settled)
            emit settled
            Assert.False(File.Exists unavailablePath)
            Assert.Equal(PendingDischarge.smtLib (PendingDischarge.ofGraph settled) + "\n", File.ReadAllText queryPath)
        finally
            PhaseConfig.setConfig previous
            Directory.Delete(directory, true)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Incomplete or empty current inventory withdraws every earlier obligation artifact`` empty =
        let ready =
            SourcePlatformFixture.check 64 "complete-emission.clef" "module CompleteEmission\n[<EntryPoint>]\nlet main _ = 0\n"

        let _, pending = graph (ObligationBody.Pending reasons)
        let complete = Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.completeness
        Assert.Empty(complete ready)
        Assert.Empty(complete pending)

        let current =
            if empty then
                { ready with
                    Nodes = Map.empty
                    Edges = []
                    DeclarationRoots = []
                }
            else
                let claim, info =
                    ready.Nodes
                    |> Map.toList
                    |> List.pick (fun (id, node) ->
                        match node.Kind with
                        | SemanticKind.Obligation info when info.Kind = "numeric-carrier-coverage" -> Some(id, info)
                        | _ -> None)

                let incidence =
                    ready.Edges
                    |> List.find (fun edge -> edge.Role = EdgeRole.Constrains && edge.Target = claim)

                let domain =
                    ready.Edges
                    |> List.pick (fun edge ->
                        match edge.Role with
                        | EdgeRole.NumericDomain domain -> Some domain
                        | _ -> None)

                let site = incidence.Sources |> List.find domain.Required.Contains

                let changed =
                    { ready with
                        Nodes = ready.Nodes.Remove claim
                        Edges =
                            ready.Edges
                            |> List.filter (fun edge -> edge.Target <> claim && not (List.contains claim edge.Sources))
                            |> List.map (fun edge ->
                                match edge.Role with
                                | EdgeRole.NumericDomain domain ->
                                    { edge with
                                        Role =
                                            EdgeRole.NumericDomain
                                                { domain with
                                                    Required = domain.Required.Remove site
                                                }
                                    }
                                | _ -> edge)
                    }

                Assert.Contains(
                    complete changed,
                    fun (_, reason) -> reason.Contains("missing or duplicate claim") && reason.Contains(info.Id)
                )

                changed

        if empty then
            Assert.Empty(PendingDischarge.ofGraph current)
            Assert.Empty(complete current)

        let directory =
            Path.Combine(Path.GetTempPath(), "clef-withdrawn-obligations-" + Guid.NewGuid().ToString("N"))

        let previous = PhaseConfig.getConfig ()
        let artifact name = Path.Combine(directory, name)

        try
            PhaseConfig.enableArtifacts directory [ 6 ]

            for earlier in [ ready; pending ] do
                emit earlier
                Assert.True(File.Exists(artifact "06a_obligations.json"))
                Assert.Equal((pendingClaims earlier).IsEmpty, File.Exists(artifact "06b_obligations.smt2"))
                Assert.Equal(not (pendingClaims earlier).IsEmpty, File.Exists(artifact "06b_obligations.unavailable.json"))
                emit current

                for name in
                    [
                        "06a_obligations.json"
                        "06b_obligations.smt2"
                        "06b_obligations.unavailable.json"
                    ] do
                    Assert.False(File.Exists(artifact name), "Stale obligation artifact survived: " + name)
        finally
            PhaseConfig.setConfig previous

            if Directory.Exists directory then
                Directory.Delete(directory, true)
