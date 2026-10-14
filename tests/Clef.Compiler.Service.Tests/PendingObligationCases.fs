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
    let foreignModel stated : ForeignResultCoverageModel =
        let hypothesis : ForeignResultHypothesis =
            { Quote = NodeId 4; Declaration = NodeId 1; Identity = "posix-read"
              Version = "profile-1"; Source = "pilot/read"
              Lower = ForeignResultBound.Constant -1I; Upper = ForeignResultBound.Argument 0 }
        { Application = { Declaration = NodeId 1; Call = NodeId 2; Context = [NodeId 5]
                          Hypothesis = if stated then Some hypothesis else None
                          Arguments = [{Index = 0; Node = NodeId 3; Enclosure = ValueRange.Bounded(4I, 4I)}] }
          Role = ForeignResultProofRole.LogicalCoverage; AbiRange = ValueRange.Bounded(-8I, 7I)
          ResultRange = ValueRange.Bounded(-1I, 4I)
          Destination = ValueRange.Bounded(-8I, 7I); DestinationDeclaration = Some(NodeId 6); Abi = Some(NodeId 7)
          AbiIdentity = None; DestinationIdentity = None }
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

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Foreign result projection preserves typed provenance and missing contract remains pending`` stated =
        let model = foreignModel stated
        let mapped = Clef.Compiler.Baker.Ingredients.PublishedFactRows.mapForeignResultCoverageModel model
        Assert.Equal(Fidelity.PSG.NodeId 1, mapped.Application.Declaration)
        Assert.Equal(Fidelity.PSG.NodeId 2, mapped.Application.Call)
        Assert.Equal<Fidelity.PSG.NodeId list>([Fidelity.PSG.NodeId 5], mapped.Application.Context)
        Assert.Equal(ValueRange.Bounded(4I, 4I), model.Application.Arguments.Head.Enclosure)
        Assert.Equal(Fidelity.PSG.ValueRange.Bounded(4I, 4I), mapped.Application.Arguments.Head.Enclosure)
        Assert.Equal(Fidelity.PSG.ForeignResultProofRole.LogicalCoverage, mapped.Role)
        match mapped.Application.Hypothesis with
        | None -> Assert.False stated
        | Some hypothesis ->
            Assert.True stated
            Assert.Equal("profile-1", hypothesis.Version)
            Assert.Equal("pilot/read", hypothesis.Source)
            Assert.Equal(Fidelity.PSG.ForeignResultBound.Constant -1I, hypothesis.Lower)
            Assert.Equal(Fidelity.PSG.ForeignResultBound.Argument 0, hypothesis.Upper)
        let info = obligation (ObligationBody.ForeignResultCoverage model)
        match stated, PendingDischarge.trySmtLib [info] with
        | true, Ok query ->
            let projected = Fidelity.PSG.ForeignResultCoverage.ofModel mapped |> Result.toOption |> Option.get
            let expected = Fidelity.PSG.ForeignResultCoverage.smtLib projected.Conclusion
            Assert.Contains("(assert (= " + info.Id + " " + expected + "))", query)
            Assert.Contains("(declare-fun foreign_arg_0 () Int)", query)
            Assert.Contains("(declare-fun foreign_result () Int)", query)
            Assert.Empty(PendingDischarge.unavailable [info])
        | false, Error rows ->
            let refusal = Assert.Single rows
            Assert.Equal(info.Id, refusal.Anchor)
            Assert.Equal(info.Source, refusal.Source)
            Assert.Equal<string list>(["Foreign result behavior contract is missing"], refusal.MissingPremises)
            let ledger = PendingDischarge.ledgerJson [info]
            Assert.Contains(info.Id, ledger)
            Assert.Contains("\"pending\"", ledger)
            Assert.DoesNotContain("\"ready\"", ledger)
            Assert.Throws<InvalidOperationException>(fun () -> PendingDischarge.smtLib [info] |> ignore) |> ignore
        | result -> failwithf "Wrong foreign projection availability: %A" result

    [<Fact>]
    member _.``Foreign projection distinguishes relevant unknown input and unknown ABI from irrelevant pointer`` () =
        let model = foreignModel true
        let pending reason changed =
            let info = obligation (ObligationBody.ForeignResultCoverage changed)
            match PendingDischarge.trySmtLib [info] with
            | Ok query -> failwithf "Missing premise produced a solver query: %s" query
            | Error rows ->
                let row = Assert.Single rows
                Assert.Equal(info.Id, row.Anchor)
                Assert.Equal(info.Source, row.Source)
                Assert.Equal<string list>([reason], row.MissingPremises)
        pending "Foreign result coverage has no established finite enclosure"
            { model with Application = { model.Application with Arguments = [{model.Application.Arguments.Head with Enclosure = ValueRange.Unbounded}] } }
        for abiRange in [ValueRange.Unbounded; ValueRange.Empty] do
            pending "Foreign result coverage has no established finite ABI enclosure" { model with AbiRange = abiRange }
        for role in [ForeignResultProofRole.LogicalCoverage; ForeignResultProofRole.AbiNarrowing] do
            pending "Foreign result coverage has no actual ABI premise" { model with Role = role; Abi = None }
        let pointer = { Index = 1; Node = NodeId 8; Enclosure = ValueRange.Unbounded }
        let admitted = {model with Application = {model.Application with Arguments = model.Application.Arguments @ [pointer]} }
        match PendingDischarge.trySmtLib [obligation (ObligationBody.ForeignResultCoverage admitted)] with
        | Error rows -> failwithf "Irrelevant pointer was assigned an integer domain: %A" rows
        | Ok query -> Assert.DoesNotContain("foreign_arg_1", query)

    [<Fact>]
    member _.``Contradictory foreign hypothesis and incompatible ABI stay projectable for satisfiability refusal`` () =
        let model = foreignModel true
        let hypothesis = model.Application.Hypothesis.Value
        for changed in
            [ {model with Application = {model.Application with Hypothesis = Some {hypothesis with Lower = ForeignResultBound.Constant 5I; Upper = ForeignResultBound.Constant 4I}}}
              {model with AbiRange = ValueRange.Bounded(5I, 6I)}
              {model with Application = {model.Application with Arguments = [{model.Application.Arguments.Head with Enclosure = ValueRange.Empty}]}}
              {model with ResultRange = ValueRange.Empty}
              {model with Destination = ValueRange.Empty} ] do
            let mapped = Clef.Compiler.Baker.Ingredients.PublishedFactRows.mapForeignResultCoverageModel changed
            let projection = Fidelity.PSG.ForeignResultCoverage.ofModel mapped |> Result.toOption |> Option.get
            let info = obligation (ObligationBody.ForeignResultCoverage changed)
            match PendingDischarge.trySmtLib [info] with
            | Error rows -> failwithf "Known contradictory premises incorrectly became Pending: %A" rows
            | Ok query ->
                Assert.Contains(Fidelity.PSG.ForeignResultCoverage.smtLib projection.Conclusion, query)
                Assert.DoesNotContain("(assert " + Fidelity.PSG.ForeignResultCoverage.smtLib projection.Premises + ")", query)
            Assert.Empty(PendingDischarge.unavailable [info])
            let premiseQuery = Fidelity.PSG.ForeignResultCoverage.premisesQuery projection
            Assert.DoesNotContain(Fidelity.PSG.ForeignResultCoverage.smtLib projection.Claim, premiseQuery)

    [<Fact>]
    member _.``Ordinary ready projection remains available beside foreign plumbing`` () =
        let info = obligation (ObligationBody.IntegerLiteralRange(4I, 4I, 4I))
        match PendingDischarge.trySmtLib [info] with
        | Ok query -> Assert.Contains("(check-sat)", query)
        | Error rows -> failwithf "Existing ready projection became unavailable: %A" rows
        let ledger = PendingDischarge.ledgerJson [info] |> ArtifactJson.parse
        Assert.Equal("1.0", ledger |> ArtifactJson.field "version" |> ArtifactJson.text)
        let text = PendingDischarge.ledgerJson [info]
        Assert.DoesNotContain("\"trustedBase\"", text)
        Assert.DoesNotContain("\"state\"", text)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Foreign ledger records ready role and exactly its external and ABI assumptions`` narrowing =
        let role, name =
            if narrowing then
                ForeignResultProofRole.AbiNarrowing, "abi-narrowing"
            else
                ForeignResultProofRole.LogicalCoverage, "logical-coverage"

        let model =
            { foreignModel true with
                Role = role
                AbiIdentity = Some "source-issued-abi"
            }

        let info = obligation (ObligationBody.ForeignResultCoverage model)
        let ledger = PendingDischarge.ledgerJson [ info ] |> ArtifactJson.parse
        Assert.Equal("1.2", ledger |> ArtifactJson.field "version" |> ArtifactJson.text)

        let row =
            ledger
            |> ArtifactJson.field "obligations"
            |> ArtifactJson.items
            |> Assert.Single

        Assert.Equal(info.Id, row |> ArtifactJson.field "id" |> ArtifactJson.text)
        Assert.Equal(info.Source, row |> ArtifactJson.field "source" |> ArtifactJson.text)
        Assert.Equal(name, row |> ArtifactJson.field "role" |> ArtifactJson.text)
        Assert.Equal("ready", row |> ArtifactJson.field "state" |> ArtifactJson.text)

        let assumptions =
            row |> ArtifactJson.field "trustedBase" |> ArtifactJson.items |> Seq.toList

        Assert.Equal(2, assumptions.Length)
        let hypothesis = assumptions[0]

        for key, expected in
            [
                "kind", "external-execution-hypothesis"
                "identity", "posix-read"
                "version", "profile-1"
                "source", "pilot/read"
                "quote", "4"
                "declaration", "1"
                "lower", "-1"
                "upper", "argument[0]"
            ] do
            Assert.Equal(expected, hypothesis |> ArtifactJson.field key |> ArtifactJson.text)

        let abi = assumptions[1]
        Assert.Equal("stated-target-abi", abi |> ArtifactJson.field "kind" |> ArtifactJson.text)
        Assert.Equal("7", abi |> ArtifactJson.field "node" |> ArtifactJson.text)
        Assert.Equal("source-issued-abi", abi |> ArtifactJson.field "identity" |> ArtifactJson.text)
        Assert.Equal(ValueRange.render model.AbiRange, abi |> ArtifactJson.field "range" |> ArtifactJson.text)
        Assert.DoesNotContain("discharged", PendingDischarge.ledgerJson [ info ])

    [<Fact>]
    member _.``Missing foreign behavior stays pending with only the independently stated ABI assumption``() =
        let model = foreignModel false
        let info = obligation (ObligationBody.ForeignResultCoverage model)
        let ledger = PendingDischarge.ledgerJson [ info ] |> ArtifactJson.parse
        Assert.Equal("1.2", ledger |> ArtifactJson.field "version" |> ArtifactJson.text)

        let row =
            ledger
            |> ArtifactJson.field "obligations"
            |> ArtifactJson.items
            |> Assert.Single

        Assert.Equal(info.Id, row |> ArtifactJson.field "id" |> ArtifactJson.text)
        Assert.Equal(info.Source, row |> ArtifactJson.field "source" |> ArtifactJson.text)
        Assert.Equal("logical-coverage", row |> ArtifactJson.field "role" |> ArtifactJson.text)
        Assert.Equal("pending", row |> ArtifactJson.field "state" |> ArtifactJson.text)

        let abi =
            row |> ArtifactJson.field "trustedBase" |> ArtifactJson.items |> Assert.Single

        Assert.Equal("stated-target-abi", abi |> ArtifactJson.field "kind" |> ArtifactJson.text)
        Assert.Equal("7", abi |> ArtifactJson.field "node" |> ArtifactJson.text)
        Assert.Equal(JsonValue.Null, abi |> ArtifactJson.field "identity")
        Assert.Equal(ValueRange.render model.AbiRange, abi |> ArtifactJson.field "range" |> ArtifactJson.text)

        let reason =
            row
            |> ArtifactJson.field "missingPremises"
            |> ArtifactJson.items
            |> Assert.Single

        Assert.Equal("Foreign result behavior contract is missing", ArtifactJson.text reason)
        Assert.DoesNotContain("discharged", PendingDischarge.ledgerJson [ info ])

    [<Fact>]
    member _.``Range context retains exact boundary declaration census including withdrawn duplicate and malformed rows`` () =
        let _, current = graph (ObligationBody.IntegerLiteralRange(4I, 4I, 4I))
        let node = current.Nodes.Values |> Seq.head |> _.Id
        let declaration : BoundaryDeclaration =
            { Binding = node; Path = [node]; Implementation = node; Formals = [node]; Body = node }
        let row =
            { current.Edges.Head with
                Class = EdgeClass.Boundary
                Role = EdgeRole.BoundaryDeclaration declaration
                Sources = [node]
                Target = node
                Ordinal = 0 }
        let census edges =
            Clef.Compiler.Baker.Ingredients.NumericValues.rangeContextRelations {current with Edges = edges}
            |> Result.defaultWith failwith
        let held = census [row]
        Assert.Equal(SourceRangeRelationKind.BoundaryDeclaration declaration, (Assert.Single held).Kind)
        Assert.NotEqual<SourceRangeRelation list>(held, census [])
        Assert.NotEqual<SourceRangeRelation list>(held, census [row; row])
        Assert.NotEqual<SourceRangeRelation list>(held, census [{row with Role = EdgeRole.BoundaryDeclaration {declaration with Formals = []}}])
        Assert.NotEqual<SourceRangeRelation list>(held, census [{row with Sources = []; Target = NodeId 999999}])
