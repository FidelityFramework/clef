namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module ProgramDeclaration = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
module ProgramLayout = Clef.Compiler.PSGSaturation.SemanticGraph.StaticStringLayout
module ProgramObligations = Clef.Compiler.Nanopass.ObligationElaboration

module private ProgramStorageFixture =
    // A selected fabric profile isolates declaration validation from unrelated
    // CPU numeric-representation offerings. No native image is emitted here.
    let context: PlatformContext = {
        PlatformId = "storage-test"; Dimensions = Map.empty; Representations = Map.empty
        EndpointReturns = Map.empty; PlatformLibraryPath = None
        PlatformDescription = Some "StorageAuthority.description"
        PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.singleton (System.IO.Path.GetFullPath "program-storage.clef")
        Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = Some SubstrateKind.FPGA; RuntimeModel = None
        AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None }

    let check source =
        match parseStringWithDefaults source "program-storage.clef" with
        | ParseError errors -> ParseFailure errors
        | ParseSuccess input ->
            let result = checkParsedInputsWithPlatform [input] (Some context)
            if CheckResult.hasErrors result then CheckFailure result else Success result

    let source designation =
        """module StorageAuthority
type MemorySpace = { Name: string; Kind: string; Capacity: int; Alignment: int; Granularity: int; Growth: string; Access: string; Base: int option }
type ProgramLifetimeSpaces = { Immutable: string; Mutable: string option }
type PlatformDescription = { Id: string; Spaces: MemorySpace array; ProgramLifetime: ProgramLifetimeSpaces option }
let image = { Name = "constant-image"; Kind = "rodata"; Capacity = 1024; Alignment = 16; Granularity = 16; Growth = "fixed"; Access = "r"; Base = None }
let state = { Name = "state-storage"; Kind = "data"; Capacity = 1024; Alignment = 16; Granularity = 16; Growth = "fixed"; Access = "rw"; Base = None }
let description = { Id = "storage-test"; Spaces = [| image; state |]; ProgramLifetime = """ + designation + """ }
[<EntryPoint>]
let main _ = if "hello" = "world" then 0 else 1
"""

    let admitted source =
        match check source with
        | Success result ->
            DimensionalCases.noErrors result
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node -> match node.Kind with SemanticKind.Error _ -> true | _ -> false)
            result.Graph
        | CheckFailure result -> failwithf "Expected admitted program storage: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed program storage: %A" errors

    let marked (source: string) =
        let start = source.IndexOf('«')
        let finish = source.IndexOf('»')
        Assert.True(start >= 0 && finish > start)
        let prefix = source.Substring(0, start)
        let position =
            { Line = 1 + (prefix |> Seq.filter ((=) '\n') |> Seq.length)
              Column = prefix.Length - (prefix.LastIndexOf('\n') + 1) }
        let extent = finish - start - 1
        source.Remove(finish, 1).Remove(start, 1),
        { File = "program-storage.clef"; Start = position; End = { position with Column = position.Column + extent } }

    let standard = "Some { Immutable = \"constant-image\"; Mutable = Some \"state-storage\" }"
    let graph () = source standard |> admitted

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ProgramLifetime")>]
type ProgramLifetimeCases() =
    [<Theory>]
    [<InlineData("Some \"state-storage\"", true)>]
    [<InlineData("None", false)>]
    member _.``Named immutable image and optional mutable authority resolve actual declarations`` (mutableName, present) =
        let graph = ProgramStorageFixture.source ("Some { Immutable = \"constant-image\"; Mutable = " + mutableName + " }") |> ProgramStorageFixture.admitted
        let platform = ProgramDeclaration.resolve graph |> Option.get
        let roles = platform.ProgramLifetime |> Option.get
        Assert.Equal(present, roles.Mutable.IsSome)
        Assert.Equal("constant-image", roles.Immutable.Space.Name)
        Assert.Equal("constant-image", graph.StaticStringPool.Value.SpaceName)
        Assert.Equal(roles.Immutable.Space.Node, graph.StaticStringPool.Value.DeclarationNode)
        Assert.Equal(Some "constant-image", ProgramDeclaration.stringOf graph roles.Immutable.Reference)
        match graph.Nodes[roles.Node].Kind with
        | SemanticKind.RecordExpr(fields, _) -> Assert.Equal(Some roles.Immutable.Reference, ProgramDeclaration.field "Immutable" fields)
        | _ -> failwith "Designation lost its actual declaration node"

    [<Fact>]
    member _.``Residence and concrete layout retain selected descriptor designation reference and space``() =
        let graph = ProgramStorageFixture.graph ()
        let platform = ProgramDeclaration.resolve graph |> Option.get
        let expected = ProgramDeclaration.immutableProgramAuthority platform |> Set.ofList
        Assert.Equal(4, expected.Count)
        let evidence = ProgramObligations.elaborate graph
        let literalIds = graph.StaticStringPool.Value.Entries |> List.collect (fun entry -> entry.NodeIds) |> Set.ofList
        let residences = evidence.NewEdges |> List.filter (fun edge -> edge.Role = EdgeRole.Resides && literalIds.Contains edge.Target)
        Assert.Equal(graph.StaticStringPool.Value.Entries.Length, residences.Length)
        for entry in graph.StaticStringPool.Value.Entries do
            residences |> List.filter (fun edge -> List.contains edge.Target entry.NodeIds) |> Assert.Single |> ignore
        for edge in residences do Assert.Equal<Set<NodeId>>(expected, Set.ofList edge.Sources)
        let settled, _ = ProgramObligations.elaborateSettled graph
        let layout = settled.NewNodes |> List.find (fun node -> match node.Kind with SemanticKind.Obligation ob -> ob.Id = "layout_user_strings" | _ -> false)
        let relation = settled.NewEdges |> List.find (fun edge -> edge.Target = layout.Id)
        for source in expected do Assert.Contains(source, relation.Sources)
        for source in literalIds do Assert.Contains(source, relation.Sources)

    [<Fact>]
    member _.``Immutable designation aliases retain the name expression and original space identity``() =
        let source =
            ProgramStorageFixture.source "namedRoles"
            |> fun text -> text.Replace("let description =", "let imageName = \"constant-image\"\nlet namedRoles = Some { Immutable = imageName; Mutable = None }\nlet description =")
        let graph = ProgramStorageFixture.admitted source
        let roles = (ProgramDeclaration.resolve graph).Value.ProgramLifetime.Value
        match graph.Nodes[roles.Immutable.Reference].Kind with
        | SemanticKind.VarRef("imageName", Some definition) ->
            match graph.Nodes[definition].Kind with
            | SemanticKind.Binding("imageName", false, _, _) -> ()
            | kind -> failwithf "Designation lost its immutable source binding: %A" kind
        | kind -> failwithf "Designation replaced the actual name reference: %A" kind
        Assert.Equal("constant-image", graph.StaticStringPool.Value.SpaceName)

    [<Fact>]
    member _.``A runtime factory cannot supply declaration authority``() =
        let marked =
            ProgramStorageFixture.source "«makeRoles ()»"
            |> fun text -> text.Replace("let description =", "let makeRoles () = Some { Immutable = \"constant-image\"; Mutable = None }\nlet description =")
        let source, expected = ProgramStorageFixture.marked marked
        match ProgramStorageFixture.check source with
        | CheckFailure result ->
            let diagnostic = result.Diagnostics |> List.filter (fun diagnostic -> Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error) |> Assert.Single
            Assert.Equal("CCS8206", diagnostic.Code)
            Assert.Contains("ProgramLifetime must be Some literal designation or None", diagnostic.Message)
            Assert.Equal(expected, diagnostic.Range)
            Assert.True(result.Graph.StaticStringPool.IsNone)
        | other -> failwithf "A runtime call became declaration authority: %A" other

    [<Theory>]
    [<InlineData("Some { Immutable = «\"missing\"»; Mutable = None }", "CCS8207", "ProgramLifetime.Immutable names undeclared memory space 'missing'")>]
    [<InlineData("Some { Immutable = \"constant-image\"; Mutable = Some «\"missing\"» }", "CCS8207", "ProgramLifetime.Mutable names undeclared memory space 'missing'")>]
    [<InlineData("Some { Immutable = «\"\"»; Mutable = None }", "CCS8207", "ProgramLifetime.Immutable must name a declared memory space")>]
    [<InlineData("Some { Immutable = \"constant-image\"; Mutable = Some «\"\"» }", "CCS8207", "ProgramLifetime.Mutable must name a declared memory space")>]
    [<InlineData("Some { Immutable = «\"state-storage\"»; Mutable = None }", "CCS8207", "ProgramLifetime.Immutable is incompatible with the declared access of memory space 'state-storage'")>]
    [<InlineData("Some { Immutable = \"constant-image\"; Mutable = Some «\"constant-image\"» }", "CCS8207", "ProgramLifetime.Mutable is incompatible with the declared access of memory space 'constant-image'")>]
    member _.``Invalid named authority is rejected at its exact declaring expression`` (designation, code, message) =
        let source, expected = ProgramStorageFixture.source designation |> ProgramStorageFixture.marked
        match ProgramStorageFixture.check source with
        | CheckFailure result ->
            let diagnostic = result.Diagnostics |> List.filter (fun diagnostic -> Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error) |> Assert.Single
            Assert.Equal(code, diagnostic.Code)
            Assert.Contains(message, diagnostic.Message)
            Assert.Equal(expected, diagnostic.Range)
            Assert.True(result.Graph.StaticStringPool.IsNone)
        | other -> failwithf "Invalid storage authority was not rejected: %A" other

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Missing designation never falls back to a conventional rodata name`` conventionalName =
        let source = ProgramStorageFixture.source "None"
        let source = if conventionalName then source.Replace("constant-image", "rodata") else source
        match ProgramStorageFixture.check source with
        | CheckFailure result ->
            let diagnostic = result.Diagnostics |> List.filter (fun diagnostic -> Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error) |> Assert.Single
            Assert.Equal("CCS8206", diagnostic.Code)
            Assert.Contains("no immutable program-lifetime space designation", diagnostic.Message)
            Assert.True(result.Graph.StaticStringPool.IsNone)
        | other -> failwithf "Missing authority was fabricated: %A" other

    [<Fact>]
    member _.``Duplicate named space is ambiguous and cannot authorize either declaration``() =
        let graph = ProgramStorageFixture.graph ()
        let platform = ProgramDeclaration.resolve graph |> Option.get
        let image = platform.ProgramLifetime.Value.Immutable.Space.Node
        let root = graph.Nodes[platform.Node]
        let fields = match root.Kind with SemanticKind.RecordExpr(fields, _) -> fields | _ -> failwith "Expected descriptor"
        let spacesId = ProgramDeclaration.field "Spaces" fields |> Option.get
        let spaces = graph.Nodes[spacesId]
        let originals = match spaces.Kind with SemanticKind.ArrayExpr items -> items | _ -> failwith "Expected space array"
        let duplicate = { spaces with Kind = SemanticKind.ArrayExpr (originals @ [image]) }
        let damaged = { graph with Nodes = graph.Nodes.Add(spacesId, duplicate) }
        let findings = (ProgramDeclaration.read damaged).Findings
        Assert.Contains(findings, fun finding -> finding.Defect = ProgramDeclaration.DeclarationDefect.Ambiguous && finding.Message.Contains "ProgramLifetime.Immutable")
        let settled, _ = ProgramLayout.settle damaged
        Assert.True(settled.StaticStringPool.IsNone)

    [<Theory>]
    [<InlineData("Immutable")>]
    [<InlineData("Mutable")>]
    member _.``Incomplete designation records fail at their retained declaration identity`` missing =
        let graph = ProgramStorageFixture.graph ()
        let roles = (ProgramDeclaration.resolve graph).Value.ProgramLifetime.Value
        let original = graph.Nodes[roles.Node]
        let fields, name = match original.Kind with SemanticKind.RecordExpr(fields, name) -> fields, name | _ -> failwith "Expected roles"
        let changed = { original with Kind = SemanticKind.RecordExpr(fields |> List.filter (fun (name, _) -> name <> missing), name) }
        let damaged = { graph with Nodes = graph.Nodes.Add(changed.Id, changed) }
        let finding = (ProgramDeclaration.read damaged).Findings |> Assert.Single
        Assert.Equal(ProgramDeclaration.DeclarationDefect.Malformed, finding.Defect)
        Assert.Equal(original.Id, finding.Node)
        Assert.Equal(original.Range, finding.Range)
        let settled, _ = ProgramLayout.settle damaged
        Assert.True(settled.StaticStringPool.IsNone)
