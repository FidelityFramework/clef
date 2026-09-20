namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module ByteStorage = Clef.Compiler.PSGSaturation.SemanticGraph.StringByteStorage

module private EncodingFixture =
    let file = "string-encoding.clef"
    let prelude = "module StringEncoding\n"
    // These are declared offerings of this test platform, not an encoding
    // fallback selected by the test or a source width annotation.
    let byteRepresentation = "uint8"
    let platform: PlatformContext =
        let byteRep: NumericRepresentation =
            { Name = byteRepresentation; Capability = "native"; Family = "uint"; Bits = 8
              MinMagnitude = "0"; MaxMagnitude = "255"; Boundary = "wrap" }
        let integerRep: NumericRepresentation =
            { Name = "int64"; Capability = "native"; Family = "int"; Bits = 64
              MinMagnitude = "-9223372036854775808"; MaxMagnitude = "9223372036854775807"; Boundary = "wrap" }
        let nonnegativeRep: NumericRepresentation =
            { Name = "uint64"; Capability = "native"; Family = "uint"; Bits = 64
              MinMagnitude = "0"; MaxMagnitude = "18446744073709551615"; Boundary = "wrap" }
        { PlatformId = "encoding-test"; Dimensions = Map.ofList ["Pointer", 64; "Register", 64]
          Representations = [byteRep; integerRep; nonnegativeRep] |> List.map (fun rep -> rep.Name, rep) |> Map.ofList
          EndpointReturns = Map.empty; PlatformLibraryPath = None; PlatformDescription = Some "EncodingPlatform.description"
          PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.singleton (System.IO.Path.GetFullPath "encoding-platform.clef")
          Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
          AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None }

    let declaration (context: PlatformContext) =
        let widths = context.Dimensions |> Map.toList |> List.map (fun (name, bits) -> sprintf "{ Name=\"%s\"; Bits=%d }" name bits) |> String.concat "; "
        let representations =
            context.Representations.Values
            |> Seq.map (fun rep ->
                sprintf "{ Name=\"%s\"; Capability=\"%s\"; Family=\"%s\"; Bits=%d; MinMagnitude=\"%s\"; MaxMagnitude=\"%s\"; Boundary=\"%s\" }"
                    rep.Name rep.Capability rep.Family rep.Bits rep.MinMagnitude rep.MaxMagnitude rep.Boundary)
            |> String.concat "; "
        """module EncodingPlatform
type WidthDeclaration = { Name: string; Bits: int }
type Representation = { Name: string; Capability: string; Family: string; Bits: int; MinMagnitude: string; MaxMagnitude: string; Boundary: string }
type TargetCore = { Widths: WidthDeclaration array; Representations: Representation array }
type MemorySpace = { Name: string; Kind: string; Capacity: int; Alignment: int; Granularity: int; Growth: string; Access: string; Base: int option }
type ProgramLifetimeSpaces = { Immutable: string; Mutable: string option }
type PlatformDescription = { Id: string; Core: TargetCore option; Spaces: MemorySpace array; ProgramLifetime: ProgramLifetimeSpaces option }
let image = { Name="encoding-image"; Kind="rodata"; Capacity=4096; Alignment=16; Granularity=16; Growth="fixed"; Access="r"; Base=None }
let core: TargetCore = { Widths = [| """ + widths + " |]; Representations = [| " + representations + """ |] }
let description = { Id="encoding-test"; Core=Some core; Spaces=[|image|]; ProgramLifetime=Some { Immutable="encoding-image"; Mutable=None } }
"""

    let checkWith context body =
        let parse path source =
            match parseStringWithDefaults source path with
            | ParseError errors -> failwithf "Encoding fixture did not parse: %A" errors
            | ParseSuccess input -> input
        let inputs =
            [ match context with
              | Some selected -> yield parse "encoding-platform.clef" (declaration selected)
              | None -> ()
              yield parse file (prelude + body) ]
        checkParsedInputsWithPlatformAndSources inputs context (Set.singleton (System.IO.Path.GetFullPath file))

    let check body = checkWith (Some platform) body

    let admitted body =
        let result = check body
        Assert.False(CheckResult.hasErrors result, sprintf "%A" result.Diagnostics)
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            match node.Kind with SemanticKind.Error _ -> true | _ -> false)
        // Late formation preserves provenance without keeping the replaced
        // intrinsic alive as an orphan executable operation.
        for node in result.Graph.Nodes.Values do
            match node.Kind with
            | SemanticKind.Intrinsic { Module = IntrinsicModule.String; Operation = operation }
                when node.IsReachable && (operation = "fromBytes" || operation = "toBytes") ->
                Assert.Contains(result.Graph.Nodes.Values, fun useSite ->
                    useSite.IsReachable &&
                    match useSite.Kind with
                    | SemanticKind.Application(callee, _) -> callee = node.Id
                    | _ -> false)
            | _ -> ()
        result.Graph

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
        |> Assert.Single

    let value name (graph: SemanticGraph) = graph.Nodes[(binding name graph).Children |> Assert.Single]

    let allocation name graph =
        Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.valueOf graph (value name graph).Id
        |> Option.defaultWith (fun () -> failwithf "Missing allocation for %s" name)

    let sameEdge (expected: Hyperedge) (actual: Hyperedge) =
        Assert.Equal(expected.Target, actual.Target)
        Assert.Equal(expected.Role, actual.Role)
        Assert.Equal(expected.Class, actual.Class)
        Assert.Equal(expected.Ordinal, actual.Ordinal)
        Assert.Equal<NodeId list>(expected.Sources, actual.Sources)

    let span (source: string) (expression: string) =
        let start = source.IndexOf(expression, System.StringComparison.Ordinal)
        Assert.True(start >= 0, expression)
        let position (prefix: string) =
            let lines = prefix.Split('\n')
            { Line = lines.Length; Column = (Array.last lines).Length }
        { File = file; Start = position (source.Substring(0, start))
          End = position (source.Substring(0, start + expression.Length)) }

    let storageEdges (graph: SemanticGraph) =
        graph.Edges |> List.filter (fun edge ->
            match edge.Role with EdgeRole.StringByteStorage _ -> true | _ -> false)

    let evidence body expression (graph: SemanticGraph) =
        let expectedRange = span (prelude + body) expression
        let edges = storageEdges graph
        Assert.NotEmpty edges
        for edge in edges do
            match edge.Role, edge.Sources with
            | EdgeRole.StringByteStorage(lower, upper, representation), site :: operand :: origin :: _ ->
                Assert.True(0I <= lower && lower <= upper && upper <= 255I)
                Assert.Equal(byteRepresentation, representation)
                Assert.Equal<SourceRange>(expectedRange, graph.Nodes[site].Range)
                Assert.True(graph.Nodes.ContainsKey operand)
                Assert.True(graph.Nodes.ContainsKey origin)
                Assert.Equal(Some (SettledSlot.Integer(8, Some byteRepresentation)), ByteStorage.element graph edge.Target)
            | other -> failwithf "Incomplete encoding evidence: %A" other
            for participant in edge.Target :: edge.Sources do
                Assert.True(graph.Nodes.ContainsKey participant, sprintf "Missing encoding participant %A" participant)
        edges

    let rejectedWith context reason body expression =
        let result = checkWith context body
        Assert.True(CheckResult.hasErrors result, "Invalid encoding input reached successful checking")
        let diagnostic =
            result.Diagnostics
            |> List.filter (fun diagnostic -> Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)
            |> Assert.Single
        Assert.Equal("CCS8404", diagnostic.Code)
        Assert.Equal<SourceRange>(span (prelude + body) expression, diagnostic.Range)
        Assert.Equal("String.fromBytes requires proved byte storage: " + reason, diagnostic.Message)
        Assert.Empty(storageEdges result.Graph)

    let rejected reason body expression = rejectedWith (Some platform) reason body expression
    let byteReason = "every stored integer must be proved within 0..255."
    let textReason = "text must be proved ASCII or an immutable constant valid UTF-8 sequence."
    let closedReason = "the array must have a closed allocation and known writes; an unknown origin or escaping alias is not admitted."

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "StringEncoding")>]
type StringEncodingCases() =
    [<Fact>]
    member _.``Source only checking retains logical encoding without inventing physical storage``() =
        let result = EncodingFixture.checkWith None "[<EntryPoint>]\nlet main _ =\n    let text = String.fromBytes [| 65 |]\n    String.length text\n"
        Assert.False(CheckResult.hasErrors result, sprintf "%A" result.Diagnostics)
        Assert.Empty(EncodingFixture.storageEdges result.Graph)
        Assert.DoesNotContain(result.Graph.Edges, fun edge -> edge.Role = EdgeRole.StringByteSnapshot || edge.Role = EdgeRole.StringByteRead)
        let site = EncodingFixture.value "text" result.Graph
        DimensionalCases.same Types.stringType site.Type
        match site.Kind with
        | SemanticKind.Application(callee, [input]) ->
            DimensionalCases.same (NativeType.TApp(Types.arrayTyCon, [Types.intType])) result.Graph.Nodes[input].Type
            match result.Graph.Nodes[callee].Kind with
            | SemanticKind.Intrinsic { Module = IntrinsicModule.String; Operation = "fromBytes" } -> ()
            | other -> failwithf "Logical encoding operation was lost: %A" other
        | other -> failwithf "Source-only encoding was physically elaborated: %A" other

    [<Fact>]
    member _.``Selected platform without an octet offering cannot invent encoding storage``() =
        let platform = { EncodingFixture.platform with Representations = EncodingFixture.platform.Representations.Remove EncodingFixture.byteRepresentation }
        EncodingFixture.rejectedWith (Some platform)
            "the platform must offer an unsigned 8-bit representation."
            "[<EntryPoint>]\nlet main _ =\n    let bytes: int array = [| 65 |]\n    let text = String.fromBytes bytes\n    String.length text\n"
            "String.fromBytes bytes"

    [<Fact>]
    member _.``ASCII and multibyte text retain exact storage and source participants``() =
        let body = "[<EntryPoint>]\nlet main _ =\n    let bytes: int array = [| 0; 127; 195; 169 |]\n    let observed = bytes[1]\n    let text = String.fromBytes bytes\n    if observed = 127 then String.length text else 0\n"
        let graph = EncodingFixture.admitted body
        let origin = EncodingFixture.allocation "bytes" graph
        let edges = EncodingFixture.evidence body "String.fromBytes bytes" graph
        Assert.Contains(edges, fun edge -> List.contains origin.Id edge.Sources)
        DimensionalCases.same (NativeType.TApp(Types.arrayTyCon, [Types.intType])) origin.Type
        let observed = EncodingFixture.value "observed" graph
        let read = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.StringByteRead && edge.Target = observed.Id) |> Assert.Single
        Assert.Contains(origin.Id, read.Sources)
        Assert.Equal<SourceRange>(EncodingFixture.span (EncodingFixture.prelude + body) "bytes[1]", observed.Range)
        Assert.True(observed.ValueRange |> Option.exists (ValueRange.contains (ValueRange.bounded 0I 255I)))

    [<Theory>]
    [<InlineData("-1")>]
    [<InlineData("256")>]
    member _.``Out of domain integers fail at the full encoding call`` value =
        let body = $"[<EntryPoint>]\nlet main _ =\n    let bytes: int array = [| {value} |]\n    let text = String.fromBytes bytes\n    String.length text\n"
        EncodingFixture.rejected EncodingFixture.byteReason body "String.fromBytes bytes"

    [<Fact>]
    member _.``Encoding units are dimensionless before physical storage selection``() =
        let body = "[<Measure>] type m\n[<EntryPoint>]\nlet main _ =\n    let bytes: int<m> array = [| 65<m> |]\n    let text = String.fromBytes bytes\n    String.length text\n"
        let result = EncodingFixture.checkWith None body
        Assert.True(CheckResult.hasErrors result)
        let diagnostic =
            result.Diagnostics
            |> List.filter (fun diagnostic -> Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)
            |> Assert.Single
        Assert.Equal("CCS8040", diagnostic.Code)
        Assert.Equal<SourceRange>(EncodingFixture.span (EncodingFixture.prelude + body) "String.fromBytes bytes", diagnostic.Range)
        Assert.Empty(EncodingFixture.storageEdges result.Graph)

    [<Theory>]
    [<InlineData("255")>]
    [<InlineData("169")>]
    member _.``Byte range alone does not admit an invalid UTF8 sequence`` value =
        let body = $"[<EntryPoint>]\nlet main _ =\n    let bytes: int array = [| {value} |]\n    let text = String.fromBytes bytes\n    String.length text\n"
        EncodingFixture.rejected EncodingFixture.textReason body "String.fromBytes bytes"

    [<Fact>]
    member _.``Alias writes cannot retain the original admissible element range``() =
        let body = "[<EntryPoint>]\nlet main _ =\n    let bytes: int array = Array.zeroCreate 1\n    let alias = bytes\n    Array.set alias 0 300\n    let text = String.fromBytes bytes\n    String.length text\n"
        EncodingFixture.rejected EncodingFixture.byteReason body "String.fromBytes bytes"

    [<Fact>]
    member _.``An ordinary callable escape is not treated as a closed storage family``() =
        let body = "let consume (input: int array) = Array.length input\n[<EntryPoint>]\nlet main _ =\n    let bytes: int array = [| 65 |]\n    ignore (consume bytes)\n    let text = String.fromBytes bytes\n    String.length text\n"
        EncodingFixture.rejected EncodingFixture.closedReason body "String.fromBytes bytes"

    [<Fact>]
    member _.``Unrelated wide integer array retains its own storage and global element range``() =
        let body = "[<EntryPoint>]\nlet main _ =\n    let wide: int array = [| 4096 |]\n    let bytes: int array = [| 65; 66 |]\n    let observedWide = wide[0]\n    let text = String.fromBytes bytes\n    if observedWide = 4096 then String.length text else 0\n"
        let graph = EncodingFixture.admitted body
        let edges = EncodingFixture.evidence body "String.fromBytes bytes" graph
        let wide = EncodingFixture.allocation "wide" graph
        Assert.Equal<SettledSlot option>(None, ByteStorage.element graph wide.Id)
        Assert.DoesNotContain(edges, fun edge -> edge.Target = wide.Id || List.contains wide.Id edge.Sources)
        let read = EncodingFixture.value "observedWide" graph
        Assert.True(read.ValueRange |> Option.exists (fun range -> ValueRange.contains range (ValueRange.point 4096I)))
        Assert.DoesNotContain(graph.Edges, fun edge -> edge.Role = EdgeRole.StringByteRead && edge.Target = read.Id)
        // The ordinary range solver rebuilds this table after physical
        // formation and must retain the unrelated wide array's stores.
        Assert.Contains(graph.ElementRanges.Value.Values, fun range -> ValueRange.contains range (ValueRange.point 4096I))

    [<Theory>]
    [<InlineData(1, 2)>]
    [<InlineData(2, 0)>]
    member _.``Nonzero offset and empty slices retain exact source operands``(start: int, count: int) =
        let body = $"[<EntryPoint>]\nlet main _ =\n    let bytes: int array = [| 65; 66; 67; 68 |]\n    let selected = Array.sub bytes {start} {count}\n    let text = String.fromBytes selected\n    String.length text\n"
        let graph = EncodingFixture.admitted body
        let edges = EncodingFixture.evidence body "String.fromBytes selected" graph
        let selected = EncodingFixture.value "selected" graph
        Assert.Contains(edges, fun edge -> edge.Target = selected.Id || List.contains selected.Id edge.Sources)
        Assert.Equal<SourceRange>(EncodingFixture.span (EncodingFixture.prelude + body) $"Array.sub bytes {start} {count}", selected.Range)

    [<Fact>]
    member _.``Known later writes retain their source identity and conversion forms a distinct snapshot``() =
        let body = "[<EntryPoint>]\nlet main _ =\n    let bytes: int array = Array.zeroCreate 1\n    let alias = bytes\n    Array.set alias 0 65\n    let text = String.fromBytes bytes\n    Array.set alias 0 66\n    String.length text\n"
        let graph = EncodingFixture.admitted body
        let origin = EncodingFixture.allocation "bytes" graph
        let edges = EncodingFixture.evidence body "String.fromBytes bytes" graph
        let writes = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with
            | SemanticKind.Application(callee, [_; _; _]) when node.IsReachable ->
                match graph.Nodes[callee].Kind with
                | SemanticKind.Intrinsic { Module = IntrinsicModule.Array; Operation = "set" } -> true
                | _ -> false
            | _ -> false) |> Seq.toList
        Assert.Equal(2, writes.Length)
        for write in writes do Assert.Contains(edges, fun edge -> List.contains write.Id edge.Sources)
        let snapshots = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with
            | SemanticKind.Application(callee, _) ->
                match graph.Nodes[callee].Kind with
                | SemanticKind.Intrinsic { Module = IntrinsicModule.Array; Operation = "sub" } -> true
                | _ -> false
            | _ -> false) |> Seq.toList
        let snapshot = Assert.Single snapshots
        Assert.NotEqual(origin.Id, snapshot.Id)
        Assert.Equal(Some (SettledSlot.Integer(8, Some EncodingFixture.byteRepresentation)), ByteStorage.element graph snapshot.Id)
        let formation = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.StringByteSnapshot) |> Assert.Single
        match formation.Sources with
        | [input; copy] ->
            Assert.Equal(snapshot.Id, copy)
            Assert.NotEqual(input, copy)
            Assert.Contains(edges, fun edge -> edge.Sources |> List.contains input)
            Assert.Equal<SourceRange>(EncodingFixture.span (EncodingFixture.prelude + body) "String.fromBytes bytes", graph.Nodes[formation.Target].Range)
        | sources -> failwithf "Snapshot lost its source and copied storage identities: %A" sources
        let settledAgain, diagnostics = Clef.Compiler.Nanopass.StringByteStorage.normalize graph
        Assert.Empty diagnostics
        Assert.Equal(graph.Nodes.Count, settledAgain.Nodes.Count)
        let repeated = settledAgain.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.StringByteSnapshot) |> Assert.Single
        EncodingFixture.sameEdge formation repeated

    [<Fact>]
    member _.``Mutable bytes own a copy of their immutable source string``() =
        let body = "[<EntryPoint>]\nlet main _ =\n    let text = String.fromBytes [| 65; 66 |]\n    let bytes = String.toBytes text\n    Array.set bytes 0 4096\n    String.length text + Array.get bytes 0\n"
        let graph = EncodingFixture.admitted body
        let formation = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.StringToBytesSnapshot) |> Assert.Single
        Assert.Equal<SourceRange>(EncodingFixture.span (EncodingFixture.prelude + body) "String.toBytes text", graph.Nodes[formation.Target].Range)
        match formation.Sources with
        | [input; view; copy] ->
            Assert.NotEqual(view, copy)
            DimensionalCases.same Types.stringType graph.Nodes[input].Type
            DimensionalCases.same graph.Nodes[view].Type graph.Nodes[copy].Type
            DimensionalCases.same (NativeType.TApp(Types.arrayTyCon, [Types.intType])) graph.Nodes[copy].Type
            Assert.Equal<SettledSlot option>(None, ByteStorage.element graph copy)
            for participant in formation.Target :: formation.Sources do Assert.True(graph.Nodes.ContainsKey participant)
            let bytes = EncodingFixture.value "bytes" graph
            Assert.Equal(formation.Target, bytes.Id)
            match bytes.Kind with
            | SemanticKind.Sequential values -> Assert.Equal(copy, List.last values)
            | other -> failwithf "Mutable bytes lost their explicit copying formation: %A" other
        | sources -> failwithf "Mutable bytes lost immutable input, internal view or fresh copy: %A" sources
        let settledAgain, diagnostics = Clef.Compiler.Nanopass.StringByteStorage.normalize graph
        Assert.Empty diagnostics
        Assert.Equal(graph.Nodes.Count, settledAgain.Nodes.Count)
        let repeated = settledAgain.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.StringToBytesSnapshot) |> Assert.Single
        EncodingFixture.sameEdge formation repeated
