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
        { PlatformLoading = None; PlatformId = "encoding-test"; Dimensions = Map.ofList ["Pointer", 64; "Register", 64]
          Representations = [byteRep; integerRep; nonnegativeRep] |> List.map (fun rep -> rep.Name, rep) |> Map.ofList
          EndpointReturns = Map.empty; PlatformLibraryPath = None; PlatformDescription = Some "EncodingPlatform.description"
          PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.singleton (System.IO.Path.GetFullPath "encoding-platform.clef")
          Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
          AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None; ProjectMemoryPolicy = None }

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
let stack = { Name="encoding-stack"; Kind="stack"; Capacity=4096; Alignment=16; Granularity=16; Growth="down"; Access="rw"; Base=None }
let core: TargetCore = { Widths = [| """ + widths + " |]; Representations = [| " + representations + """ |] }
let description = { Id="encoding-test"; Core=Some core; Spaces=[|image;stack|]; ProgramLifetime=Some { Immutable="encoding-image"; Mutable=None } }
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

    // A real selected project supplies the captured parsed policy. The fixture
    // never injects a permission tuple or constructs a Ready memory account.
    let returned model heap capacity body =
        let root=System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__,"../../artifacts/utf8-checked-20261016/returned-probe/cases",System.Guid.NewGuid().ToString("N")))
        System.IO.Directory.CreateDirectory root |> ignore
        let authority=
            (declaration platform)
                .Replace("type TargetCore = { Widths:","type TargetCore = { Arch: string; Os: string; Runtime: string; Triple: string; Widths:")
                .Replace("let core: TargetCore = { Widths", "let core: TargetCore = { Arch=\"x86_64\"; Os=\"linux\"; Runtime=\"freestanding\"; Triple=\"x86_64-unknown-linux-gnu\"; Widths")
        let authority=
            if heap then
                authority.Replace("let core:",sprintf "let heap = { Name=\"encoding-heap\"; Kind=\"heap\"; Capacity=%d; Alignment=16; Granularity=16; Growth=\"dynamic\"; Access=\"rw\"; Base=None }\nlet core:" capacity)
                         .Replace("Spaces=[|image;stack|]","Spaces=[|image;stack;heap|]")
            else authority
        System.IO.File.WriteAllText(System.IO.Path.Combine(root,"Platform.clef"),authority)
        System.IO.File.WriteAllText(System.IO.Path.Combine(root,"Main.clef"),prelude+body)
        let project=System.IO.Path.Combine(root,"CheckedReturn.fidproj")
        let text=sprintf "[package]\nname=\"CheckedReturn\"\nversion=\"0.1.0\"\n[compilation]\ntarget=\"cpu\"\nmemory_model=\"%s\"\n[build]\noutput_kind=\"console\"\nsources=[\"Platform.clef\",\"Main.clef\"]\n[platform]\ndescription=\"EncodingPlatform.description\"\nruntime_model=\"freestanding\"\nos=\"linux\"\narch=\"x86_64\"\n" model
        System.IO.File.WriteAllText(project,text)
        Clef.Compiler.Project.ProjectChecker.checkProject project
        |> Result.defaultWith(fun error->failwithf "Returned checked fixture project failed: %A" error)
        |> fun result->result.CheckResult

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

    let memory (graph: SemanticGraph) =
        match Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication.project graph with
        | Result.Ok facts -> facts
        | Result.Error failures -> failwithf "Encoding memory authority is not current: %A" failures

    // This resolves aliases, but deliberately retains a source Sequential
    // wrapper. Allocation identity comes from its current construction row.
    let sourceValue (graph: SemanticGraph) id =
        Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.valueOf graph id
        |> Option.defaultWith (fun () -> failwithf "Encoding operand lost its exact source value: %A" id)

    let guardedAccess (graph: SemanticGraph) (facts: MemoryWitnessProjection) (source: SemanticNode) =
        match source.Kind with
        | SemanticKind.Sequential [required; operation] ->
            match facts.Operations.TryFind operation with
            | Some(MemoryWitnessOperation.ArrayAccess access) ->
                let guard = access.Bounds.Requirement
                Assert.Equal(operation, access.Site)
                Assert.Equal(operation, guard.Continuation)
                Assert.Equal(source.Id, guard.Frontier)
                Assert.Equal(required, guard.Site)
                Assert.Equal(SemanticKind.Require(guard.Condition, guard.Diagnostic), graph.Nodes[required].Kind)
                let correspondence =
                    graph.Edges
                    |> List.filter (fun edge -> edge.Role = EdgeRole.MemoryAccessGuard && edge.Target = operation)
                    |> Assert.Single
                Assert.Equal(EdgeClass.Provenance, correspondence.Class)
                Assert.Equal(0, correspondence.Ordinal)
                match correspondence.Sources with
                | [buffer; index; _length; _zero; _lower; _upper; condition; requirement; frontier] ->
                    Assert.Equal(access.Buffer, buffer)
                    Assert.Equal(access.Index, index)
                    Assert.Equal(guard.Condition, condition)
                    Assert.Equal(required, requirement)
                    Assert.Equal(source.Id, frontier)
                | other -> failwithf "Encoding access lost its exact source-to-continuation correspondence: %A" other
                access
            | other -> failwithf "Encoding operation has no exact current array-access witness: %A" other
        | other -> failwithf "Encoding source access lost its guard and success operation: %A" other

    let evidence body expression (graph: SemanticGraph) =
        let expectedRange = span (prelude + body) expression
        let edges = storageEdges graph
        Assert.NotEmpty edges
        let facts = memory graph
        // Array construction transports a byte-storage row to its allocation.
        // Walk that exact current lineage before checking the source conversion.
        let rec conversionSite (visited: Set<NodeId>) (edge: Hyperedge) =
            Assert.False(Set.contains edge.Target visited, "Cyclic derived encoding lineage")
            let visited = Set.add edge.Target visited
            let allocationRows =
                graph.Edges |> List.choose (fun row ->
                    match row.Role with
                    | EdgeRole.ArrayAllocationConstruction construction when construction.Site = edge.Target -> Some(row, construction)
                    | _ -> None)
            match edge.Sources, allocationRows with
            | copySite :: allocation :: parentSources, _ when allocation = edge.Target && not (List.isEmpty allocationRows) ->
                let allocationRow, construction = Assert.Single allocationRows
                Assert.Equal(copySite, construction.Owner)
                sameEdge (Clef.Compiler.Baker.Ingredients.MemoryValues.allocationConstructionRow construction) allocationRow
                let copies =
                    graph.Edges |> List.choose (fun row ->
                        match row.Role with
                        | EdgeRole.ArrayCopyConstruction copy when copy.Site = copySite && copy.Allocation = Some allocation -> Some(row, copy)
                        | _ -> None)
                match construction.Default with
                | None ->
                    let copyRow, copy = Assert.Single copies
                    sameEdge (Clef.Compiler.Baker.Ingredients.MemoryValues.copyConstructionRow copy) copyRow
                    Assert.Equal(Some allocation, facts.ArrayCopies[copySite].Allocation)
                | Some zero ->
                    // zeroCreate has its own source initialization, not a copy.
                    Assert.Empty copies
                    match graph.Nodes[zero].Kind with
                    | SemanticKind.Literal(NativeLiteral.Int(0L, _)) -> ()
                    | other -> failwithf "Encoding zero allocation lost its explicit integer default: %A" other
                    let allocated =
                        match facts.Operations[allocation] with
                        | MemoryWitnessOperation.ArrayAllocation allocation -> allocation
                        | other -> failwithf "Encoding allocation has no current memory witness: %A" other
                    Assert.Equal(construction.Guard.Requirement, allocated.Requirement.Site)
                    Assert.Equal(construction.Guard.Frontier, allocated.Requirement.Frontier)
                    match construction.Initialization with
                    | Some initialization ->
                        let write = guardedAccess graph facts graph.Nodes[initialization.Write]
                        Assert.Equal(initialization.Buffer, write.Buffer)
                        Assert.Equal(initialization.Current, write.Index)
                        Assert.Equal(Some zero, write.Value)
                    | None -> Assert.Equal(0I, allocated.MaximumCount)
                let parent =
                    edges |> List.filter (fun row ->
                        row.Target = copySite && row.Class = edge.Class && row.Role = edge.Role &&
                        row.Ordinal = edge.Ordinal && row.Sources = parentSources)
                    |> Assert.Single
                conversionSite visited parent
            | site :: _, [] ->
                match graph.Nodes[edge.Target].Kind with
                | SemanticKind.ArrayAllocate _ -> failwithf "Missing derived encoding allocation authority: %A" edge
                | _ -> site
            | _ -> failwithf "Incomplete derived encoding lineage: %A" edge
        for edge in edges do
            match edge.Role, edge.Sources with
            | EdgeRole.StringByteStorage(lower, upper, representation), _ :: operand :: origin :: _ ->
                Assert.True(0I <= lower && lower <= upper && upper <= 255I)
                Assert.Equal(byteRepresentation, representation)
                Assert.Equal<SourceRange>(expectedRange, graph.Nodes[conversionSite Set.empty edge].Range)
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
        let errors = CheckResult.errors result
        let diagnostic =
            errors |> List.filter (fun diagnostic -> diagnostic.Code = "CCS8404")
            |> Assert.Single
        Assert.Equal("CCS8404", diagnostic.Code)
        Assert.Equal<SourceRange>(span (prelude + body) expression, diagnostic.Range)
        Assert.Equal("String.fromBytes requires proved byte storage: " + reason, diagnostic.Message)
        // Source admission owns this refusal. Missing physical snapshot and
        // residence facts cannot become independent witness diagnostics, and
        // stopping before publication must not certify those absent facts.
        Assert.Single(errors) |> ignore
        Assert.Empty(storageEdges result.Graph)
        Assert.DoesNotContain(result.Graph.Edges, fun edge -> edge.Role = EdgeRole.StringByteSnapshot)
        Assert.True(result.Graph.Codata.Value.WitnessEmission.IsNone)
        Assert.True(result.Graph.WitnessProvenance.IsNone)
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication.project result.Graph |> Result.isError)
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.tryRead result.Graph |> Result.isError)
        Assert.True(Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph |> Result.isError)

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
        let memory = EncodingFixture.memory graph
        let access = EncodingFixture.guardedAccess graph memory observed
        Assert.Equal<NodeId option>(None, access.Value)
        let read =
            graph.Edges
            |> List.filter (fun edge -> edge.Role = EdgeRole.StringByteRead && edge.Target = access.Site)
            |> Assert.Single
        Assert.Contains(origin.Id, read.Sources)
        Assert.Equal<SourceRange>(EncodingFixture.span (EncodingFixture.prelude + body) "bytes[1]", observed.Range)
        Assert.Equal<SourceRange>(observed.Range, graph.Nodes[access.Site].Range)
        Assert.Equal(Some (SettledSlot.Integer(8, Some EncodingFixture.byteRepresentation)), ByteStorage.element graph access.Buffer)
        Assert.True(observed.ValueRange |> Option.exists (ValueRange.contains (ValueRange.bounded 0I 255I)))
        Assert.True(graph.Nodes[access.Site].ValueRange |> Option.exists (ValueRange.contains (ValueRange.bounded 0I 255I)))

    [<Theory>]
    [<InlineData("-1")>]
    [<InlineData("256")>]
    member _.``Out of domain integers fail at the full encoding call`` value =
        let body = $"[<EntryPoint>]\nlet main _ =\n    let bytes: int array = [| {value} |]\n    let text = String.fromBytes bytes\n    String.length text\n"
        EncodingFixture.rejected EncodingFixture.byteReason body "String.fromBytes bytes"

    [<Fact>]
    member _.``Rejected encoding retains an independent source measure error``() =
        let body = "[<Measure>] type m\n[<Measure>] type s\n[<EntryPoint>]\nlet main _ =\n    let bytes: int array = [| 256 |]\n    let text = String.fromBytes bytes\n    let mismatch = 1<m> + 2<s>\n    if mismatch > 0<m> then String.length text else 0\n"
        let result = EncodingFixture.check body
        let errors = CheckResult.errors result
        Assert.Equal<string list>(["CCS8040"; "CCS8404"], errors |> List.map _.Code |> List.sort)
        let encoding = errors |> List.filter (fun error -> error.Code = "CCS8404") |> Assert.Single
        Assert.Equal("String.fromBytes requires proved byte storage: " + EncodingFixture.byteReason, encoding.Message)
        Assert.Equal<SourceRange>(EncodingFixture.span (EncodingFixture.prelude + body) "String.fromBytes bytes", encoding.Range)
        let measure = errors |> List.filter (fun error -> error.Code = "CCS8040") |> Assert.Single
        Assert.Equal<SourceRange>(EncodingFixture.span (EncodingFixture.prelude + body) "1<m> + 2<s>", measure.Range)
        let independent = EncodingFixture.check (body.Replace("[| 256 |]", "[| 65 |]")) |> CheckResult.errors |> Assert.Single
        Assert.Equal(independent.Code, measure.Code)
        Assert.Equal(independent.Message, measure.Message)
        Assert.Equal<SourceRange>(independent.Range, measure.Range)
        Assert.Empty(EncodingFixture.storageEdges result.Graph)
        Assert.True(Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph |> Result.isError)

    [<Fact>]
    member _.``Encoding units are dimensionless before physical storage selection``() =
        let body = "[<Measure>] type m\n[<EntryPoint>]\nlet main _ =\n    let bytes: int<m> array = [| 65<m> |]\n    let text = String.fromBytes bytes\n    String.length text\n"
        let result = EncodingFixture.checkWith None body
        Assert.True(CheckResult.hasErrors result)
        let errors = CheckResult.errors result
        let diagnostic =
            errors |> List.filter (fun diagnostic -> diagnostic.Code = "CCS8040")
            |> Assert.Single
        Assert.Equal("CCS8040", diagnostic.Code)
        Assert.Equal<SourceRange>(EncodingFixture.span (EncodingFixture.prelude + body) "String.fromBytes bytes", diagnostic.Range)
        Assert.Equal("Measure mismatch: '1' vs 'm'; the residual '1 / m' is not 1", diagnostic.Message)
        Assert.Empty diagnostic.RelatedNodes
        // Type refusal grants no logical string extent. Source checking still
        // reports the unobservable length and its synthetic entry-call result.
        let entry = EncodingFixture.span (EncodingFixture.prelude + body) "[<EntryPoint>]"
        let expected =
            [ "CCS8040", diagnostic.Message, diagnostic.Range
              "CCS8011", "The range of 'the result of 'length'' in 'main' cannot be observed; bound it with a comparison, a modulus or a clamp",
                  EncodingFixture.span (EncodingFixture.prelude + body) "String.length text"
              "CCS8011", "The range of 'main …' in '__clef_program_entry' cannot be observed; bound it with a comparison, a modulus or a clamp",
                  {entry with End=entry.Start} ]
        let signature (code,message,range:SourceRange) =
            code,message,range.File,range.Start.Line,range.Start.Column,range.End.Line,range.End.Column
        let actual = errors |> List.map (fun error ->
            if error.Code="CCS8011" then
                let node = result.Graph.Nodes[Assert.Single error.RelatedNodes]
                Assert.True(node.IsReachable)
                Assert.Equal<SourceRange>(node.Range,error.Range)
                Assert.True(node.ValueRange |> Option.exists (ValueRange.isObservable >> not))
            error.Code,error.Message,error.Range)
        Assert.Equal<(string * string * string * int * int * int * int) list>(
            expected |> List.map signature |> List.sort,
            actual |> List.map signature |> List.sort)
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
        let memory = EncodingFixture.memory graph
        let originalAllocationRow, originalAllocation =
            graph.Edges
            |> List.choose (fun row ->
                match row.Role with
                | EdgeRole.ArrayAllocationConstruction construction when construction.Owner = origin.Id -> Some(row, construction)
                | _ -> None)
            |> Assert.Single
        EncodingFixture.sameEdge
            (Clef.Compiler.Baker.Ingredients.MemoryValues.allocationConstructionRow originalAllocation) originalAllocationRow
        Assert.True(originalAllocation.Default.IsSome)
        match memory.Operations.TryFind originalAllocation.Site with
        | Some(MemoryWitnessOperation.ArrayAllocation allocation) ->
            Assert.Equal(originalAllocation.Site, allocation.Site)
            Assert.Equal(originalAllocation.Count.Reference, allocation.Count)
            Assert.Equal(originalAllocation.Guard.Requirement, allocation.Requirement.Site)
        | other -> failwithf "Original byte storage has no current allocation witness: %A" other
        let writes =
            [ "Array.set alias 0 65", 65I; "Array.set alias 0 66", 66I ]
            |> List.map (fun (expression, value) ->
                let expectedRange = EncodingFixture.span (EncodingFixture.prelude + body) expression
                let access =
                    memory.Operations.Values
                    |> Seq.choose (function
                        | MemoryWitnessOperation.ArrayAccess access
                            when access.Value.IsSome && graph.Nodes[access.Bounds.Requirement.Frontier].Range = expectedRange -> Some access
                        | _ -> None)
                    |> Assert.Single
                let source = graph.Nodes[access.Bounds.Requirement.Frontier]
                Assert.True(source.IsReachable)
                Assert.Equal(access, EncodingFixture.guardedAccess graph memory source)
                Assert.Equal<SourceRange>(expectedRange, source.Range)
                Assert.Equal(Some(ValueRange.point value), graph.Nodes[access.Value.Value].ValueRange)
                Assert.Equal(origin.Id, (EncodingFixture.sourceValue graph access.Buffer).Id)
                // Byte-storage premises name the current IndexSet writer.
                // Its unique guard row above retains the original source ID
                // and span; the frontier itself no longer performs the store.
                Assert.Contains(edges, fun edge -> List.contains access.Site edge.Sources)
                source)
        Assert.Equal(2, writes.Length)
        Assert.NotEqual(writes[0].Id, writes[1].Id)
        let formation =
            graph.Edges
            |> List.filter (fun edge -> edge.Role = EdgeRole.StringByteSnapshot)
            |> Assert.Single
        match formation.Sources with
        | [input; copy] ->
            let snapshot = memory.ArrayCopies[copy]
            Assert.Equal(copy, snapshot.Site)
            Assert.NotEqual(origin.Id, copy)
            Assert.Equal(Some (SettledSlot.Integer(8, Some EncodingFixture.byteRepresentation)), ByteStorage.element graph copy)
            let allocation = snapshot.Allocation |> Option.defaultWith (fun () -> failwith "Snapshot lost its distinct allocation")
            Assert.NotEqual(origin.Id, allocation)
            Assert.NotEqual(originalAllocation.Site, allocation)
            let read = snapshot.Read |> Option.defaultWith (fun () -> failwith "Nonempty snapshot lost its source read")
            let write = snapshot.Write |> Option.defaultWith (fun () -> failwith "Nonempty snapshot lost its destination store")
            Assert.Equal(Some read.Site, write.Value)
            Assert.Equal(origin.Id, (EncodingFixture.sourceValue graph snapshot.Source).Id)
            Assert.Equal(origin.Id, (EncodingFixture.sourceValue graph read.Buffer).Id)
            Assert.Equal(snapshot.Destination, write.Buffer)
            Assert.Equal(allocation, (EncodingFixture.sourceValue graph write.Buffer).Id)
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

module LogicalShapes = Clef.Compiler.Baker.Ingredients.ArrayShapes

module private LogicalEncodingFixture =

    let check expression =
        EncodingFixture.checkWith None
            ($"[<EntryPoint>]\nlet main _ =\n    let text = String.fromBytes {expression}\n    String.length text\n")

    let identities (graph:SemanticGraph) =
        let site = EncodingFixture.value "text" graph
        let callee, input =
            match site.Kind with
            | SemanticKind.Application(callee,[input]) -> callee,input
            | other -> failwithf "The logical constructor changed: %A" other
        let length = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind, LogicalShapes.intrinsicApplication graph node.Id with
            | SemanticKind.Application _, Some({Module=IntrinsicModule.String;Operation="length"},[_],_) -> true
            | _ -> false) |> Assert.Single
        site,callee,input,length

    let noStorage (graph:SemanticGraph) =
        Assert.True(graph.Platform.IsNone)
        Assert.Empty(EncodingFixture.storageEdges graph)
        Assert.DoesNotContain(graph.Edges, fun edge -> edge.Role=EdgeRole.StringByteSnapshot || edge.Role=EdgeRole.StringByteRead)
        for edge in graph.Edges do
            match edge.Role with
            | EdgeRole.StringExtent extent -> Assert.Empty extent.StaticOrigins
            | _ -> ()

    let admitted expression count =
        let result = check expression
        Assert.False(CheckResult.hasErrors result, sprintf "%A" result.Diagnostics)
        let graph = result.Graph
        let site,callee,input,length = identities graph
        let extent = LogicalShapes.reader graph site.Id |> Option.defaultWith (fun () -> failwith "Missing logical extent")
        Assert.Equal<LogicalShapes.Length list>([LogicalShapes.Length.Constant count],extent.Sources)
        Assert.Equal<Set<NodeId>>(Set.singleton site.Id,extent.StringSources)
        for participant in site.Id::callee::input::graph.Nodes[input].Children do
            Assert.Contains(participant,extent.Participants)
        Assert.Equal<ValueRange option>(Some(ValueRange.point count),length.ValueRange)
        noStorage graph
        graph,site,callee,input,length

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "StringEncoding")>]
type LogicalStringExtentCases() =
    [<Theory>]
    [<InlineData("[| 65 |]",1)>]
    [<InlineData("[| 195; 169 |]",2)>]
    [<InlineData("[||]",0)>]
    member _.``Private constant encoding has its byte count without storage authority``(expression:string,count:int) =
        LogicalEncodingFixture.admitted expression (bigint count) |> ignore

    [<Theory>]
    [<InlineData("[| -1 |]")>]
    [<InlineData("[| 256 |]")>]
    [<InlineData("[| 195 |]")>]
    [<InlineData("[| 169 |]")>]
    member _.``Invalid logical byte payloads do not acquire an extent``(expression:string) =
        let result = LogicalEncodingFixture.check expression
        let site,_,_,_ = LogicalEncodingFixture.identities result.Graph
        Assert.True(CheckResult.hasErrors result)
        Assert.True((LogicalShapes.reader result.Graph site.Id).IsNone)
        LogicalEncodingFixture.noStorage result.Graph

    [<Theory>]
    [<InlineData("constructor-children")>]
    [<InlineData("array-children")>]
    [<InlineData("array-type")>]
    [<InlineData("argument-parent")>]
    [<InlineData("invalid-current-byte")>]
    [<InlineData("extra-kind-reference")>]
    [<InlineData("extra-attached-reference")>]
    [<InlineData("extra-recorded-reference")>]
    [<InlineData("unexpected-argument-incidence")>]
    [<InlineData("mismatched-array-incidence")>]
    [<InlineData("duplicate-argument-incidence")>]
    [<InlineData("extra-literal-incidence")>]
    [<InlineData("captured-input")>]
    [<InlineData("unknown-array-capture")>]
    member _.``Logical encoding rereads current inline structure and complete input uses``(mutation:string) =
        // The unchanged graph must pass before any mutation can discriminate.
        // This tests the source reader itself, not admission of a damaged graph.
        let graph,site,_,input,length = LogicalEncodingFixture.admitted "[| 65 |]" 1I
        let array = graph.Nodes[input]
        let replace (node:SemanticNode) = {graph with Nodes=graph.Nodes.Add(node.Id,node)}
        let argument =
            match length.Kind with
            | SemanticKind.Application(_,[argument]) -> graph.Nodes[argument]
            | other -> failwithf "Missing length argument: %A" other
        let mutated =
            match mutation with
            | "constructor-children" -> replace {site with Children=[]}
            | "array-children" -> replace {array with Children=[]}
            | "array-type" -> replace {array with Type=Types.stringType}
            | "argument-parent" -> replace {array with Parent=None}
            | "invalid-current-byte" ->
                let value = graph.Nodes[array.Children |> Assert.Single]
                match value.Kind with
                | SemanticKind.Literal(NativeLiteral.Int(_,kind)) ->
                    replace {value with Kind=SemanticKind.Literal(NativeLiteral.Int(169L,kind))}
                | other -> failwithf "Missing scalar byte: %A" other
            | "extra-kind-reference" ->
                replace {argument with Kind=SemanticKind.VarRef("extra",Some input);Type=array.Type}
            | "extra-attached-reference" -> replace {argument with Children=[input]}
            | "extra-recorded-reference" ->
                let edge = Hyperedge.edge1 EdgeClass.Reference EdgeRole.Definition 0 input argument.Id
                {graph with Edges=edge::graph.Edges}
            | "unexpected-argument-incidence" ->
                let edge = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence site
                           |> List.filter (fun edge -> edge.Role=EdgeRole.Argument) |> Assert.Single
                {graph with Edges={edge with Ordinal=edge.Ordinal+1}::graph.Edges}
            | "mismatched-array-incidence" ->
                let edge = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence array |> Assert.Single
                {graph with Edges={edge with Ordinal=edge.Ordinal+1}::graph.Edges}
            | "duplicate-argument-incidence" ->
                let edge = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence site
                           |> List.filter (fun edge -> edge.Role=EdgeRole.Argument) |> Assert.Single
                {graph with Edges=edge::edge::graph.Edges}
            | "extra-literal-incidence" ->
                let value = array.Children |> Assert.Single
                let edge = Hyperedge.edge1 EdgeClass.Reference EdgeRole.Definition 0 input value
                {graph with Edges=edge::graph.Edges}
            | "captured-input" | "unknown-array-capture" ->
                let main = EncodingFixture.value "main" graph
                let capture:CaptureInfo =
                    {Name="input";Type=array.Type;IsMutable=false
                     SourceNodeId=if mutation="captured-input" then Some input else None}
                match main.Kind with
                | SemanticKind.Lambda(formals,body,captures,arg,returnType) ->
                    replace {main with Kind=SemanticKind.Lambda(formals,body,capture::captures,arg,returnType)}
                | other -> failwithf "Missing entry source lambda: %A" other
            | other -> failwithf "Unknown mutation: %s" other
        // A changed complete use census may first invalidate ordinary demand.
        // Prove that refusal, then renew only its owning rows before checking
        // the extent owner. The old numeric annotation remains, not evidence.
        match Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.tryRead mutated with
        | Result.Error failures ->
            Assert.NotEmpty failures
            let withdrawn, diagnostics = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.run None mutated
            // Error Handling (CCS8415): "The exclusion SHALL be withdrawn when its
            // supporting activation, use, capture or ownership facts change".
            // Withdraw stale ranges while preserving every source field and incidence.
            Assert.Equal(mutated.Nodes.Count, withdrawn.Nodes.Count)
            for KeyValue(id, node) in mutated.Nodes do
                let current = withdrawn.Nodes[id]
                Assert.True(System.Object.Equals(node.Id, current.Id), "Id changed during range withdrawal")
                Assert.True(System.Object.Equals(node.Kind, current.Kind), "Kind changed during range withdrawal")
                Assert.True(System.Object.Equals(node.Range, current.Range), "Range changed during range withdrawal")
                Assert.True(System.Object.Equals(node.Type, current.Type), "Type changed during range withdrawal")
                Assert.True(System.Object.Equals(node.SRTPResolution, current.SRTPResolution), "SRTPResolution changed during range withdrawal")
                Assert.True(System.Object.Equals(node.ArenaAffinity, current.ArenaAffinity), "ArenaAffinity changed during range withdrawal")
                Assert.True(System.Object.Equals(node.LayoutHint, current.LayoutHint), "LayoutHint changed during range withdrawal")
                Assert.True(System.Object.Equals(node.Children, current.Children), "Children changed during range withdrawal")
                Assert.True(System.Object.Equals(node.Parent, current.Parent), "Parent changed during range withdrawal")
                Assert.True(System.Object.Equals(node.Metadata, current.Metadata), "Metadata changed during range withdrawal")
                Assert.True(System.Object.Equals(node.IsReachable, current.IsReachable), "IsReachable changed during range withdrawal")
                Assert.True(System.Object.Equals(node.EmissionStrategy, current.EmissionStrategy), "EmissionStrategy changed during range withdrawal")
                Assert.True(current.ValueRange.IsNone)
            Assert.Equal<Hyperedge list>(mutated.Edges, withdrawn.Edges)
            Assert.True(mutated.DeclarationRoots = withdrawn.DeclarationRoots)
            Assert.Same(mutated.Types, withdrawn.Types)
            Assert.Same(mutated.Modules, withdrawn.Modules)
            Assert.Empty(withdrawn.FieldRanges.Value)
            Assert.Empty(withdrawn.ElementRanges.Value)
            Assert.Empty(withdrawn.Escaping.Value)
            Assert.Empty(Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.sourceFacts withdrawn)
            Assert.Equal<Diagnostic list>(Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.diagnostics mutated failures,diagnostics)
        | Result.Ok _ -> ()
        let current = Clef.Compiler.Nanopass.OrdinaryDemand.normalize mutated
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.tryRead current |> Result.isOk)
        Assert.Equal<ValueRange option>(Some(ValueRange.point 1I),mutated.Nodes[length.Id].ValueRange)
        Assert.Equal<ValueRange option>(mutated.Nodes[length.Id].ValueRange,current.Nodes[length.Id].ValueRange)
        Assert.True((LogicalShapes.reader current site.Id).IsNone,mutation)
        if mutation = "invalid-current-byte" then
            let analyzed, diagnostics = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.run None current
            Assert.True(analyzed.Nodes[length.Id].ValueRange |> Option.exists (ValueRange.isObservable >> not))
            Assert.Contains(diagnostics, fun diagnostic ->
                diagnostic.Code = "CCS8011" && diagnostic.RelatedNodes = [length.Id] && diagnostic.Range = length.Range)

    [<Fact>]
    member _.``A fresh logical payload changes the observed length``() =
        LogicalEncodingFixture.admitted "[| 65 |]" 1I |> ignore
        LogicalEncodingFixture.admitted "[| 65; 66 |]" 2I |> ignore

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "StringEncoding")>]
type CheckedStringEncodingCases() =
    static member private Program bytes =
        "[<EntryPoint>]\nlet main _ =\n    let bytes = " + bytes + "\n    let checkedText = String.tryFromBytes bytes\n    match checkedText with\n    | ValueSome text -> String.length text\n    | ValueNone -> 0\n"

    [<Theory>]
    [<InlineData("[| |]")>]
    [<InlineData("[| 65; 0; 66 |]")>]
    [<InlineData("[| 194; 128 |]")>]
    [<InlineData("[| 224; 160; 128 |]")>]
    [<InlineData("[| 240; 144; 128; 128 |]")>]
    [<InlineData("[| 244; 143; 191; 191 |]")>]
    [<InlineData("[| 128 |]")>]
    [<InlineData("[| 192; 128 |]")>]
    [<InlineData("[| 224; 128; 128 |]")>]
    [<InlineData("[| 237; 160; 128 |]")>]
    [<InlineData("[| 244; 144; 128; 128 |]")>]
    [<InlineData("[| 226; 130 |]")>]
    member _.``Checked text authors one private snapshot and native value outcomes``(bytes: string) =
        let graph = EncodingFixture.admitted (CheckedStringEncodingCases.Program bytes)
        let memory = EncodingFixture.memory graph
        let validator = memory.Operations.Values |> Seq.choose(function MemoryWitnessOperation.Utf8Validation value -> Some value | _ -> None) |> Assert.Single
        let construction = validator.Construction
        Assert.Equal("RFC3629-v1", construction.Validator)
        Assert.NotEqual(construction.Input, construction.Snapshot)
        Assert.Equal(validator.Copy, memory.ArrayCopies[construction.Snapshot])
        Assert.Equal(Some validator.Allocation.Site, validator.Copy.Allocation)
        Assert.Equal(SemanticKind.DUConstruct("ValueSome",1,Some construction.Text,None), graph.Nodes[construction.Success].Kind)
        Assert.Equal(SemanticKind.DUConstruct("ValueNone",0,None,None), graph.Nodes[construction.Failure].Kind)
        DimensionalCases.same (NativeType.TApp(Types.voptionTyCon,[Types.stringType])) graph.Nodes[construction.Success].Type
        let retirement = match memory.Operations[construction.Retirement] with MemoryWitnessOperation.SnapshotRetirement value -> value | other -> failwithf "%A" other
        Assert.Equal(construction, retirement.Construction)
        Assert.Equal(validator.Allocation, retirement.Allocation)
        let revision = Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph |> Result.defaultWith(fun failures -> failwithf "%A" failures)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)

    [<Theory>]
    [<InlineData("validation-snapshot")>]
    [<InlineData("success-case")>]
    [<InlineData("failure-retirement")>]
    [<InlineData("missing-construction")>]
    member _.``Checked text refuses changed snapshot validation and outcome facts``(mutation: string) =
        let graph = EncodingFixture.admitted (CheckedStringEncodingCases.Program "[| 65; 255 |]")
        let memory = EncodingFixture.memory graph
        let validator = memory.Operations.Values |> Seq.choose(function MemoryWitnessOperation.Utf8Validation value -> Some value | _ -> None) |> Assert.Single
        let construction = validator.Construction
        let replace id kind = {graph with Nodes=graph.Nodes.Add(id,{graph.Nodes[id] with Kind=kind})}
        let changed =
            match mutation with
            | "validation-snapshot" ->
                match graph.Nodes[construction.Validation].Kind with
                | SemanticKind.Application(fn,_) -> replace construction.Validation (SemanticKind.Application(fn,[construction.Input]))
                | other -> failwithf "%A" other
            | "success-case" -> replace construction.Success (SemanticKind.DUConstruct("ValueSome",1,Some construction.Input,None))
            | "failure-retirement" ->
                match graph.Nodes[construction.Decision].Kind with
                | SemanticKind.IfThenElse(guard,success,_) -> replace construction.Decision (SemanticKind.IfThenElse(guard,success,Some construction.Failure))
                | other -> failwithf "%A" other
            | "missing-construction" -> {graph with Edges=graph.Edges |> List.filter(fun edge -> match edge.Role with EdgeRole.StringCheckedConstruction _ -> false | _ -> true)}
            | _ -> failwith mutation
        let numeric = Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph |> Result.defaultWith(fun failures -> failwithf "%A" failures)
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication.project changed |> Result.isError)
        // The complete use change first revokes ordinary-demand exclusion.
        // Renew only that owner before discriminating this recipe's own guard.
        let current = Clef.Compiler.Nanopass.OrdinaryDemand.normalize changed
        let admitted, failures, _ = Clef.Compiler.Baker.Recipes.StringViewRecipes.settle current numeric memory.Operations memory.ArrayCopies
        Assert.DoesNotContain(admitted,fun (_,operation) -> match operation with MemoryWitnessOperation.Utf8Validation _ -> true | _ -> false)
        Assert.Contains(failures.Values,fun reason -> reason.Contains("checked string") || reason.Contains("UTF-8 validity premise"))

    [<Fact>]
    member _.``Checked text stale owner never supplies current outcome authority``() =
        let graph = EncodingFixture.admitted (CheckedStringEncodingCases.Program "[| 65 |]")
        let memory = EncodingFixture.memory graph
        let changed = {graph with Edges=graph.Edges |> List.map(fun edge -> match edge.Role with EdgeRole.StringCheckedConstruction c -> {edge with Role=EdgeRole.StringCheckedConstruction {c with Owner=c.Input}} | _ -> edge)}
        let numeric = Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph |> Result.defaultWith(fun failures -> failwithf "%A" failures)
        let _,failures,_ = Clef.Compiler.Baker.Recipes.StringViewRecipes.settle changed numeric memory.Operations memory.ArrayCopies
        Assert.Contains(failures.Values,fun reason -> reason="The checked string lost its exact snapshot/validator/outcome construction relation.")

    [<Fact>]
    member _.``Checked text incompatible integers refuse before runtime absence``() =
        let result = EncodingFixture.check (CheckedStringEncodingCases.Program "[| 256 |]")
        Assert.Contains(CheckResult.errors result,fun diagnostic -> diagnostic.Code="CCS8404" && diagnostic.Message.EndsWith(EncodingFixture.byteReason))
        Assert.DoesNotContain(result.Graph.Edges,fun edge -> match edge.Role with EdgeRole.StringCheckedConstruction _ -> true | _ -> false)

    [<Fact>]
    member _.``Checked text without octet authority stays logical``() =
        let body = (CheckedStringEncodingCases.Program "[| 65 |]").Replace("String.length text", "0")
        let result = EncodingFixture.checkWith None body
        Assert.False(CheckResult.hasErrors result,sprintf "%A" result.Diagnostics)
        Assert.DoesNotContain(result.Graph.Edges,fun edge -> match edge.Role with EdgeRole.StringCheckedConstruction _ -> true | _ -> false)
        let site = EncodingFixture.value "checkedText" result.Graph
        match site.Kind with
        | SemanticKind.Application(fn,_) ->
            match result.Graph.Nodes[fn].Kind with
            | SemanticKind.Intrinsic info -> Assert.Equal("tryFromBytes",info.Operation)
            | other -> failwithf "%A" other
        | other -> failwithf "%A" other

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Checked text backing cannot return or cross a captured activation``(capture: bool) =
        let body =
            if capture then
                "[<EntryPoint>]\nlet main _ =\n    let bytes = [| 65 |]\n    let checkedText = String.tryFromBytes bytes\n    let observe () = match checkedText with | ValueSome text -> String.length text | ValueNone -> 0\n    observe ()\n"
            else
                "let choose () =\n    let bytes = [| 65 |]\n    let checkedText = String.tryFromBytes bytes\n    match checkedText with\n    | ValueSome text -> text\n    | ValueNone -> \"\"\n[<EntryPoint>]\nlet main _ = String.length (choose ())\n"
        let result = EncodingFixture.check body
        Assert.Contains(CheckResult.errors result,fun diagnostic -> diagnostic.Code="CCS8403" && diagnostic.Message.Contains("complete use family"))

    [<Fact>]
    member _.``Checked text validates private copy despite a later original alias write``() =
        let body = "[<EntryPoint>]\nlet main _ =\n    let bytes = [| 65 |]\n    let alias = bytes\n    let checkedText = String.tryFromBytes bytes\n    alias.[0] <- 255\n    match checkedText with | ValueSome text -> String.length text | ValueNone -> 0\n"
        let graph = EncodingFixture.admitted body
        let memory = EncodingFixture.memory graph
        let validator = memory.Operations.Values |> Seq.choose(function MemoryWitnessOperation.Utf8Validation value -> Some value | _ -> None) |> Assert.Single
        Assert.NotEqual(validator.Construction.Input,validator.Construction.Snapshot)
        Assert.NotEqual(validator.Copy.Source,validator.Copy.Destination)

    [<Theory>]
    [<InlineData("input")>]
    [<InlineData("length")>]
    member _.``Checked text passive copy incidence refuses metadata withdrawal``(field: string) =
        let graph=EncodingFixture.admitted (CheckedStringEncodingCases.Program "[| 65 |]")
        let revision=Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph |> Result.defaultWith(fun failures -> failwithf "%A" failures)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let operations=revision.Emission.Memory.Operations |> Map.map(fun _ operation ->
            match operation with
            | Fidelity.PSG.MemoryWitnessOperation.Utf8Validation row ->
                let construction=if field="input" then {row.Construction with Input=row.Construction.Snapshot} else {row.Construction with Length=row.Construction.Snapshot}
                Fidelity.PSG.MemoryWitnessOperation.Utf8Validation {row with Construction=construction}
            | _ -> operation)
        let changed={revision with Emission={revision.Emission with Memory={revision.Emission.Memory with Operations=operations}}}
        Assert.Contains("The UTF-8 copy source/count differs from its exact construction input/length.",sprintf "%A" (Fidelity.PSG.Integrity.check changed))

    [<Fact>]
    member _.``Demanded parameter checked text requires explicit unsettled memory authority``() =
        let file=System.IO.Path.GetFullPath "string-encoding-demanded.clef"
        let source="module DemandedCheckedText\nlet decode (bytes:array<int>) =\n    match String.tryFromBytes bytes with\n    | ValueSome _ -> 1\n    | ValueNone -> 0\n"
        let parse path text=match parseStringWithDefaults text path with ParseSuccess value -> value | ParseError errors -> failwithf "%A" errors
        let result=checkParsedInputsWithDeclarations
                       [parse "encoding-platform.clef" (EncodingFixture.declaration EncodingFixture.platform);parse file source]
                       (Some EncodingFixture.platform) Set.empty (Some(Set.singleton file)) None
        let site=result.Graph.Nodes.Values |> Seq.filter(fun node ->
            node.IsReachable && match node.Kind with
                                | SemanticKind.Application(fn,[_]) ->
                                    match result.Graph.Nodes[fn].Kind with SemanticKind.Intrinsic info -> info.Module=IntrinsicModule.String && info.Operation="tryFromBytes" | _ -> false
                                | _ -> false) |> Assert.Single
        let domains=result.Graph.Edges |> List.choose(fun edge -> match edge.Role with EdgeRole.MemoryDomain domain -> Some domain | _ -> None)
        Assert.Contains(domains,fun domain -> domain.Required.Contains site.Id && domain.Unresolved.TryFind site.Id=Some "The demanded String.tryFromBytes lacks proved byte storage and its private snapshot/validation/outcome construction.")
        Assert.True(Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph |> Result.isError)

    [<Fact>]
    member _.``Checked native cases own exact local stack storage and layout``() =
        let graph=EncodingFixture.admitted (CheckedStringEncodingCases.Program "[| 65; 0; 66 |]")
        let memory=EncodingFixture.memory graph
        let validator=memory.Operations.Values |> Seq.choose(function MemoryWitnessOperation.Utf8Validation row -> Some row | _ -> None) |> Assert.Single
        let rows=[validator.Construction.Success;validator.Construction.Failure] |> List.map(fun site ->
            Assert.Contains(site,memory.Required)
            Assert.False(memory.Unresolved.ContainsKey site)
            match memory.Operations[site] with
            | MemoryWitnessOperation.ConstructedValue row ->
                Assert.Equal(site,row.Site)
                Assert.Equal(validator.Construction.Owner,row.Owner)
                Assert.Equal(Clef.Compiler.NativeTypedTree.TypeIdentities.ofType graph.Nodes[site].Type,row.SourceType)
                Assert.Contains(site,row.Uses)
                let support=Clef.Compiler.Baker.Ingredients.MemoryValues.participants memory.Operations (MemoryWitnessOperation.ConstructedValue row)
                Assert.True(Set.isSubset row.Uses support)
                match row.Residence with
                | MemoryResidence.Stack(scope,space) ->
                    Assert.Equal(Some scope,Clef.Compiler.Baker.Recipes.MemoryAccessRecipes.nearestLambda graph site)
                    Assert.Contains(scope,support)
                    Assert.Contains(space,support)
                | other -> failwithf "Expected source stack authority, got %A" other
                row
            | other -> failwithf "Expected constructed-instance authority, got %A" other)
        Assert.Equal(rows[0].Residence,rows[1].Residence)
        let revision=Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph |> Result.defaultWith(fun failures -> failwithf "%A" failures)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        for operation in revision.Emission.Memory.Operations.Values do
            match operation with
            | Fidelity.PSG.MemoryWitnessOperation.ConstructedValue row -> Assert.True(revision.Emission.Numeric.Layouts.ContainsKey row.SourceType)
            | _ -> ()

    [<Theory>]
    [<InlineData("missing")>]
    [<InlineData("scope")>]
    [<InlineData("layout")>]
    [<InlineData("capacity")>]
    member _.``Checked native storage refuses missing instance or forged scope``(change:string) =
        let graph=EncodingFixture.admitted (CheckedStringEncodingCases.Program "[| 65 |]")
        let revision=Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph |> Result.defaultWith(fun failures -> failwithf "%A" failures)
        let row=revision.Emission.Memory.Operations.Values |> Seq.choose(function Fidelity.PSG.MemoryWitnessOperation.ConstructedValue row -> Some row | _ -> None) |> Seq.head
        let operations=
            if change="missing" then revision.Emission.Memory.Operations.Remove row.Site
            elif change="layout" || change="capacity" then
                let changed=if change="layout" then {row with Layout=row.Site} else {row with Capacity=row.Site}
                revision.Emission.Memory.Operations.Add(row.Site,Fidelity.PSG.MemoryWitnessOperation.ConstructedValue changed)
            else
                let residence=match row.Residence with Fidelity.PSG.MemoryResidence.Stack(_,space) -> Fidelity.PSG.MemoryResidence.Stack(row.Site,space) | _ -> failwith "stack"
                revision.Emission.Memory.Operations.Add(row.Site,Fidelity.PSG.MemoryWitnessOperation.ConstructedValue {row with Residence=residence})
        let changed={revision with Emission={revision.Emission with Memory={revision.Emission.Memory with Operations=operations}}}
        let reason=match change with
                   | "missing" -> "exact source-authorized checked native-case storage"
                   | "layout" -> "The constructed instance lost its exact current layout proof supported by this site."
                   | "capacity" -> "The constructed instance lost its exact declared-space capacity proof supported by this site."
                   | _ -> "The constructed instance's stack lifetime has no exact activation scope."
        Assert.Contains(reason,sprintf "%A" (Fidelity.PSG.Integrity.check changed))

    [<Fact>]
    member _.``Checked native storage refuses disagreement with snapshot space capacity``() =
        let graph=EncodingFixture.admitted (CheckedStringEncodingCases.Program "[| 65 |]")
        let revision=Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph |> Result.defaultWith(fun failures -> failwithf "%A" failures)
        let row=revision.Emission.Memory.Operations.Values |> Seq.choose(function Fidelity.PSG.MemoryWitnessOperation.ConstructedValue row -> Some row | _ -> None) |> Seq.head
        let claim=revision.CurrentClaims[row.Capacity]
        let body=match claim.Body with Fidelity.PSG.ObligationBody.CapacityFits(bytes,capacity) -> Fidelity.PSG.ObligationBody.CapacityFits(bytes,capacity+1L) | _ -> failwith "capacity claim"
        let changed={revision with CurrentClaims=revision.CurrentClaims.Add(row.Capacity,{claim with Body=body})}
        Assert.Contains("The same-space source allocation capacity claims disagree.",sprintf "%A" (Fidelity.PSG.Integrity.check changed))

    static member private ReturnedProgram bytes =
        "let checked () = String.tryFromBytes " + bytes + "\n[<EntryPoint>]\nlet main _ =\n    match checked () with\n    | ValueSome text -> String.length text\n    | ValueNone -> 0\n"

    [<Theory>]
    [<InlineData("[| 65; 66 |]")>]
    [<InlineData("[| 0 |]")>]
    [<InlineData("[| 255 |]")>]
    member _.``Returned checked text owns exact helper instance and ordered cleanup``(bytes:string) =
        let result=EncodingFixture.returned "standard" true 4096 (CheckedStringEncodingCases.ReturnedProgram bytes)
        Assert.False(CheckResult.hasErrors result,sprintf "%A" result.Diagnostics)
        let graph=result.Graph
        let memory=EncodingFixture.memory graph
        let validation=memory.Operations.Values |> Seq.choose(function MemoryWitnessOperation.Utf8Validation row -> Some row | _ -> None) |> Assert.Single
        let life=validation.Construction.Returned |> Option.defaultWith(fun()->failwith "Missing authored returned lifetime")
        Assert.NotEqual(life.Application,validation.Construction.Owner)
        Assert.NotEqual(life.Actual,validation.Construction.Success)
        Assert.Equal(MemoryResidence.Heap(life.Application,life.Space),validation.Allocation.Residence)
        let carriers=memory.Operations.Values |> Seq.choose(function MemoryWitnessOperation.ConstructedValue row -> Some row | _ -> None) |> Seq.toList
        Assert.Equal(2,carriers.Length)
        for row in carriers do Assert.Equal(validation.Allocation.Residence,row.Residence)
        let cleanup=memory.Operations.Values |> Seq.choose(function MemoryWitnessOperation.CheckedResultRetirement row -> Some row | _ -> None) |> Seq.toList
        Assert.Equal(3,cleanup.Length)
        Assert.Equal(Set.ofList[life.SomeBackingRetirement;life.SomeCarrierRetirement;life.NoneCarrierRetirement],cleanup |> List.map _.Site |> Set.ofList)
        let revision=Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph |> Result.defaultWith(fun failures->failwithf "%A" failures)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        Assert.True(revision.CurrentClaims.ContainsKey(Fidelity.PSG.NodeId(NodeId.value life.Capacity)))

    [<Theory>]
    [<InlineData("stack_only",true,4096,"forbids returned checked storage")>]
    [<InlineData("standard",false,4096,"exactly one declared writable heap")>]
    [<InlineData("standard",true,50,"combined returned checked live extent")>]
    member _.``Returned checked text requires actual policy heap and combined capacity``(model:string,heap:bool,capacity:int,reason:string) =
        let result=EncodingFixture.returned model heap capacity (CheckedStringEncodingCases.ReturnedProgram "[| 65; 0; 66 |]")
        Assert.Contains(CheckResult.errors result,fun diagnostic->diagnostic.Code="CCS8403" && diagnostic.Message.Contains(reason))
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication.project result.Graph |> Result.isError)

    [<Fact>]
    member _.``Returned checked text has no standalone allocation permission``() =
        let result=EncodingFixture.check (CheckedStringEncodingCases.ReturnedProgram "[| 65 |]")
        Assert.Contains(CheckResult.errors result,fun diagnostic->diagnostic.Code="CCS8403" && diagnostic.Message.Contains("no captured project memory policy"))

    [<Fact>]
    member _.``Returned checked text keeps zero count outside its heap profile``() =
        let result=EncodingFixture.returned "standard" true 4096 (CheckedStringEncodingCases.ReturnedProgram "[||]")
        Assert.Contains(CheckResult.errors result,fun diagnostic->diagnostic.Code="CCS8403" && diagnostic.Message.Contains("zero remains local-only"))

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Returned checked text refuses a second application or captured instance``(capture:bool) =
        let body=
            if capture then
                "let checked () = String.tryFromBytes [|65|]\n[<EntryPoint>]\nlet main _ =\n    let value = checked ()\n    let observe () = match value with | ValueSome text -> String.length text | ValueNone -> 0\n    observe ()\n"
            else
                "let checked () = String.tryFromBytes [|65|]\n[<EntryPoint>]\nlet main _ =\n    let first = checked ()\n    let second = checked ()\n    let a = match first with | ValueSome text -> String.length text | ValueNone -> 0\n    let b = match second with | ValueSome text -> String.length text | ValueNone -> 0\n    a + b\n"
        let reason=if capture then "requires its exact Some elimination" else "exactly one complete helper application"
        let result=EncodingFixture.returned "standard" true 4096 body
        Assert.Contains(CheckResult.errors result,fun diagnostic->diagnostic.Code="CCS8403" && diagnostic.Message.Contains(reason))

    [<Theory>]
    [<InlineData("policy")>]
    [<InlineData("call")>]
    [<InlineData("formal")>]
    [<InlineData("cleanup")>]
    [<InlineData("body")>]
    [<InlineData("case")>]
    [<InlineData("capacity")>]
    [<InlineData("capacity-body")>]
    [<InlineData("capacity-support")>]
    [<InlineData("case-arm")>]
    member _.``Returned checked current account refuses withdrawn source incidence``(change:string) =
        let result=EncodingFixture.returned "standard" true 4096 (CheckedStringEncodingCases.ReturnedProgram "[|65|]")
        Assert.False(CheckResult.hasErrors result,sprintf "%A" result.Diagnostics)
        let graph=result.Graph
        let memory=EncodingFixture.memory graph
        let validation=memory.Operations.Values |> Seq.choose(function MemoryWitnessOperation.Utf8Validation row -> Some row | _ -> None) |> Assert.Single
        let life=Option.get validation.Construction.Returned
        let changed=
            match change with
            | "policy" -> {graph with Platform=graph.Platform |> Option.map(fun context->{context with ProjectMemoryPolicy=None})}
            | "capacity-support" ->
                {graph with Edges=graph.Edges |> List.filter(fun edge->not(edge.Target=life.Capacity && edge.Role=EdgeRole.Constrains))}
            | "capacity-body" ->
                let citizen=graph.Nodes[life.Capacity]
                let info=match citizen.Kind with SemanticKind.Obligation info->info | _ -> failwith "Missing capacity citizen"
                {graph with Nodes=graph.Nodes.Add(citizen.Id,{citizen with Kind=SemanticKind.Obligation{info with Body=ObligationBody.CapacityFits(0L,0L)}})}
            | "case-arm" ->
                let node=graph.Nodes[life.Elimination]
                let kind=match node.Kind with SemanticKind.CaseElimination(value,arms)->SemanticKind.CaseElimination(value,List.rev arms) | _ -> failwith "Missing caller cases"
                {graph with Nodes=graph.Nodes.Add(node.Id,{node with Kind=kind})}
            | _ ->
                let id=match change with
                       | "call"->life.Application | "formal"->life.Formal | "body"->life.Body
                       | "case"->validation.Construction.Success | "capacity"->life.Capacity | _ -> life.SomeBackingRetirement
                {graph with Nodes=graph.Nodes.Remove id}
        let failure=Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication.project changed
        Assert.True(Result.isError failure)
        let reason=
            match change with
            | "policy" -> "allocation permission"
            | "capacity-support" -> "exact owning source support"
            | "capacity" | "capacity-body" -> "source, guard, meet or declaration premises changed"
            | _ -> "the published OrdinaryUnusedFormal/OrdinaryUnusedActual rows do not match the current complete use proof"
        Assert.Contains(reason,sprintf "%A" failure)
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication.project graph |> Result.isOk)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Returned checked text refuses loop placement and repeated consumers``(loop:bool) =
        let body=
            if loop then
                "let checked () = String.tryFromBytes [|65|]\n[<EntryPoint>]\nlet main _ =\n    let mutable remaining = 2\n    let mutable answer = 0\n    while remaining > 0 do\n        answer <- match checked () with | ValueSome text -> String.length text | ValueNone -> 0\n        remaining <- remaining - 1\n    answer\n"
            else
                "let checked () = String.tryFromBytes [|65|]\n[<EntryPoint>]\nlet main _ =\n    let value = checked ()\n    let a = match value with | ValueSome text -> String.length text | ValueNone -> 0\n    let b = match value with | ValueSome text -> String.length text | ValueNone -> 0\n    a + b\n"
        let result=EncodingFixture.returned "standard" true 4096 body
        let reason=if loop then "conditional, captured or inside a loop" else "exact Some elimination"
        Assert.Contains(CheckResult.errors result,fun diagnostic->diagnostic.Code="CCS8403" && diagnostic.Message.Contains(reason))
