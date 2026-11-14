namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module BoundarySource = Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission
module BoundaryDeclarations = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
module BoundaryWitness = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission

module private BoundaryEmissionFixture =
    let vocabulary = """module BoundaryFixture
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type PassBy = Value | Reference
type CallConv = | CDecl
type Transfer = | Borrowed | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
"""

    let descriptor = """
let combineDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "combine"
    Parameters = [| { Name = "left"; Type = Integer (Signed, 32); PassBy = Value }; { Name = "right"; Type = Integer (Signed, 32); PassBy = Value } |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
"""

    let declaration = """
[<FidelityExtern("c", "combine")>]
let combine (left: int) (right: int) : int = NativeDefault.zeroed ()
"""

    let entry = """
[<EntryPoint>]
let main _ = combine 11 7
"""

    let booleanDeclaration = """
[<FidelityExtern("c", "toggle")>]
let toggle (value: bool) : bool = NativeDefault.zeroed ()
let toggleDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "toggle"; Parameters = [| { Name = "value"; Type = Bool; PassBy = Value } |]
    ReturnType = Bool; CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
"""

    let booleanEntry = """
[<EntryPoint>]
let main _ = if toggle true then 0 else 1
"""

    let platform : PlatformContext =
        let signed: NumericRepresentation =
            { Name = "int32"; Capability = "native"; Family = "int"; Bits = 32
              MinMagnitude = "-2147483648"; MaxMagnitude = "2147483647"; Boundary = "wrap" }
        let unsigned: NumericRepresentation =
            { Name = "uint32"; Capability = "native"; Family = "uint"; Bits = 32
              MinMagnitude = "0"; MaxMagnitude = "4294967295"; Boundary = "wrap" }
        { PlatformLoading = None; PlatformId = "boundary-emission-test"
          Dimensions = Map.ofList ["Pointer", 64; "Register", 32]
          Representations = Map.ofList [signed.Name, signed; unsigned.Name, unsigned]
          EndpointReturns = Map.empty; PlatformLibraryPath = None; PlatformDescription = None
          PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.empty
          Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None
          RuntimeModel = Some RuntimeModel.Libc; AvailableMemorySpaces = []; DefaultMemorySpace = None
          ClockFrequencyMhz = None; NsPerWeightUnit = None; ProjectMemoryPolicy = None }

    let authority (context: PlatformContext) =
        let widths = context.Dimensions |> Map.toList |> List.map (fun (name, bits) ->
            sprintf "{ Name = %A; Bits = %d }" name bits) |> String.concat "; "
        let representations = context.Representations.Values |> Seq.map (fun representation ->
            sprintf "{ Name = %A; Capability = %A; Family = %A; Bits = %d; MinMagnitude = %A; MaxMagnitude = %A; Boundary = %A }"
                representation.Name representation.Capability representation.Family representation.Bits
                representation.MinMagnitude representation.MaxMagnitude representation.Boundary) |> String.concat "; "
        let declarations = """module BoundaryAuthority
type WidthDeclaration = { Name: string; Bits: int }
type Representation = { Name: string; Capability: string; Family: string; Bits: int; MinMagnitude: string; MaxMagnitude: string; Boundary: string }
type TargetCore = { Runtime: string; Widths: WidthDeclaration array; Representations: Representation array }
type PlatformDescription = { Id: string; Core: TargetCore option }
"""
        declarations + sprintf "let description = { Id = %A; Core = Some { Runtime = \"libc\"; Widths = [| %s |]; Representations = [| %s |] } }\n"
                           context.PlatformId widths representations

    let checkWithAuthority transform context body =
        let parse source path =
            match parseStringWithDefaults source path with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Expected parsed boundary source: %A" errors
        let input = parse (vocabulary + body) "boundary-emission.clef"
        match context with
        | None -> checkParsedInputsWithPlatform [input] None
        | Some context ->
            let authority = parse (transform (authority context)) "boundary-authority.clef"
            let selected =
                { context with PlatformDescription = Some "BoundaryAuthority.description"
                               PlatformSourcePaths = Set.singleton (System.IO.Path.GetFullPath "boundary-authority.clef") }
            checkParsedInputsWithPlatform [authority; input] (Some selected)

    let check context body = checkWithAuthority id context body

    let checkedGraph body =
        let result = check (Some platform) body
        DimensionalCases.noErrors result
        result.Graph

    let scalar () = checkedGraph (declaration + descriptor + entry)

    let project graph =
        match BoundarySource.project graph with
        | Ok projection -> projection
        | Error failures -> failwithf "Source boundary publication failed: %A" failures

    let rejected (graph: SemanticGraph) =
        match BoundarySource.project graph with
        | Ok projection -> failwithf "Invalid boundary was admitted: %A" projection
        | Error failures ->
            Assert.NotEmpty failures
            Assert.Contains(failures, fun failure -> failure.Occurrence.IsSome && not failure.Participants.IsEmpty)
            failures

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values
        |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
        |> Assert.Single

    // Two owned-nullable resource pairs with an fclose-shaped unary release. Each
    // pair has its own C symbols. releaseResult is the release binding's source
    // result type; releaseReturn is the ReturnType its FunctionDescriptor declares.
    let resourceSource (releaseResult: string) (releaseReturn: string) =
        let pair (suffix: string) =
            """
[<FidelityExtern("c", "stream_open_@SYMBOL@")>]
let openStream@SUFFIX@ (mode: int) : option<CHandle<unit>> = NativeDefault.zeroed ()
let openStream@SUFFIX@Descriptor: Expr<FunctionDescriptor> = <@ {
    CName = "stream_open_@SYMBOL@"; Parameters = [| { Name = "mode"; Type = Integer (Signed, 32); PassBy = Value } |]
    ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let openStream@SUFFIX@ResourceDescriptor: Expr<ResourceDescriptor> = <@ {
    Resource = OwnedNullableReturn ({ Binding = "BoundaryFixture.closeStream@SUFFIX@"; Parameter = 0 })
    Hypothesis = { Identity = "fixture-stream-@SUFFIX@"; Version = "1"; Source = "explicit status release test premise" } } @>
[<FidelityExtern("c", "stream_close_@SYMBOL@")>]
let closeStream@SUFFIX@ (handle: CHandle<unit>) : @RESULT@ = NativeDefault.zeroed ()
let closeStream@SUFFIX@Descriptor: Expr<FunctionDescriptor> = <@ {
    CName = "stream_close_@SYMBOL@"; Parameters = [| { Name = "handle"; Type = Pointer 64; PassBy = Value } |]
    ReturnType = @RETURN@; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
"""
                .Replace("@SYMBOL@", suffix.ToLowerInvariant()).Replace("@SUFFIX@", suffix)
                .Replace("@RESULT@", releaseResult).Replace("@RETURN@", releaseReturn)
        vocabulary + """
type ExternalExecutionHypothesis = { Identity: string; Version: string; Source: string }
type ResourceRelease = { Binding: string; Parameter: int }
type ResourceProtocol = OwnedNullableReturn of ResourceRelease
type ResourceDescriptor = { Resource: ResourceProtocol; Hypothesis: ExternalExecutionHypothesis }
"""
        + pair "First" + pair "Second"

    /// One complete project check of the resource declarations and a main module.
    /// The scratch project directory is deleted after the check returns.
    let resourceApplication (source: string) (main: string) =
        let root =
            System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__, "../../artifacts/scratch/boundary-emission-resource-tests", System.Guid.NewGuid().ToString("N")))
        System.IO.Directory.CreateDirectory root |> ignore
        let write (name: string) (text: string) = System.IO.File.WriteAllText(System.IO.Path.Combine(root, name), text)
        write "authority.clef" (SourcePlatformFixture.authority.Replace("Runtime = \"freestanding\"", "Runtime = \"libc\""))
        write "resource.clef" source
        write "main.clef" ("module StatusReleaseMain\n" + main)
        write "resource.fidproj" """
[package]
name="StatusReleaseBoundary"
version="0.1.0"
[compilation]
target="cpu"
memory_model="stack_only"
[build]
output_kind="console"
sources=["authority.clef","resource.clef","main.clef"]
[platform]
description="WriteAuthority.description"
runtime_model="libc"
os="linux"
arch="x86_64"
[link]
libraries=["c"]
"""
        try
            Clef.Compiler.Project.ProjectChecker.checkProject (System.IO.Path.Combine(root, "resource.fidproj"))
            |> Result.defaultWith (fun error -> failwithf "%A" error)
        finally
            System.IO.Directory.Delete(root, true)

    /// An entry point whose body is one acquisition match with the given Some arm.
    let statusMain (someArm: string) =
        "[<EntryPoint>]\nlet main _ =\n    match BoundaryFixture.openStreamFirst 8 with\n" + someArm + "    | None -> 1\n"

    /// The Void release, and four uses of a signed 32-bit status release: the status
    /// as the activation result, discarded, bound to a name, and compared by a caller.
    let releaseApplication (shape: string) =
        let status = shape <> "void"
        let source =
            if status then resourceSource "int" "Integer (Signed, 32)"
            else resourceSource "unit" "Void"
        let main =
            match shape with
            | "void" -> statusMain "    | Some handle -> BoundaryFixture.closeStreamFirst handle; 0\n"
            | "status-result" -> statusMain "    | Some handle -> BoundaryFixture.closeStreamFirst handle\n"
            | "status-discarded" -> statusMain "    | Some handle -> BoundaryFixture.closeStreamFirst handle; 0\n"
            | "status-bound" ->
                statusMain "    | Some handle ->\n        let status = BoundaryFixture.closeStreamFirst handle\n        status\n"
            | "status-caller" ->
                // The status is the resource activation's result. The caller's
                // comparison is outside the cleanup evaluation census.
                "let closeStatus () : int =\n    match BoundaryFixture.openStreamFirst 8 with\n"
                + "    | Some handle -> BoundaryFixture.closeStreamFirst handle\n    | None -> 1\n"
                + "[<EntryPoint>]\nlet main _ = if closeStatus () = 0 then 0 else 2\n"
            | _ -> failwithf "Unknown release shape: %s" shape
        status, resourceApplication source main

    let cleanupClaims (graph: SemanticGraph) =
        graph.Nodes.Values
        |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Obligation info ->
                match info.Body with
                | ObligationBody.ResourceCleanup model -> Some(node.Id, info, model)
                | _ -> None
            | _ -> None)
        |> Seq.toList

    /// Each release event of a cleanup model: the released actual and the release binding.
    let releaseEvents (cleanup: ResourceCleanupModel) =
        cleanup.Points
        |> List.choose (fun point ->
            match point.Port, point.Event with
            | EvaluationPort.Exit, Some(ResourceFlowEvent.Release(actual, binding)) -> Some(actual, binding)
            | _ -> None)
        |> List.distinct

    let diagnosticText (diagnostics: Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.Diagnostic list) =
        diagnostics |> List.map (fun diagnostic -> diagnostic.Code + ": " + diagnostic.Message) |> String.concat "\n"

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "BoundaryEmission")>]
type BoundaryEmissionCases() =
    [<Fact>]
    member _.``Declared integer reads retain exact unary values before signed64 admission``() =
        // Owner-level reader controls: reuse checked unary nodes without claiming
        // these edited graphs are admitted source/publication fixtures.
        let checked = DimensionalCases.check "let negate (value: int) = -(-value)\n"
        DimensionalCases.noErrors checked
        let graph = checked.Graph
        let unary (node: SemanticNode) =
            match node.Kind with
            | SemanticKind.Application(funcId, [arg]) ->
                match BoundaryDeclarations.valueOf graph funcId with
                | Some { Kind = SemanticKind.Intrinsic { Operation = "op_UnaryNegation" } } -> Some arg
                | _ -> None
            | _ -> None
        let outer, inner, operand =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                unary node |> Option.bind (fun innerId ->
                    graph.Nodes.TryFind innerId |> Option.bind (fun inner ->
                        unary inner |> Option.map (fun operand -> node, inner, graph.Nodes[operand]))))
            |> Assert.Single
        let kind = NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register)
        let cases =
            [ NativeLiteral.Int(System.Int64.MinValue, kind), 0, Some System.Int64.MinValue
              NativeLiteral.Int(System.Int64.MaxValue, kind), 0, Some System.Int64.MaxValue
              NativeLiteral.UInt(0UL, kind), 0, Some 0L
              NativeLiteral.UInt(uint64 System.Int64.MaxValue, kind), 0, Some System.Int64.MaxValue
              NativeLiteral.UInt(9223372036854775808UL, kind), 0, None
              NativeLiteral.UInt(System.UInt64.MaxValue, kind), 0, None
              NativeLiteral.UInt(9223372036854775808UL, kind), 1, Some System.Int64.MinValue
              NativeLiteral.Int(System.Int64.MinValue, kind), 1, None
              NativeLiteral.UInt(System.UInt64.MaxValue, kind), 1, None
              NativeLiteral.Int(5L, kind), 2, Some 5L
              NativeLiteral.Int(System.Int64.MinValue, kind), 2, Some System.Int64.MinValue ]
        for literal, depth, expected in cases do
            let leaf = { operand with Kind = SemanticKind.Literal literal; Type = Types.intType; Children = [] }
            let changed = { graph with Nodes = graph.Nodes.Add(leaf.Id, leaf) }
            let id = if depth = 0 then leaf.Id elif depth = 1 then inner.Id else outer.Id
            let actual = BoundaryDeclarations.int64Of changed id
            Assert.True((actual = expected), sprintf "Exact unary reader literal=%A depth=%d expected=%A actual=%A" literal depth expected actual)

    [<Theory>]
    [<InlineData("absent")>]
    [<InlineData("equal")>]
    [<InlineData("mismatch")>]
    [<InlineData("unreadable")>]
    member _.``WordSize presence preserves exact declarations and refuses unreadable fields`` shape =
        let transform (source: string) =
            if shape = "absent" then source
            else source.Replace("type TargetCore = {", "type TargetCore = { WordSizeBits: int;").Replace("Core = Some {", "Core = Some { WordSizeBits = 32;")
        let checked = BoundaryEmissionFixture.checkWithAuthority transform (Some BoundaryEmissionFixture.platform) "[<EntryPoint>]\nlet main _ = 0\n"
        DimensionalCases.noErrors checked
        let original = checked.Graph
        let graph, field =
            if shape = "absent" then original, None
            else
                let core = original.Nodes.Values |> Seq.find (fun node -> BoundaryDeclarations.typeName node = Some "TargetCore" && match node.Kind with SemanticKind.RecordExpr _ -> true | _ -> false)
                let _, fields = BoundaryDeclarations.recordOf original core.Id |> Option.get
                let fieldId = fields |> List.find (fst >> (=) "WordSizeBits") |> snd
                let value = BoundaryDeclarations.valueOf original fieldId |> Option.get
                let changed =
                    match value.Kind with
                    | SemanticKind.Literal(NativeLiteral.Int(_, kind)) ->
                        let literal = if shape = "unreadable" then NativeLiteral.UInt(System.UInt64.MaxValue, kind) elif shape = "mismatch" then NativeLiteral.Int(64L, kind) else NativeLiteral.Int(32L, kind)
                        { value with Kind = SemanticKind.Literal literal }
                    | _ -> failwith "Expected the declared WordSize literal."
                { original with Nodes = original.Nodes.Add(value.Id, changed) }, Some value.Id
        let findings = (BoundaryDeclarations.read graph).Findings
        match shape with
        | "unreadable" -> Assert.Contains(findings, fun finding -> finding.Node = field.Value && finding.Defect = BoundaryDeclarations.DeclarationDefect.Malformed && finding.Message = "a TargetCore's WordSizeBits must be an exact signed 64-bit integer declaration")
        | "mismatch" -> Assert.Contains(findings, fun finding -> finding.Defect = BoundaryDeclarations.DeclarationDefect.Invalid && finding.Message = "the declared Register width 32 disagrees with WordSizeBits 64")
        | _ -> Assert.Empty findings

    [<Theory>]
    [<InlineData("PointerBits", "uint-overflow")>]
    [<InlineData("ScalarAggregateRegisterBytes", "uint-overflow")>]
    [<InlineData("PointerBits", "int32-overflow")>]
    [<InlineData("ScalarAggregateRegisterBytes", "int32-overflow")>]
    [<InlineData("PointerBits", "missing")>]
    [<InlineData("Name", "missing")>]
    member _.``Malformed selected C ABI refuses before valid descriptor cardinality``(field: string, defect: string) =
        let declarations = "\ntype CAbiDescriptor = { Name: string; PointerBits: int; ScalarAggregateRegisterBytes: int }\nlet firstAbi = { Name = \"first\"; PointerBits = 32; ScalarAggregateRegisterBytes = 16 }\nlet secondAbi = { Name = \"second\"; PointerBits = 64; ScalarAggregateRegisterBytes = 16 }\n"
        let checked = BoundaryEmissionFixture.checkWithAuthority (fun source -> source + declarations) (Some BoundaryEmissionFixture.platform) "[<EntryPoint>]\nlet main _ = 0\n"
        DimensionalCases.noErrors checked
        let graph = checked.Graph
        Assert.Equal(Ok [("first", 32, 16); ("second", 64, 16)], BoundaryDeclarations.cAbiOfGraph graph)
        let binding = BoundaryEmissionFixture.binding "firstAbi" graph
        let record, fields = BoundaryDeclarations.recordOf graph (binding.Children |> List.last) |> Option.get
        let fieldId = fields |> List.find (fst >> (=) field) |> snd
        let value = BoundaryDeclarations.valueOf graph fieldId |> Option.get
        let changed =
            if defect = "missing" then
                match record.Kind with
                | SemanticKind.RecordExpr(_, info) ->
                    let revised = { record with Kind = SemanticKind.RecordExpr(fields |> List.filter (fst >> (<>) field), info) }
                    { graph with Nodes = graph.Nodes.Add(record.Id, revised) }
                | _ -> failwith "Expected a C ABI record."
            else
                match value.Kind with
                | SemanticKind.Literal(NativeLiteral.Int(_, kind)) ->
                    let literal = if defect = "uint-overflow" then NativeLiteral.UInt(System.UInt64.MaxValue, kind) else NativeLiteral.Int(4294967328L, kind)
                    { graph with Nodes = graph.Nodes.Add(value.Id, { value with Kind = SemanticKind.Literal literal }) }
                | _ -> failwith "Expected a C ABI numeric field."
        let reason = if field = "Name" then "CAbiDescriptor 'firstAbi' Name must be a string declaration." else sprintf "CAbiDescriptor 'firstAbi' %s must be an exact signed 32-bit integer declaration." field
        Assert.Equal(Error reason, BoundaryDeclarations.cAbiOfGraph changed)
        let layout : Clef.Compiler.PSGSaturation.SemanticGraph.BorrowedViews.Layout =
            { Schema = "byte"; ElementBits = 8; Range = ValueRange.unsignedOf 8; Alignment = 1; Access = "ReadOnly" }
        Assert.Equal(Error reason, Clef.Compiler.PSGSaturation.SemanticGraph.MappedSpans.forLayout changed layout)
        Assert.Equal(Error "Mapped span requires one supported declared C pointer representation.", Clef.Compiler.PSGSaturation.SemanticGraph.MappedSpans.forLayout graph layout)
        let onlySecond = { graph with Nodes = graph.Nodes.Remove(binding.Id) }
        Assert.Equal(Ok [("second", 64, 16)], BoundaryDeclarations.cAbiOfGraph onlySecond)
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.MappedSpans.forLayout onlySecond layout |> Result.isOk)

    [<Theory>]
    [<InlineData("integer")>]
    [<InlineData("boolean")>]
    member _.``Undeclared ownership preserves scalar value boundary admission`` scalarKind =
        let body =
            match scalarKind with
            | "integer" -> BoundaryEmissionFixture.declaration + BoundaryEmissionFixture.descriptor + BoundaryEmissionFixture.entry
            | "boolean" -> BoundaryEmissionFixture.booleanDeclaration + BoundaryEmissionFixture.booleanEntry
            | _ -> failwithf "Unknown scalar boundary kind: %s" scalarKind
        let graph = BoundaryEmissionFixture.checkedGraph (body.Replace("OwnershipTransfer = Borrowed", "OwnershipTransfer = Undeclared"))
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let call = Assert.Single projection.Calls.Values
        let expected = if scalarKind = "integer" then BoundaryScalar.Integer(32, true) else BoundaryScalar.Boolean
        Assert.Equal(Some expected, imported.Result)
        Assert.Equal(Some expected, call.Result)
        Assert.All(call.Arguments, fun argument -> Assert.Equal(expected, argument.Abi))
        Assert.Contains(imported.DeclarationFacts.Values, fun fact -> fact.Text = ["Undeclared"])
        Assert.True(BoundaryWitness.tryBoundary graph |> Result.isOk)

    [<Theory>]
    [<InlineData("pointer-parameter")>]
    [<InlineData("pointer-result")>]
    [<InlineData("reference-parameter")>]
    member _.``Undeclared ownership cannot grant a pointer or reference adapter`` shape =
        let body = BoundaryEmissionFixture.declaration + BoundaryEmissionFixture.descriptor + BoundaryEmissionFixture.entry
        let revised, reason =
            match shape with
            | "pointer-parameter" ->
                body.Replace("Type = Integer (Signed, 32)", "Type = Pointer 64"),
                "pointer and aggregate values require a source-settled adapter"
            | "pointer-result" ->
                body.Replace("ReturnType = Integer (Signed, 32)", "ReturnType = Pointer 64"),
                "source-settled adapter beyond the scalar C contract"
            | "reference-parameter" ->
                body.Replace("PassBy = Value", "PassBy = Reference"),
                "the reference parameter 'left' of 'combine' requires a bounded scalar array"
            | _ -> failwithf "Unknown unsupported boundary shape: %s" shape
        let result = BoundaryEmissionFixture.check (Some BoundaryEmissionFixture.platform)
                         (revised.Replace("OwnershipTransfer = Borrowed", "OwnershipTransfer = Undeclared"))
        let failures = BoundaryEmissionFixture.rejected result.Graph
        Assert.Contains(failures, fun failure -> failure.Reason.Contains reason)
        Assert.True(BoundaryWitness.admit result.Graph |> Result.isError)

    [<Fact>]
    member _.``Changing ownership declaration invalidates evidence without replacing the scalar import``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let imported = Assert.Single (BoundaryEmissionFixture.project graph).Imports.Values
        let _, fields = BoundaryDeclarations.recordOf graph imported.Identity |> Option.get
        let ownershipId = fields |> List.find (fst >> (=) "OwnershipTransfer") |> snd
        let declared = BoundaryDeclarations.valueOf graph ownershipId |> Option.get
        let revised =
            match declared.Kind with
            | SemanticKind.UnionCase("Borrowed", _, payload) ->
                { declared with Kind = SemanticKind.UnionCase("Undeclared", 1, payload) }
            | SemanticKind.DUConstruct("Borrowed", _, payload, allocated) ->
                { declared with Kind = SemanticKind.DUConstruct("Undeclared", 1, payload, allocated) }
            | other -> failwithf "Expected declared ownership case, got %A" other
        Assert.True(imported.DeclarationFacts.ContainsKey declared.Id)
        let changed = { graph with Nodes = graph.Nodes.Add(declared.Id, revised) }
        BoundaryEmissionFixture.rejected changed |> ignore
        Assert.True(BoundaryWitness.admit changed |> Result.isError)
        // Since 0a97c8d boundary projection composes numeric publication for an
        // integer-result call, and the ownership declaration is a numeric
        // range-context premise. Boundary-only settlement leaves that context
        // stale; the source pipeline settles numeric before boundary.
        let boundaryOnly = BoundaryEmissionFixture.rejected (Clef.Compiler.Nanopass.BoundarySettlement.normalize changed)
        Assert.Contains(boundaryOnly, fun failure -> failure.Reason = "NumericPublication: Invocation-context range premises changed or the producer receipt is absent; source range settlement is required.")
        let settled = changed |> Clef.Compiler.Nanopass.NumericSettlement.normalize |> Clef.Compiler.Nanopass.BoundarySettlement.normalize
        let current = Assert.Single (BoundaryEmissionFixture.project settled).Imports.Values
        Assert.Equal(imported.Identity, current.Identity)
        Assert.Equal(imported.Binding, current.Binding)
        Assert.Equal(imported.DeclarationFacts.Count, current.DeclarationFacts.Count)
        Assert.NotEqual<BoundaryDeclarationFact>(imported.DeclarationFacts[declared.Id], current.DeclarationFacts[declared.Id])
        Assert.Equal<string list>(["Undeclared"], current.DeclarationFacts[declared.Id].Text)

    [<Theory>]
    [<InlineData("CHandle<unit>")>]
    [<InlineData("option<CHandle<unit>>")>]
    member _.``Pointer returns require an admitted nullability ownership and lifetime adapter`` returnType =
        let body = """
[<FidelityExtern("c", "acquire")>]
let acquire () : ReturnedHandle = NativeDefault.zeroed ()
let acquireDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "acquire"; Parameters = [||]; ReturnType = Pointer 64
    CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
[<EntryPoint>]
let main _ = let value = acquire () in if value = value then 0 else 1
"""
        let result = BoundaryEmissionFixture.check (Some BoundaryEmissionFixture.platform) (body.Replace("ReturnedHandle", returnType))
        Assert.DoesNotContain(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8010")
        let failures = BoundaryEmissionFixture.rejected result.Graph
        Assert.Contains(failures, fun failure -> failure.Reason.Contains("source-settled adapter beyond the scalar C contract"))
        Assert.True(BoundaryWitness.admit result.Graph |> Result.isError)

    [<Fact>]
    member _.``A release declaration cannot acquire an implicit ownership premise``() =
        let body = """
[<FidelityExtern("c", "release")>]
let release (value: CHandle<unit>) : unit = NativeDefault.zeroed ()
let releaseDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "release"; Parameters = [| { Name = "value"; Type = Pointer 64; PassBy = Value } |]
    ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
let callback (value: CHandle<unit>) : unit = release value
[<EntryPoint>]
let main _ = let pointer = FnPtr.ofFunction callback in 0
"""
        let result = BoundaryEmissionFixture.check (Some BoundaryEmissionFixture.platform) body
        let failures = BoundaryEmissionFixture.rejected result.Graph
        Assert.Contains(failures, fun failure -> failure.Reason.Contains("pointer and aggregate values require a source-settled adapter"))
        Assert.True(BoundaryWitness.admit result.Graph |> Result.isError)

    [<Fact>]
    member _.``Quoted boundary descriptor retains declaration evidence without runtime allocation residence``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let descriptor =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.RecordExpr(fields, _) when imported.DeclarationFacts.ContainsKey node.Id &&
                                                           (fields |> List.exists (fst >> (=) "CName")) -> Some node
                | _ -> None)
            |> Assert.Single
        Assert.False descriptor.IsReachable
        Assert.True(graph.Codata.Value.Escapes.ContainsKey descriptor.Id)
        let selected = graph.Codata.Value.WitnessLiveRows |> Option.defaultWith (fun () -> failwith "The source-selected fact account is absent.")
        Assert.Contains(descriptor.Id, selected.FactIdentities)
        Assert.False(selected.Codata.Escapes.ContainsKey descriptor.Id)
        Assert.False(selected.Emission.Callable.ValueShapes.ContainsKey descriptor.Id)
        Assert.False(selected.Emission.Callable.AliasTargets.ContainsKey descriptor.Id)
        Assert.DoesNotContain(descriptor.Id, selected.Emission.Callable.ClosedData)
        Assert.False(selected.Emission.Callable.Supports.ContainsKey descriptor.Id)
        Assert.False(selected.Emission.Numeric.SourceTypes.ContainsKey descriptor.Id)
        Assert.False(selected.Emission.Numeric.OccurrenceRepresentations.ContainsKey descriptor.Id)
        Assert.False(selected.Demand.Operands.ContainsKey descriptor.Id)
        Assert.False(selected.Demand.Relations.ContainsKey descriptor.Id)
        let revision = Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph |> Result.defaultWith (sprintf "%A" >> failwith)
        let publicId = Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId
        Assert.False(revision.Nodes.ContainsKey(publicId descriptor.Id))
        Assert.False(revision.Codata.Escapes.ContainsKey(publicId descriptor.Id))
        Assert.False(revision.Emission.Callable.ValueShapes.ContainsKey(publicId descriptor.Id))
        Assert.False(revision.Emission.Numeric.SourceTypes.ContainsKey(publicId descriptor.Id))
        Assert.Equal(Clef.Compiler.Baker.Ingredients.PublishedFactRows.mapBoundaryImport imported,
                     revision.Emission.Boundary.Imports[publicId imported.Identity])
        Assert.True(graph.Codata.Value.Escapes.ContainsKey descriptor.Id)

    [<Fact>]
    member _.``Scalar publication preserves descriptor identity module scope and argument order``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let call = Assert.Single projection.Calls.Values
        let binding = BoundaryEmissionFixture.binding "combine" graph
        let descriptor = Assert.Single (BoundaryDeclarations.readDescriptors graph).Functions
        let parameters, body = BoundaryDeclarations.lambdaOfBinding graph binding.Id |> Option.get
        let scope = binding.Parent |> Option.get
        let site = graph.Nodes[call.Site]
        let callee, actuals =
            match site.Kind with
            | SemanticKind.Application(callee, actuals) -> callee, actuals
            | other -> failwithf "Boundary call lost its source application: %A" other
        Assert.Equal(descriptor.Node, imported.Identity)
        Assert.Equal(binding.Id, imported.Binding)
        Assert.Equal(scope, imported.Scope)
        Assert.Equal<Set<NodeId>>(Set.singleton binding.Id, projection.DeclarationLeaves)
        for participant in List.tail imported.DeclarationPath @ (parameters |> List.map (fun (_, _, formal) -> formal)) @ [body] do
            Assert.Contains(participant, projection.DeclarationOnly)
        Assert.DoesNotContain(binding.Id, projection.DeclarationOnly)
        Assert.Empty(Set.intersect projection.DeclarationOnly (Set.ofList (call.Site :: callee :: actuals)))
        Assert.Equal("c", imported.Library)
        Assert.Equal("combine", imported.Symbol)
        Assert.Equal("CDecl", imported.CallingConvention)
        Assert.Equal<NodeId list>([imported.Identity], projection.ByScope[scope])
        Assert.Equal<(NodeId * BoundaryScalar) list>(
            parameters |> List.map (fun (_, _, formal) -> formal, BoundaryScalar.Integer(32, true)), imported.Parameters)
        Assert.Equal(Some(BoundaryScalar.Integer(32, true)), imported.Result)
        Assert.Equal(imported.Identity, call.Import)
        Assert.Equal(callee, call.Callee)
        Assert.Equal<NodeId list>(actuals, call.Arguments |> List.map _.Actual)
        Assert.Equal<NodeId list>(parameters |> List.map (fun (_, _, formal) -> formal), call.Arguments |> List.map _.Formal)
        Assert.All(call.Arguments, fun argument -> Assert.Equal(BoundaryScalar.Integer(32, true), argument.Abi))
        let omitted =
            graph.Codata.Value.OrdinaryDemand.Parameters.TryFind (List.last imported.DeclarationPath)
            |> Option.defaultValue Set.empty
        for argument in call.Arguments do
            Assert.DoesNotContain(argument.Actual, graph.Codata.Value.OrdinaryDemand.DeferredOnly)
            Assert.DoesNotContain(argument.Formal, omitted)
        Assert.Empty call.ErasedUnitArguments
        Assert.Equal(imported.Result, call.Result)
        let domainRow = graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.BoundaryDomain _ -> true | _ -> false) |> Assert.Single
        Assert.Equal<Set<NodeId>>(
            Set.add domainRow.Target (Set.union (imported.DeclarationFacts |> Map.keys |> Set.ofSeq)
                (Set.ofList (scope :: body :: (BoundaryEmissionFixture.binding "combineDescriptor" graph).Id ::
                             (parameters |> List.map (fun (_, _, formal) -> formal)) @ imported.DeclarationPath))),
            imported.Participants)
        Assert.Equal(binding.Id, List.head imported.DeclarationPath)
        match graph.Nodes[List.last imported.DeclarationPath].Kind with
        | SemanticKind.Lambda(formals, declaredBody, _, _, _) ->
            Assert.Equal<(string * NativeType * NodeId) list>(parameters, formals)
            Assert.Equal(body, declaredBody)
        | other -> failwithf "The admitted declaration path lost its source lambda: %A" other
        Assert.Equal<Set<NodeId>>(
            Set.union imported.Participants (Set.ofList (call.Site :: callee :: actuals)), call.Participants)
        let sourceMeets = graph.Codata.Value.Meets.TryFind call.Site |> Option.defaultValue []
        for argument in call.Arguments do
            Assert.Equal<Meet option>(sourceMeets |> List.tryFind (fun meet -> meet.Operand = argument.Actual), argument.Adaptation)
        Assert.Equal<Meet option>(sourceMeets |> List.tryFind (fun meet -> meet.Operand = call.Site), call.ResultAdaptation)
        for participant in [imported.Identity; binding.Id; scope] do
            Assert.Contains(participant, imported.Participants)
            Assert.Contains(participant, call.Participants)
        for participant in call.Site :: callee :: actuals @ (parameters |> List.map (fun (_, _, formal) -> formal)) do
            Assert.Contains(participant, call.Participants)
        let published =
            match BoundaryWitness.tryBoundary graph with
            | Ok published -> published
            | Error reason -> failwith reason
        Assert.Equal<BoundaryEmissionProjection>(projection, published)

    [<Fact>]
    member _.``Unit domain is erased explicitly and void result has no scalar ABI``() =
        let graph = BoundaryEmissionFixture.checkedGraph """
[<FidelityExtern("c", "tick")>]
let tick () : unit = NativeDefault.zeroed ()
let tickDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "tick"; Parameters = [||]; ReturnType = Void
    CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
[<EntryPoint>]
let main _ =
    tick ()
    0
"""
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let call = Assert.Single projection.Calls.Values
        let actuals =
            match graph.Nodes[call.Site].Kind with
            | SemanticKind.Application(_, actuals) -> actuals
            | other -> failwithf "Expected unit application, got %A" other
        Assert.Empty imported.Parameters
        Assert.Empty call.Arguments
        Assert.Equal<NodeId list>(actuals, call.ErasedUnitArguments)
        Assert.Single call.ErasedUnitArguments |> ignore
        Assert.True imported.Result.IsNone
        Assert.True call.Result.IsNone

    [<Fact>]
    member _.``Boolean descriptor retains the boolean boundary universe``() =
        let graph = BoundaryEmissionFixture.checkedGraph (BoundaryEmissionFixture.booleanDeclaration + BoundaryEmissionFixture.booleanEntry)
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let call = Assert.Single projection.Calls.Values
        Assert.Equal(BoundaryScalar.Boolean, snd (Assert.Single imported.Parameters))
        Assert.Equal(Some BoundaryScalar.Boolean, imported.Result)
        Assert.Equal(BoundaryScalar.Boolean, (Assert.Single call.Arguments).Abi)
        Assert.True (Assert.Single call.Arguments).Adaptation.IsNone

    [<Theory>]
    [<InlineData("repeated-integer")>]
    [<InlineData("boolean")>]
    member _.``Plain scalar public arguments retain their exact current meets`` shape =
        let body, expected =
            match shape with
            | "repeated-integer" ->
                BoundaryEmissionFixture.declaration +
                BoundaryEmissionFixture.descriptor.Replace(
                    "Name = \"right\"; Type = Integer (Signed, 32)",
                    "Name = \"right\"; Type = Integer (Signed, 64)") +
                BoundaryEmissionFixture.entry.Replace("combine 11 7", "let x = 11 in combine x x"),
                [BoundaryScalar.Integer(32, true); BoundaryScalar.Integer(64, true)]
            | "boolean" ->
                BoundaryEmissionFixture.booleanDeclaration + BoundaryEmissionFixture.booleanEntry,
                [BoundaryScalar.Boolean]
            | _ -> failwithf "Unknown plain scalar shape: %s" shape
        let context =
            if shape = "repeated-integer" then
                let signed64: NumericRepresentation =
                    { Name = "int64"; Capability = "native"; Family = "int"; Bits = 64
                      MinMagnitude = "-9223372036854775808"; MaxMagnitude = "9223372036854775807"; Boundary = "wrap" }
                { BoundaryEmissionFixture.platform with
                    Representations = BoundaryEmissionFixture.platform.Representations.Add(signed64.Name, signed64) }
            else BoundaryEmissionFixture.platform
        let result = BoundaryEmissionFixture.check (Some context) body
        let graph = result.Graph
        let projected = BoundarySource.project graph
        match projected with
        | Ok projection ->
            for call in projection.Calls.Values do
                printfn "G1 shape=%s site=%A actuals=%A currentMeets=%A" shape call.Site
                    (call.Arguments |> List.map (fun argument -> argument.Actual, graph.Nodes[argument.Actual].Kind, argument.Abi, argument.Adaptation))
                    (graph.Codata.Value.Meets.TryFind call.Site |> Option.defaultValue [])
        | Error failures -> printfn "G1 shape=%s failures=%A currentMeets=%A" shape failures graph.Codata.Value.Meets
        DimensionalCases.noErrors result
        let projection = projected |> Result.defaultWith (sprintf "%A" >> failwith)
        let call = Assert.Single projection.Calls.Values
        let imported = Assert.Single projection.Imports.Values
        Assert.Equal<BoundaryScalar list>(expected, call.Arguments |> List.map _.Abi)
        Assert.Equal<(NodeId * BoundaryScalar) list>(imported.Parameters, call.Arguments |> List.map (fun argument -> argument.Formal, argument.Abi))
        if shape = "repeated-integer" then
            let left, right = call.Arguments[0], call.Arguments[1]
            Assert.NotEqual(left.Actual, right.Actual)
            match graph.Nodes[left.Actual].Kind, graph.Nodes[right.Actual].Kind with
            | SemanticKind.VarRef("x", Some leftBinding), SemanticKind.VarRef("x", Some rightBinding) ->
                Assert.Equal(leftBinding, rightBinding)
            | actuals -> failwithf "The repeated variable lost its distinct source references: %A" actuals
            Assert.True left.Adaptation.IsNone
            let meet = right.Adaptation |> Option.defaultWith (fun () -> failwith "The i64 argument lost its own current meet.")
            Assert.Equal(right.Actual, meet.Operand)
            Assert.Equal(32, meet.From)
            Assert.Equal(64, meet.To)
            Assert.Equal(MeetKind.ExtendUnsigned, meet.Adapt)
        let sourceMeets = graph.Codata.Value.Meets.TryFind call.Site |> Option.defaultValue []
        for argument in call.Arguments do
            let exact = sourceMeets |> List.filter (fun meet -> meet.Operand = argument.Actual) |> List.distinct
            Assert.True(exact.Length <= 1, sprintf "The source argument has ambiguous current meets: %A" exact)
            Assert.Equal<Meet option>(List.tryHead exact, argument.Adaptation)
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph
            |> Result.defaultWith (sprintf "%A" >> failwith)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let publicId = Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId
        let published = revision.Emission.Boundary.Calls[publicId call.Site]
        Assert.Equal<Fidelity.PSG.NodeId list>(call.Arguments |> List.map (fun argument -> publicId argument.Actual), published.Arguments |> List.map _.Actual)
        Assert.Equal<Fidelity.PSG.NodeId list>(call.Arguments |> List.map (fun argument -> publicId argument.Formal), published.Arguments |> List.map _.Formal)
        let current = revision.Codata.Meets.TryFind published.Site |> Option.defaultValue []
        for argument in published.Arguments do
            let exact = current |> List.filter (fun meet -> meet.Operand = argument.Actual) |> List.distinct
            Assert.True(exact.Length <= 1, sprintf "The public argument has ambiguous current meets: %A" exact)
            Assert.Equal<Fidelity.PSG.Meet option>(List.tryHead exact, argument.Adaptation)
            if shape = "boolean" then
                Assert.Empty exact
                Assert.True argument.Adaptation.IsNone

    [<Fact>]
    member _.``Foreign alias rewrite retains its exact import call and callable origin``() =
        let graph = BoundaryEmissionFixture.checkedGraph
                        (BoundaryEmissionFixture.booleanDeclaration + "\nlet alias = toggle\n" +
                         BoundaryEmissionFixture.booleanEntry.Replace("toggle true", "alias true"))
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let call = Assert.Single projection.Calls.Values
        let declaration = BoundaryEmissionFixture.binding "toggle" graph
        let alias = BoundaryEmissionFixture.binding "alias" graph
        Assert.Equal(declaration.Id, imported.Binding)
        Assert.Equal(imported.Identity, call.Import)
        Assert.Contains(call.Callee, call.Participants)
        Assert.Contains(declaration.Id, call.Participants)
        match graph.Nodes[call.Callee].Kind with
        | SemanticKind.VarRef("toggle", Some binding) -> Assert.Equal(declaration.Id, binding)
        | other -> failwithf "The rewritten foreign call lost its exact declaration reference: %A" other
        // Baker reifies the value-position alias through a capture-free
        // wrapper. The retained origin belongs to that rewrite; the boundary
        // call's current direct callee belongs to the original declaration.
        let origin = graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.CallableReferenceOrigin &&
            (match edge.Sources with [source; _] -> source = alias.Id | _ -> false)) |> Assert.Single
        let implementation = List.item 1 origin.Sources
        match graph.Nodes[origin.Target].Kind with
        | SemanticKind.VarRef("alias", Some target) -> Assert.Equal(implementation, target)
        | other -> failwithf "The alias rewrite lost its exact callable reference: %A" other
        let wrapperParameters, wrapperBody = BoundaryDeclarations.lambdaOfBinding graph implementation |> Option.get
        Assert.Equal(call.Site, wrapperBody)
        let wrapperLambda = Assert.Single graph.Nodes[implementation].Children
        let omitted = graph.Codata.Value.OrdinaryDemand.Parameters.TryFind wrapperLambda |> Option.defaultValue Set.empty
        for _, _, formal in wrapperParameters do Assert.DoesNotContain(formal, omitted)

    [<Theory>]
    [<InlineData("missing")>]
    [<InlineData("duplicate")>]
    [<InlineData("symbol-mismatch")>]
    [<InlineData("pointer")>]
    member _.``Incomplete ambiguous mismatched and unsupported declarations fail at source`` defect =
        let descriptor = BoundaryEmissionFixture.descriptor
        let revised =
            match defect with
            | "missing" -> ""
            | "duplicate" -> descriptor + descriptor
            | "symbol-mismatch" -> descriptor.Replace("CName = \"combine\"", "CName = \"other\"")
            | "pointer" -> descriptor.Replace("Type = Integer (Signed, 32)", "Type = Pointer 64")
            | _ -> failwithf "Unknown boundary defect: %s" defect
        let result = BoundaryEmissionFixture.check (Some BoundaryEmissionFixture.platform)
                         (BoundaryEmissionFixture.declaration + revised + BoundaryEmissionFixture.entry)
        let binding = BoundaryEmissionFixture.binding "combine" result.Graph
        let failures = BoundaryEmissionFixture.rejected result.Graph
        Assert.Contains(failures, fun failure -> failure.Participants.Contains binding.Id)

    [<Fact>]
    member _.``Explicit libc runtime remains authoritative when startup metadata exists``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let context = { graph.Platform.Value with FreestandingStartup = Some FreestandingStartup.defaultLinux_x86_64 }
        let settled = Clef.Compiler.Nanopass.BoundarySettlement.normalize { graph with Platform = Some context }
        let projection = BoundaryEmissionFixture.project settled
        Assert.Single projection.Imports |> ignore
        Assert.Single projection.Calls |> ignore

    [<Theory>]
    [<InlineData("bare")>]
    [<InlineData("freestanding")>]
    [<InlineData("undeclared")>]
    [<InlineData("no-target")>]
    member _.``Reachable C calls require explicit libc runtime authority`` runtime =
        let graph = BoundaryEmissionFixture.scalar ()
        let selected =
            match runtime with
            | "bare" -> Some { graph.Platform.Value with RuntimeModel = Some RuntimeModel.Bare }
            | "freestanding" -> Some { graph.Platform.Value with RuntimeModel = Some RuntimeModel.Freestanding }
            | "undeclared" -> Some { graph.Platform.Value with RuntimeModel = None }
            | "no-target" -> None
            | _ -> failwithf "Unknown runtime: %s" runtime
        let changed =
            if runtime = "undeclared" then
                let core = (BoundaryDeclarations.resolve graph |> Option.get).Core.Value
                let _, fields = BoundaryDeclarations.recordOf graph core.Node |> Option.get
                let runtimeId = fields |> List.find (fst >> (=) "Runtime") |> snd
                let declared = BoundaryDeclarations.valueOf graph runtimeId |> Option.get
                { graph with Platform = selected
                             Nodes = graph.Nodes.Add(declared.Id, { declared with Kind = SemanticKind.Literal (NativeLiteral.String "") }) }
            else { graph with Platform = selected }
        BoundaryEmissionFixture.rejected changed |> ignore
        let settled = Clef.Compiler.Nanopass.BoundarySettlement.normalize changed
        let failures = BoundaryEmissionFixture.rejected settled
        if runtime = "bare" || runtime = "freestanding" then
            Assert.Contains(failures, fun failure -> failure.Reason.Contains "project consistency")

    [<Fact>]
    member _.``Target free unreachable declarations project an empty boundary without witness authority``() =
        let result = BoundaryEmissionFixture.check None
                         (BoundaryEmissionFixture.declaration + BoundaryEmissionFixture.descriptor + "\n[<EntryPoint>]\nlet main _ = 0\n")
        DimensionalCases.noErrors result
        let projection = BoundaryEmissionFixture.project result.Graph
        Assert.Empty projection.Imports
        Assert.Empty projection.ByScope
        Assert.Empty projection.Calls
        Assert.Empty projection.DeclarationLeaves
        Assert.Empty projection.DeclarationOnly
        // Target-free checking has not committed every witness domain. Its
        // empty boundary projection does not grant complete witness authority.
        Assert.True(BoundaryWitness.tryBoundary result.Graph |> Result.isError)

    [<Fact>]
    member _.``Changed actual order retracts the published call contract``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let projection = BoundaryEmissionFixture.project graph
        let call = Assert.Single projection.Calls.Values
        let site = graph.Nodes[call.Site]
        let revised =
            match site.Kind with
            | SemanticKind.Application(callee, actuals) ->
                { site with Kind = SemanticKind.Application(callee, List.rev actuals) }
            | other -> failwithf "Expected boundary application, got %A" other
        let changed = { graph with Nodes = graph.Nodes.Add(site.Id, revised) }
        Assert.True(BoundaryWitness.admit changed |> Result.isError)
        BoundaryEmissionFixture.rejected changed |> ignore

    [<Fact>]
    member _.``Boundary recipe records ordered relations actual range obligations and rewrite evidence``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let call = Assert.Single (BoundaryEmissionFixture.project graph).Calls.Values
        let declarationRows = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryDeclaration value -> Some value | _ -> None)
        Assert.Single declarationRows |> ignore
        let operands = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryOperand value -> Some (edge.Ordinal, value) | _ -> None) |> List.sortBy fst
        Assert.Equal<BoundaryOperand list>(call.Arguments, operands |> List.map snd)
        let coverages = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryCoverage value -> Some value | _ -> None)
        // Since 0a97c8d the integer foreign result is owned by numeric
        // publication (ForeignResultUses), not by the boundary coverage census:
        // each scalar operand carries boundary coverage and the result does not.
        Assert.Equal(Some(BoundaryScalar.Integer(32, true)), call.Result)
        Assert.Equal<int list>([0 .. call.Arguments.Length - 1], coverages |> List.map _.Ordinal |> List.sort)
        let numeric =
            match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph with
            | Ok numeric -> numeric
            | Error failures -> failwithf "Missing numeric projection: %A" failures
        let account = numeric.ForeignResultUses |> List.filter (fun account -> account.Application.Call = call.Site) |> Assert.Single
        Assert.Equal<ForeignResultProofRole list>([ForeignResultProofRole.AbiNarrowing], account.Claims |> List.map fst)
        for coverage in coverages do
            Assert.Contains(graph.Edges, fun edge -> edge.Target = coverage.Obligation && edge.Role = EdgeRole.Constrains)
            Assert.Contains(graph.Edges, fun edge -> edge.Target = coverage.Obligation && edge.Role = EdgeRole.EnrichedWith)
            Assert.Contains(graph.Edges, fun edge -> edge.Target = call.Site && edge.Ordinal = coverage.Ordinal && edge.Role = EdgeRole.BoundaryProof BoundaryProofOutcome.Proven)
            match graph.Nodes[coverage.Obligation].Kind with
            | SemanticKind.Obligation info -> Assert.Equal("boundary-range-coverage", info.Kind)
            | other -> failwithf "Expected a real range obligation, got %A" other

    [<Theory>]
    [<InlineData("missing-proof")>]
    [<InlineData("refuted-proof")>]
    [<InlineData("missing-call")>]
    [<InlineData("duplicate-operand")>]
    [<InlineData("missing-rewrite")>]
    member _.``Publication validates complete source rows and cannot create or repair evidence`` defect =
        let graph = BoundaryEmissionFixture.scalar ()
        let edges =
            match defect with
            | "missing-proof" -> graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.BoundaryProof _ -> false | _ -> true)
            | "refuted-proof" -> graph.Edges |> List.map (fun edge -> match edge.Role with EdgeRole.BoundaryProof _ -> { edge with Role = EdgeRole.BoundaryProof BoundaryProofOutcome.Refuted } | _ -> edge)
            | "missing-call" -> graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.BoundaryCall _ -> false | _ -> true)
            | "duplicate-operand" ->
                (graph.Edges |> List.find (fun edge -> match edge.Role with EdgeRole.BoundaryOperand _ -> true | _ -> false)) :: graph.Edges
            | "missing-rewrite" -> graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.EnrichedWith)
            | _ -> failwith "Unknown relation defect"
        BoundaryEmissionFixture.rejected { graph with Edges = edges } |> ignore

    [<Fact>]
    member _.``Synthetic actual rewriting requires current invocation context before boundary publication``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let call = Assert.Single (BoundaryEmissionFixture.project graph).Calls.Values
        let site = graph.Nodes[call.Site]
        let repeated = [call.Arguments.Head.Actual; call.Arguments.Head.Actual]
        let changedSite = { site with Kind = SemanticKind.Application(call.Callee, repeated); Children = call.Callee :: repeated }
        let changed = { graph with Nodes = graph.Nodes.Add(site.Id, changedSite) }
        BoundaryEmissionFixture.rejected changed |> ignore
        let settled = Clef.Compiler.Nanopass.BoundarySettlement.normalize changed
        let failures = BoundaryEmissionFixture.rejected settled
        Assert.Contains(failures, fun failure ->
            failure.Reason = "NumericPublication: Invocation-context range premises changed or the producer receipt is absent; source range settlement is required.")
        Assert.True(BoundaryWitness.tryBoundary settled |> Result.isError)

    [<Fact>]
    member _.``Refuted range coverage remains an obligation and prevents publication``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let call = Assert.Single (BoundaryEmissionFixture.project graph).Calls.Values
        let actual = graph.Nodes[call.Arguments.Head.Actual]
        let changed = { graph with Nodes = graph.Nodes.Add(actual.Id, { actual with ValueRange = Some (ValueRange.Bounded(0I, 2147483648I)) }) }
        let settled = Clef.Compiler.Nanopass.BoundarySettlement.normalize changed
        BoundaryEmissionFixture.rejected settled |> ignore
        Assert.Contains(settled.Edges, fun edge -> edge.Role = EdgeRole.BoundaryProof BoundaryProofOutcome.Refuted)
        Assert.Contains(settled.Nodes.Values, fun node ->
            match node.Kind with
            | SemanticKind.Obligation info -> info.Body = ObligationBody.IntegerRepresentationCoverage(0I, 2147483648I, -2147483648I, 2147483647I)
            | _ -> false)

    [<Fact>]
    member _.``Resolved source runtime remains authoritative without a project runtime claim``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let context = { graph.Platform.Value with RuntimeModel = None }
        let changed = { graph with Platform = Some context }
        // Since 0a97c8d boundary projection composes numeric publication for an
        // integer-result call, whose invocation context retains the full
        // platform premise. Boundary-only settlement leaves that context stale;
        // the source pipeline settles numeric before boundary.
        let boundaryOnly = BoundaryEmissionFixture.rejected (Clef.Compiler.Nanopass.BoundarySettlement.normalize changed)
        Assert.Contains(boundaryOnly, fun failure -> failure.Reason = "NumericPublication: Invocation-context range premises changed or the producer receipt is absent; source range settlement is required.")
        let settled = changed |> Clef.Compiler.Nanopass.NumericSettlement.normalize |> Clef.Compiler.Nanopass.BoundarySettlement.normalize
        let projection = BoundaryEmissionFixture.project settled
        Assert.Single projection.Imports |> ignore
        Assert.Equal<Set<string>>(Set.singleton "c", projection.Links)

    [<Theory>]
    [<InlineData("non-tuple-payload")>]
    [<InlineData("unrepresentable-width")>]
    member _.``One typed TypeRef reader rejects malformed shape and unrepresentable width`` defect =
        let graph = BoundaryEmissionFixture.scalar ()
        let imported = Assert.Single (BoundaryEmissionFixture.project graph).Imports.Values
        let _, fields = BoundaryDeclarations.recordOf graph imported.Identity |> Option.get
        let typeId = fields |> List.find (fst >> (=) "ReturnType") |> snd
        Assert.Equal(Ok (BoundaryDeclarations.DeclaredTypeRef.Scalar (BoundaryScalar.Integer(32, true))), BoundaryDeclarations.readTypeRef graph typeId)
        let _, _, payload = BoundaryDeclarations.caseOf graph typeId |> Option.get
        let pair = BoundaryDeclarations.valueOf graph payload.Value |> Option.get
        let sign, bits = match pair.Kind with SemanticKind.TupleExpr [sign; bits] -> sign, bits | other -> failwithf "Expected TypeRef tuple: %A" other
        let revised =
            match defect with
            | "non-tuple-payload" -> { pair with Kind = SemanticKind.Application(sign, [bits]); Children = [sign; bits] }
            | "unrepresentable-width" ->
                let width = graph.Nodes[bits]
                match width.Kind with
                | SemanticKind.Literal (NativeLiteral.Int(_, kind)) -> { width with Kind = SemanticKind.Literal (NativeLiteral.Int(int64 System.Int32.MaxValue + 1L, kind)) }
                | other -> failwithf "Expected literal TypeRef width: %A" other
            | _ -> failwith "Unknown TypeRef defect"
        let changed = { graph with Nodes = graph.Nodes.Add(revised.Id, revised) }
        Assert.True(BoundaryDeclarations.readTypeRef changed typeId |> Result.isError)
        Assert.NotEmpty((BoundaryDeclarations.readDescriptors changed).Findings)

    [<Theory>]
    [<InlineData("extern")>]
    [<InlineData("descriptor")>]
    member _.``Deleting a declared module member retracts the import owner contract`` memberRole =
        let graph = BoundaryEmissionFixture.scalar ()
        let imported = Assert.Single (BoundaryEmissionFixture.project graph).Imports.Values
        let scope = graph.Nodes[imported.Scope]
        let memberId =
            match memberRole with
            | "extern" -> imported.Binding
            | "descriptor" -> (BoundaryEmissionFixture.binding "combineDescriptor" graph).Id
            | _ -> failwithf "Unknown boundary module member role: %s" memberRole
        let changedScope =
            match scope.Kind with
            | SemanticKind.ModuleDef(name, members) ->
                Assert.Contains(memberId, members)
                { scope with Kind = SemanticKind.ModuleDef(name, members |> List.filter ((<>) memberId)) }
            | other -> failwithf "Expected admitted module owner, got %A" other
        let changed = { graph with Nodes = graph.Nodes.Add(scope.Id, changedScope) }
        BoundaryEmissionFixture.rejected changed |> ignore
        Assert.True(BoundaryWitness.admit changed |> Result.isError)

    [<Fact>]
    member _.``Changed descriptor symbol retracts the published import contract``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let descriptor = graph.Nodes[imported.Identity]
        let cname =
            match descriptor.Kind with
            | SemanticKind.RecordExpr(fields, _) -> fields |> List.find (fst >> (=) "CName") |> snd
            | other -> failwithf "Expected exact descriptor record identity, got %A" other
        let node = graph.Nodes[cname]
        let changed = { graph with Nodes = graph.Nodes.Add(cname, { node with Kind = SemanticKind.Literal(NativeLiteral.String "changed") }) }
        BoundaryEmissionFixture.rejected changed |> ignore
        Assert.True(BoundaryWitness.admit changed |> Result.isError)

    [<Theory>]
    [<InlineData("reference")>]
    [<InlineData("binding-value")>]
    member _.``Executable uses cannot borrow an external placeholder body`` useKind =
        let graph = BoundaryEmissionFixture.scalar ()
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let call = Assert.Single projection.Calls.Values
        let _, body = BoundaryDeclarations.lambdaOfBinding graph imported.Binding |> Option.get
        let actual = graph.Nodes[call.Arguments.Head.Actual]
        let changed, useSite =
            match useKind with
            | "reference" ->
                { graph with Nodes = graph.Nodes.Add(actual.Id, { actual with Kind = SemanticKind.VarRef("placeholder", Some body); Children = [] }) }, actual.Id
            | "binding-value" ->
                let outside =
                    { actual with Id = NodeId.fresh(); Kind = SemanticKind.Binding("outside", false, false, None)
                                  Children = [body]; Parent = Some imported.Scope; Metadata = Map.empty }
                let owner = graph.Nodes[imported.Scope]
                let owner =
                    match owner.Kind with
                    | SemanticKind.ModuleDef(name, members) -> { owner with Kind = SemanticKind.ModuleDef(name, members @ [outside.Id]) }
                    | other -> failwithf "Expected exact source module owner, got %A" other
                { graph with Nodes = graph.Nodes.Add(outside.Id, outside).Add(owner.Id, owner) }, outside.Id
            | _ -> failwithf "Unknown executable placeholder use: %s" useKind
        BoundaryEmissionFixture.rejected changed |> ignore
        let settled = Clef.Compiler.Nanopass.BoundarySettlement.normalize changed
        let failures = BoundaryEmissionFixture.rejected settled
        Assert.Contains(failures, fun failure ->
            failure.Occurrence = Some useSite && failure.Participants.Contains body &&
            failure.Reason.Contains "outside its declaration leaf")
        Assert.True(BoundaryWitness.admit changed |> Result.isError)

    [<Fact>]
    member _.``Negative scalar extension preserves the settled meet and rejects an unsigned replacement``() =
        let signed8: NumericRepresentation =
            { Name = "int8"; Capability = "native"; Family = "int"; Bits = 8
              MinMagnitude = "-128"; MaxMagnitude = "127"; Boundary = "wrap" }
        let context =
            { BoundaryEmissionFixture.platform with
                Representations = BoundaryEmissionFixture.platform.Representations.Add(signed8.Name, signed8) }
        let result = BoundaryEmissionFixture.check (Some context)
                         (BoundaryEmissionFixture.declaration + BoundaryEmissionFixture.descriptor +
                          BoundaryEmissionFixture.entry.Replace("combine 11 7", "combine (-11) 7"))
        DimensionalCases.noErrors result
        let graph = result.Graph
        let projection = BoundaryEmissionFixture.project graph
        let call = Assert.Single projection.Calls.Values
        let signed = call.Arguments |> List.choose _.Adaptation |> List.filter (fun meet -> meet.Adapt = MeetKind.ExtendSigned) |> Assert.Single
        Assert.Equal(8, signed.From)
        Assert.Equal(32, signed.To)
        Assert.Contains(signed, graph.Codata.Value.Meets[call.Site])
        let changedMeets = graph.Codata.Value.Meets[call.Site] |> List.map (fun meet ->
            if meet = signed then { meet with Adapt = MeetKind.ExtendUnsigned } else meet)
        let changed =
            { graph with Codata = lazy { graph.Codata.Value with Meets = graph.Codata.Value.Meets.Add(call.Site, changedMeets) } }
        BoundaryEmissionFixture.rejected changed |> ignore
        Assert.True(BoundaryWitness.admit changed |> Result.isError)

    [<Fact>]
    member _.``Unsigned foreign result retains the source selected unsigned representation``() =
        let graph = BoundaryEmissionFixture.checkedGraph
                        (BoundaryEmissionFixture.declaration +
                         BoundaryEmissionFixture.descriptor.Replace("ReturnType = Integer (Signed, 32)", "ReturnType = Integer (Unsigned, 32)") +
                         BoundaryEmissionFixture.entry)
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let call = Assert.Single projection.Calls.Values
        Assert.Equal(Some(BoundaryScalar.Integer(32, false)), imported.Result)
        Assert.Equal(imported.Result, call.Result)
        Assert.Equal(Some(ValueRange.unsignedOf 32), graph.Nodes[call.Site].ValueRange)
        let selected = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedRepresentation graph call.Site |> Option.get
        Assert.Equal("uint32", selected.Name)
        Assert.Equal("uint", selected.Family)
        Assert.Equal(32, selected.Bits)
        Assert.True call.ResultAdaptation.IsNone

    [<Fact>]
    member _.``Declared foreign return range rejects narrowing justified only by a changed call range``() =
        let unsigned8: NumericRepresentation =
            { Name = "uint8"; Capability = "native"; Family = "uint"; Bits = 8
              MinMagnitude = "0"; MaxMagnitude = "255"; Boundary = "wrap" }
        let context =
            { BoundaryEmissionFixture.platform with
                Representations = BoundaryEmissionFixture.platform.Representations.Add(unsigned8.Name, unsigned8) }
        let result = BoundaryEmissionFixture.check (Some context)
                         (BoundaryEmissionFixture.declaration + BoundaryEmissionFixture.descriptor +
                          "\n[<EntryPoint>]\nlet main _ = if combine 11 7 = 0 then 0 else 1\n")
        DimensionalCases.noErrors result
        let graph = result.Graph
        let projection = BoundaryEmissionFixture.project graph
        let call = Assert.Single projection.Calls.Values
        let site = graph.Nodes[call.Site]
        Assert.Equal(Some(BoundaryScalar.Integer(32, true)), call.Result)
        Assert.True call.ResultAdaptation.IsNone
        // This deliberately stale consumer range cannot replace the declared
        // signed 32-bit return's proof premises with an unsigned byte range.
        let narrowed = { site with ValueRange = Some(ValueRange.Bounded(0I, 255I)) }
        let truncation: Meet = { Consumer = site.Id; Operand = site.Id; From = 32; To = 8; Adapt = MeetKind.Truncate }
        let meets = (graph.Codata.Value.Meets.TryFind site.Id |> Option.defaultValue []) @ [truncation]
        let changed =
            { graph with Nodes = graph.Nodes.Add(site.Id, narrowed)
                         Codata = lazy { graph.Codata.Value with Meets = graph.Codata.Value.Meets.Add(site.Id, meets) } }
        Assert.Equal(Some 8, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth changed site.Id)
        BoundaryEmissionFixture.rejected changed |> ignore
        Assert.True(BoundaryWitness.admit changed |> Result.isError)

    [<Theory>]
    [<InlineData("void")>]
    [<InlineData("status-result")>]
    [<InlineData("status-discarded")>]
    [<InlineData("status-bound")>]
    [<InlineData("status-caller")>]
    member _.``Owned nullable release publishes its declared Void or signed32 status result`` (shape: string) =
        let status, result = BoundaryEmissionFixture.releaseApplication shape
        Assert.False(Clef.Compiler.Project.ProjectChecker.hasErrors result,
                     String.concat "\n" (Clef.Compiler.Project.ProjectChecker.getErrorMessages result))
        let graph = result.CheckResult.Graph
        let projection = BoundaryEmissionFixture.project graph
        let resource =
            (BoundaryDeclarations.readDescriptors graph).Resources
            |> List.filter (fun row -> row.Contract.Hypothesis.Identity = "fixture-stream-First")
            |> Assert.Single
        let expected = if status then Some(BoundaryScalar.Integer(32, true)) else None
        let handleAbi = BoundaryScalar.ResourceHandle(resource.Quote, false)
        let released = projection.Imports.Values |> Seq.filter (fun import -> import.Binding = resource.Release.Binding) |> Assert.Single
        Assert.Equal(expected, released.Result)
        Assert.Equal<(NodeId * BoundaryScalar) list>([resource.ReleaseFormal, handleAbi], released.Parameters)
        let release = projection.Calls.Values |> Seq.filter (fun call -> call.Import = released.Identity) |> Assert.Single
        Assert.Equal(expected, release.Result)
        Assert.True release.ResultAdaptation.IsNone
        let operand = Assert.Single release.Arguments
        Assert.Equal(handleAbi, operand.Abi)
        Assert.Equal(resource.ReleaseFormal, operand.Formal)
        // The cleanup account is attached to the handle operand for both results.
        let cleanupId, cleanupInfo, cleanup = BoundaryEmissionFixture.cleanupClaims graph |> Assert.Single
        Assert.Equal(resource.Quote, cleanup.Declaration)
        Assert.Equal(resource.Release.Binding, cleanup.Release)
        match release.Resource with
        | Some(BoundaryResourceUse.ReleaseOwned account) ->
            Assert.Equal(resource.Quote, account.Declaration)
            Assert.Equal(cleanup.Acquisition, account.Acquisition)
            Assert.Equal(cleanupId, account.Cleanup)
        | other -> failwithf "The release call has no cleanup account: %A" other
        Assert.Equal<(NodeId * NodeId) list>([operand.Actual, resource.Release.Binding], BoundaryEmissionFixture.releaseEvents cleanup)
        Assert.Contains(cleanup.Points, fun point ->
            point.Site = release.Site && point.Port = EvaluationPort.Exit &&
            point.Event = Some(ResourceFlowEvent.Release(operand.Actual, resource.Release.Binding)))
        let site = graph.Nodes[release.Site]
        if status then
            // The status is an ordinary declared integer result: the full signed
            // 32-bit range, a source-selected 32-bit representation and the numeric
            // owner's ABI account.
            Assert.Equal(Some(ValueRange.twosComplement 32), site.ValueRange)
            let selected = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedRepresentation graph release.Site |> Option.get
            Assert.Equal("int", selected.Family)
            Assert.Equal(32, selected.Bits)
            let numeric =
                Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph
                |> Result.defaultWith (fun failures -> failwithf "Missing numeric projection: %A" failures)
            let account = numeric.ForeignResultUses |> List.filter (fun account -> account.Application.Call = release.Site) |> Assert.Single
            Assert.Equal(resource.Release.Binding, account.Application.Declaration)
            Assert.Equal<ForeignResultProofRole list>([ForeignResultProofRole.AbiNarrowing], account.Claims |> List.map fst)
        else
            Assert.Equal(Some NTUKind.NTUunit, Types.tryGetNTUKind site.Type)
        match Clef.Compiler.Nanopass.ObligationDischarge.discharge [cleanupInfo] with
        | Ok receipt -> Assert.Equal("unsat", (Assert.Single receipt.Evidence).Verdict)
        | Error reason -> failwithf "The single-release cleanup obligation was not discharged: %s" reason
        let revision =
            Clef.Compiler.Project.ProjectChecker.publish result
            |> Result.defaultWith (fun reason -> failwithf "The release application could not publish: %s" reason)
        let publicId = Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId
        Assert.Equal(Clef.Compiler.Baker.Ingredients.PublishedFactRows.mapBoundaryImport released,
                     revision.Emission.Boundary.Imports[publicId released.Identity])
        let published = revision.Emission.Boundary.Calls[publicId release.Site]
        Assert.Equal((if status then Some(Fidelity.PSG.BoundaryScalar.Integer(32, true)) else None), published.Result)
        Assert.Equal(Fidelity.PSG.BoundaryScalar.ResourceHandle(publicId resource.Quote, false), (Assert.Single published.Arguments).Abi)

    // Fidelity.PSG owns the published-contract check. Its
    // Emission.Boundary.ResourceDeclarations.Signature rule reads the release
    // descriptor's ReturnType from the published declaration facts.
    [<Theory>]
    [<InlineData("void")>]
    [<InlineData("status-result")>]
    member _.``Published owned nullable release revision passes the Fidelity.PSG integrity check`` (shape: string) =
        let _, result = BoundaryEmissionFixture.releaseApplication shape
        let revision =
            Clef.Compiler.Project.ProjectChecker.publish result
            |> Result.defaultWith (fun reason -> failwithf "The release application could not publish: %s" reason)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)

    [<Theory>]
    [<InlineData("int", "Integer (Signed, 64)")>]
    [<InlineData("int", "Integer (Signed, 16)")>]
    [<InlineData("int", "Integer (Unsigned, 32)")>]
    [<InlineData("bool", "Bool")>]
    [<InlineData("int", "Pointer 64")>]
    member _.``A release result other than Void or signed32 is a ResourceDescriptor error`` (releaseResult: string, releaseReturn: string) =
        let result =
            BoundaryEmissionFixture.resourceApplication
                (BoundaryEmissionFixture.resourceSource releaseResult releaseReturn)
                (BoundaryEmissionFixture.statusMain "    | Some handle -> BoundaryFixture.closeStreamFirst handle; 0\n")
        let graph = result.CheckResult.Graph
        let reason = "A ResourceDescriptor requires matching nullable CHandle return and unary nonnullable same-handle release declaring a Void or signed 32-bit integer result, with identical declared pointer widths."
        let declared = BoundaryDeclarations.readDescriptors graph
        Assert.Empty declared.Resources
        Assert.Equal(2, declared.Findings |> List.filter (fun finding -> finding.Message = reason) |> List.length)
        Assert.True(Clef.Compiler.Project.ProjectChecker.hasErrors result)
        Assert.True(
            result.CheckResult.Diagnostics |> List.exists (fun diagnostic ->
                diagnostic.Code = "CCS8403" && diagnostic.Message = "Source settlement is required before witnessing: BoundaryEmission: " + reason),
            BoundaryEmissionFixture.diagnosticText result.CheckResult.Diagnostics)
        Assert.True(BoundaryWitness.admit graph |> Result.isError)

    [<Theory>]
    [<InlineData("reference")>]
    [<InlineData("width")>]
    [<InlineData("handle")>]
    member _.``A signed32 status release still requires a by-value same-width same-handle parameter`` (defect: string) =
        let replace (before: string) (after: string) (source: string) =
            let changed = source.Replace(before, after)
            if changed = source then failwithf "Missing status release fixture token: %s" before
            changed
        let edit =
            match defect with
            | "reference" -> replace "Name = \"handle\"; Type = Pointer 64; PassBy = Value" "Name = \"handle\"; Type = Pointer 64; PassBy = Reference"
            | "width" -> replace "Name = \"handle\"; Type = Pointer 64" "Name = \"handle\"; Type = Pointer 32"
            | "handle" ->
                replace "type ResourceDescriptor = {" "type OtherStream = private | OpaqueOtherStream\ntype ResourceDescriptor = {"
                >> replace "(handle: CHandle<unit>) : int" "(handle: CHandle<OtherStream>) : int"
            | _ -> failwithf "Unknown release parameter defect: %s" defect
        let result =
            BoundaryEmissionFixture.resourceApplication
                (edit (BoundaryEmissionFixture.resourceSource "int" "Integer (Signed, 32)"))
                (BoundaryEmissionFixture.statusMain "    | Some handle -> 0\n")
        let graph = result.CheckResult.Graph
        let reason = "A ResourceDescriptor requires matching nullable CHandle return and unary nonnullable same-handle release declaring a Void or signed 32-bit integer result, with identical declared pointer widths."
        let declared = BoundaryDeclarations.readDescriptors graph
        Assert.Empty declared.Resources
        Assert.Equal(2, declared.Findings |> List.filter (fun finding -> finding.Message = reason) |> List.length)
        Assert.True(Clef.Compiler.Project.ProjectChecker.hasErrors result)
        Assert.True(
            result.CheckResult.Diagnostics |> List.exists (fun diagnostic ->
                diagnostic.Code = "CCS8403" && diagnostic.Message = "Source settlement is required before witnessing: BoundaryEmission: " + reason),
            BoundaryEmissionFixture.diagnosticText result.CheckResult.Diagnostics)
        Assert.True(BoundaryWitness.admit graph |> Result.isError)

    [<Theory>]
    [<InlineData("void", "missing")>]
    [<InlineData("status", "missing")>]
    [<InlineData("void", "repeated")>]
    [<InlineData("status", "repeated")>]
    [<InlineData("void", "wrong")>]
    [<InlineData("status", "wrong")>]
    member _.``Missing repeated and wrong releases fail for Void and signed32 status releases alike`` (release: string, defect: string) =
        let status = release = "status"
        let source =
            if status then BoundaryEmissionFixture.resourceSource "int" "Integer (Signed, 32)"
            else BoundaryEmissionFixture.resourceSource "unit" "Void"
        let arm =
            match defect, status with
            | "missing", _ -> "    | Some handle -> 0\n"
            | "repeated", true ->
                "    | Some handle -> BoundaryFixture.closeStreamFirst handle; BoundaryFixture.closeStreamFirst handle\n"
            | "repeated", false -> "    | Some handle -> BoundaryFixture.closeStreamFirst handle; BoundaryFixture.closeStreamFirst handle; 0\n"
            | "wrong", true -> "    | Some handle -> BoundaryFixture.closeStreamSecond handle\n"
            | "wrong", false -> "    | Some handle -> BoundaryFixture.closeStreamSecond handle; 0\n"
            | _ -> failwithf "Unknown release defect: %s" defect
        let result = BoundaryEmissionFixture.resourceApplication source (BoundaryEmissionFixture.statusMain arm)
        let graph = result.CheckResult.Graph
        let hasErrors = Clef.Compiler.Project.ProjectChecker.hasErrors result
        let diagnostics = BoundaryEmissionFixture.diagnosticText result.CheckResult.Diagnostics
        let claims = BoundaryEmissionFixture.cleanupClaims graph
        let resources = (BoundaryDeclarations.readDescriptors graph).Resources
        let first = resources |> List.filter (fun row -> row.Contract.Hypothesis.Identity = "fixture-stream-First") |> Assert.Single
        let second = resources |> List.filter (fun row -> row.Contract.Hypothesis.Identity = "fixture-stream-Second") |> Assert.Single
        let incomplete = "The finite resource cleanup profile is incomplete: the cleanup graph structure or event census is inconsistent."
        match defect with
        | "missing" ->
            // The source check has no error; the cleanup obligation has no
            // release event and the solver finds a counterexample.
            Assert.False(hasErrors, diagnostics)
            let _, info, cleanup = Assert.Single claims
            Assert.Empty(BoundaryEmissionFixture.releaseEvents cleanup)
            match Clef.Compiler.Nanopass.ObligationDischarge.discharge [info] with
            | Ok _ -> failwith "A cleanup obligation without a release was discharged."
            | Error reason -> Assert.Equal(sprintf "Obligation '%s' (%s) was not discharged: solver returned 'sat'" info.Id info.Source, reason)
        | "wrong" ->
            // The other resource's release is recorded as the event; the
            // cleanup profile is inconsistent and the check fails with CCS8403.
            let _, info, cleanup = Assert.Single claims
            Assert.Equal(first.Release.Binding, cleanup.Release)
            Assert.Equal<NodeId list>([second.Release.Binding], BoundaryEmissionFixture.releaseEvents cleanup |> List.map snd)
            Assert.True(hasErrors, diagnostics)
            Assert.True(
                result.CheckResult.Diagnostics |> List.exists (fun diagnostic ->
                    diagnostic.Code = "CCS8403" && diagnostic.Message.EndsWith(incomplete, System.StringComparison.Ordinal)),
                diagnostics)
            match Clef.Compiler.Nanopass.ObligationDischarge.discharge [info] with
            | Ok _ -> failwith "A cleanup obligation with another resource's release was discharged."
            | Error reason -> Assert.Equal(sprintf "Required obligations have unavailable premises: '%s' (%s): %s" info.Id info.Source incomplete, reason)
        | "repeated" ->
            // The source check has no error; both release events are recorded
            // and the solver finds a counterexample.
            Assert.False(hasErrors, diagnostics)
            let _, info, cleanup = Assert.Single claims
            let events = BoundaryEmissionFixture.releaseEvents cleanup
            Assert.Equal(2, events.Length)
            Assert.All(events, fun (_, binding) -> Assert.Equal(first.Release.Binding, binding))
            match Clef.Compiler.Nanopass.ObligationDischarge.discharge [info] with
            | Ok _ -> failwith "A cleanup obligation with two releases of one handle was discharged."
            | Error reason -> Assert.Equal(sprintf "Obligation '%s' (%s) was not discharged: solver returned 'sat'" info.Id info.Source, reason)
        | _ -> failwithf "Unknown release defect: %s" defect

    [<Theory>]
    [<InlineData("int", "consume 7")>]
    [<InlineData("CHandle<unit>", "let pointer = FnPtr.ofFunction forward in 0")>]
    [<InlineData("int array", "consume (Array.zeroCreate 4)")>]
    member _.``A by-value pointer parameter without a declared adapter fails with CCS8403`` (formal: string, entry: string) =
        let body =
            """
[<FidelityExtern("c", "consume")>]
let consume (value: @FORMAL@) : int = NativeDefault.zeroed ()
let consumeDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "consume"; Parameters = [| { Name = "value"; Type = Pointer 64; PassBy = Value } |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
let forward (value: @FORMAL@) : int = consume value
[<EntryPoint>]
let main _ = @ENTRY@
"""
                .Replace("@FORMAL@", formal).Replace("@ENTRY@", entry)
        let result = BoundaryEmissionFixture.check (Some BoundaryEmissionFixture.platform) body
        let reason = "A boundary parameter has no admitted integer or boolean declaration; pointer and aggregate values require a source-settled adapter."
        let failures = BoundaryEmissionFixture.rejected result.Graph
        let binding = BoundaryEmissionFixture.binding "consume" result.Graph
        Assert.Contains(failures, fun failure -> failure.Reason = "BoundaryEmission: " + reason && failure.Participants.Contains binding.Id)
        Assert.True(
            result.Diagnostics |> List.exists (fun diagnostic ->
                diagnostic.Code = "CCS8403" && diagnostic.Message = "Source settlement is required before witnessing: BoundaryEmission: " + reason),
            BoundaryEmissionFixture.diagnosticText result.Diagnostics)
        Assert.True(BoundaryWitness.admit result.Graph |> Result.isError)

    static member private B1bCheck(name: string, source: string, ?prelude: (string * string) list) =
        let authority =
            SourcePlatformFixture.authority
                .Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")
                .Replace("Spaces = [| rodata |]", "Spaces = [| rodata; { Name = \"stack\"; Kind = \"stack\"; Capacity = 1048576; Alignment = 16; Granularity = 16; Growth = \"fixed\"; Access = \"rw\"; Base = None } |]")
        let root = System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__, "../../artifacts/scratch/step-b1b-projects", System.Guid.NewGuid().ToString("N")))
        System.IO.Directory.CreateDirectory root |> ignore
        try
            let write file (text: string) = System.IO.File.WriteAllText(System.IO.Path.Combine(root, file), text)
            let extra = defaultArg prelude []
            for fileName, content in extra do
                write fileName content
            let appSources =
                (extra |> List.map fst) @ [ name ]
                |> List.map (sprintf "\"%s\"")
                |> String.concat ", "
            write "Platform.clef" authority
            write name ("module BoundaryFixture\n" + source)
            write "Platform.fidproj" "[package]\nname = \"Platform\"\n[compilation]\ntarget = \"cpu\"\n[build]\noutput_kind = \"library\"\nsources = [\"Platform.clef\"]\n[platform]\nruntime_model = \"libc\"\ndescription = \"WriteAuthority.description\"\n"
            write "App.fidproj" ($"[package]\nname = \"App\"\n[compilation]\ntarget = \"cpu\"\nmemory_model = \"stack_only\"\n[build]\noutput_kind = \"executable\"\nsources = [{appSources}]\n[dependencies]\nplatform = {{ path = \"Platform.fidproj\" }}\n[link]\nlibraries = [\"c\"]\n")
            let res =
                Clef.Compiler.Project.ProjectChecker.checkProject (System.IO.Path.Combine(root, "App.fidproj"))
                |> Result.defaultWith (fun failures -> failwithf "%A" failures)
            if not res.ParseErrors.IsEmpty then failwithf "Parse errors in %s: %A" name res.ParseErrors
            res.CheckResult
        finally
            if System.IO.Directory.Exists root then
                try System.IO.Directory.Delete(root, true) with _ -> ()

    [<Fact>]
    member _.``Step B1b readonly explicit-count buffer emits zero-copy and satisfies PSG integrity``() =
        let source = """
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type EntrySentinel = EntrySentinel of string * int
type PassBy = Value | Reference | ReadOnlyReference | Fixed of EntrySentinel
type CallConv = | CDecl
type Transfer = | Borrowed | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type ExternalExecutionHypothesis = { Identity: string; Version: string; Source: string }
type ReadOnlyBufferExtent = ExplicitCount of int | UncountedNulTerminated
type BorrowedContent = | Utf8Text | RawBytes
type OwnerReleaseTarget = { Binding: string; Parameter: int }
type RetentionRelease = Redefinition of int array | OwnerRelease of OwnerReleaseTarget
type BufferRetention = DuringCall | RetainedUntil of int * RetentionRelease array
type ReadOnlyBufferDescriptor = { Binding: string; Parameter: int; Extent: ReadOnlyBufferExtent; Content: BorrowedContent; Retention: BufferRetention; Hypothesis: ExternalExecutionHypothesis }

[<FidelityExtern("c", "digest_bytes")>]
let digestBytes (handle: int) (data: int array) (len: int) : int = NativeDefault.zeroed ()
let digestBytesDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "digest_bytes"
    Parameters = [|
        { Name = "handle"; Type = Integer (Signed, 32); PassBy = Value }
        { Name = "data"; Type = Integer (Unsigned, 8); PassBy = ReadOnlyReference }
        { Name = "len"; Type = Integer (Signed, 32); PassBy = Value }
        { Name = "destructor"; Type = Pointer 64; PassBy = Fixed (EntrySentinel ("SQLITE_TRANSIENT", -1)) } |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let digestBytesReadOnlyBufferDescriptor: Expr<ReadOnlyBufferDescriptor> = <@ {
    Binding = "BoundaryFixture.digestBytes"; Parameter = 1
    Extent = ExplicitCount 2; Content = RawBytes; Retention = DuringCall
    Hypothesis = { Identity = "test.digest.ro"; Version = "1"; Source = "b1b-ro" } } @>

[<EntryPoint>]
let main _ =
    let payload = Array.zeroCreate 4
    if digestBytes 7 payload 4 = 0 then 0 else 1
"""
        let result = BoundaryEmissionCases.B1bCheck("b1b-ro.clef", source)
        DimensionalCases.noErrors result
        let projection = BoundaryEmissionFixture.project result.Graph
        let roDecl = Assert.Single projection.ReadOnlyBufferDeclarations.Values
        Assert.Equal(1, roDecl.Parameter)
        Assert.Equal(Some 2, roDecl.CountParameter)
        let roUse = Assert.Single projection.ReadOnlyBufferUses.Values
        Assert.Equal(0, roUse.Copies)
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph
            |> Result.defaultWith (sprintf "%A" >> failwith)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)

    [<Fact>]
    member _.``Step B1b readonly buffer rejects explicit-count overflow with CCS8424 and mutation alias with CCS8426``() =
        let mkSource mutateCall =
            let head = """
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type PassBy = Value | Reference | ReadOnlyReference
type CallConv = | CDecl
type Transfer = | Borrowed | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type ExternalExecutionHypothesis = { Identity: string; Version: string; Source: string }
type ReadOnlyBufferExtent = ExplicitCount of int | UncountedNulTerminated
type BorrowedContent = | Utf8Text | RawBytes
type OwnerReleaseTarget = { Binding: string; Parameter: int }
type RetentionRelease = Redefinition of int array | OwnerRelease of OwnerReleaseTarget
type BufferRetention = DuringCall | RetainedUntil of int * RetentionRelease array
type ReadOnlyBufferDescriptor = { Binding: string; Parameter: int; Extent: ReadOnlyBufferExtent; Content: BorrowedContent; Retention: BufferRetention; Hypothesis: ExternalExecutionHypothesis }

[<FidelityExtern("c", "digest_check")>]
let digestCheck (data: int array) (len: int) : int = NativeDefault.zeroed ()
let digestCheckDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "digest_check"
    Parameters = [| { Name = "data"; Type = Integer (Unsigned, 8); PassBy = ReadOnlyReference }; { Name = "len"; Type = Integer (Signed, 32); PassBy = Value } |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let digestCheckReadOnlyBufferDescriptor: Expr<ReadOnlyBufferDescriptor> = <@ {
    Binding = "BoundaryFixture.digestCheck"; Parameter = 0
    Extent = ExplicitCount 1; Content = RawBytes; Retention = DuringCall
    Hypothesis = { Identity = "test.digest.check"; Version = "1"; Source = "b1b-ro-neg" } } @>

[<EntryPoint>]
let main _ =
    let payload = [| 1; 2; 3 |]
"""
            head + mutateCall
        let run call =
            let res = BoundaryEmissionCases.B1bCheck("b1b-ro-neg.clef", mkSource call)
            BoundaryEmissionFixture.rejected res.Graph
        let overflowFailures = run "    if digestCheck payload 5 = 0 then 0 else 1\n"
        Assert.Contains(overflowFailures, fun f -> f.Reason.Contains "CCS8424:")
        let aliasSource = """
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type EntrySentinel = EntrySentinel of string * int
type PassBy = Value | Reference | ReadOnlyReference | Fixed of EntrySentinel
type CallConv = | CDecl
type Transfer = | Borrowed | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type ExternalExecutionHypothesis = { Identity: string; Version: string; Source: string }
type ResourceRelease = { Binding: string; Parameter: int }
type ResourceProtocol = OwnedNullableReturn of ResourceRelease
type ResourceDescriptor = { Resource: ResourceProtocol; Hypothesis: ExternalExecutionHypothesis }
type ReadOnlyBufferExtent = ExplicitCount of int | UncountedNulTerminated
type BorrowedContent = | Utf8Text | RawBytes
type OwnerReleaseTarget = { Binding: string; Parameter: int }
type RetentionRelease = Redefinition of int array | OwnerRelease of OwnerReleaseTarget
type BufferRetention = DuringCall | RetainedUntil of int * RetentionRelease array
type ReadOnlyBufferDescriptor = { Binding: string; Parameter: int; Extent: ReadOnlyBufferExtent; Content: BorrowedContent; Retention: BufferRetention; Hypothesis: ExternalExecutionHypothesis }

[<FidelityExtern("c", "stmt_create_alias")>]
let createStmt (k: int) : option<CHandle<unit>> = NativeDefault.zeroed ()
let createStmtDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "stmt_create_alias"; Parameters = [| { Name = "k"; Type = Integer (Signed, 32); PassBy = Value } |]
    ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let createStmtResourceDescriptor: Expr<ResourceDescriptor> = <@ {
    Resource = OwnedNullableReturn ({ Binding = "BoundaryFixture.finalizeStmt"; Parameter = 0 })
    Hypothesis = { Identity = "test.stmt.alias"; Version = "1"; Source = "b1b-ro-alias" } } @>

[<FidelityExtern("c", "stmt_finalize_alias")>]
let finalizeStmt (stmt: CHandle<unit>) : unit = NativeDefault.zeroed ()
let finalizeStmtDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "stmt_finalize_alias"; Parameters = [| { Name = "stmt"; Type = Pointer 64; PassBy = Value } |]
    ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>

[<FidelityExtern("c", "stmt_bind_alias")>]
let bindStatic (stmt: CHandle<unit>) (idx: int) (data: int array) (len: int) : int = NativeDefault.zeroed ()
let bindStaticDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "stmt_bind_alias"
    Parameters = [|
        { Name = "stmt"; Type = Pointer 64; PassBy = Value }
        { Name = "idx"; Type = Integer (Signed, 32); PassBy = Value }
        { Name = "data"; Type = Integer (Unsigned, 8); PassBy = ReadOnlyReference }
        { Name = "len"; Type = Integer (Signed, 32); PassBy = Value }
        { Name = "dtor"; Type = Pointer 64; PassBy = Fixed (EntrySentinel ("SQLITE_STATIC", 0)) } |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
let bindStaticReadOnlyBufferDescriptor: Expr<ReadOnlyBufferDescriptor> = <@ {
    Binding = "BoundaryFixture.bindStatic"; Parameter = 2
    Extent = ExplicitCount 3; Content = RawBytes
    Retention = RetainedUntil (0, [| OwnerRelease { Binding = "BoundaryFixture.finalizeStmt"; Parameter = 0 } |])
    Hypothesis = { Identity = "test.bind.alias"; Version = "1"; Source = "b1b-ro-alias" } } @>

let runTest () : int =
    match createStmt 1 with
    | None -> 1
    | Some s ->
        let payload = [| 9; 8 |]
        let rc = bindStatic s 1 payload 2
        payload[0] <- 7
        finalizeStmt s
        rc

[<EntryPoint>]
let main _ = if runTest () = 0 then 0 else 1
"""
        let aliasRes = BoundaryEmissionCases.B1bCheck("b1b-ro-alias.clef", aliasSource)
        let aliasFailures = BoundaryEmissionFixture.rejected aliasRes.Graph
        Assert.Contains(aliasFailures, fun f -> f.Reason.Contains "CCS8426:")

    [<Fact>]
    member _.``Step B1b uncounted NUL-terminated static path borrows static pool and rejects interior NUL``() =
        let mkSource pathExpr =
            let head = """
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type PassBy = Value | Reference | ReadOnlyReference
type CallConv = | CDecl
type Transfer = | Borrowed | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type ExternalExecutionHypothesis = { Identity: string; Version: string; Source: string }
type ReadOnlyBufferExtent = ExplicitCount of int | UncountedNulTerminated
type BorrowedContent = | Utf8Text | RawBytes
type OwnerReleaseTarget = { Binding: string; Parameter: int }
type RetentionRelease = Redefinition of int array | OwnerRelease of OwnerReleaseTarget
type BufferRetention = DuringCall | RetainedUntil of int * RetentionRelease array
type ReadOnlyBufferDescriptor = { Binding: string; Parameter: int; Extent: ReadOnlyBufferExtent; Content: BorrowedContent; Retention: BufferRetention; Hypothesis: ExternalExecutionHypothesis }

[<FidelityExtern("c", "open_path")>]
let openPath (path: string) : int = NativeDefault.zeroed ()
let openPathDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "open_path"; Parameters = [| { Name = "path"; Type = Pointer 64; PassBy = Value } |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let openPathReadOnlyBufferDescriptor: Expr<ReadOnlyBufferDescriptor> = <@ {
    Binding = "BoundaryFixture.openPath"; Parameter = 0
    Extent = UncountedNulTerminated; Content = Utf8Text; Retention = DuringCall
    Hypothesis = { Identity = "test.open.path"; Version = "1"; Source = "b1b-nul" } } @>

[<EntryPoint>]
let main _ = if openPath """
            head + pathExpr + " = 0 then 0 else 1\n"
        let okRes = BoundaryEmissionCases.B1bCheck("b1b-nul.clef", mkSource "\"/tmp/test.db\"")
        DimensionalCases.noErrors okRes
        let projection = BoundaryEmissionFixture.project okRes.Graph
        let roUse = Assert.Single projection.ReadOnlyBufferUses.Values
        Assert.Equal(0, roUse.Copies)
        match roUse.Crossing with
        | BoundaryReadOnlyBufferCrossing.StaticImageNulBorrowed _ -> ()
        | other -> failwithf "Expected StaticImageNulBorrowed, got %A" other
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish okRes.Graph
            |> Result.defaultWith (sprintf "%A" >> failwith)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let badRes = BoundaryEmissionCases.B1bCheck("b1b-nul-bad.clef", mkSource "\"bad\\u0000path\"")
        let badFailures = BoundaryEmissionFixture.rejected badRes.Graph
        Assert.Contains(badFailures, fun f -> f.Reason.Contains "CCS8424:")

    [<Fact>]
    member _.``Step B1b retained buffer requires owner retirement and rejects non-retiring reset``() =
        let mkSource trailer =
            let head = """
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type EntrySentinel = EntrySentinel of string * int
type PassBy = Value | Reference | ReadOnlyReference | Fixed of EntrySentinel
type CallConv = | CDecl
type Transfer = | Borrowed | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type ExternalExecutionHypothesis = { Identity: string; Version: string; Source: string }
type ResourceRelease = { Binding: string; Parameter: int }
type ResourceProtocol = OwnedNullableReturn of ResourceRelease
type ResourceDescriptor = { Resource: ResourceProtocol; Hypothesis: ExternalExecutionHypothesis }
type ReadOnlyBufferExtent = ExplicitCount of int | UncountedNulTerminated
type BorrowedContent = | Utf8Text | RawBytes
type OwnerReleaseTarget = { Binding: string; Parameter: int }
type RetentionRelease = Redefinition of int array | OwnerRelease of OwnerReleaseTarget
type BufferRetention = DuringCall | RetainedUntil of int * RetentionRelease array
type ReadOnlyBufferDescriptor = { Binding: string; Parameter: int; Extent: ReadOnlyBufferExtent; Content: BorrowedContent; Retention: BufferRetention; Hypothesis: ExternalExecutionHypothesis }

[<FidelityExtern("c", "stmt_create")>]
let createStmt (k: int) : option<CHandle<unit>> = NativeDefault.zeroed ()
let createStmtDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "stmt_create"; Parameters = [| { Name = "k"; Type = Integer (Signed, 32); PassBy = Value } |]
    ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let createStmtResourceDescriptor: Expr<ResourceDescriptor> = <@ {
    Resource = OwnedNullableReturn ({ Binding = "BoundaryFixture.finalizeStmt"; Parameter = 0 })
    Hypothesis = { Identity = "test.stmt"; Version = "1"; Source = "b1b-ret" } } @>

[<FidelityExtern("c", "stmt_reset")>]
let resetStmt (stmt: CHandle<unit>) : int = NativeDefault.zeroed ()
let resetStmtDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "stmt_reset"; Parameters = [| { Name = "stmt"; Type = Pointer 64; PassBy = Value } |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>

[<FidelityExtern("c", "stmt_finalize")>]
let finalizeStmt (stmt: CHandle<unit>) : unit = NativeDefault.zeroed ()
let finalizeStmtDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "stmt_finalize"; Parameters = [| { Name = "stmt"; Type = Pointer 64; PassBy = Value } |]
    ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>

[<FidelityExtern("c", "stmt_bind_static")>]
let bindStatic (stmt: CHandle<unit>) (idx: int) (data: int array) (len: int) : int = NativeDefault.zeroed ()
let bindStaticDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "stmt_bind_static"
    Parameters = [|
        { Name = "stmt"; Type = Pointer 64; PassBy = Value }
        { Name = "idx"; Type = Integer (Signed, 32); PassBy = Value }
        { Name = "data"; Type = Integer (Unsigned, 8); PassBy = ReadOnlyReference }
        { Name = "len"; Type = Integer (Signed, 32); PassBy = Value }
        { Name = "dtor"; Type = Pointer 64; PassBy = Fixed (EntrySentinel ("SQLITE_STATIC", 0)) } |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
let bindStaticReadOnlyBufferDescriptor: Expr<ReadOnlyBufferDescriptor> = <@ {
    Binding = "BoundaryFixture.bindStatic"; Parameter = 2
    Extent = ExplicitCount 3; Content = RawBytes
    Retention = RetainedUntil (0, [| OwnerRelease { Binding = "BoundaryFixture.finalizeStmt"; Parameter = 0 } |])
    Hypothesis = { Identity = "test.bind.static"; Version = "1"; Source = "b1b-ret" } } @>

let runTest () : int =
    match createStmt 1 with
    | None -> 1
    | Some s ->
        let buf = [| 9; 8 |]
        let rc = bindStatic s 1 buf 2
"""
            head + trailer
        let okSource = mkSource "        let rc2 = resetStmt s\n        finalizeStmt s\n        rc + rc2\n\n[<EntryPoint>]\nlet main _ = if runTest () = 0 then 0 else 1\n"
        let okRes = BoundaryEmissionCases.B1bCheck("b1b-ret.clef", okSource)
        DimensionalCases.noErrors okRes
        let proj = BoundaryEmissionFixture.project okRes.Graph
        let roUse = Assert.Single proj.ReadOnlyBufferUses.Values
        Assert.NotEmpty roUse.Retirements
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish okRes.Graph
            |> Result.defaultWith (sprintf "%A" >> failwith)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let noFinalize = mkSource "        let rc2 = resetStmt s\n        rc + rc2\n\n[<EntryPoint>]\nlet main _ = if runTest () = 0 then 0 else 1\n"
        let badRes = BoundaryEmissionCases.B1bCheck("b1b-ret-bad.clef", noFinalize)
        let badFailures = BoundaryEmissionFixture.rejected badRes.Graph
        Assert.Contains(badFailures, fun f -> f.Reason.Contains "CCS8425:")

    [<Fact>]
    member _.``Step B1b BufferAbsenceContract converts Option None and Some cleanly and rejects missing contract``() =
        let barePrelude =
            [ "BAREWireDescriptors.clef",
              "namespace BAREWire.Descriptors\n"
              + "type ExternalExecutionHypothesis = { Identity: string; Version: string; Source: string }\n"
              + "type BufferAbsenceContract = { Binding: string; Parameter: int; Hypothesis: ExternalExecutionHypothesis }\n" ]
        let mkSource includeContract =
            let contractDecl =
                if includeContract then
                    """
let sendOptBufferAbsenceDescriptor: Expr<BAREWire.Descriptors.BufferAbsenceContract> = <@ {
    BAREWire.Descriptors.BufferAbsenceContract.Binding = "BoundaryFixture.sendOpt"; Parameter = 0
    Hypothesis = { BAREWire.Descriptors.ExternalExecutionHypothesis.Identity = "test.abs"; Version = "1"; Source = "b1b-abs" } } @>
"""
                else ""
            let decls = """
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type PassBy = Value | Reference | ReadOnlyReference
type CallConv = | CDecl
type Transfer = | Borrowed | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type ExternalExecutionHypothesis = { Identity: string; Version: string; Source: string }
type ReadOnlyBufferExtent = ExplicitCount of int | UncountedNulTerminated
type BorrowedContent = | Utf8Text | RawBytes
type OwnerReleaseTarget = { Binding: string; Parameter: int }
type RetentionRelease = Redefinition of int array | OwnerRelease of OwnerReleaseTarget
type BufferRetention = DuringCall | RetainedUntil of int * RetentionRelease array
type ReadOnlyBufferDescriptor = { Binding: string; Parameter: int; Extent: ReadOnlyBufferExtent; Content: BorrowedContent; Retention: BufferRetention; Hypothesis: ExternalExecutionHypothesis }

[<FidelityExtern("c", "send_opt")>]
let sendOpt (buf: option<string>) (len: int) : int = NativeDefault.zeroed ()
let sendOptDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "send_opt"
    Parameters = [| { Name = "buf"; Type = Pointer 64; PassBy = Value }; { Name = "len"; Type = Integer (Signed, 32); PassBy = Value } |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let sendOptReadOnlyBufferDescriptor: Expr<ReadOnlyBufferDescriptor> = <@ {
    Binding = "BoundaryFixture.sendOpt"; Parameter = 0
    Extent = ExplicitCount 1; Content = RawBytes; Retention = DuringCall
    Hypothesis = { Identity = "test.send.ro"; Version = "1"; Source = "b1b-abs" } } @>
"""
            let entry = """
[<EntryPoint>]
let main _ =
    let a = sendOpt None 0
    let b = sendOpt (Some "ab") 2
    if a + b = 0 then 0 else 1
"""
            decls + contractDecl + entry
        let okRes = BoundaryEmissionCases.B1bCheck("b1b-abs.clef", mkSource true, barePrelude)
        DimensionalCases.noErrors okRes
        let proj = BoundaryEmissionFixture.project okRes.Graph
        Assert.NotEmpty proj.BufferAbsences
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish okRes.Graph
            |> Result.defaultWith (sprintf "%A" >> failwith)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let badRes = BoundaryEmissionCases.B1bCheck("b1b-abs-bad.clef", mkSource false, barePrelude)
        let badFailures = BoundaryEmissionFixture.rejected badRes.Graph
        Assert.Contains(badFailures, fun f -> f.Reason.Contains "CCS8427:")

    [<Fact>]
    member _.``Step B1b BorrowedResultViewDescriptor validates companion extent and rejects read past invalidation``() =
        let mkSource useAfterInvalidate =
            let body =
                if useAfterInvalidate then
                    """
        let v = colText s 0
        finalizeStmt s
        readView v 0
"""
                else
                    """
        let col = 0
        let v = colText s col
        let n = colBytes s col
        let r = readView v n
        finalizeStmt s
        r
"""
            let head = """
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type PassBy = Value | Reference | ReadOnlyReference
type CallConv = | CDecl
type Transfer = | Borrowed | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type ExternalExecutionHypothesis = { Identity: string; Version: string; Source: string }
type ResourceRelease = { Binding: string; Parameter: int }
type ResourceProtocol = OwnedNullableReturn of ResourceRelease
type ResourceDescriptor = { Resource: ResourceProtocol; Hypothesis: ExternalExecutionHypothesis }
type BorrowedContent = | Utf8Text | RawBytes
type BorrowedExtent = NulTerminated | CompanionCall of string * int array
type OwnerInvalidationCall = { Binding: string; Parameter: int }
type BorrowInvalidation = AnyOwnerCall | OwnerCall of OwnerInvalidationCall
type BorrowedResultViewDescriptor = { Binding: string; Content: BorrowedContent; Extent: BorrowedExtent; Owner: int; InvalidatedBy: BorrowInvalidation array; Hypothesis: ExternalExecutionHypothesis }
type StmtHandle = | StmtHandle

[<FidelityExtern("c", "stmt_create2")>]
let createStmt (k: int) : option<CHandle<StmtHandle>> = NativeDefault.zeroed ()
let createStmtDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "stmt_create2"; Parameters = [| { Name = "k"; Type = Integer (Signed, 32); PassBy = Value } |]
    ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let createStmtResourceDescriptor: Expr<ResourceDescriptor> = <@ {
    Resource = OwnedNullableReturn ({ Binding = "BoundaryFixture.finalizeStmt"; Parameter = 0 })
    Hypothesis = { Identity = "test.stmt2"; Version = "1"; Source = "b1b-bv" } } @>

[<FidelityExtern("c", "stmt_finalize2")>]
let finalizeStmt (stmt: CHandle<StmtHandle>) : unit = NativeDefault.zeroed ()
let finalizeStmtDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "stmt_finalize2"; Parameters = [| { Name = "stmt"; Type = Pointer 64; PassBy = Value } |]
    ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>

[<FidelityExtern("c", "stmt_col_bytes")>]
let colBytes (stmt: CHandle<StmtHandle>) (col: int) : int = NativeDefault.zeroed ()
let colBytesDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "stmt_col_bytes"; Parameters = [| { Name = "stmt"; Type = Pointer 64; PassBy = Value }; { Name = "col"; Type = Integer (Signed, 32); PassBy = Value } |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>

[<FidelityExtern("c", "stmt_col_text")>]
let colText (stmt: CHandle<StmtHandle>) (col: int) : option<CHandle<unit>> = NativeDefault.zeroed ()
let colTextDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "stmt_col_text"; Parameters = [| { Name = "stmt"; Type = Pointer 64; PassBy = Value }; { Name = "col"; Type = Integer (Signed, 32); PassBy = Value } |]
    ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
let colTextBorrowedResultViewDescriptor: Expr<BorrowedResultViewDescriptor> = <@ {
    Binding = "BoundaryFixture.colText"; Content = RawBytes
    Extent = CompanionCall ("BoundaryFixture.colBytes", [| 0; 1 |]); Owner = 0
    InvalidatedBy = [| OwnerCall { Binding = "BoundaryFixture.finalizeStmt"; Parameter = 0 } |]
    Hypothesis = { Identity = "test.bv"; Version = "1"; Source = "b1b-bv" } } @>

let readView (v: option<CHandle<unit>>) (n: int) : int =
    match v with
    | Some _ -> if n >= 0 then 0 else 1
    | None -> 0

[<EntryPoint>]
let main (argv: string[]) =
    match createStmt 1 with
    | None -> 1
    | Some s ->
"""
            head + body
        let okRes = BoundaryEmissionCases.B1bCheck("b1b-bv.clef", mkSource false)
        DimensionalCases.noErrors okRes
        let proj = BoundaryEmissionFixture.project okRes.Graph
        Assert.NotEmpty proj.BorrowedResultViewDeclarations
        Assert.NotEmpty proj.BorrowedResultViewUses
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish okRes.Graph
            |> Result.defaultWith (sprintf "%A" >> failwith)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let badRes = BoundaryEmissionCases.B1bCheck("b1b-bv-bad.clef", mkSource true)
        let badFailures = BoundaryEmissionFixture.rejected badRes.Graph
        let mutSource =
            (mkSource false).Replace(
                "        let col = 0\n        let v = colText s col",
                "        let mutable col = 0\n        let v = colText s col\n        col <- 1")
        let mutRes = BoundaryEmissionCases.B1bCheck("b1b-bv-mut.clef", mutSource)
        let mutFailures = BoundaryEmissionFixture.rejected mutRes.Graph
        Assert.Contains(mutFailures, fun f -> f.Reason.Contains "CCS8424:")
        Assert.Contains(mutRes.Diagnostics, fun d -> d.Code = "CCS8424")
        let condSource =
            (mkSource false).Replace(
                "        let n = colBytes s col",
                "        let n = if argv.Length > 0 then colBytes s col else 0")
        let condRes = BoundaryEmissionCases.B1bCheck("b1b-bv-cond.clef", condSource)
        let condFailures = BoundaryEmissionFixture.rejected condRes.Graph
        Assert.Contains(condFailures, fun f -> f.Reason.Contains "CCS8424:")
        Assert.Contains(condRes.Diagnostics, fun d -> d.Code = "CCS8424")
        Assert.Contains(badFailures, fun f -> f.Reason.Contains "CCS8425:")

    [<Fact>]
    member _.``Step B1b RetainedCallbackDescriptor and CountedEntryArrayDescriptor emit clean PSG``() =
        let mkSource uncontractedCallbackUnit useUndeclared =
            let ctxType = if uncontractedCallbackUnit then "CHandle<unit>" else "CHandle<CtxMarker>"
            let transferCase = if useUndeclared then "Undeclared" else "Borrowed"
            $"""
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void | Entry of string
type EntrySentinel = EntrySentinel of string * int
type PassBy = Value | Reference | ReadOnlyReference | Fixed of EntrySentinel
type CallConv = | CDecl
type Transfer = | Borrowed | Undeclared
type ParameterInfo = {{ Name: string; Type: TypeRef; PassBy: PassBy }}
type FunctionDescriptor = {{ CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }}
type EntrySignature = {{ Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv }}
type ExternalExecutionHypothesis = {{ Identity: string; Version: string; Source: string }}
type ResourceRelease = {{ Binding: string; Parameter: int }}
type ResourceProtocol = OwnedNullableReturn of ResourceRelease
type ResourceDescriptor = {{ Resource: ResourceProtocol; Hypothesis: ExternalExecutionHypothesis }}
type OwnerReleaseTarget = {{ Binding: string; Parameter: int }}
type RetentionRelease = Redefinition of int array | OwnerRelease of OwnerReleaseTarget
type RetainedCallbackDescriptor = {{ Binding: string; Parameter: string; Owner: int; Releases: RetentionRelease array }}
type CountedElement = Text | NullableText | Handle of string | NullableHandle of string
type CountedEntryArrayDescriptor = {{ Binding: string; Parameter: int; Argument: int; CountArgument: int; Element: CountedElement }}
type CallbackInvocationContract = {{ Binding: string; Parameter: int; Signature: EntrySignature; Hypothesis: ExternalExecutionHypothesis; Scope: string }}
type DbMarker = | DbMarker
type CtxMarker = | CtxMarker

[<FidelityExtern("c", "db_open")>]
let dbOpen (k: int) : option<CHandle<DbMarker>> = NativeDefault.zeroed ()
let dbOpenDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "db_open"; Parameters = [| {{ Name = "k"; Type = Integer (Signed, 32); PassBy = Value }} |]
    ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Undeclared }} @>
let dbOpenResourceDescriptor: Expr<ResourceDescriptor> = <@ {{
    Resource = OwnedNullableReturn ({{ Binding = "BoundaryFixture.dbClose"; Parameter = 0 }})
    Hypothesis = {{ Identity = "test.db"; Version = "1"; Source = "b1b-cb" }} }} @>

[<FidelityExtern("c", "db_close")>]
let dbClose (db: CHandle<DbMarker>) : unit = NativeDefault.zeroed ()
let dbCloseDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "db_close"; Parameters = [| {{ Name = "db"; Type = Pointer 64; PassBy = Value }} |]
    ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared }} @>

[<FidelityExtern("c", "db_create_fn")>]
let createFn (db: CHandle<DbMarker>) (xFunc: FnPtr<{ctxType} -> int -> CHandle<unit> -> unit>) : int = NativeDefault.zeroed ()
let createFnDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "db_create_fn"
    Parameters = [|
        {{ Name = "db"; Type = Pointer 64; PassBy = Value }}
        {{ Name = "eTextRep"; Type = Integer (Signed, 32); PassBy = Fixed (EntrySentinel ("SQLITE_UTF8", 1)) }}
        {{ Name = "xFunc"; Type = Entry "BoundaryFixture.xFuncCallbackInvocationContract"; PassBy = Value }} |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = {transferCase} }} @>

let xFuncScope: Expr<RetainedCallbackDescriptor> = <@ {{
    Binding = "BoundaryFixture.createFn"; Parameter = "xFunc"; Owner = 0
    Releases = [| OwnerRelease {{ Binding = "BoundaryFixture.dbClose"; Parameter = 0 }} |] }} @>

let xFuncCallbackInvocationContract: Expr<CallbackInvocationContract> = <@ {{
    Binding = "BoundaryFixture.createFn"; Parameter = 2
    Signature = {{
        Parameters = [|
            {{ Name = "ctx"; Type = Pointer 64; PassBy = Value }}
            {{ Name = "argc"; Type = Integer (Signed, 32); PassBy = Value }}
            {{ Name = "argv"; Type = Pointer 64; PassBy = Value }} |]
        ReturnType = Void; CallingConvention = CDecl }}
    Hypothesis = {{ Identity = "test.xfunc.inv"; Version = "1"; Source = "b1b-cb" }}
    Scope = "BoundaryFixture.xFuncScope" }} @>
let xFuncCountedEntryArrayDescriptor: Expr<CountedEntryArrayDescriptor> = <@ {{
    Binding = "BoundaryFixture.createFn"; Parameter = 2; Argument = 2; CountArgument = 1; Element = Text }} @>

let handler (_ctx: {ctxType}) (argc: int) (_argv: CHandle<unit>) : unit =
    let a = if argc < 0 then 0 elif argc > 15 then 15 else argc
    if a >= 0 then () else ()

let runTest () : int =
    match dbOpen 1 with
    | None -> 1
    | Some db ->
        let rc = createFn db (FnPtr.ofFunction handler)
        dbClose db
        rc

[<EntryPoint>]
let main _ =
    if runTest () = 0 then 0 else 1
"""
        let okRes = BoundaryEmissionCases.B1bCheck("b1b-cb.clef", mkSource false false)
        DimensionalCases.noErrors okRes
        let proj = BoundaryEmissionFixture.project okRes.Graph
        Assert.NotEmpty proj.CountedEntryArrays
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish okRes.Graph
            |> Result.defaultWith (sprintf "%A" >> failwith)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let badRes = BoundaryEmissionCases.B1bCheck("b1b-cb-bad.clef", mkSource true false)
        let badFailures = BoundaryEmissionFixture.rejected badRes.Graph
        Assert.Contains(badFailures, fun f -> f.Reason.Contains "CCS8403:")
        Assert.Contains(badRes.Diagnostics, fun d -> d.Code = "CCS8403")
        let badUndeclaredRes = BoundaryEmissionCases.B1bCheck("b1b-cb-undecl.clef", mkSource true true)
        let badUndeclaredFailures = BoundaryEmissionFixture.rejected badUndeclaredRes.Graph
        Assert.Contains(badUndeclaredFailures, fun f -> f.Reason.Contains "CCS8403:")
        Assert.Contains(badUndeclaredRes.Diagnostics, fun d -> d.Code = "CCS8403")

    [<Fact>]
    member _.``Step B1b alias and extern writes during retained borrow are rejected with CCS8426``() =
        let mkSource useExternWrite =
            let mutStmt =
                if useExternWrite then
                    "        writeBuf alias 2"
                else
                    "        alias[0] <- 7"
            $"""
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type EntrySentinel = EntrySentinel of string * int
type PassBy = Value | Reference | ReadOnlyReference | Fixed of EntrySentinel
type CallConv = | CDecl
type Transfer = | Borrowed | Undeclared
type ParameterInfo = {{ Name: string; Type: TypeRef; PassBy: PassBy }}
type FunctionDescriptor = {{ CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }}
type ExternalExecutionHypothesis = {{ Identity: string; Version: string; Source: string }}
type ResourceRelease = {{ Binding: string; Parameter: int }}
type ResourceProtocol = OwnedNullableReturn of ResourceRelease
type ResourceDescriptor = {{ Resource: ResourceProtocol; Hypothesis: ExternalExecutionHypothesis }}
type ReadOnlyBufferExtent = ExplicitCount of int | UncountedNulTerminated
type BorrowedContent = | Utf8Text | RawBytes
type OwnerReleaseTarget = {{ Binding: string; Parameter: int }}
type RetentionRelease = Redefinition of int array | OwnerRelease of OwnerReleaseTarget
type BufferRetention = DuringCall | RetainedUntil of int * RetentionRelease array
type ReadOnlyBufferDescriptor = {{ Binding: string; Parameter: int; Extent: ReadOnlyBufferExtent; Content: BorrowedContent; Retention: BufferRetention; Hypothesis: ExternalExecutionHypothesis }}
type WritableBufferDescriptor = {{ Binding: string; Parameter: int; CountParameter: int; Hypothesis: ExternalExecutionHypothesis }}

[<FidelityExtern("c", "stmt_create_alias")>]
let createStmt (k: int) : option<CHandle<unit>> = NativeDefault.zeroed ()
let createStmtDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "stmt_create_alias"; Parameters = [| {{ Name = "k"; Type = Integer (Signed, 32); PassBy = Value }} |]
    ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Undeclared }} @>
let createStmtResourceDescriptor: Expr<ResourceDescriptor> = <@ {{
    Resource = OwnedNullableReturn ({{ Binding = "BoundaryFixture.finalizeStmt"; Parameter = 0 }})
    Hypothesis = {{ Identity = "test.stmt.alias"; Version = "1"; Source = "b1b-alias" }} }} @>

[<FidelityExtern("c", "stmt_finalize_alias")>]
let finalizeStmt (stmt: CHandle<unit>) : unit = NativeDefault.zeroed ()
let finalizeStmtDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "stmt_finalize_alias"; Parameters = [| {{ Name = "stmt"; Type = Pointer 64; PassBy = Value }} |]
    ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared }} @>

[<FidelityExtern("c", "stmt_write_buf")>]
let writeBuf (data: int array) (len: int) : unit = NativeDefault.zeroed ()
let writeBufDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "stmt_write_buf"
    Parameters = [|
        {{ Name = "data"; Type = Integer (Unsigned, 8); PassBy = Reference }}
        {{ Name = "len"; Type = Integer (Signed, 32); PassBy = Value }} |]
    ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Borrowed }} @>
let writeBufWritableBufferDescriptor: Expr<WritableBufferDescriptor> = <@ {{
    Binding = "BoundaryFixture.writeBuf"; Parameter = 0; CountParameter = 1
    Hypothesis = {{ Identity = "test.write.alias"; Version = "1"; Source = "b1b-alias" }} }} @>

[<FidelityExtern("c", "stmt_bind_alias")>]
let bindStatic (stmt: CHandle<unit>) (idx: int) (data: int array) (len: int) : int = NativeDefault.zeroed ()
let bindStaticDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "stmt_bind_alias"
    Parameters = [|
        {{ Name = "stmt"; Type = Pointer 64; PassBy = Value }}
        {{ Name = "idx"; Type = Integer (Signed, 32); PassBy = Value }}
        {{ Name = "data"; Type = Integer (Unsigned, 8); PassBy = ReadOnlyReference }}
        {{ Name = "len"; Type = Integer (Signed, 32); PassBy = Value }}
        {{ Name = "dtor"; Type = Pointer 64; PassBy = Fixed (EntrySentinel ("SQLITE_STATIC", 0)) }} |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Borrowed }} @>
let bindStaticReadOnlyBufferDescriptor: Expr<ReadOnlyBufferDescriptor> = <@ {{
    Binding = "BoundaryFixture.bindStatic"; Parameter = 2
    Extent = ExplicitCount 3; Content = RawBytes
    Retention = RetainedUntil (0, [| OwnerRelease {{ Binding = "BoundaryFixture.finalizeStmt"; Parameter = 0 }} |])
    Hypothesis = {{ Identity = "test.bind.alias"; Version = "1"; Source = "b1b-alias" }} }} @>

let runTest () : int =
    match createStmt 1 with
    | None -> 1
    | Some s ->
        let arr = Array.zeroCreate 2
        let alias = arr
        let rc = bindStatic s 1 arr 2
{mutStmt}
        finalizeStmt s
        rc

[<EntryPoint>]
let main _ = if runTest () = 0 then 0 else 1
"""
        for useExternWrite in [ false; true ] do
            let name = if useExternWrite then "b1b-alias-ext-mut.clef" else "b1b-alias-idx-mut.clef"
            let source = mkSource useExternWrite
            let res = BoundaryEmissionCases.B1bCheck(name, source)
            let failures = BoundaryEmissionFixture.rejected res.Graph
            Assert.Contains(failures, fun f -> f.Reason.Contains "CCS8426:")
            Assert.Contains(res.Diagnostics, fun d -> d.Code = "CCS8426")

    [<Fact>]
    member _.``Step B1b BorrowedResultView rejects match pattern escape and conditional invalidation with CCS8425``() =
        let mkSource patternEscape =
            let body =
                if patternEscape then
                    """
        let v = colText s 0
        match v with
        | Some p ->
            finalizeStmt s
            touchPtr p
        | None -> 1
"""
                else
                    """
        let v = colText s 0
        let r = touchView v
        if r > 0 then finalizeStmt s else ()
        r
"""
            $"""
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type PassBy = Value | Reference | ReadOnlyReference
type CallConv = | CDecl
type Transfer = | Borrowed | Undeclared
type ParameterInfo = {{ Name: string; Type: TypeRef; PassBy: PassBy }}
type FunctionDescriptor = {{ CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }}
type ExternalExecutionHypothesis = {{ Identity: string; Version: string; Source: string }}
type ResourceRelease = {{ Binding: string; Parameter: int }}
type ResourceProtocol = OwnedNullableReturn of ResourceRelease
type ResourceDescriptor = {{ Resource: ResourceProtocol; Hypothesis: ExternalExecutionHypothesis }}
type BorrowedContent = | Utf8Text | RawBytes
type BorrowedExtent = NulTerminated | CompanionCall of string * int array
type OwnerInvalidationCall = {{ Binding: string; Parameter: int }}
type BorrowInvalidation = AnyOwnerCall | OwnerCall of OwnerInvalidationCall
type BorrowedResultViewDescriptor = {{ Binding: string; Content: BorrowedContent; Extent: BorrowedExtent; Owner: int; InvalidatedBy: BorrowInvalidation array; Hypothesis: ExternalExecutionHypothesis }}
type StmtHandle = | StmtHandle

[<FidelityExtern("c", "stmt_create3")>]
let createStmt (k: int) : option<CHandle<StmtHandle>> = NativeDefault.zeroed ()
let createStmtDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "stmt_create3"; Parameters = [| {{ Name = "k"; Type = Integer (Signed, 32); PassBy = Value }} |]
    ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Undeclared }} @>
let createStmtResourceDescriptor: Expr<ResourceDescriptor> = <@ {{
    Resource = OwnedNullableReturn ({{ Binding = "BoundaryFixture.finalizeStmt"; Parameter = 0 }})
    Hypothesis = {{ Identity = "test.stmt3"; Version = "1"; Source = "b1b-bv-neg" }} }} @>

[<FidelityExtern("c", "stmt_finalize3")>]
let finalizeStmt (stmt: CHandle<StmtHandle>) : unit = NativeDefault.zeroed ()
let finalizeStmtDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "stmt_finalize3"; Parameters = [| {{ Name = "stmt"; Type = Pointer 64; PassBy = Value }} |]
    ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared }} @>

[<FidelityExtern("c", "stmt_col_text3")>]
let colText (stmt: CHandle<StmtHandle>) (col: int) : option<CHandle<unit>> = NativeDefault.zeroed ()
let colTextDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "stmt_col_text3"; Parameters = [| {{ Name = "stmt"; Type = Pointer 64; PassBy = Value }}; {{ Name = "col"; Type = Integer (Signed, 32); PassBy = Value }} |]
    ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Borrowed }} @>
let colTextBorrowedResultViewDescriptor: Expr<BorrowedResultViewDescriptor> = <@ {{
    Binding = "BoundaryFixture.colText"; Content = Utf8Text
    Extent = NulTerminated; Owner = 0
    InvalidatedBy = [| OwnerCall {{ Binding = "BoundaryFixture.finalizeStmt"; Parameter = 0 }} |]
    Hypothesis = {{ Identity = "test.bv.neg"; Version = "1"; Source = "b1b-bv-neg" }} }} @>

let touchPtr (_p: CHandle<unit>) : int = 0
let touchView (v: option<CHandle<unit>>) : int =
    match v with
    | Some _ -> 1
    | None -> 0

[<EntryPoint>]
let main (argv: string[]) =
    match createStmt 1 with
    | None -> 1
    | Some s ->
{body}
"""
        let patRes = BoundaryEmissionCases.B1bCheck("b1b-bv-pat-escape.clef", mkSource true)
        let patFailures = BoundaryEmissionFixture.rejected patRes.Graph
        Assert.Contains(patFailures, fun f -> f.Reason.Contains "CCS8425:")
        Assert.Contains(patRes.Diagnostics, fun d -> d.Code = "CCS8425")
        let condRes = BoundaryEmissionCases.B1bCheck("b1b-bv-cond-inv.clef", mkSource false)
        let condFailures = BoundaryEmissionFixture.rejected condRes.Graph
        Assert.Contains(condFailures, fun f -> f.Reason.Contains "CCS8425:")
        Assert.Contains(condRes.Diagnostics, fun d -> d.Code = "CCS8425")

    [<Fact>]
    member _.``Step B1b BorrowedResultView rejects deferred closure site, closure/tuple escape, and loop back-edge with CCS8425``() =
        let mkSource mode =
            let body =
                match mode with
                | "deferred" ->
                    """
        let f () =
            let v = colText s 0
            touchView v
        let rc = f ()
        finalizeStmt s
        rc
"""
                | "loop" ->
                    """
        let v = colText s 0
        while argv.Length >= 0 do
            let _ = touchView v
            let _ = resetStmt s
            ()
        finalizeStmt s
        0
"""
                | _ ->
                    """
        let v = colText s 0
        let box = (v, 0)
        let readV () = touchView (fst box)
        finalizeStmt s
        readV ()
"""
            $"""
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type PassBy = Value | Reference | ReadOnlyReference
type CallConv = | CDecl
type Transfer = | Borrowed | Undeclared
type ParameterInfo = {{ Name: string; Type: TypeRef; PassBy: PassBy }}
type FunctionDescriptor = {{ CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }}
type ExternalExecutionHypothesis = {{ Identity: string; Version: string; Source: string }}
type ResourceRelease = {{ Binding: string; Parameter: int }}
type ResourceProtocol = OwnedNullableReturn of ResourceRelease
type ResourceDescriptor = {{ Resource: ResourceProtocol; Hypothesis: ExternalExecutionHypothesis }}
type BorrowedContent = | Utf8Text | RawBytes
type BorrowedExtent = NulTerminated | CompanionCall of string * int array
type OwnerInvalidationCall = {{ Binding: string; Parameter: int }}
type BorrowInvalidation = AnyOwnerCall | OwnerCall of OwnerInvalidationCall
type BorrowedResultViewDescriptor = {{ Binding: string; Content: BorrowedContent; Extent: BorrowedExtent; Owner: int; InvalidatedBy: BorrowInvalidation array; Hypothesis: ExternalExecutionHypothesis }}
type StmtHandle = | StmtHandle

[<FidelityExtern("c", "stmt_create4")>]
let createStmt (k: int) : option<CHandle<StmtHandle>> = NativeDefault.zeroed ()
let createStmtDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "stmt_create4"; Parameters = [| {{ Name = "k"; Type = Integer (Signed, 32); PassBy = Value }} |]
    ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Undeclared }} @>
let createStmtResourceDescriptor: Expr<ResourceDescriptor> = <@ {{
    Resource = OwnedNullableReturn ({{ Binding = "BoundaryFixture.finalizeStmt"; Parameter = 0 }})
    Hypothesis = {{ Identity = "test.stmt4"; Version = "1"; Source = "b1b-bv-r3" }} }} @>

[<FidelityExtern("c", "stmt_reset4")>]
let resetStmt (stmt: CHandle<StmtHandle>) : int = NativeDefault.zeroed ()
let resetStmtDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "stmt_reset4"; Parameters = [| {{ Name = "stmt"; Type = Pointer 64; PassBy = Value }} |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Undeclared }} @>

[<FidelityExtern("c", "stmt_finalize4")>]
let finalizeStmt (stmt: CHandle<StmtHandle>) : unit = NativeDefault.zeroed ()
let finalizeStmtDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "stmt_finalize4"; Parameters = [| {{ Name = "stmt"; Type = Pointer 64; PassBy = Value }} |]
    ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared }} @>

[<FidelityExtern("c", "stmt_col_text4")>]
let colText (stmt: CHandle<StmtHandle>) (col: int) : option<CHandle<unit>> = NativeDefault.zeroed ()
let colTextDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "stmt_col_text4"; Parameters = [| {{ Name = "stmt"; Type = Pointer 64; PassBy = Value }}; {{ Name = "col"; Type = Integer (Signed, 32); PassBy = Value }} |]
    ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Borrowed }} @>
let colTextBorrowedResultViewDescriptor: Expr<BorrowedResultViewDescriptor> = <@ {{
    Binding = "BoundaryFixture.colText"; Content = Utf8Text
    Extent = NulTerminated; Owner = 0
    InvalidatedBy = [| OwnerCall {{ Binding = "BoundaryFixture.finalizeStmt"; Parameter = 0 }}; OwnerCall {{ Binding = "BoundaryFixture.resetStmt"; Parameter = 0 }} |]
    Hypothesis = {{ Identity = "test.bv.r3"; Version = "1"; Source = "b1b-bv-r3" }} }} @>

let touchView (v: option<CHandle<unit>>) : int =
    match v with
    | Some _ -> 1
    | None -> 0

[<EntryPoint>]
let main (argv: string[]) =
    match createStmt 1 with
    | None -> 1
    | Some s ->
{body}
"""
        for mode in [ "deferred"; "loop"; "closure-tuple" ] do
            let res = BoundaryEmissionCases.B1bCheck($"b1b-bv-{mode}.clef", mkSource mode)
            let failures = BoundaryEmissionFixture.rejected res.Graph
            Assert.Contains(failures, fun f -> f.Reason.Contains "CCS8425:")
            if mode = "deferred" then
                Assert.Contains(failures, fun f -> f.Reason.Contains "does not dominate")
            Assert.Contains(res.Diagnostics, fun d -> d.Code = "CCS8425")

    [<Fact>]
    member _.``Step B1b RetainedUntil allows pure local closure, rejects closure/tuple write and loop alias mutation with CCS8426``() =
        let mkSource mode =
            let dataParamType, dataCAbi, helperDecl, runParams, body =
                match mode with
                | "loop" ->
                    "int array",
                    "Integer (Unsigned, 8); PassBy = ReadOnlyReference",
                    "",
                    "()",
                    """
        let arr = Array.zeroCreate 2
        let alias = arr
        let rc = bindStatic s 1 arr 2
        while rc < 0 do
            alias.[0] <- 7
        finalizeStmt s
        rc
"""
                | "pure-closure" ->
                    "string",
                    "Pointer 64; PassBy = Value",
                    "let touchData (_: string) : unit = ()\n",
                    "()",
                    """
        let data = "ab"
        let pair = (data, 0)
        let poke () = touchData (fst pair)
        let rc = bindStatic s 1 data 2
        poke ()
        finalizeStmt s
        rc
"""
                | "mixed-factory" ->
                    "string",
                    "Pointer 64; PassBy = Value",
                    "let mk (c: int) (h: string -> unit) : string -> unit = if c > 0 then (fun _ -> ()) else h\n",
                    "(hook: string -> unit)",
                    """
        let data = "ab"
        let rc = bindStatic s 1 data 2
        (mk rc hook) data
        finalizeStmt s
        rc
"""
                | "mixed-branch" ->
                    "string",
                    "Pointer 64; PassBy = Value",
                    "",
                    "(hook: string -> unit)",
                    """
        let data = "ab"
        let rc = bindStatic s 1 data 2
        (if rc > 0 then (fun _ -> ()) else hook) data
        finalizeStmt s
        rc
"""
                | "mixed-apply" ->
                    "string",
                    "Pointer 64; PassBy = Value",
                    "let pass (f: string -> unit) : string -> unit = f\n",
                    "(hook: string -> unit)",
                    """
        let data = "ab"
        let rc = bindStatic s 1 data 2
        (if rc > 0 then (fun _ -> ()) else pass hook) data
        finalizeStmt s
        rc
"""
                | "extern-alias" ->
                    "string",
                    "Pointer 64; PassBy = Value",
                    "[<FidelityExtern(\"c\", \"ext_touch5\")>]\n"
                    + "let extTouch (buf: string) : unit = NativeDefault.zeroed ()\n",
                    "()",
                    "        let data = \"ab\"\n"
                    + "        let rc = bindStatic s 1 data 2\n"
                    + "        let w = if rc > 0 then (fun _ -> ()) else extTouch\n"
                    + "        w data\n"
                    + "        finalizeStmt s\n"
                    + "        rc\n"
                | _ ->
                    "string",
                    "Pointer 64; PassBy = Value",
                    "",
                    "(hook: string -> unit)",
                    """
        let data = "ab"
        let pair = (data, 0)
        let poke () = hook (fst pair)
        let rc = bindStatic s 1 data 2
        poke ()
        finalizeStmt s
        rc
"""
            let mainBody =
                if mode = "closure-write" || mode = "mixed-factory" || mode = "mixed-branch" || mode = "mixed-apply" then
                    "if runTest (fun _ -> ()) = 0 && runTest (fun s -> let _ = s in ()) = 0 then 0 else 1"
                else
                    "if runTest () = 0 then 0 else 1"
            $"""
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type EntrySentinel = EntrySentinel of string * int
type PassBy = Value | Reference | ReadOnlyReference | Fixed of EntrySentinel
type CallConv = | CDecl
type Transfer = | Borrowed | Undeclared
type ParameterInfo = {{ Name: string; Type: TypeRef; PassBy: PassBy }}
type FunctionDescriptor = {{ CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }}
type ExternalExecutionHypothesis = {{ Identity: string; Version: string; Source: string }}
type ResourceRelease = {{ Binding: string; Parameter: int }}
type ResourceProtocol = OwnedNullableReturn of ResourceRelease
type ResourceDescriptor = {{ Resource: ResourceProtocol; Hypothesis: ExternalExecutionHypothesis }}
type ReadOnlyBufferExtent = ExplicitCount of int | UncountedNulTerminated
type BorrowedContent = | Utf8Text | RawBytes
type OwnerReleaseTarget = {{ Binding: string; Parameter: int }}
type RetentionRelease = Redefinition of int array | OwnerRelease of OwnerReleaseTarget
type BufferRetention = DuringCall | RetainedUntil of int * RetentionRelease array
type ReadOnlyBufferDescriptor = {{ Binding: string; Parameter: int; Extent: ReadOnlyBufferExtent; Content: BorrowedContent; Retention: BufferRetention; Hypothesis: ExternalExecutionHypothesis }}
type StmtHandle = | StmtHandle

[<FidelityExtern("c", "stmt_create5")>]
let createStmt (k: int) : option<CHandle<StmtHandle>> = NativeDefault.zeroed ()
let createStmtDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "stmt_create5"; Parameters = [| {{ Name = "k"; Type = Integer (Signed, 32); PassBy = Value }} |]
    ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Undeclared }} @>
let createStmtResourceDescriptor: Expr<ResourceDescriptor> = <@ {{
    Resource = OwnedNullableReturn ({{ Binding = "BoundaryFixture.finalizeStmt"; Parameter = 0 }})
    Hypothesis = {{ Identity = "test.stmt5"; Version = "1"; Source = "b1b-ret-clos" }} }} @>

[<FidelityExtern("c", "stmt_finalize5")>]
let finalizeStmt (stmt: CHandle<StmtHandle>) : unit = NativeDefault.zeroed ()
let finalizeStmtDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "stmt_finalize5"; Parameters = [| {{ Name = "stmt"; Type = Pointer 64; PassBy = Value }} |]
    ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared }} @>

[<FidelityExtern("c", "stmt_bind_static5")>]
let bindStatic (stmt: CHandle<StmtHandle>) (col: int) (data: {dataParamType}) (n: int) : int = NativeDefault.zeroed ()
let bindStaticDescriptor: Expr<FunctionDescriptor> = <@ {{
    CName = "stmt_bind_static5"
    Parameters = [|
        {{ Name = "stmt"; Type = Pointer 64; PassBy = Value }}
        {{ Name = "col"; Type = Integer (Signed, 32); PassBy = Value }}
        {{ Name = "data"; Type = {dataCAbi} }}
        {{ Name = "n"; Type = Integer (Signed, 32); PassBy = Value }}
        {{ Name = "dtor"; Type = Pointer 64; PassBy = Fixed (EntrySentinel ("SQLITE_STATIC", 0)) }} |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Borrowed }} @>
let bindStaticReadOnlyBufferDescriptor: Expr<ReadOnlyBufferDescriptor> = <@ {{
    Binding = "BoundaryFixture.bindStatic"; Parameter = 2
    Extent = ExplicitCount 3; Content = RawBytes
    Retention = RetainedUntil (0, [| OwnerRelease {{ Binding = "BoundaryFixture.finalizeStmt"; Parameter = 0 }} |])
    Hypothesis = {{ Identity = "test.bind.clos"; Version = "1"; Source = "b1b-ret-clos" }} }} @>

{helperDecl}let runTest {runParams} : int =
    match createStmt 1 with
    | None -> 1
    | Some s ->
{body}

[<EntryPoint>]
let main _ = {mainBody}
"""
        let pureRes = BoundaryEmissionCases.B1bCheck("b1b-ret-pure-clos.clef", mkSource "pure-closure")
        DimensionalCases.noErrors pureRes
        let closRes = BoundaryEmissionCases.B1bCheck("b1b-ret-clos.clef", mkSource "closure-write")
        let closFailures = BoundaryEmissionFixture.rejected closRes.Graph
        Assert.Contains(closFailures, fun f -> f.Reason.Contains "CCS8426:")
        Assert.Contains(closRes.Diagnostics, fun d -> d.Code = "CCS8426")
        let mixedRes = BoundaryEmissionCases.B1bCheck("b1b-ret-mixed.clef", mkSource "mixed-factory")
        let mixedFailures = BoundaryEmissionFixture.rejected mixedRes.Graph
        Assert.Contains(mixedFailures, fun f -> f.Reason.Contains "CCS8426:")
        Assert.Contains(mixedRes.Diagnostics, fun d -> d.Code = "CCS8426")
        let branchRes = BoundaryEmissionCases.B1bCheck("b1b-ret-branch.clef", mkSource "mixed-branch")
        let branchFailures = BoundaryEmissionFixture.rejected branchRes.Graph
        Assert.Contains(branchFailures, fun f -> f.Reason.Contains "CCS8426:")
        Assert.Contains(branchRes.Diagnostics, fun d -> d.Code = "CCS8426")
        let idRes = BoundaryEmissionCases.B1bCheck("b1b-ret-id.clef", mkSource "mixed-apply")
        let idFailures = BoundaryEmissionFixture.rejected idRes.Graph
        Assert.Contains(idFailures, fun f -> f.Reason.Contains "CCS8426:")
        Assert.Contains(idRes.Diagnostics, fun d -> d.Code = "CCS8426")
        let extRes = BoundaryEmissionCases.B1bCheck("b1b-ret-ext.clef", mkSource "extern-alias")
        let extFailures = BoundaryEmissionFixture.rejected extRes.Graph
        Assert.Contains(extFailures, fun f -> f.Reason.Contains "CCS8426:")
        Assert.Contains(extRes.Diagnostics, fun d -> d.Code = "CCS8426")
        let loopRes = BoundaryEmissionCases.B1bCheck("b1b-ret-loop.clef", mkSource "loop")
        let loopFailures = BoundaryEmissionFixture.rejected loopRes.Graph
        Assert.Contains(loopFailures, fun f -> f.Reason.Contains "CCS8426:")
        Assert.Contains(loopRes.Diagnostics, fun d -> d.Code = "CCS8426")

    [<Fact>]
    member _.``Step B1b Fixed sentinel before optional buffer resolves BufferAbsenceContract cleanly``() =
        let barePrelude =
            [ "BAREWireDescriptors.clef",
              "namespace BAREWire.Descriptors\n"
              + "type ExternalExecutionHypothesis = { Identity: string; Version: string; Source: string }\n"
              + "type BufferAbsenceContract = { Binding: string; Parameter: int; Hypothesis: ExternalExecutionHypothesis }\n" ]
        let mkSource includeContract =
            let contractDecl =
                if includeContract then
                    """
let sendPrefixedBufferAbsenceDescriptor: Expr<BAREWire.Descriptors.BufferAbsenceContract> = <@ {
    BAREWire.Descriptors.BufferAbsenceContract.Binding = "BoundaryFixture.sendPrefixed"; Parameter = 1
    Hypothesis = { BAREWire.Descriptors.ExternalExecutionHypothesis.Identity = "test.abs.fixed"; Version = "1"; Source = "b1b-abs-fixed" } } @>
"""
                else ""
            let decls = """
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type EntrySentinel = EntrySentinel of string * int
type PassBy = Value | Reference | ReadOnlyReference | Fixed of EntrySentinel
type CallConv = | CDecl
type Transfer = | Borrowed | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type ExternalExecutionHypothesis = { Identity: string; Version: string; Source: string }
type ReadOnlyBufferExtent = ExplicitCount of int | UncountedNulTerminated
type BorrowedContent = | Utf8Text | RawBytes
type OwnerReleaseTarget = { Binding: string; Parameter: int }
type RetentionRelease = Redefinition of int array | OwnerRelease of OwnerReleaseTarget
type BufferRetention = DuringCall | RetainedUntil of int * RetentionRelease array
type ReadOnlyBufferDescriptor = { Binding: string; Parameter: int; Extent: ReadOnlyBufferExtent; Content: BorrowedContent; Retention: BufferRetention; Hypothesis: ExternalExecutionHypothesis }

[<FidelityExtern("c", "send_prefixed")>]
let sendPrefixed (buf: option<string>) (len: int) : int = NativeDefault.zeroed ()
let sendPrefixedDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "send_prefixed"
    Parameters = [|
        { Name = "flags"; Type = Integer (Signed, 32); PassBy = Fixed (EntrySentinel ("FLAGS_ZERO", 0)) }
        { Name = "buf"; Type = Pointer 64; PassBy = Value }
        { Name = "len"; Type = Integer (Signed, 32); PassBy = Value } |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let sendPrefixedReadOnlyBufferDescriptor: Expr<ReadOnlyBufferDescriptor> = <@ {
    Binding = "BoundaryFixture.sendPrefixed"; Parameter = 1
    Extent = ExplicitCount 2; Content = RawBytes; Retention = DuringCall
    Hypothesis = { Identity = "test.send.fixed.ro"; Version = "1"; Source = "b1b-abs-fixed" } } @>
"""
            let entry = """
[<EntryPoint>]
let main _ =
    let a = sendPrefixed None 0
    let b = sendPrefixed (Some "ab") 2
    if a + b = 0 then 0 else 1
"""
            decls + contractDecl + entry
        let okRes = BoundaryEmissionCases.B1bCheck("b1b-abs-fixed.clef", mkSource true, barePrelude)
        DimensionalCases.noErrors okRes
        let proj = BoundaryEmissionFixture.project okRes.Graph
        Assert.NotEmpty proj.BufferAbsences
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish okRes.Graph
            |> Result.defaultWith (sprintf "%A" >> failwith)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let badRes = BoundaryEmissionCases.B1bCheck("b1b-abs-fixed-bad.clef", mkSource false, barePrelude)
        let badFailures = BoundaryEmissionFixture.rejected badRes.Graph
        Assert.Contains(badFailures, fun f -> f.Reason.Contains "CCS8427:")

    [<Fact>]
    member _.``Step B1b import-side Pointer CHandle rejects ambiguous resource declarations with CCS8403``() =
        let src =
            """
[<FidelityExtern("c", "res_destroy_a")>]
let destroyA (h: CHandle<unit>) : unit = NativeDefault.zeroed ()
let destroyADescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "res_destroy_a"; Parameters = [| { Name = "h"; Type = Pointer 64; PassBy = Value } |]
    ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>

[<FidelityExtern("c", "res_destroy_b")>]
let destroyB (h: CHandle<unit>) : unit = NativeDefault.zeroed ()
let destroyBDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "res_destroy_b"; Parameters = [| { Name = "h"; Type = Pointer 64; PassBy = Value } |]
    ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>

[<FidelityExtern("c", "res_create_a")>]
let createA (k: int) : option<CHandle<unit>> = NativeDefault.zeroed ()
let createADescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "res_create_a"; Parameters = [| { Name = "k"; Type = Integer (Signed, 32); PassBy = Value } |]
    ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let createAResourceDescriptor: Expr<ResourceDescriptor> = <@ {
    Resource = OwnedNullableReturn ({ Binding = "BoundaryFixture.destroyA"; Parameter = 0 })
    Hypothesis = { Identity = "test.res.a"; Version = "1"; Source = "b1b-amb" } } @>

[<FidelityExtern("c", "res_create_b")>]
let createB (k: int) : option<CHandle<unit>> = NativeDefault.zeroed ()
let createBDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "res_create_b"; Parameters = [| { Name = "k"; Type = Integer (Signed, 32); PassBy = Value } |]
    ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let createBResourceDescriptor: Expr<ResourceDescriptor> = <@ {
    Resource = OwnedNullableReturn ({ Binding = "BoundaryFixture.destroyB"; Parameter = 0 })
    Hypothesis = { Identity = "test.res.b"; Version = "1"; Source = "b1b-amb" } } @>

[<FidelityExtern("c", "res_use")>]
let useRes (h: CHandle<unit>) : int = NativeDefault.zeroed ()
let useResDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "res_use"; Parameters = [| { Name = "h"; Type = Pointer 64; PassBy = Value } |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>

[<EntryPoint>]
let main _ =
    match createA 1, createB 1 with
    | Some a, Some b ->
        let r = useRes a
        destroyA a
        destroyB b
        r
    | _ -> 1
"""
        let res = BoundaryEmissionFixture.check (Some BoundaryEmissionFixture.platform) ("""
type ExternalExecutionHypothesis = { Identity: string; Version: string; Source: string }
type ResourceRelease = { Binding: string; Parameter: int }
type ResourceProtocol = OwnedNullableReturn of ResourceRelease
type ResourceDescriptor = { Resource: ResourceProtocol; Hypothesis: ExternalExecutionHypothesis }
""" + src)
        let failures = BoundaryEmissionFixture.rejected res.Graph
        Assert.Contains(failures, fun f -> f.Reason.Contains "Ambiguous")
        Assert.Contains(res.Diagnostics, fun d -> d.Code = "CCS8403" && d.Message.Contains "Ambiguous")
