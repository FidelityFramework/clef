namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeService
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module ForeignDeclarations = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

module private ForeignCases =
    let vocabulary = """module Foreign
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Pointer of int | Void
type PassBy = Value | Reference
type CallConv = | CDecl
type Transfer = | Borrowed
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
"""
    let check body =
        match parseAndCheck (vocabulary + body) "foreign.clef" with
        | Success result | CheckFailure result -> result
        | ParseFailure errors -> failwithf "%A" errors

    let resultVocabulary = """
type ResultBound = Constant of int | Argument of int
type ResultRole = | ReturnValue
type ExternalExecutionHypothesis = { Identity:string; Version:string; Source:string }
type ResultRangeDescriptor = { Binding:string; Role:ResultRole; Hypothesis:ExternalExecutionHypothesis; Lower:ResultBound; Upper:ResultBound }
[<FidelityExtern("c", "native_read")>]
let read (count: int) : int = NativeDefault.zeroed ()
let readDescriptor: Expr<FunctionDescriptor> = <@ {
    CName="native_read"; Parameters=[| {Name="count";Type=Integer(Unsigned,32);PassBy=Value} |]
    ReturnType=Integer(Signed,64); CallingConvention=CDecl; OwnershipTransfer=Borrowed } @>
"""
    // This synthetic pilot supplies an execution hypothesis explicitly. The
    // placeholder body and ABI width do not promise this behavior.
    let resultContract = """
let readRange: Expr<ResultRangeDescriptor> = <@ {
    Binding="Foreign.read"; Role=ResultRole.ReturnValue
    Hypothesis={Identity="fixture.read";Version="1";Source="foreign.clef:synthetic-pilot"}
    Lower=Constant (-1); Upper=Argument 0 } @>
"""
    let resultGraph contract body = (check (resultVocabulary + contract + body)).Graph
    let resultPlatformCheck contract body =
        let parse source path =
            match parseStringWithDefaults source path with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "%A" errors
        let authority = SourcePlatformFixture.authority.Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")
        checkParsedInputsWithPlatform
            [parse authority "write-authority.clef"; parse (vocabulary + resultVocabulary + contract + body) "foreign.clef"]
            (Some SourcePlatformFixture.platform)
    let resultPlatformGraph contract body =
        resultPlatformCheck contract body
        |> fun result -> DimensionalCases.noErrors result; result.Graph
    let resultClaims (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Obligation info ->
                match info.Body with
                | ObligationBody.ForeignResultCoverage model -> Some(node.Id, info, model)
                | _ -> None
            | _ -> None) |> Seq.toList
    let resultUses graph =
        graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.NumericDomain domain -> Some domain.ForeignResultUses | _ -> None)
        |> List.collect id
    let resultEvidence graph facts =
        Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.foreignResultApplications graph facts
        |> function Ok rows -> rows | Error (site, reason) -> failwithf "%A: %s" site reason

    let mapped = """
type Owner = private | OpaqueOwner
type Pixel = private | OpaquePixel
type ViewLayoutDescriptor = { Schema: string; Element: string; Alignment: int; Access: string }
type MappedValue = Input of string | Output of string
type MappedReturnDescriptor = { Binding: string; Acquire: string; Release: string; Layout: string; CallbackParameter: string; Owner: MappedValue; RowStride: MappedValue; RowCount: MappedValue; RowWidth: MappedValue; ReleaseArguments: MappedValue array; FailureStatus: int }
type ScopedCallbackDescriptor = { Binding: string; Parameter: string }
[<FidelityExtern("sample", "acquire")>]
let acquire (owner: CHandle<Owner>) (width: int) (height: int) (stride: int array) (cookie: option<CHandle<unit>> array) : option<CHandle<unit>> = NativeDefault.zeroed ()
let acquireDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "acquire"
    Parameters = [| {Name="owner";Type=Pointer 64;PassBy=Value}; {Name="width";Type=Integer(Unsigned,32);PassBy=Value}; {Name="height";Type=Integer(Unsigned,32);PassBy=Value}; {Name="stride";Type=Integer(Unsigned,32);PassBy=Reference}; {Name="cookie";Type=Pointer 64;PassBy=Reference} |]
    ReturnType=Pointer 64; CallingConvention=CDecl; OwnershipTransfer=Borrowed } @>
[<FidelityExtern("sample", "release")>]
let release (owner: CHandle<Owner>) (cookie: option<CHandle<unit>>) : unit = NativeDefault.zeroed ()
let releaseDescriptor: Expr<FunctionDescriptor> = <@ {
    CName="release"; Parameters=[| {Name="owner";Type=Pointer 64;PassBy=Value}; {Name="cookie";Type=Pointer 64;PassBy=Value} |]
    ReturnType=Void; CallingConvention=CDecl; OwnershipTransfer=Borrowed } @>
let borrow (owner: CHandle<Owner>) (width: int) (height: int) (work: BorrowedView<Pixel> -> int) : int = NativeDefault.zeroed ()
let pixelLayout: Expr<ViewLayoutDescriptor> = <@ {Schema="Foreign.Pixel";Element="u32";Alignment=4;Access="wo"} @>
let mappedDescriptor: Expr<MappedReturnDescriptor> = <@ {
    Binding="Foreign.borrow"; Acquire="Foreign.acquire"; Release="Foreign.release"; Layout="Foreign.Pixel"; CallbackParameter="work"
    Owner=Input "owner"; RowStride=Output "stride"; RowCount=Input "height"; RowWidth=Input "width"
    ReleaseArguments=[| Input "owner"; Output "cookie" |]; FailureStatus= -1 } @>
let scopedDescriptor: Expr<ScopedCallbackDescriptor> = <@ {Binding="Foreign.borrow";Parameter="work"} @>
let invoke (owner: CHandle<Owner>) = borrow owner 2 3 (fun _view -> 7)
[<EntryPoint>]
let main _ = 0
"""

    let publishedLabs =
        lazy
            (let vocabulary =
                (vocabulary
                 + resultVocabulary
                 + resultContract)
                    .Replace("native_read", "labs")
                    .Replace("read", "labs")
                    .Replace("Integer(Unsigned,32)", "Integer(Signed,64)")
                    .Replace("Lower=Constant (-1)", "Lower=Constant 0")

             let parse source path =
                 match parseStringWithDefaults source path with
                 | ParseSuccess input -> input
                 | ParseError errors -> failwithf "%A" errors

             let result =
                 checkParsedInputsWithPlatform
                     [
                         parse
                             (SourcePlatformFixture.authority.Replace(
                                 "Runtime = \"freestanding\"",
                                 "Runtime = \"libc\""
                             ))
                             "write-authority.clef"
                         parse
                             (vocabulary + "\n[<EntryPoint>]\nlet main _ = if labs 5 = 5 then 0 else 1\n")
                             "foreign.clef"
                     ]
                     (Some SourcePlatformFixture.platform)

             DimensionalCases.noErrors result

             let prepared =
                 Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare result.Graph
                 |> function
                     | Ok graph -> graph
                     | Error errors -> failwithf "%A" errors

             let revision =
                 Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish prepared
                 |> function
                     | Ok revision -> revision
                     | Error errors -> failwithf "%A" errors

             revision)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ForeignReferences")>]
type ForeignReferenceTests() =
    [<Fact>]
    member _.``Published conditional foreign result keeps metadata identities without executable bodies``() =
        let revision = ForeignCases.publishedLabs.Value

        let claims =
            revision.Obligations
            |> List.choose (fun info ->
                match info.Body with
                | Fidelity.PSG.ObligationBody.ForeignResultCoverage model -> Some model
                | _ -> None)

        Assert.Equal(2, claims.Length)

        for model in claims do
            let identities =
                (model.Application.Hypothesis |> Option.map _.Quote |> Option.toList)
                @ Option.toList model.Abi
                @ Option.toList model.DestinationDeclaration

            for identity in identities do
                let imports = revision.Emission.Boundary.Imports.Values |> Seq.toList
                Assert.False(revision.Nodes.ContainsKey identity)

                if model.Abi = Some identity then
                    Assert.Contains(imports, fun row -> row.DeclarationFacts.ContainsKey identity)
                elif model.DestinationDeclaration = Some identity then
                    Assert.Equal(Some identity, revision.Emission.Numeric.Values[model.Application.Call].Declaration)
                else
                    Assert.Contains(revision.Emission.Boundary.ResultHypotheses, fun row -> row.Quote = identity)

        let defects = Fidelity.PSG.Integrity.check revision
        Assert.True(defects.IsEmpty, Fidelity.PSG.Integrity.describe defects)
        let positions = Fidelity.PSG.Integrity.named revision |> List.map fst
        Assert.Contains("Obligations.Body.ForeignResultCoverage", positions)
        Assert.Contains("CurrentClaims.Body.ForeignResultCoverage", positions)
        Assert.DoesNotContain("CurrentClaims.Body", positions)

    [<Theory>]
    [<InlineData("quote")>]
    [<InlineData("abi")>]
    [<InlineData("destination")>]
    member _.``Published conditional foreign result refuses unknown metadata role identity`` role =
        let original = ForeignCases.publishedLabs.Value
        let unknown = Fidelity.PSG.NodeId 1000001

        let change (model: Fidelity.PSG.ForeignResultCoverageModel) =
            match role with
            | "quote" ->
                { model with
                    Application =
                        { model.Application with
                            Hypothesis =
                                model.Application.Hypothesis
                                |> Option.map (fun hypothesis -> { hypothesis with Quote = unknown })
                        }
                }
            | "abi" -> { model with Abi = Some unknown }
            | _ ->
                { model with
                    DestinationDeclaration = Some unknown
                }

        let claim (info: Fidelity.PSG.ObligationInfo) =
            match info.Body with
            | Fidelity.PSG.ObligationBody.ForeignResultCoverage model ->
                { info with
                    Body = Fidelity.PSG.ObligationBody.ForeignResultCoverage(change model)
                }
            | _ -> info

        let revision =
            { original with
                Obligations = List.map claim original.Obligations
                CurrentClaims = Map.map (fun _ info -> claim info) original.CurrentClaims
            }

        let defects = Fidelity.PSG.Integrity.check revision

        Assert.Contains(
            defects,
            fun defect ->
                defect.Part = "CurrentClaims.Body.ForeignResultCoverage"
                && defect.Node = Some unknown
                && defect.Reason.Contains "is named and is not held"
        )

    [<Fact>]
    member _.``Published conditional foreign result cannot supply a runtime callee body``() =
        let original = ForeignCases.publishedLabs.Value
        let account = original.Emission.Numeric.ForeignResultUses.Head
        let quote = account.Application.Hypothesis.Value.Quote
        let call = original.Emission.Boundary.Calls[account.Application.Call]

        let revision =
            { original with
                Emission =
                    { original.Emission with
                        Boundary =
                            { original.Emission.Boundary with
                                Calls = original.Emission.Boundary.Calls.Add(call.Site, { call with Callee = quote })
                            }
                    }
            }

        Assert.Contains(
            Fidelity.PSG.Integrity.check revision,
            fun defect ->
                defect.Part = "Emission.Boundary.Calls.Callee"
                && defect.Node = Some quote
                && defect.Reason.Contains "is named and is not held"
        )

    [<Fact>]
    member _.``Published conditional foreign result destination requires its own carrier``() =
        let original = ForeignCases.publishedLabs.Value
        let account = original.Emission.Numeric.ForeignResultUses.Head
        let quote = account.Application.Hypothesis.Value.Quote

        let change (info: Fidelity.PSG.ObligationInfo) =
            match info.Body with
            | Fidelity.PSG.ObligationBody.ForeignResultCoverage model when
                model.Role = Fidelity.PSG.ForeignResultProofRole.AbiNarrowing
                ->
                { info with
                    Body =
                        Fidelity.PSG.ObligationBody.ForeignResultCoverage
                            { model with
                                DestinationDeclaration = Some quote
                            }
                }
            | _ -> info

        let account =
            { account with
                Participants =
                    let changeRows rows =
                        rows
                        |> List.map (fun (row: Fidelity.PSG.Participant) ->
                            if row.Role = Fidelity.PSG.ParticipantRole.ForeignResultDestination then
                                { row with Node = quote }
                            else
                                row)

                    match account.Participants with
                    | Fidelity.PSG.ParticipantEvidence.Established rows ->
                        Fidelity.PSG.ParticipantEvidence.Established(changeRows rows)
                    | Fidelity.PSG.ParticipantEvidence.Pending early ->
                        Fidelity.PSG.ParticipantEvidence.Pending
                            { early with
                                Derived = changeRows early.Derived
                            }
            }

        let uses = [ account ]

        let participants =
            match account.Participants with
            | Fidelity.PSG.ParticipantEvidence.Established rows -> rows
            | Fidelity.PSG.ParticipantEvidence.Pending early -> early.Derived

        let sources =
            account.Claims
            |> List.fold
                (fun map (_, citizen) ->
                    Map.add citizen [ List.map (fun (row: Fidelity.PSG.Participant) -> row.Node) participants ] map)
                original.ObligationSources

        let revision =
            { original with
                Obligations = List.map change original.Obligations
                CurrentClaims = Map.map (fun _ info -> change info) original.CurrentClaims
                ObligationSources = sources
                Emission =
                    { original.Emission with
                        Numeric =
                            { original.Emission.Numeric with
                                ForeignResultUses = uses
                            }
                    }
                Edges =
                    original.Edges
                    |> List.map (fun edge ->
                        match edge.Role with
                        | Fidelity.PSG.EdgeRole.NumericDomain domain ->
                            { edge with
                                Role = Fidelity.PSG.EdgeRole.NumericDomain { domain with ForeignResultUses = uses }
                            }
                        | _ -> edge)
            }

        let defects = Fidelity.PSG.Integrity.check revision

        Assert.Contains(
            defects,
            fun defect ->
                defect.Part = "Emission.Numeric.ForeignResultUses.Destination"
                && defect.Node = Some quote
                && defect.Reason.Contains "own call's selected numeric carrier"
        )

    [<Fact>]
    member _.``Mapped stride retains native output bounds and length retains checked extent bounds``() =
        let context: PlatformContext = {
            PlatformLoading = None
            PlatformId="mapped-boundary-test"; Dimensions=Map.ofList ["Pointer",64;"Register",64]
            Representations=Map.empty; EndpointReturns=Map.empty; PlatformLibraryPath=None
            PlatformDescription=None; PlatformArchitecture=None; PlatformOS=None
            PlatformSourcePaths=Set.empty
            Predicates=Map.empty; FreestandingStartup=None; SubstrateKind=None; RuntimeModel=None
            AvailableMemorySpaces=[]; DefaultMemorySpace=None; ClockFrequencyMhz=None; NsPerWeightUnit=None }
        for operation, bits, range in ["stride",32,ValueRange.unsignedOf 32; "length",64,ValueRange.Bounded(0I,9223372036854775807I)] do
            let result = ForeignCases.check (ForeignCases.mapped.Replace("fun _view -> 7", sprintf "fun view -> BorrowedView.%s view" operation))
            let graph = {result.Graph with Platform=Some context}
            let boundary = graph.Nodes.Values |> Seq.choose (fun node ->
                Clef.Compiler.PSGSaturation.SemanticGraph.BorrowedViews.numericBoundary graph node.Id
                |> Option.filter (fun declared -> declared.Name="BorrowedView." + operation)) |> Assert.Single
            Assert.Equal(bits, boundary.Bits)
            Assert.Equal(range, boundary.Range)

    [<Fact>]
    member _.``Mapped span proof cites schema and ABI without inventing native extent evidence``() =
        let abi = "type CAbiDescriptor = { Name:string; PointerBits:int; ScalarAggregateRegisterBytes:int }\nlet abi:Expr<CAbiDescriptor> = <@ {Name=\"sysv-amd64\";PointerBits=64;ScalarAggregateRegisterBytes=16} @>\n"
        let result = ForeignCases.check (abi + ForeignCases.mapped)
        let mapping = Assert.Single (Clef.Compiler.PSGSaturation.SemanticGraph.MappedBindings.read result.Graph).Mappings
        let model =
            match Clef.Compiler.PSGSaturation.SemanticGraph.MappedSpans.ofMapping result.Graph mapping with
            | Ok model -> model
            | Error error -> failwith error
        Assert.Equal(9223372036854775807I, model.MaximumExtent)
        Assert.Equal(4, model.ElementBytes)
        Assert.Equal(4, model.ElementAlignment)
        let site = result.Graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with
            | SemanticKind.Application (callee, arguments) when arguments.Length = mapping.Parameters.Length ->
                Clef.Compiler.PSGSaturation.SemanticGraph.MappedBindings.tryFindCall result.Graph callee |> Option.isSome
            | _ -> false)
        let graph = {result.Graph with Nodes = result.Graph.Nodes.Add(site.Id, {site with IsReachable=true})}
        let enrichment, _ = Clef.Compiler.Nanopass.ObligationElaboration.elaborateSettled graph
        let obligation = enrichment.NewNodes |> List.choose (fun node ->
            match node.Kind with SemanticKind.Obligation ob when ob.Kind="mapped-element-span" -> Some ob | _ -> None) |> Assert.Single
        Assert.Equal(ObligationBody.MappedElementSpan model, obligation.Body)
        Assert.Contains("Native extent provenance", obligation.Statement)
        Assert.Equal("QF_LIA", obligation.Logic)
        let sources = Clef.Compiler.PSGSaturation.SemanticGraph.MappedSpans.declarationSources graph mapping
        Assert.Equal(2, sources.Length)
        Assert.All(sources, fun source -> Assert.Contains(enrichment.NewEdges, fun edge -> List.contains source edge.Sources))
        let smt = Clef.Compiler.Nanopass.ObligationDischarge.smtLib [obligation]
        Assert.Contains("(div mapped_bytes 4)", smt)
        Assert.Contains("(<= mapped_base (- 9223372036854775807 mapped_bytes))", smt)

    [<Fact>]
    member _.``Mapped span never invents a pointer width when no ABI is declared``() =
        let result = ForeignCases.check ForeignCases.mapped
        let mapping = Assert.Single (Clef.Compiler.PSGSaturation.SemanticGraph.MappedBindings.read result.Graph).Mappings
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.MappedSpans.ofMapping result.Graph mapping |> Result.isError)

    [<Fact>]
    member _.``Scoped mapping preserves actual foreign arities and opaque cookie type``() =
        let result = ForeignCases.check ForeignCases.mapped
        let reading = Clef.Compiler.PSGSaturation.SemanticGraph.MappedBindings.read result.Graph
        Assert.Empty reading.Findings
        let mapping = Assert.Single reading.Mappings
        Assert.Equal(4, mapping.Parameters.Length)
        Assert.Equal(5, mapping.AcquireParameters.Length)
        Assert.Equal(2, mapping.ReleaseParameters.Length)
        Assert.Equal("Foreign.Pixel", mapping.Layout)
        Assert.Equal(-1, mapping.FailureStatus)
        let reachable = Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.computeReachable result.Graph [mapping.Binding]
        Assert.Contains(mapping.AcquireBinding, reachable)
        Assert.Contains(mapping.ReleaseBinding, reachable)
        let _, placeholderBody = ForeignDeclarations.lambdaOfBinding result.Graph mapping.Binding |> Option.get
        Assert.DoesNotContain(placeholderBody, reachable)
        let calls = result.Graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Application(func, _) -> Clef.Compiler.PSGSaturation.SemanticGraph.MappedBindings.tryFindCall result.Graph func
            | _ -> None)
        Assert.NotEmpty calls

    [<Theory>]
    [<InlineData("RowStride=Output \"stride\"", "RowStride=Output \"cookie\"")>]
    [<InlineData("RowCount=Input \"height\"", "RowCount=Output \"stride\"")>]
    [<InlineData("Owner=Input \"owner\"", "Owner=Input \"width\"")>]
    [<InlineData("Input \"owner\"; Output \"cookie\"", "Output \"cookie\"; Input \"owner\"")>]
    [<InlineData("FailureStatus= -1", "FailureStatus= 0")>]
    member _.``Malformed mapped extent owner release and status are rejected``(oldText: string, newText: string) =
        let result = ForeignCases.check (ForeignCases.mapped.Replace(oldText, newText))
        let reading = Clef.Compiler.PSGSaturation.SemanticGraph.MappedBindings.read result.Graph
        Assert.Empty reading.Mappings
        Assert.NotEmpty reading.Findings

    [<Fact>]
    member _.``Opaque handle annotations retain the pointee identity through a native callback``() =
        let result = ForeignCases.check """
let identity (handle: CHandle<unit>) : CHandle<unit> = handle
let apply (handle: CHandle<unit>) = FnPtr.invoke (FnPtr.ofFunction identity) handle
[<EntryPoint>]
let main _ = 0
"""
        DimensionalCases.noErrors result
        match DimensionalCases.bindingType "identity" result with
        | NativeType.TFun (NativeType.TApp (arg, [a]), NativeType.TApp (ret, [b])) ->
            Assert.Equal("CHandle", arg.Name)
            Assert.Equal("CHandle", ret.Name)
            Assert.True(Types.tryGetNTUKind a = Some NTUKind.NTUunit && Types.tryGetNTUKind b = Some NTUKind.NTUunit)
        | other -> failwithf "Handle identity was lost: %A" other

    [<Fact>]
    member _.``Foreign scalar reference seeds array elements from its ABI declaration``() =
        let result = ForeignCases.check """
[<FidelityExtern("c", "output")>]
let output (cell: int array) : int = NativeDefault.zeroed ()
let outputDescriptor : Expr<FunctionDescriptor> =
    <@ { CName = "output"; Parameters = [| { Name = "cell"; Type = Integer (Unsigned, 64); PassBy = Reference } |]
         ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
[<EntryPoint>]
let main _ =
    let cell = [| 0 |]
    if output cell = 0 && cell[0] = 0 then 0 else 1
"""
        DimensionalCases.noErrors result
        let declarations = ForeignDeclarations.readDescriptors result.Graph
        Assert.Empty declarations.Findings
        let reference = Assert.Single((Assert.Single declarations.Functions).References)
        Assert.Equal(64, (snd reference).Bits)
        Assert.Contains(result.Graph.ElementRanges.Value.Values, fun range -> range = ValueRange.unsignedOf 64)
        let sites = result.Graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Application (func, args) ->
                match ForeignDeclarations.referenceArguments result.Graph func args with
                | [] -> None
                | refs -> Some refs
            | _ -> None) |> Seq.toList
        Assert.NotEmpty sites
        let returns = result.Graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Application (func, _) -> ForeignDeclarations.returnOfCall result.Graph func
            | _ -> None) |> Seq.toList
        Assert.NotEmpty returns
        Assert.All(returns, fun returned ->
            Assert.Equal(32, returned.Bits)
            Assert.Equal(ValueRange.twosComplement 32, returned.Range))

        let graph = result.Graph
        let guard = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.MemoryAccessGuard) |> Assert.Single
        let generated = graph.Nodes[guard.Target]
        let frontier = graph.Nodes[generated.Parent |> Option.get]
        Assert.Contains(frontier.Id, guard.Sources)
        let role = "numeric-carrier-coverage"
        let sourceClaim = Clef.Compiler.Baker.Ingredients.Obligations.sourceClaimId role frontier |> Option.get
        Assert.True(frontier.Id <> generated.Id)
        Assert.False(generated.Metadata.ContainsKey "Source.ObligationSite")
        Assert.False(generated.Metadata.ContainsKey "Source.DeclarationIncarnation")
        Assert.Equal(None, Clef.Compiler.Baker.Ingredients.Obligations.sourceClaimId role generated)
        let claims = graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Obligation info when info.Kind = role -> Some info.Id
            | _ -> None) |> Seq.toList
        Assert.Contains(sourceClaim, claims)
        Assert.Contains($"numeric_carrier_{NodeId.value generated.Id}", claims)
        Assert.Empty(Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.completeness graph)

        let incarnationOnly =
            { generated with Metadata = generated.Metadata.Add("Source.DeclarationIncarnation", MetadataValue.String "foreign-test-incarnation") }
        Assert.Equal(None, Clef.Compiler.Baker.Ingredients.Obligations.sourceClaimId role incarnationOnly)

        let copied = { generated with Metadata = generated.Metadata.Add("Source.ObligationSite", frontier.Metadata["Source.ObligationSite"]) }
        let corrupt = { graph with Nodes = graph.Nodes.Add(generated.Id, copied) }
        let failures = Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.completeness corrupt
        for id in [frontier.Id; generated.Id] do
            Assert.Contains(failures, fun (site, reason) -> site = id && reason = "Numeric obligation identity collision: " + sourceClaim)

    [<Fact>]
    member _.``Reference descriptor cannot be attached to an unbounded scalar address``() =
        let result = ForeignCases.check """
[<FidelityExtern("c", "output")>]
let output (cell: int) : int = NativeDefault.zeroed ()
let outputDescriptor : Expr<FunctionDescriptor> =
    <@ { CName = "output"; Parameters = [| { Name = "cell"; Type = Integer (Unsigned, 64); PassBy = Reference } |]
         ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
[<EntryPoint>]
let main _ = output 0
"""
        Assert.NotEmpty (ForeignDeclarations.readDescriptors result.Graph).Findings

    [<Fact>]
    member _.``Unit domain is not a C argument``() =
        let result = ForeignCases.check """
[<FidelityExtern("c", "thread_identity")>]
let threadIdentity () : int = NativeDefault.zeroed ()
let threadIdentityDescriptor : Expr<FunctionDescriptor> =
    <@ { CName = "thread_identity"; Parameters = [||]
         ReturnType = Integer (Unsigned, 64); CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
[<EntryPoint>]
let main _ = if threadIdentity () = 0 then 1 else 0
"""
        DimensionalCases.noErrors result
        let descriptors = ForeignDeclarations.readDescriptors result.Graph
        Assert.Empty descriptors.Findings
        Assert.Empty ((Assert.Single descriptors.Functions).Parameters)

    [<Fact>]
    member _.``Opaque foreign pointee marker is not a record laid out by its companion descriptor``() =
        let result = ForeignCases.check """
type Mutex = private | OpaqueMutex
type FieldDescriptor = { Name: string; Repr: string; Offset: int; Count: int; BitFields: int array }
type PeripheralLayout = { Fields: FieldDescriptor array }
type StructDescriptor = { Name: string; Layout: PeripheralLayout }
let mutexLayout : StructDescriptor =
    { Name = "Mutex"; Layout = { Fields = [| { Name = "Storage"; Repr = "u8"; Offset = 0; Count = 1; BitFields = [||] } |] } }
[<EntryPoint>]
let main _ = 0
"""
        DimensionalCases.noErrors result
        let descriptors = ForeignDeclarations.readDescriptors result.Graph
        Assert.Empty descriptors.Findings
        Assert.True((Assert.Single descriptors.Layouts).RecordType.IsNone)
        let layout = Assert.Single descriptors.Layouts
        let physical = Assert.Single layout.PhysicalFields
        Assert.Equal("Storage", physical.Name)
        Assert.Equal("u8", physical.Repr)
        Assert.Equal(0, physical.Offset)
        Assert.Equal(1, physical.Count)
        let fieldNode = result.Graph.Nodes[physical.Node]
        let fields, recordName =
            match fieldNode.Kind with
            | SemanticKind.RecordExpr(fields, name) -> fields, name
            | other -> failwithf "Missing physical field declaration: %A" other
        // Opaque nominal identity neither supplies missing field measurements
        // nor turns the marker into a source record. Keep old graph data.
        for missing in ["Offset"; "Count"] do
            let retained = fields |> List.filter (fun (name, _) -> name <> missing)
            let changed =
                { fieldNode with
                    Kind = SemanticKind.RecordExpr(retained, recordName)
                    Children = List.map snd retained }
            let damaged = { result.Graph with Nodes = result.Graph.Nodes.Add(changed.Id, changed) }
            let reading = ForeignDeclarations.readDescriptors damaged
            let incomplete = Assert.Single reading.Layouts
            Assert.True(incomplete.RecordType.IsNone)
            Assert.Empty incomplete.PhysicalFields
            let finding = Assert.Single reading.Findings
            Assert.Equal(ForeignDeclarations.DeclarationDefect.Malformed, finding.Defect)
            Assert.Equal(fieldNode.Id, finding.Node)
            Assert.Equal<SourceRange>(fieldNode.Range, finding.Range)
            Assert.Equal("the field 'Storage' must declare its Offset and Count as integer literals", finding.Message)
        let restored = Assert.Single (ForeignDeclarations.readDescriptors result.Graph).Layouts
        Assert.True(restored.RecordType.IsNone)
        Assert.Empty (ForeignDeclarations.readDescriptors result.Graph).Findings
        Assert.Equal<ForeignDeclarations.DeclaredPhysicalField>(physical, Assert.Single restored.PhysicalFields)

    [<Fact>]
    member _.``Foreign result contracts instantiate each ordinary call actual independently``() =
        let graph =
            ForeignCases.resultGraph
                ForeignCases.resultContract
                """
let ordinary x = x + 1
let ordinaryZero () : int = NativeDefault.zeroed ()
[<EntryPoint>]
let main _ =
    let small = read 4
    let large = read 1024
    let unchanged = ordinary 9
    let zero = ordinaryZero ()
    if small <= 4 && large <= 1024 && unchanged = 10 && zero = 0 then 0 else 1
"""

        let rows = ForeignCases.resultEvidence graph graph.RangeContextFacts

        let ranges =
            rows
            |> List.map (fun row -> row.Application.Arguments.Head.Enclosure, row.ResultRange)
            |> List.distinct

        Assert.Contains((ValueRange.point 4I, ValueRange.bounded -1I 4I), ranges)
        Assert.Contains((ValueRange.point 1024I, ValueRange.bounded -1I 1024I), ranges)

        let ordinary =
            graph.Nodes.Values
            |> Seq.find (fun node ->
                match node.Kind with
                | SemanticKind.Binding("unchanged", _, _, _) -> true
                | _ -> false)

        Assert.Equal(Some(ValueRange.point 10I), ordinary.ValueRange)

        let zero =
            graph.Nodes.Values
            |> Seq.find (fun node ->
                match node.Kind with
                | SemanticKind.Binding("zero", _, _, _) -> true
                | _ -> false)

        Assert.Equal(Some(ValueRange.point 0I), zero.ValueRange)

        let descriptor =
            Assert.Single (ForeignDeclarations.readDescriptors graph).ResultRanges

        Assert.NotEqual(descriptor.Node, descriptor.Hypothesis.Quote)

        match graph.Nodes[descriptor.Hypothesis.Quote].Kind with
        | SemanticKind.Quote _ -> ()
        | other -> failwithf "Quote identity was replaced: %A" other

        match graph.Nodes[descriptor.Node].Kind with
        | SemanticKind.RecordExpr _ -> ()
        | other -> failwithf "Record identity was replaced: %A" other

        Assert.Contains(descriptor.Hypothesis.Quote, descriptor.SourcePath)
        Assert.Equal(descriptor.Declaration.Binding, descriptor.Hypothesis.Declaration)

        Assert.All(
            rows,
            fun row ->
                Assert.True(row.Abi.IsSome)
                Assert.True(row.Descriptor.IsSome)
                Assert.NotEmpty row.Reads
        )

    [<Fact>]
    member _.``Foreign result transfer consumes the existing branch narrowed actual``() =
        let graph =
            ForeignCases.resultGraph
                ForeignCases.resultContract
                """
[<EntryPoint>]
let main args =
    let count = if args.Length = 0 then 1 else 1024
    let result = if count <= 4 then read count else 0
    if result <= 4 then 0 else 1
"""

        let rows = ForeignCases.resultEvidence graph graph.RangeContextFacts

        Assert.Contains(
            rows,
            fun row ->
                row.Application.Arguments.Head.Enclosure = ValueRange.bounded 1I 4I
                && row.ResultRange = ValueRange.bounded -1I 4I
        )

    [<Fact>]
    member _.``Missing foreign result contract remains unbounded despite a concrete return ABI``() =
        let graph =
            ForeignCases.resultGraph
                ""
                """
[<EntryPoint>]
let main _ = if read 4 = 0 then 0 else 1
"""

        let rows = ForeignCases.resultEvidence graph graph.RangeContextFacts
        Assert.NotEmpty rows

        Assert.All(
            rows,
            fun row ->
                Assert.True(row.Application.Hypothesis.IsNone)
                Assert.True(row.Abi.IsSome)
                Assert.Equal(ValueRange.Unbounded, row.ResultRange)
        )

    [<Fact>]
    member _.``Foreign result contract refuses to substitute ABI bounds for an unknown actual``() =
        let graph =
            ForeignCases.resultGraph
                ForeignCases.resultContract
                """
[<FidelityExtern("c", "unknown")>]
let unknown () : int = NativeDefault.zeroed ()
let unknownDescriptor: Expr<FunctionDescriptor> = <@ {
    CName="unknown"; Parameters=[||]; ReturnType=Integer(Unsigned,32); CallingConvention=CDecl; OwnershipTransfer=Borrowed } @>
[<EntryPoint>]
let main _ = if read (unknown ()) = 0 then 0 else 1
"""

        let rows =
            ForeignCases.resultEvidence graph graph.RangeContextFacts
            |> List.filter (fun row -> row.Descriptor.IsSome)

        Assert.NotEmpty rows

        Assert.All(
            rows,
            fun row ->
                Assert.Equal(ValueRange.Unbounded, row.Application.Arguments.Head.Enclosure)
                Assert.Equal(ValueRange.Unbounded, row.ResultRange)
        )

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Unavailable foreign range evidence retains current applications without old values``(stale: bool) =
        let graph =
            ForeignCases.resultGraph
                ForeignCases.resultContract
                """
[<EntryPoint>]
let main _ = if read 4 = 0 then 0 else 1
"""

        let facts =
            if stale then
                graph.RangeContextFacts
                |> Option.map (fun facts -> { facts with Premises = Map.empty })
            else
                None

        let rows = ForeignCases.resultEvidence graph facts
        Assert.NotEmpty rows

        Assert.All(
            rows,
            fun row ->
                Assert.True(row.Application.Hypothesis.IsSome)
                Assert.Equal(ValueRange.Unbounded, row.ResultRange)
                Assert.Equal(ValueRange.Unbounded, row.Application.Arguments.Head.Enclosure)
                Assert.Empty row.Reads
        )

    [<Theory>]
    [<InlineData("Binding=\"Foreign.read\"", "Binding=\"read\"", "fully qualified extern")>]
    [<InlineData("Version=\"1\"", "Version=\" \"", "nonempty literal hypothesis")>]
    [<InlineData("Upper=Argument 0", "Upper=Argument 1", "exact native arity")>]
    member _.``Foreign result descriptor defects are located and never become ranges``
        (oldText: string, replacement: string, reason: string)
        =
        let graph =
            ForeignCases.resultGraph
                (ForeignCases.resultContract.Replace(oldText, replacement))
                """
[<EntryPoint>]
let main _ = if read 4 = 0 then 0 else 1
"""

        let reading = ForeignDeclarations.readDescriptors graph
        Assert.Empty reading.ResultRanges
        Assert.Contains(reading.Findings, fun finding -> finding.Message.Contains reason && finding.Range.File = "foreign.clef")

    [<Fact>]
    member _.``Duplicate foreign result contracts retain their source census and refuse range authority``() =
        let graph =
            ForeignCases.resultGraph
                (ForeignCases.resultContract
                 + ForeignCases.resultContract.Replace("let readRange:", "let secondRange:"))
                """
[<EntryPoint>]
let main _ = if read 4 = 0 then 0 else 1
"""

        let reading = ForeignDeclarations.readDescriptors graph
        Assert.Equal(2, reading.ResultRanges.Length)
        Assert.Contains(reading.Findings, fun finding -> finding.Message.Contains "declared twice")
        let rows = ForeignCases.resultEvidence graph graph.RangeContextFacts
        Assert.NotEmpty rows

        Assert.All(
            rows,
            fun row ->
                Assert.True(row.Descriptor.IsNone)
                Assert.Equal(ValueRange.Unbounded, row.ResultRange)
        )

    [<Fact>]
    member _.``Foreign integer behavior scope leaves a boolean result unchanged``() =
        let body =
            """
[<FidelityExtern("c", "native_bool")>]
let nativeBool () : bool = NativeDefault.zeroed ()
[<EntryPoint>]
let main _ = if nativeBool () then 0 else 1
"""

        let graph = (ForeignCases.check body).Graph
        Assert.Empty(ForeignCases.resultEvidence graph graph.RangeContextFacts)
        Assert.Empty(ForeignCases.resultClaims graph)

    [<Fact>]
    member _.``Foreign result accounts retain four role citizens through numeric renewal``() =
        let graph =
            ForeignCases.resultPlatformGraph
                ForeignCases.resultContract
                """
[<EntryPoint>]
let main _ =
    let first = read 4
    let second = read 7
    if first >= -1 && second <= 7 then 0 else 1
"""

        let descriptor =
            Assert.Single (ForeignDeclarations.readDescriptors graph).ResultRanges

        Assert.False(graph.Nodes[descriptor.Declaration.Body].IsReachable)
        let before = ForeignCases.resultClaims graph
        Assert.Equal(4, before.Length)
        let uses = ForeignCases.resultUses graph
        Assert.Equal(2, uses.Length)

        Assert.All(
            uses,
            fun account ->
                Assert.Equal<ForeignResultProofRole list>(
                    [ ForeignResultProofRole.LogicalCoverage; ForeignResultProofRole.AbiNarrowing ],
                    account.Claims |> List.map fst
                )
        )

        Assert.Equal(4, before |> List.map (fun (_, info, _) -> info.Id) |> List.distinct |> List.length)
        let foreignIds = before |> List.map (fun (id, _, _) -> id) |> Set.ofList

        let erased =
            { graph with
                Nodes = graph.Nodes |> Map.filter (fun id _ -> not (foreignIds.Contains id))
                Edges =
                    graph.Edges
                    |> List.choose (fun edge ->
                        if
                            foreignIds.Contains edge.Target
                            || edge.Sources |> List.exists foreignIds.Contains
                        then
                            None
                        else
                            match edge.Role with
                            | EdgeRole.NumericDomain domain ->
                                Some
                                    { edge with
                                        Role = EdgeRole.NumericDomain { domain with ForeignResultUses = [] }
                                    }
                            | _ -> Some edge)
            }

        let completeness =
            Clef.Compiler.Baker.Recipes.NumericCarrierRecipes.completeness erased

        Assert.Contains(
            completeness,
            fun (site, reason) ->
                uses |> List.exists (fun account -> account.Application.Call = site)
                && reason.Contains "missing or duplicate"
        )

        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project erased with
        | Error _ -> ()
        | Ok _ -> failwith "An erased foreign account and its citizens self-certified an empty ledger"


        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph with
        | Ok projection -> Assert.Equal<ForeignResultUse list>(uses, projection.ForeignResultUses)
        | Error failures -> failwithf "Expected complete source-selected numeric account: %A" failures

        let renewed = Clef.Compiler.Nanopass.NumericSettlement.normalize graph
        let after = ForeignCases.resultClaims renewed

        let identity rows =
            rows
            |> List.map (fun (_, info: ObligationInfo, _) -> info.Id, info.Source)
            |> List.sort

        Assert.Equal<(string * string) list>(identity before, identity after)

        Assert.Empty(
            Set.intersect (before |> List.map (fun (id, _, _) -> id) |> Set.ofList) (after |> List.map (fun (id, _, _) -> id) |> Set.ofList)
        )

    [<Fact>]
    member _.``Missing foreign behavior retains both pending role claims``() =
        let graph =
            ForeignCases.resultGraph
                ""
                """
[<EntryPoint>]
let main _ = if read 4 = 0 then 0 else 1
"""

        let claims = ForeignCases.resultClaims graph
        Assert.Equal(2, claims.Length)
        Assert.All(claims, fun (_, _, model) -> Assert.True(model.Application.Hypothesis.IsNone))

        let pending =
            claims
            |> List.map (fun (_, info, _) -> info)
            |> Clef.Compiler.Nanopass.ObligationDischarge.unavailable

        Assert.Equal(2, pending.Length)
        Assert.All(pending, fun row -> Assert.Contains(row.MissingPremises, fun reason -> reason.Contains "behavior contract is missing"))

    [<Fact>]
    member _.``Foreign hypothesis version renewal rejects old evidence without reminting the claim``() =
        let graph =
            ForeignCases.resultGraph
                ForeignCases.resultContract
                """
[<EntryPoint>]
let main _ = if read 4 = 0 then 0 else 1
"""

        let descriptor =
            Assert.Single (ForeignDeclarations.readDescriptors graph).ResultRanges

        let version =
            descriptor.Participants
            |> List.distinct
            |> List.map (fun id -> graph.Nodes[id])
            |> List.filter (fun node -> node.Kind = SemanticKind.Literal(NativeLiteral.String "1"))
            |> Assert.Single

        let changed =
            { graph with
                Nodes =
                    graph.Nodes.Add(
                        version.Id,
                        { version with
                            Kind = SemanticKind.Literal(NativeLiteral.String "2")
                        }
                    )
            }

        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project changed with
        | Error _ -> ()
        | Ok _ -> failwith "Old numeric evidence survived a changed descriptor version"

        let before = ForeignCases.resultClaims graph

        let after =
            Clef.Compiler.Nanopass.NumericSettlement.normalize changed
            |> ForeignCases.resultClaims

        let identity rows =
            rows
            |> List.map (fun (_, info: ObligationInfo, _) -> info.Id, info.Source)
            |> List.sort

        Assert.Equal<(string * string) list>(identity before, identity after)
        Assert.All(after, fun (_, _, model) -> Assert.Equal("2", model.Application.Hypothesis.Value.Version))
        Assert.All(before, fun (_, _, model) -> Assert.Equal("1", model.Application.Hypothesis.Value.Version))

    [<Fact>]
    member _.``Foreign behavior source withdrawal preserves call coordinates and pending accounts``() =
        let body =
            """
[<EntryPoint>]
let main _ = if read 4 = 0 then 0 else 1
"""

        let graph = ForeignCases.resultGraph ForeignCases.resultContract body

        let withdrawnText =
            ForeignCases.resultContract
            |> Seq.map (fun character ->
                if character = '\n' || character = '\r' then
                    character
                else
                    ' ')
            |> Seq.toArray
            |> System.String

        let withdrawn = ForeignCases.resultGraph withdrawnText body
        let before = ForeignCases.resultClaims graph
        let after = ForeignCases.resultClaims withdrawn
        Assert.Equal(2, after.Length)

        Assert.Equal<string list>(
            before |> List.map (fun (_, info, _) -> info.Source) |> List.sort,
            after |> List.map (fun (_, info, _) -> info.Source) |> List.sort
        )

        Assert.All(after, fun (_, _, model) -> Assert.True(model.Application.Hypothesis.IsNone))

        Assert.Equal(
            2,
            after
            |> List.map (fun (_, info, _) -> info)
            |> Clef.Compiler.Nanopass.ObligationDischarge.unavailable
            |> List.length
        )

        Assert.NotEqual<ForeignResultCoverageModel list>(
            before |> List.map (fun (_, _, model) -> model),
            after |> List.map (fun (_, _, model) -> model)
        )

    [<Fact>]
    member _.``Missing boundary declaration cannot restore foreign result ABI behavior``() =
        let graph =
            ForeignCases.resultGraph
                ForeignCases.resultContract
                """
[<EntryPoint>]
let main _ = if read 4 = 0 then 0 else 1
"""

        let descriptor =
            Assert.Single (ForeignDeclarations.readDescriptors graph).ResultRanges

        let withdrawn =
            { graph with
                Edges =
                    graph.Edges
                    |> List.filter (fun edge ->
                        match edge.Role with
                        | EdgeRole.BoundaryDeclaration declaration -> declaration.Binding <> descriptor.Declaration.Binding
                        | _ -> true)
            }

        match Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.issue withdrawn with
        | Error _ -> ()
        | Ok facts ->
            Assert.True(
                facts.Values.TryFind(RangeContext.Shared, descriptor.Declaration.Body)
                |> Option.forall ((=) ValueRange.Unbounded)
            )

        match Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.foreignResultApplications withdrawn None with
        | Error(site, reason) ->
            Assert.Equal(descriptor.Declaration.Binding, site)
            Assert.Contains("boundary declaration", reason)
        | Ok _ -> failwith "Missing source declaration incidence silently omitted its conditional claims"

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Foreign calls discard mutable guard facts while ordinary pure calls retain them``(foreign: bool) =
        let tick =
            if foreign then
                "[<FidelityExtern(\"c\", \"native_tick\")>]\nlet tick () : unit = NativeDefault.zeroed ()"
            else
                "let tick () = ()"

        let body =
            """
[<EntryPoint>]
let main args =
    let mutable count = if args.Length = 0 then 1 else 1024
    let result =
        if count <= 4 then
            tick ()
            read count
        else 0
    if result <= 1024 then 0 else 1
"""

        let graph = ForeignCases.resultGraph ForeignCases.resultContract (tick + body)
        let rows = ForeignCases.resultEvidence graph graph.RangeContextFacts

        let expected =
            if foreign then
                ValueRange.bounded 1I 1024I
            else
                ValueRange.bounded 1I 4I

        Assert.NotEmpty rows
        Assert.All(rows, fun row -> Assert.Equal(expected, row.Application.Arguments.Head.Enclosure))

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Foreign boolean placeholder predicates grant no guard refinement``(foreign: bool) =
        let annotation =
            if foreign then
                "[<FidelityExtern(\"c\", \"native_predicate\")>]\n"
            else
                ""

        let body =
            """
let predicate (count: int) : bool = count <= 4
[<EntryPoint>]
let main args =
    let count = if args.Length = 0 then 1 else 1024
    let result = if predicate count then read count else 0
    if result <= 1024 then 0 else 1
"""

        let graph = ForeignCases.resultGraph ForeignCases.resultContract (annotation + body)
        let rows = ForeignCases.resultEvidence graph graph.RangeContextFacts

        let expected =
            if foreign then
                ValueRange.bounded 1I 1024I
            else
                ValueRange.bounded 1I 4I

        Assert.NotEmpty rows
        Assert.All(rows, fun row -> Assert.Equal(expected, row.Application.Arguments.Head.Enclosure))

    [<Fact>]
    member _.``Ordinary wrapper foreign calls retain distinct caller contexts``() =
        let graph =
            ForeignCases.resultGraph
                ForeignCases.resultContract
                """
let wrapper count = read count
[<EntryPoint>]
let main _ =
    let small = wrapper 4
    let large = wrapper 1024
    if small <= 4 && large <= 1024 then 0 else 1
"""

        let rows = ForeignCases.resultEvidence graph graph.RangeContextFacts
        Assert.Equal(2, rows.Length)

        Assert.Equal(
            1,
            rows
            |> List.map (fun row -> row.Application.Call)
            |> List.distinct
            |> List.length
        )

        Assert.Equal(
            2,
            rows
            |> List.map (fun row -> row.Application.Context)
            |> List.distinct
            |> List.length
        )

        let ranges =
            rows
            |> List.map (fun row -> row.Application.Arguments.Head.Enclosure, row.ResultRange)

        Assert.Contains((ValueRange.point 4I, ValueRange.bounded -1I 4I), ranges)
        Assert.Contains((ValueRange.point 1024I, ValueRange.bounded -1I 1024I), ranges)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Mixed callable boolean values retain the external alternative enclosure``(foreign: bool) =
        let alternate =
            if foreign then
                "[<FidelityExtern(\"c\", \"native_flag\")>]\nlet alternate () : bool = NativeDefault.zeroed ()"
            else
                "let alternate () = false"

        let body =
            """
let ordinary () = false
[<EntryPoint>]
let main args =
    let chosen = if args.Length = 0 then ordinary else alternate
    let result = chosen ()
    if result then 1 else 0
"""

        let graph = (ForeignCases.check (alternate + body)).Graph

        let result =
            graph.Nodes.Values
            |> Seq.find (fun node ->
                match node.Kind with
                | SemanticKind.Binding("result", _, _, _) -> true
                | _ -> false)

        // Ordinary value-call selection is already conservative in this fixture.
        // The external alternative must retain the complete boolean enclosure.
        let expected = ValueRange.boolean
        Assert.Equal(Some expected, result.ValueRange)


    [<Fact>]
    member _.``Rowless foreign boolean predicates grant no placeholder guard refinement``() =
        let graph =
            ForeignCases.resultGraph
                ForeignCases.resultContract
                """
[<FidelityExtern("c", "native_predicate")>]
let predicate (count: int) : bool = count <= 4
[<EntryPoint>]
let main args =
    let count = if args.Length = 0 then 1 else 1024
    let result = if predicate count then read count else 0
    if result <= 1024 then 0 else 1
"""

        let predicate =
            graph.Edges
            |> List.choose (fun edge ->
                match edge.Role with
                | EdgeRole.BoundaryDeclaration declaration when
                    (match graph.Nodes[declaration.Binding].Kind with
                     | SemanticKind.Binding("predicate", _, _, _) -> true
                     | _ -> false)
                    ->
                    Some declaration
                | _ -> None)
            |> Assert.Single

        let withdrawn =
            { graph with
                Edges =
                    graph.Edges
                    |> List.filter (fun edge ->
                        match edge.Role with
                        | EdgeRole.BoundaryDeclaration declaration -> declaration.Binding <> predicate.Binding
                        | _ -> true)
            }
            |> Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable

        Assert.True(withdrawn.Nodes[predicate.Body].IsReachable)

        let facts =
            Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.issue withdrawn
            |> function
                | Ok facts -> facts
                | Error reason -> failwith reason

        let rows = ForeignCases.resultEvidence withdrawn (Some facts)
        Assert.NotEmpty rows
        Assert.All(rows, fun row -> Assert.Equal(ValueRange.bounded 1I 1024I, row.Application.Arguments.Head.Enclosure))

    [<Fact>]
    member _.``Infeasible foreign result source premises retain projectable logical claims``() =
        let contract =
            ForeignCases.resultContract.Replace("Lower=Constant (-1); Upper=Argument 0", "Lower=Argument 0; Upper=Constant 5")

        let graph =
            ForeignCases.resultPlatformCheck
                contract
                """
[<EntryPoint>]
let main _ = if read 10 = 0 then 0 else 1
"""
            |> fun result -> result.Graph

        let rows = ForeignCases.resultEvidence graph graph.RangeContextFacts
        let row = Assert.Single rows
        Assert.Equal(ValueRange.point 10I, row.Application.Arguments.Head.Enclosure)
        Assert.Equal(ValueRange.Empty, row.ResultRange)
        let claims = ForeignCases.resultClaims graph
        Assert.Equal(2, claims.Length)

        let narrowing =
            claims
            |> List.filter (fun (_, _, model) -> model.Role = ForeignResultProofRole.AbiNarrowing)
            |> List.map (fun (_, info, _) -> info)
            |> Clef.Compiler.Nanopass.ObligationDischarge.unavailable
            |> Assert.Single

        Assert.Contains(narrowing.MissingPremises, fun reason -> reason.Contains "no established finite enclosure")

        let _, info, model =
            claims
            |> List.filter (fun (_, _, model) -> model.Role = ForeignResultProofRole.LogicalCoverage)
            |> Assert.Single

        Assert.NotEmpty info.Id
        Assert.NotEmpty info.Source
        Assert.Equal(row.Application, model.Application)

        let projection =
            Clef.Compiler.Baker.Ingredients.PublishedFactRows.mapForeignResultCoverageModel model
            |> Fidelity.PSG.ForeignResultCoverage.ofModel
            |> function
                | Ok projection -> projection
                | Error reason -> failwith reason

        let premiseQuery = Fidelity.PSG.ForeignResultCoverage.premisesQuery projection
        Assert.Contains("(<= foreign_arg_0 foreign_result)", premiseQuery)
        Assert.Contains("(<= foreign_result 5)", premiseQuery)

        System.Console.WriteLine(
            "SOURCE_VACUITY_PREMISES_BEGIN\n"
            + premiseQuery
            + "\nSOURCE_VACUITY_PREMISES_END"
        )
