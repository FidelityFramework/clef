namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeService
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module ForeignDeclarations = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

module private ForeignCases =
    let check body =
        let vocabulary = """module Foreign
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Pointer of int | Void
type PassBy = Value | Reference
type CallConv = | CDecl
type Transfer = | Borrowed
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
"""
        match parseAndCheck (vocabulary + body) "foreign.clef" with
        | Success result | CheckFailure result -> result
        | ParseFailure errors -> failwithf "%A" errors

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

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ForeignReferences")>]
type ForeignReferenceTests() =
    [<Fact>]
    member _.``Mapped stride retains native output bounds and length retains checked extent bounds``() =
        let context: PlatformContext = {
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
type FieldDescriptor = { Name: string; Repr: string; BitFields: int array }
type PeripheralLayout = { Fields: FieldDescriptor array }
type StructDescriptor = { Name: string; Layout: PeripheralLayout }
let mutexLayout : StructDescriptor =
    { Name = "Mutex"; Layout = { Fields = [| { Name = "Storage"; Repr = "u8"; BitFields = [||] } |] } }
[<EntryPoint>]
let main _ = 0
"""
        DimensionalCases.noErrors result
        let descriptors = ForeignDeclarations.readDescriptors result.Graph
        Assert.Empty descriptors.Findings
        Assert.True((Assert.Single descriptors.Layouts).RecordType.IsNone)
