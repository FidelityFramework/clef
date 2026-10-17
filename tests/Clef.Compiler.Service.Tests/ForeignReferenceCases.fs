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

    // Explicit test-stated resource hypotheses. The declarations share a
    // phantom carrier and C symbols, while their source bodies stay distinct.
    let resourceSource =
        let declarations suffix =
            let template = """
[<FidelityExtern("c", "malloc")>]
let malloc@SUFFIX@ (size:int) : option<CHandle<unit>> = NativeDefault.zeroed ()
let malloc@SUFFIX@Descriptor: Expr<FunctionDescriptor> = <@ {
    CName="malloc"; Parameters=[| {Name="size";Type=Integer(Unsigned,64);PassBy=Value} |]
    ReturnType=Pointer 64; CallingConvention=CDecl; OwnershipTransfer=Undeclared } @>
let malloc@SUFFIX@ResourceDescriptor: Expr<ResourceDescriptor> = <@ {
    Resource=OwnedNullableReturn ({Binding="Foreign.free@SUFFIX@";Parameter=0})
    Hypothesis={Identity="fixture-owned-@SUFFIX@";Version="1";Source="explicit resource test premise"} } @>
[<FidelityExtern("c", "free")>]
let free@SUFFIX@ (handle:CHandle<unit>) : unit = NativeDefault.zeroed ()
let free@SUFFIX@Descriptor: Expr<FunctionDescriptor> = <@ {
    CName="free"; Parameters=[| {Name="handle";Type=Pointer 64;PassBy=Value} |]
    ReturnType=Void; CallingConvention=CDecl; OwnershipTransfer=Undeclared } @>
"""
            template.Replace("@SUFFIX@", suffix)
        vocabulary.Replace("type Transfer = | Borrowed", "type Transfer = Borrowed | Undeclared")
        + """
type ExternalExecutionHypothesis = { Identity:string; Version:string; Source:string }
type ResourceRelease = { Binding:string; Parameter:int }
type ResourceProtocol = OwnedNullableReturn of ResourceRelease
type ResourceDescriptor = { Resource:ResourceProtocol; Hypothesis:ExternalExecutionHypothesis }
"""
        + declarations "First" + declarations "Second"

    let declarationCheckFor sources =
        let parse source path =
            match parseStringWithDefaults source path with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "%A" errors
        checkParsedInputsWithPlatform
                ([parse (SourcePlatformFixture.authority.Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")) "write-authority.clef"]
                 @ (sources |> List.map(fun (source,path) -> parse source path))
                 @ [parse "module ResourceDeclarationMain\n[<EntryPoint>]\nlet main _ = 0\n" "resource-main.clef"])
                (Some SourcePlatformFixture.platform)

    let resourceGraphFor sources =
        let result=declarationCheckFor sources
        DimensionalCases.noErrors result
        Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare result.Graph
        |> Result.defaultWith (fun errors -> failwithf "%A" errors)

    let resourceGraph () = resourceGraphFor [resourceSource,"resource-declarations.clef"]

    // Actual Farscape writable-buffer prototype and quotation (Native.clef),
    // with this owner's existing local vocabulary fixture. No call roots it.
    let writableSource =
        vocabulary.Replace("module Foreign", "module Test.Native").Replace("type Transfer = | Borrowed", "type Transfer = Borrowed | Undeclared")
        + """
type ExternalExecutionHypothesis = { Identity:string; Version:string; Source:string }
type WritableBufferDescriptor = { Binding:string; Parameter:int; CountParameter:int; Hypothesis:ExternalExecutionHypothesis }
[<FidelityExtern("c", "native_read")>]
let read (fd: int) (buffer: int array) (count: int) : int = NativeDefault.zeroed ()
let readDescriptor : Expr<FunctionDescriptor> = <@ {
    CName = "native_read"
    Parameters = [|
        { Name = "fd"; Type = Integer (Signed, 32); PassBy = Value }
        { Name = "buffer"; Type = Integer (Unsigned, 8); PassBy = Reference }
        { Name = "count"; Type = Integer (Unsigned, 64); PassBy = Value } |]
    ReturnType = Integer (Signed, 64); CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let readWritableBuffer1Descriptor : Expr<WritableBufferDescriptor> = <@ {
    Binding = "Test.Native.read"; Parameter = 1; CountParameter = 2
    Hypothesis = { Identity = "posix.read.borrow"; Version = "2024"; Source = "read-contract.pilot.toml" } } @>
"""
    let writableGraph = lazy(resourceGraphFor [writableSource,"writable-declarations.clef"])
    let publishedWritable = lazy(writableGraph.Value
        |> Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish
        |> Result.defaultWith(fun errors -> failwithf "%A" errors))

    let applicationForAuthority authority source moduleName body =
        let root =
            System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__, "../../artifacts/resource-application-tests", System.Guid.NewGuid().ToString("N")))
        System.IO.Directory.CreateDirectory root |> ignore
        let write (name:string) (text:string) = System.IO.File.WriteAllText(System.IO.Path.Combine(root,name),text)
        write "authority.clef" authority
        write "resource.clef" source
        write "main.clef" ("module "+moduleName+"\n[<EntryPoint>]\nlet main _ =\n" + body)
        write "resource.fidproj" """
[package]
name="ResourceApplicationRequirement"
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
        Clef.Compiler.Project.ProjectChecker.checkProject (System.IO.Path.Combine(root,"resource.fidproj"))
        |> Result.defaultWith(fun error -> failwithf "%A" error)

    let applicationFor source moduleName body =
        applicationForAuthority (SourcePlatformFixture.authority.Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")) source moduleName body

    let resourceApplication body = applicationFor resourceSource "ResourceApplicationMain" body
    let writableApplication body = applicationFor writableSource "WritableApplicationMain" body
    let writableVoidSource =
        let replace (before:string) (after:string) (source:string) =
            let changed=source.Replace(before,after)
            if changed=source then failwithf "Missing writable void fixture token: %s" before
            changed
        writableSource
        |> replace "let read (fd: int) (buffer: int array) (count: int) : int" "let read (buffer: int array) (count: int) : unit"
        |> replace "        { Name = \"fd\"; Type = Integer (Signed, 32); PassBy = Value }\n" ""
        |> replace "ReturnType = Integer (Signed, 64)" "ReturnType = Void"
        |> replace "Parameter = 1; CountParameter = 2" "Parameter = 0; CountParameter = 1"
    let writableVoidApplication source body =
        let authority=SourcePlatformFixture.authority.Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")
                        .Replace("Spaces = [| rodata |]", "Spaces = [| rodata; { Name = \"stack\"; Kind = \"stack\"; Capacity = 1048576; Alignment = 16; Granularity = 16; Growth = \"fixed\"; Access = \"rw\"; Base = None } |]")
        applicationForAuthority authority source "WritableNativeMain" body
    let writableNative = lazy(
        writableVoidApplication writableVoidSource "    let buffer = Array.zeroCreate 4\n    Test.Native.read buffer 3\n    if buffer[0] = 102 then 0 else 1\n")
    let publishedWritableNative = lazy(
        let result=writableNative.Value
        Assert.False(Clef.Compiler.Project.ProjectChecker.hasErrors result,String.concat "\n" (Clef.Compiler.Project.ProjectChecker.getErrorMessages result))
        Clef.Compiler.Project.ProjectChecker.publish result |> Result.defaultWith failwith)
    let writableRelationalSource =
        writableVoidSource.Replace("(count: int) : unit", "(count: int) : int")
                          .Replace("ReturnType = Void", "ReturnType = Integer (Signed, 64)")
        + """
type ResultBound = Constant of int | Argument of int
type ResultRole = | ReturnValue
type ResultRangeDescriptor = { Binding:string; Role:ResultRole; Hypothesis:ExternalExecutionHypothesis; Lower:ResultBound; Upper:ResultBound }
let readResultRange : Expr<ResultRangeDescriptor> = <@ {
    Binding = "Test.Native.read"; Role = ReturnValue
    Hypothesis = { Identity = "fixture.writable.result"; Version = "1"; Source = "writable-result.pilot.toml" }
    Lower = Constant (-1); Upper = Argument 1 } @>
"""
    let writableRelationalBody = "    let buffer = Array.zeroCreate 4\n    let answer = Test.Native.read buffer 3\n    if answer < 0 then -1 elif answer = 0 then 0 else answer\n"
    let writableRelational = lazy(writableVoidApplication writableRelationalSource writableRelationalBody)
    let publishedWritableRelational = lazy(
        let result=writableRelational.Value
        Assert.False(Clef.Compiler.Project.ProjectChecker.hasErrors result,String.concat "\n" (Clef.Compiler.Project.ProjectChecker.getErrorMessages result))
        Clef.Compiler.Project.ProjectChecker.publish result |> Result.defaultWith failwith)
    let writablePosixSource =
        writableRelationalSource.Replace("let read (buffer: int array)","let read (fd: int) (buffer: int array)")
                                .Replace("    Parameters = [|\n","    Parameters = [|\n        { Name = \"fd\"; Type = Integer (Signed, 32); PassBy = Value }\n")
                                .Replace("Parameter = 0; CountParameter = 1","Parameter = 1; CountParameter = 2")
                                .Replace("Upper = Argument 1","Upper = Argument 2")
    let writablePosixBody = writableRelationalBody.Replace("Test.Native.read buffer 3","Test.Native.read 0 buffer 3")
    let writablePosix = lazy(writableVoidApplication writablePosixSource writablePosixBody)
    let publishedWritablePosix = lazy(
        let result=writablePosix.Value
        Assert.False(Clef.Compiler.Project.ProjectChecker.hasErrors result,String.concat "\n" (Clef.Compiler.Project.ProjectChecker.getErrorMessages result))
        Clef.Compiler.Project.ProjectChecker.publish result |> Result.defaultWith failwith)

    let writableProof expected (info:ObligationInfo) =
        let query=Clef.Compiler.Nanopass.ObligationDischarge.trySmtLib [info]
                  |> Result.defaultWith(fun unavailable -> failwithf "A concrete writable coverage body was unavailable: %A" unavailable)
        let start=System.Diagnostics.ProcessStartInfo("cvc5",UseShellExecute=false,RedirectStandardInput=true,RedirectStandardOutput=true,RedirectStandardError=true)
        start.ArgumentList.Add "--lang=smt2"
        use child=System.Diagnostics.Process.Start start |> Option.ofObj |> Option.defaultWith(fun ()->failwith "cvc5 did not start")
        child.StandardInput.Write query
        child.StandardInput.Close()
        let output,error=child.StandardOutput.ReadToEndAsync(),child.StandardError.ReadToEndAsync()
        if not(child.WaitForExit(10000)) then
            child.Kill(true)
            child.WaitForExit()
            failwith "The owned cvc5 coverage check exceeded its 10-second bound."
        let directory=System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__,"../../artifacts/writable-buffer-proof-tests"))
        System.IO.Directory.CreateDirectory directory |> ignore
        let path=System.IO.Path.Combine(directory,System.Guid.NewGuid().ToString("N")+".smt2")
        System.IO.File.WriteAllText(path,query)
        let digest=System.Security.Cryptography.SHA256.HashData(System.Text.Encoding.UTF8.GetBytes query) |> System.Convert.ToHexString
        printfn "WRITABLE_PROOF body=%A query=%s sha256=%s solver=%s" info.Body path digest (output.Result.Trim())
        Assert.Equal(0,child.ExitCode)
        Assert.True(error.Result="",error.Result)
        Assert.Equal(expected,output.Result.Trim())

    let resourceRequirements (graph:SemanticGraph) =
        graph.Nodes.Values |> Seq.choose(fun node ->
            match node.Kind with
            | SemanticKind.Obligation info when info.Kind.StartsWith("foreign-resource-",System.StringComparison.Ordinal) -> Some(node.Id,info)
            | _ -> None) |> Seq.toList

    let resourceRequirementSupport (graph:SemanticGraph) id =
        graph.Edges |> List.filter(fun edge -> edge.Target=id && edge.Role=EdgeRole.Constrains)
        |> function [edge] -> edge.Sources | rows -> failwithf "Expected one exact requirement incidence: %A" rows

    let publishedResources =
        lazy (resourceGraph ()
              |> Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish
              |> Result.defaultWith (fun errors -> failwithf "%A" errors))

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
    member _.``Writable buffer generated declaration publishes provenance without call authority``() =
        let graph=ForeignCases.writableGraph.Value
        let declaration=Assert.Single (ForeignDeclarations.readDescriptors graph).WritableBuffers
        Assert.Equal("Test.Native.read",declaration.Contract.Binding)
        Assert.Equal(1,declaration.Parameter)
        Assert.Equal(2,declaration.CountParameter)
        Assert.Equal(3,declaration.Declaration.Formals.Length)
        let revision=ForeignCases.publishedWritable.Value
        let row=Assert.Single revision.Emission.Boundary.WritableBufferDeclarations.Values
        Assert.Equal("posix.read.borrow",row.Contract.Hypothesis.Identity)
        Assert.Equal("2024",row.Contract.Hypothesis.Version)
        let scope=row.DeclarationFacts[row.Declaration].Parent |> Option.get
        let header=revision.SourceReadings.ContextHeaders[scope]
        Assert.Equal("Test.Native",header.Name)
        Assert.True(header.Ports.ContainsKey Fidelity.PSG.OccurrencePort.ModuleDeclaration)
        Assert.Empty revision.Emission.Boundary.Calls
        let defects=Fidelity.PSG.Integrity.check revision
        Assert.True(defects.IsEmpty,Fidelity.PSG.Integrity.describe defects)
        let limits:Fidelity.PSG.Binary.Limits={MaxBytes=8000000;MaxCollectionLength=100000;MaxDepth=128;MaxStringBytes=1000000;MaxBigIntegerBytes=4096;MaxValues=2000000}
        let bytes=Fidelity.PSG.Binary.encode limits revision |> Result.defaultWith(fun error -> failwithf "%A" error)
        let copy=Fidelity.PSG.Binary.decode limits bytes |> Result.defaultWith(fun error -> failwithf "%A" error)
        Assert.True(revision.Emission.Boundary.WritableBufferDeclarations=copy.Emission.Boundary.WritableBufferDeclarations)

    [<Theory>]
    [<InlineData("same-ordinal","distinct in-range native buffer/count ordinals")>]
    [<InlineData("missing-formal","complete unchanged FunctionDescriptor/formal vector")>]
    [<InlineData("wide-element","explicit unsigned-8 Reference element contract")>]
    [<InlineData("readonly","explicit unsigned-8 Reference element contract")>]
    [<InlineData("wrong-binding","Binding must select one exact qualified extern")>]
    [<InlineData("empty-version","nonempty versioned hypothesis")>]
    [<InlineData("reference-count","CountParameter requires")>]
    [<InlineData("boolean-count","CountParameter requires")>]
    [<InlineData("cname","FunctionDescriptor.CName differs")>]
    member _.``Writable buffer declaration source refuses wrong association and missing premise``(shape:string,reason:string) =
        let original=ForeignCases.writableSource
        let changed=
            match shape with
            | "same-ordinal" -> original.Replace("Parameter = 1; CountParameter = 2","Parameter = 1; CountParameter = 1")
            | "missing-formal" -> original.Replace("CountParameter = 2","CountParameter = 3")
            | "wide-element" -> original.Replace("Integer (Unsigned, 8)","Integer (Unsigned, 32)")
            | "readonly" -> original.Replace("Value | Reference","Value | Reference | ReadOnlyReference").Replace("PassBy = Reference","PassBy = ReadOnlyReference")
            | "wrong-binding" -> original.Replace("Binding = \"Test.Native.read\"","Binding = \"Test.Native.native_read\"")
            | "empty-version" -> original.Replace("Version = \"2024\"","Version = \"\"")
            | "reference-count" -> original.Replace("(count: int)","(count: int array)").Replace("Name = \"count\"; Type = Integer (Unsigned, 64); PassBy = Value","Name = \"count\"; Type = Integer (Unsigned, 8); PassBy = Reference")
            | "boolean-count" -> original.Replace("| Void","| Void | Bool").Replace("(count: int)","(count: bool)").Replace("Type = Integer (Unsigned, 64)","Type = Bool")
            | "cname" -> original.Replace("CName = \"native_read\"","CName = \"different_symbol\"")
            | _ -> failwith "Unknown writable declaration perturbation"
        Assert.NotEqual<string>(original,changed)
        let result=ForeignCases.declarationCheckFor [changed,"writable-declarations.clef"]
        let reading=ForeignDeclarations.readDescriptors result.Graph
        Assert.Empty reading.WritableBuffers
        Assert.Contains(reading.Findings,fun finding -> finding.Message.Contains reason)

    [<Theory>]
    [<InlineData("formal-order","Ordinals")>]
    [<InlineData("binding","Contract")>]
    [<InlineData("version","Contract")>]
    [<InlineData("byte","Element")>]
    [<InlineData("withdrawal","Contract")>]
    [<InlineData("missing-context","Declaration")>]
    [<InlineData("reference-count","Count")>]
    [<InlineData("boolean-count","Count")>]
    member _.``Writable buffer public replay refuses changed exact declaration facts``(shape:string,part:string) =
        let revision=ForeignCases.publishedWritable.Value
        let boundary=revision.Emission.Boundary
        let original=Assert.Single boundary.WritableBufferDeclarations.Values
        let row=
            match shape with
            | "formal-order" -> {original with Formals=[original.Formals[2];original.Formals[1];original.Formals[0]]}
            | "binding" -> {original with Contract={original.Contract with Binding="Test.Native.native_read"}}
            | "version" -> {original with Contract={original.Contract with Hypothesis={original.Contract.Hypothesis with Version="changed"}}}
            | "byte" ->
                let key,fact=original.DeclarationFacts |> Map.toList |> List.filter(fun(_,fact)->fact.Form="integer" && fact.Numbers=[8I]) |> Assert.Single
                {original with DeclarationFacts=original.DeclarationFacts.Add(key,{fact with Numbers=[32I]})}
            | "withdrawal" -> {original with DeclarationFacts=original.DeclarationFacts.Remove original.Identity}
            | "missing-context" -> original
            | "reference-count" | "boolean-count" ->
                let fields id = let fact=original.DeclarationFacts[id] in List.zip fact.Text fact.References |> Map.ofList
                let parameters=original.DeclarationFacts[(fields original.Descriptor)["Parameters"]].References
                let parameter=fields parameters[original.CountParameter]
                let key=parameter[if shape="reference-count" then "PassBy" else "Type"]
                let fact=original.DeclarationFacts[key]
                {original with DeclarationFacts=original.DeclarationFacts.Add(key,{fact with Text=[if shape="reference-count" then "Reference" else "Bool"];References=[];Children=[]})}
            | _ -> failwith "Unknown writable public perturbation"
        let changed={revision with Emission={revision.Emission with Boundary={boundary with WritableBufferDeclarations=boundary.WritableBufferDeclarations.Add(row.Identity,row)}}}
        let changed=
            if shape="missing-context" then
                let scope=row.DeclarationFacts[row.Declaration].Parent |> Option.get
                {changed with SourceReadings={changed.SourceReadings with ContextHeaders=changed.SourceReadings.ContextHeaders.Remove scope}}
            else changed
        Assert.Contains(Fidelity.PSG.Integrity.check changed,fun issue -> issue.Part="Emission.Boundary.WritableBufferDeclarations."+part)

    [<Fact>]
    member _.``Writable buffer source currentness retains descriptor absence and version premises``() =
        let graph=ForeignCases.writableGraph.Value
        let declaration=Assert.Single (ForeignDeclarations.readDescriptors graph).WritableBuffers
        let version=graph.Nodes.Values |> Seq.filter(fun node -> node.Kind=SemanticKind.Literal(NativeLiteral.String "2024")) |> Assert.Single
        let changed=[{graph with Nodes=graph.Nodes.Add(version.Id,{version with Kind=SemanticKind.Literal(NativeLiteral.String "changed")})}
                     {graph with Nodes=graph.Nodes.Remove declaration.Quote}]
        for current in changed do
            match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project current with
            | Error failures -> Assert.Contains(failures,fun failure -> failure.Reason.Contains "A source boundary premise, membership, scope, type, range, platform claim or numeric meet changed")
            | Ok _ -> failwith "Changed writable descriptor retained the old current boundary account"

    [<Fact>]
    member _.``Writable effect retains byte ingress alias range and exact bound citizens while native stays pending``() =
        let result=ForeignCases.writableApplication "    let buffer = Array.zeroCreate 4\n    let alias = buffer\n    let readResult = Test.Native.read 0 alias 3\n    if readResult < 0 then alias[0] else alias[0]\n"
        let graph=result.CheckResult.Graph
        let application=Clef.Compiler.Baker.Recipes.StringByteStorageRecipes.writableApplications graph |> Map.toList |> Assert.Single |> snd
        let application=application |> Result.defaultWith(fun failure -> failwith failure.Reason)
        Assert.Equal(ValueRange.bounded 0I 255I,application.StorageRange)
        Assert.Equal(ValueRange.point 3I,application.CountRange)
        Assert.Equal(ValueRange.point 4I,application.CapacityRange)
        let claims=graph.Nodes.Values |> Seq.choose(fun node -> match node.Kind with SemanticKind.Obligation info when info.Kind.StartsWith "foreign-writable-buffer-" -> Some(node.Id,info) | _ -> None) |> Seq.toList
        Assert.Equal(3,claims.Length)
        Assert.Contains(claims,fun(_,info)->info.Kind="foreign-writable-buffer-count" && info.Body=ObligationBody.IntegerRepresentationCoverage(3I,3I,0I,4I))
        Assert.Contains(claims,fun(_,info)->info.Kind="foreign-writable-buffer-storage" && info.Body=ObligationBody.IntegerRepresentationCoverage(0I,255I,0I,255I))
        Assert.Contains(claims,fun(_,info)->info.Kind="foreign-writable-buffer-adapter" && (match info.Body with ObligationBody.Pending reasons -> List.contains "MemoryPublication: A dynamic array requires exactly one declared writable stack space." reasons | _ -> false))
        for id,info in claims do
            Assert.StartsWith("foreign_writable_",info.Id)
            let anchor=System.Convert.FromHexString(info.Id.Substring("foreign_writable_".Length)) |> System.Text.Encoding.UTF8.GetString
            Assert.Contains("Test.Native.read",anchor)
            Assert.Contains("WritableApplicationMain",anchor)
            Assert.Contains("posix.read.borrow",info.Refs)
            match info.Body with ObligationBody.IntegerRepresentationCoverage _ -> ForeignCases.writableProof "unsat" info | _ -> ()
            let sources=ForeignCases.resourceRequirementSupport graph id
            for required in application.Participants do Assert.Contains(required,sources)
        let reads=graph.Nodes.Values |> Seq.filter(fun node -> match node.Kind with SemanticKind.IndexGet(input,_) -> input<>application.Allocation | _ -> false) |> Seq.toList
        Assert.Contains(reads,fun node->node.ValueRange=Some(ValueRange.bounded 0I 255I))
        Assert.Contains(Clef.Compiler.Project.ProjectChecker.getErrorMessages result,fun message->
            message.Contains "A writable byte ABI requires its exact direct application, allocation and current count/storage proof account.")

    [<Theory>]
    [<InlineData("unknown-count")>]
    [<InlineData("oversize")>]
    member _.``Writable effect missing finite count remains visible Pending with descriptor support``(shape:string) =
        let source=if shape="unknown-count" then "    let buffer = Array.zeroCreate 4\n    let mutable n = 0\n    while n >= 0 do\n        n <- n + 1\n    Test.Native.read 0 buffer n\n" else "    let buffer = Array.zeroCreate 4\n    Test.Native.read 0 buffer 5\n"
        let result=ForeignCases.writableApplication source
        let graph=result.CheckResult.Graph
        let site,application=Clef.Compiler.Baker.Recipes.StringByteStorageRecipes.writableApplications graph |> Map.toList |> Assert.Single
        let failure=match application with Error failure -> failure | Ok _ -> failwith "Missing count coverage was admitted"
        Assert.Contains("count domain",failure.Reason)
        let claims=graph.Nodes.Values |> Seq.choose(fun node -> match node.Kind with SemanticKind.Obligation info when info.Kind="foreign-writable-buffer-adapter" -> Some(node.Id,info) | _ -> None) |> Seq.toList
        let id,info=Assert.Single claims
        match info.Body with ObligationBody.Pending reasons -> Assert.Contains(reasons,fun reason->reason.Contains "count domain") | _ -> failwith "Missing count became a finite claim"
        let support=ForeignCases.resourceRequirementSupport graph id
        Assert.Contains(site,support)
        Assert.Contains(failure.Declaration.Quote,support)
        Assert.Contains(failure.Declaration.CountFormal,support)
        let bounds=graph.Nodes.Values |> Seq.choose(fun node -> match node.Kind with SemanticKind.Obligation info when info.Kind="foreign-writable-buffer-count" -> Some info | _ -> None) |> Seq.toList
        if shape="unknown-count" then Assert.Empty bounds else
            let bound=Assert.Single bounds
            Assert.Equal(ObligationBody.IntegerRepresentationCoverage(5I,5I,0I,4I),bound.Body)
            Assert.Equal(BoundaryProofOutcome.Refuted,Clef.Compiler.Baker.Ingredients.StringBytes.proofOutcome bound.Body)
            ForeignCases.writableProof "sat" bound

    [<Fact>]
    member _.``Writable effect old zero does not establish postcall ASCII``() =
        let result=ForeignCases.writableApplication "    let buffer = Array.zeroCreate 4\n    let alias = buffer\n    let readResult = Test.Native.read 0 alias 3\n    let text = String.fromBytes alias\n    if readResult < 0 then String.length text else String.length text\n"
        Assert.Contains(Clef.Compiler.Project.ProjectChecker.getErrorMessages result,fun message->message.Contains "text must be proved ASCII")

    [<Fact>]
    member _.``Writable effect fresh postcall read is not the immutable precall zero read``() =
        let result=ForeignCases.writableApplication "    let buffer = Array.zeroCreate 4\n    let alias = buffer\n    let before = alias[0]\n    if before = 0 then\n        let readResult = Test.Native.read 0 alias 3\n        if readResult < 0 then alias[0] else alias[0]\n    else 0\n"
        let graph=result.CheckResult.Graph
        let application=Clef.Compiler.Baker.Recipes.StringByteStorageRecipes.writableApplications graph |> Map.toList |> Assert.Single |> snd
        let application=application |> Result.defaultWith(fun failure -> failwith failure.Reason)
        Assert.Equal(ValueRange.bounded 0I 255I,application.StorageRange)
        let reads=graph.Nodes.Values |> Seq.filter(fun node -> match node.Kind with SemanticKind.IndexGet _ -> true | _ -> false) |> Seq.toList
        let latest=reads |> List.filter(fun node -> node.Range.Start.Line>7)
        Assert.NotEmpty latest
        Assert.All(latest,fun node->Assert.Equal(Some(ValueRange.bounded 0I 255I),node.ValueRange))

    [<Theory>]
    [<InlineData("relation")>]
    member _.``Writable relational source requires exact result relation and count domain``(shape:string) =
        let source,body,reason=
            match shape with
            | "relation" ->
                let source=ForeignCases.writableRelationalSource.Replace("Lower = Constant (-1)","Lower = Constant 0")
                Assert.NotEqual<string>(ForeignCases.writableRelationalSource,source)
                source,ForeignCases.writableRelationalBody,"The writable result hypothesis or ordered actuals differ from this call's exact -1..count relation."
            | _ -> failwith "Unknown relational premise change"
        let graph=(ForeignCases.writableVoidApplication source body).CheckResult.Graph
        Assert.DoesNotContain(graph.Edges,fun edge->match edge.Role with EdgeRole.BoundaryWritableBufferUse _->true | _->false)
        Assert.Contains(graph.Nodes.Values,fun node->
            match node.Kind with
            | SemanticKind.Obligation info when info.Kind="foreign-writable-buffer-adapter" ->
                match info.Body with ObligationBody.Pending reasons->List.contains reason reasons | _->false
            | _->false)

    [<Fact>]
    member _.``Writable relational count two retains its exact current result account``() =
        let body=ForeignCases.writableRelationalBody.Replace("Test.Native.read buffer 3","Test.Native.read buffer 2")
        let program=ForeignCases.writableVoidApplication ForeignCases.writableRelationalSource body
        Assert.False(Clef.Compiler.Project.ProjectChecker.hasErrors program,String.concat "\n" (Clef.Compiler.Project.ProjectChecker.getErrorMessages program))
        let revision=Clef.Compiler.Project.ProjectChecker.publish program |> Result.defaultWith failwith
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let row=Assert.Single revision.Emission.Boundary.WritableBufferUses.Values
        Assert.Equal(Fidelity.PSG.ValueRange.Bounded(2I,2I),revision.Emission.Numeric.Values[row.Count].Range)
        Assert.Equal(Fidelity.PSG.ValueRange.Bounded(-1I,2I),revision.Emission.Numeric.Values[row.Call].Range)
        let result=revision.Emission.Numeric.ForeignResultUses |> List.filter(fun use'->use'.Application.Call=row.Call) |> Assert.Single
        Assert.Equal(2,result.Claims |> List.map snd |> List.distinct |> List.length)
        Assert.Equal<Fidelity.PSG.ForeignResultProofRole list>([Fidelity.PSG.ForeignResultProofRole.LogicalCoverage;Fidelity.PSG.ForeignResultProofRole.AbiNarrowing],result.Claims |> List.map fst)

    [<Theory>]
    [<InlineData("version")>]
    [<InlineData("quotation")>]
    [<InlineData("count")>]
    member _.``Writable effect old applied account refuses changed hypothesis quote or count``(shape:string) =
        let result=ForeignCases.writableApplication "    let buffer = Array.zeroCreate 4\n    Test.Native.read 0 buffer 3\n"
        let graph=result.CheckResult.Graph
        let site,observed=Clef.Compiler.Baker.Recipes.StringByteStorageRecipes.writableApplications graph |> Map.toList |> Assert.Single
        let application=observed |> Result.defaultWith(fun failure -> failwith failure.Reason)
        let changed=
            match shape with
            | "quotation" -> {graph with Nodes=graph.Nodes.Remove application.Declaration.Quote}
            | "version" ->
                let node=graph.Nodes.Values |> Seq.filter(fun node->node.Kind=SemanticKind.Literal(NativeLiteral.String "2024")) |> Assert.Single
                {graph with Nodes=graph.Nodes.Add(node.Id,{node with Kind=SemanticKind.Literal(NativeLiteral.String "next")})}
            | "count" ->
                let node=graph.Nodes[application.Count]
                let kind=match node.Kind with SemanticKind.Literal(NativeLiteral.Int(_,kind)) -> kind | other -> failwithf "Expected exact literal actual: %A" other
                {graph with Nodes=graph.Nodes.Add(node.Id,{node with Kind=SemanticKind.Literal(NativeLiteral.Int(4L,kind))})}
            | _ -> failwith "Unknown writable application change"
        match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project changed with
        | Error failures -> Assert.Contains(failures,fun failure->failure.Reason.Contains "A source boundary premise, membership, scope, type, range, platform claim or numeric meet changed")
        | Ok _ -> failwithf "Old applied account at %A survived changed source evidence" site

    [<Fact>]
    member _.``Writable effect storage citizen retains complete local writer value and alias support``() =
        let result=ForeignCases.writableApplication "    let buffer = Array.zeroCreate 4\n    let alias = buffer\n    alias[0] <- 65\n    let readResult = Test.Native.read 0 alias 3\n    if readResult < 0 then alias[0] else alias[0]\n"
        let graph=result.CheckResult.Graph
        let application=Clef.Compiler.Baker.Recipes.StringByteStorageRecipes.writableApplications graph |> Map.toList |> Assert.Single |> snd
        let application=application |> Result.defaultWith(fun failure -> failwith failure.Reason)
        let writer=graph.Nodes.Values |> Seq.filter(fun node -> node.IsReachable && (match node.Kind with SemanticKind.IndexSet(_,_,value) -> graph.Nodes.TryFind value |> Option.exists(fun node->match node.Kind with SemanticKind.Literal(NativeLiteral.Int(65L,_)) -> true | _ -> false) | _ -> false)) |> Assert.Single
        let buffer,value=match writer.Kind with SemanticKind.IndexSet(buffer,_,value)->buffer,value | _ -> failwith "Expected original writer"
        let citizen=graph.Nodes.Values |> Seq.filter(fun node -> match node.Kind with SemanticKind.Obligation info -> info.Kind="foreign-writable-buffer-storage" | _ -> false) |> Assert.Single
        let support=ForeignCases.resourceRequirementSupport graph citizen.Id
        for required in [writer.Id;buffer;value;application.Buffer] do
            Assert.Contains(required,application.Participants)
            Assert.Contains(required,support)
        let stored=graph.Nodes[value]
        let kind=match stored.Kind with SemanticKind.Literal(NativeLiteral.Int(_,kind))->kind | _ -> failwith "Expected source integer"
        let changed={graph with Nodes=graph.Nodes.Add(value,{stored with Kind=SemanticKind.Literal(NativeLiteral.Int(256L,kind))})}
        match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project changed with
        | Error failures -> Assert.Contains(failures,fun failure->failure.Reason.Contains "A source boundary premise, membership, scope, type, range, platform claim or numeric meet changed")
        | Ok _ -> failwith "Changed local writer retained old writable storage authority"

    [<Fact>]
    member _.``Writable effect out of byte local store remains Pending without a storage claim``() =
        let result=ForeignCases.writableApplication "    let buffer = Array.zeroCreate 4\n    let alias = buffer\n    alias[0] <- 300\n    let readResult = Test.Native.read 0 alias 3\n    if readResult < 0 then alias[0] else alias[0]\n"
        let graph=result.CheckResult.Graph
        let observed=Clef.Compiler.Baker.Recipes.StringByteStorageRecipes.writableApplications graph |> Map.toList |> Assert.Single |> snd
        match observed with
        | Error failure -> Assert.Contains("within 0..255",failure.Reason)
        | Ok _ -> failwith "An out-of-byte local writer acquired a writable storage account"
        let claims=graph.Nodes.Values |> Seq.choose(fun node->match node.Kind with SemanticKind.Obligation info when info.Kind.StartsWith "foreign-writable-buffer-" -> Some info | _->None) |> Seq.toList
        Assert.DoesNotContain(claims,fun info->info.Kind="foreign-writable-buffer-storage")
        Assert.Contains(claims,fun info->info.Kind="foreign-writable-buffer-adapter" && (match info.Body with ObligationBody.Pending reasons -> reasons |> List.exists(fun reason->reason.Contains "within 0..255") | _->false))

    [<Theory>]
    [<InlineData(4, 3)>]
    [<InlineData(1024, 1024)>]
    member _.``Writable extent observation retains initialized storage and exact count support``(capacity:int,count:int) =
        let countActual=if count=capacity then "requested" else "(requested - 1)"
        let body=
            sprintf "    let buffer = Array.zeroCreate %d\n    let requested = buffer.Length\n    let result = Test.Native.read 0 buffer %s\n    if result < 0 then 11\n    elif result = 0 then 12\n    else\n        let prefix = eager (Array.sub buffer 0 result)\n        prefix.Length\n" capacity countActual
        let program=ForeignCases.writableVoidApplication ForeignCases.writablePosixSource body
        let graph=program.CheckResult.Graph
        let application=
            Clef.Compiler.Baker.Recipes.StringByteStorageRecipes.writableApplications graph
            |> Map.toList |> Assert.Single |> snd
            |> Result.defaultWith(fun failure->failwith failure.Reason)
        Assert.Equal(ValueRange.point(bigint count),application.CountRange)
        Assert.Equal(ValueRange.point(bigint capacity),application.CapacityRange)
        Assert.Equal(ValueRange.bounded 0I 255I,application.StorageRange)
        let extent=graph.Nodes.Values |> Seq.filter(fun node->
            node.IsReachable && (match node.Kind with
                                 | SemanticKind.FieldGet(_,"Length") -> node.Range.Start.Line=5
                                 | _ -> false)) |> Assert.Single
        let input=match extent.Kind with SemanticKind.FieldGet(input,_) -> input | _ -> failwith "Expected extent observation"
        Assert.Contains(extent.Id,application.Participants)
        Assert.Contains(input,application.Participants)
        let changed={graph with Nodes=graph.Nodes.Add(extent.Id,{extent with Kind=SemanticKind.FieldGet(input,"UnownedField")})}
        match Clef.Compiler.Baker.Recipes.StringByteStorageRecipes.writableApplications changed |> Map.toList |> Assert.Single |> snd with
        | Error failure -> Assert.Equal("The writable count domain must be finite, nonnegative and contained in the actual allocation's byte-slot capacity domain.",failure.Reason)
        | Ok _ -> failwith "An unowned member access retained writable storage authority"
        Assert.Contains(graph.Edges,fun edge->match edge.Role with EdgeRole.BoundaryWritableBufferUse _->true | _->false)
        Assert.False(Clef.Compiler.Project.ProjectChecker.hasErrors program,String.concat "\n" (Clef.Compiler.Project.ProjectChecker.getErrorMessages program))
        let revision=Clef.Compiler.Project.ProjectChecker.publish program |> Result.defaultWith failwith
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let row=Assert.Single revision.Emission.Boundary.WritableBufferUses.Values
        Assert.Equal(Fidelity.PSG.ValueRange.Bounded(bigint count,bigint count),revision.Emission.Numeric.Values[row.Count].Range)
        Assert.Equal(Fidelity.PSG.ValueRange.Bounded(-1I,bigint count),revision.Emission.Numeric.Values[row.Call].Range)

    [<Fact>]
    member _.``Writable extent observation does not grant captured storage``() =
        let body="    let buffer = Array.zeroCreate 4\n    let requested = buffer.Length\n    let peek () = buffer[0]\n    let result = Test.Native.read 0 buffer (requested - 1)\n    if result < 0 then peek () else requested\n"
        let graph=(ForeignCases.writableVoidApplication ForeignCases.writablePosixSource body).CheckResult.Graph
        match Clef.Compiler.Baker.Recipes.StringByteStorageRecipes.writableApplications graph |> Map.toList |> Assert.Single |> snd with
        | Error failure -> Assert.Contains("complete local write family is not established within 0..255",failure.Reason)
        | Ok _ -> failwith "An extent observation admitted captured writable storage"
        Assert.DoesNotContain(graph.Edges,fun edge->match edge.Role with EdgeRole.BoundaryWritableBufferUse _->true | _->false)

    [<Fact>]
    member _.``Writable unit adapter retains its original four slot profile``() =
        let program=ForeignCases.writableVoidApplication ForeignCases.writableVoidSource "    let buffer = Array.zeroCreate 1024\n    Test.Native.read buffer 1024\n    0\n"
        let graph=program.CheckResult.Graph
        Assert.DoesNotContain(graph.Edges,fun edge->match edge.Role with EdgeRole.BoundaryWritableBufferUse _->true | _->false)
        Assert.Contains(graph.Nodes.Values,fun node->
            match node.Kind with
            | SemanticKind.Obligation info when info.Kind="foreign-writable-buffer-adapter" ->
                match info.Body with
                | ObligationBody.Pending reasons -> List.contains "The first writable adapter requires its original four explicitly unsigned-8 byte slots." reasons
                | _ -> false
            | _ -> false)

    [<Fact>]
    member _.``Writable relational capacity must remain fixed for its own call``() =
        let body="    let seed = Array.zeroCreate 4\n    let first = Test.Native.read 0 seed 3\n    let capacity = if first < 0 then 4 else 5\n    let buffer = Array.zeroCreate capacity\n    Test.Native.read 0 buffer 3\n"
        let graph=(ForeignCases.writableVoidApplication ForeignCases.writablePosixSource body).CheckResult.Graph
        let uses=graph.Edges |> List.choose(fun edge->match edge.Role with EdgeRole.BoundaryWritableBufferUse row->Some row | _->None)
        Assert.Single uses |> ignore
        Assert.Equal(2,Clef.Compiler.Baker.Recipes.StringByteStorageRecipes.writableApplications graph |> Map.count)
        Assert.Contains(graph.Nodes.Values,fun node->
            match node.Kind with
            | SemanticKind.Obligation info when info.Kind="foreign-writable-buffer-adapter" ->
                match info.Body with
                | ObligationBody.Pending reasons -> List.contains "The relational writable adapter requires its exact fixed positive initialized unsigned-8 byte capacity." reasons
                | _ -> false
            | _ -> false)

    [<Theory>]
    [<InlineData("count")>]
    [<InlineData("capacity")>]
    member _.``Writable effect indirect scalar provenance reaches literal and retracts old evidence``(shape:string) =
        let result=ForeignCases.writableApplication "    let n = 3\n    let size = 4\n    let buffer = Array.zeroCreate size\n    let readResult = Test.Native.read 0 buffer n\n    if readResult < 0 then buffer[0] else buffer[0]\n"
        let graph=result.CheckResult.Graph
        let observed=Clef.Compiler.Baker.Recipes.StringByteStorageRecipes.writableApplications graph |> Map.toList |> Assert.Single |> snd
        let application=observed |> Result.defaultWith(fun failure->failwith failure.Reason)
        let expected=if shape="count" then 3L else 4L
        let literal=graph.Nodes.Values |> Seq.filter(fun node->node.IsReachable && (match node.Kind with SemanticKind.Literal(NativeLiteral.Int(value,_))->value=expected && node.Range.File.EndsWith "main.clef" | _->false)) |> Assert.Single
        Assert.Contains(literal.Id,application.Participants)
        let citizen=graph.Nodes.Values |> Seq.filter(fun node->match node.Kind with SemanticKind.Obligation info->info.Kind="foreign-writable-buffer-count" | _->false) |> Assert.Single
        Assert.Contains(literal.Id,ForeignCases.resourceRequirementSupport graph citizen.Id)
        let kind=match literal.Kind with SemanticKind.Literal(NativeLiteral.Int(_,kind))->kind | _->failwith "Expected source literal"
        let changed={graph with Nodes=graph.Nodes.Add(literal.Id,{literal with Kind=SemanticKind.Literal(NativeLiteral.Int(expected+1L,kind))})}
        match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project changed with
        | Error failures -> Assert.Contains(failures,fun failure->failure.Reason.Contains "A source boundary premise, membership, scope, type, range, platform claim or numeric meet changed")
        | Ok _ -> failwith "A changed scalar derivation retained the old writable count account"

    [<Theory>]
    [<InlineData("Integer (Unsigned, 32)")>]
    [<InlineData("Integer (Signed, 8)")>]
    [<InlineData("Pointer 8")>]
    member _.``Writable native descriptor requires exact unsigned byte reference``(element:string) =
        let original=ForeignCases.writableVoidSource
        let changed=original.Replace("Name = \"buffer\"; Type = Integer (Unsigned, 8); PassBy = Reference",
                                     "Name = \"buffer\"; Type = "+element+"; PassBy = Reference")
        Assert.NotEqual<string>(original,changed)
        let result=ForeignCases.writableVoidApplication changed "    let buffer = Array.zeroCreate 4\n    Test.Native.read buffer 3\n    0\n"
        let graph=result.CheckResult.Graph
        let descriptors=ForeignDeclarations.readDescriptors graph
        Assert.Empty descriptors.WritableBuffers
        Assert.Contains(descriptors.Findings,fun finding->finding.Message.Contains "explicit unsigned-8 Reference element contract")
        Assert.DoesNotContain(graph.Edges,fun edge->match edge.Role with EdgeRole.BoundaryWritableBufferUse _->true | _->false)
        if element="Pointer 8" then
            Assert.DoesNotContain(graph.Edges,fun edge->
                match edge.Role with EdgeRole.BoundaryImport import->import.Symbol="native_read" | _->false)
        else
            Assert.Contains(Clef.Compiler.Project.ProjectChecker.getErrorMessages result,fun message->
                message.Contains "Reference arguments require source-settled boundary adapters")

    [<Fact>]
    member _.``Writable native constant count without storage domain stays Pending without a use``() =
        let result=ForeignCases.writableVoidApplication ForeignCases.writableVoidSource "    let buffer = Array.zeroCreate 4\n    let touch (values:int array) = values[0] <- 0\n    touch buffer\n    Test.Native.read buffer 3\n    0\n"
        let graph=result.CheckResult.Graph
        let observed=Clef.Compiler.Baker.Recipes.StringByteStorageRecipes.writableApplications graph |> Map.toList |> Assert.Single |> snd
        match observed with
        | Error failure -> Assert.Contains("complete local write family is not established within 0..255",failure.Reason)
        | Ok _ -> failwith "Unknown storage acquired a writable application account"
        Assert.DoesNotContain(graph.Edges,fun edge->match edge.Role with EdgeRole.BoundaryWritableBufferUse _->true | _->false)
        let claims=graph.Nodes.Values |> Seq.choose(fun node->match node.Kind with SemanticKind.Obligation info->Some info | _->None) |> Seq.toList
        Assert.DoesNotContain(claims,fun info->info.Kind="foreign-writable-buffer-storage")
        Assert.Contains(claims,fun info->
            info.Kind="foreign-writable-buffer-adapter" &&
            (match info.Body with ObligationBody.Pending reasons->reasons |> List.exists(fun reason->reason.Contains "complete local write family is not established within 0..255") | _->false))

    [<Fact>]
    member _.``Writable native direct void profile publishes exact byte allocation count and claims``() =
        let revision=ForeignCases.publishedWritableNative.Value
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let row=Assert.Single revision.Emission.Boundary.WritableBufferUses.Values
        let call=revision.Emission.Boundary.Calls[row.Call]
        Assert.Equal(0,row.Parameter)
        Assert.Equal(1,row.CountParameter)
        Assert.Equal<Fidelity.PSG.NodeId list>([row.Buffer;row.Count],call.Arguments |> List.map _.Actual)
        Assert.Equal(Fidelity.PSG.BoundaryScalar.WritableBytes row.Declaration,call.Arguments.Head.Abi)
        Assert.Equal(None,call.Result)
        Assert.Equal(Fidelity.PSG.ValueRange.Bounded(3I,3I),revision.Emission.Numeric.Values[row.Count].Range)
        match revision.Emission.Memory.Operations[row.Allocation] with
        | Fidelity.PSG.MemoryWitnessOperation.ArrayAllocation allocation ->
            Assert.Equal(1,allocation.ElementBytes)
            Assert.Equal(4I,allocation.MinimumCount)
            Assert.Equal(4I,allocation.MaximumCount)
        | _ -> failwith "The writable buffer lost its original allocation"
        for citizen in [row.CountCoverage;row.StorageCoverage] do
            Assert.True(revision.CurrentClaims.ContainsKey citizen)
            Assert.Contains(revision.CurrentClaims[citizen],revision.Obligations)

    [<Fact>]
    member _.``Writable relational result shares original call with separate current proof citizens``() =
        let revision=ForeignCases.publishedWritableRelational.Value
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let row=Assert.Single revision.Emission.Boundary.WritableBufferUses.Values
        let call=revision.Emission.Boundary.Calls[row.Call]
        Assert.Equal(Some(Fidelity.PSG.BoundaryScalar.Integer(64,true)),call.Result)
        Assert.True(call.ResultAdaptation.IsSome)
        let useRow=revision.Emission.Numeric.ForeignResultUses |> List.filter(fun account->account.Application.Call=row.Call) |> Assert.Single
        Assert.Equal<Fidelity.PSG.NodeId list>(call.Arguments |> List.map _.Actual,useRow.Application.Arguments |> List.map _.Node)
        Assert.Equal(Fidelity.PSG.ValueRange.Bounded(-1I,3I),revision.Emission.Numeric.Values[row.Call].Range)
        Assert.Equal<Fidelity.PSG.ForeignResultProofRole list>([Fidelity.PSG.ForeignResultProofRole.LogicalCoverage;Fidelity.PSG.ForeignResultProofRole.AbiNarrowing],useRow.Claims |> List.map fst)
        for _,citizen in useRow.Claims do
            Assert.Contains(citizen,row.Participants)
            Assert.NotEqual(row.CountCoverage,citizen)
            Assert.NotEqual(row.StorageCoverage,citizen)
            Assert.Contains(revision.CurrentClaims[citizen],revision.Obligations)

    [<Fact>]
    member _.``Writable relational missing behavior retains Pending without call authority``() =
        let source=ForeignCases.writableRelationalSource
        let changed=source.Substring(0,source.IndexOf("let readResultRange",System.StringComparison.Ordinal))
        Assert.NotEqual<string>(source,changed)
        let result=ForeignCases.writableVoidApplication changed ForeignCases.writableRelationalBody
        let graph=result.CheckResult.Graph
        Assert.DoesNotContain(graph.Edges,fun edge->match edge.Role with EdgeRole.BoundaryWritableBufferUse _->true | _->false)
        Assert.Contains(graph.Nodes.Values,fun node->
            match node.Kind with
            | SemanticKind.Obligation info when info.Kind="foreign-writable-buffer-adapter" ->
                match info.Body with ObligationBody.Pending reasons->List.contains "The writable result requires its current declared -1..count behavior hypothesis." reasons | _->false
            | _->false)

    [<Theory>]
    [<InlineData("version")>]
    [<InlineData("descriptor")>]
    [<InlineData("count")>]
    member _.``Writable relational held account withdraws changed current premises``(shape:string) =
        let graph=ForeignCases.writableRelational.Value.CheckResult.Graph
        let expected=if shape="version" then "1" else "native_read"
        let target=
            if shape="count" then
                graph.Nodes.Values |> Seq.filter(fun node->
                    node.IsReachable && node.Range.File.EndsWith "main.clef" &&
                    (match node.Kind with SemanticKind.Literal(NativeLiteral.Int(3L,_))->true | _->false)) |> Assert.Single
            else
                graph.Nodes.Values |> Seq.filter(fun node->
                    node.Range.File.EndsWith "resource.clef" &&
                    (match node.Kind with SemanticKind.Literal(NativeLiteral.String value)->value=expected | _->false)) |> Assert.Single
        let kind=match target.Kind with
                 | SemanticKind.Literal(NativeLiteral.Int(value,kind))->SemanticKind.Literal(NativeLiteral.Int(value+1L,kind))
                 | SemanticKind.Literal(NativeLiteral.String value)->SemanticKind.Literal(NativeLiteral.String(value+"-changed"))
                 | _->failwith "The exact fixture premise is not a literal"
        let changed={graph with Nodes=graph.Nodes.Add(target.Id,{target with Kind=kind})}
        match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project changed with
        | Error failures->Assert.Contains(failures,fun failure->failure.Reason.Contains "A source boundary premise, membership, scope, type, range, platform claim or numeric meet changed")
        | Ok _->failwith "A changed relational premise retained writable call authority"

    [<Theory>]
    [<InlineData("support")>]
    [<InlineData("hypothesis")>]
    [<InlineData("claim")>]
    member _.``Writable relational public replay requires its own current result account``(shape:string) =
        let revision=ForeignCases.publishedWritableRelational.Value
        let boundary=revision.Emission.Boundary
        let key,row=boundary.WritableBufferUses |> Map.toList |> Assert.Single
        let account=revision.Emission.Numeric.ForeignResultUses |> List.filter(fun useRow->useRow.Application.Call=row.Call) |> Assert.Single
        let citizen=account.Claims.Head |> snd
        let changed=
            match shape with
            | "support"->
                let row={row with Participants=row.Participants.Remove citizen}
                {revision with Emission={revision.Emission with Boundary={boundary with WritableBufferUses=boundary.WritableBufferUses.Add(key,row)}}}
            | "hypothesis"->
                {revision with Emission={revision.Emission with Boundary={boundary with ResultHypotheses=[]}}}
            | _->{revision with CurrentClaims=revision.CurrentClaims.Remove citizen}
        Assert.Contains(Fidelity.PSG.Integrity.check changed,fun issue->issue.Part="Emission.Boundary.WritableBufferUses.Account")

    [<Fact>]
    member _.``Writable relational public result requires its selected adaptation``() =
        let revision=ForeignCases.publishedWritableRelational.Value
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let boundary=revision.Emission.Boundary
        let row=Assert.Single boundary.WritableBufferUses.Values
        let call=boundary.Calls[row.Call]
        Assert.True(call.ResultAdaptation.IsSome)
        let changedCall={call with ResultAdaptation=None}
        let changed={revision with Emission={revision.Emission with Boundary={boundary with Calls=boundary.Calls.Add(row.Call,changedCall)}}}
        let issues=Fidelity.PSG.Integrity.check changed
        Assert.Contains(issues,fun issue->issue.Node=Some row.Call && issue.Part="Emission.Boundary.Calls.ResultAdaptation" && issue.Reason="The boundary result adaptation differs from its exact current source numeric meet.")

    [<Fact>]
    member _.``Writable relational public result refuses ambiguous current adaptations``() =
        let revision=ForeignCases.publishedWritableRelational.Value
        let row=Assert.Single revision.Emission.Boundary.WritableBufferUses.Values
        let call=revision.Emission.Boundary.Calls[row.Call]
        let current=revision.Codata.Meets[call.Site]
        let original=current |> List.filter(fun meet->meet.Operand=call.Site) |> Assert.Single
        Assert.Equal(Some original,call.ResultAdaptation)
        Assert.Equal(64,original.From)
        Assert.Equal(32,original.To)
        let ambiguous=current@[{original with To=16}]
        Assert.Equal(2,ambiguous |> List.filter(fun meet->meet.Operand=call.Site) |> List.distinct |> List.length)
        let changed={revision with Codata={revision.Codata with Meets=revision.Codata.Meets.Add(call.Site,ambiguous)}}
        Assert.Contains(Fidelity.PSG.Integrity.check changed,fun issue->issue.Node=Some call.Site && issue.Part="Emission.Boundary.Calls.ResultAdaptation")

    [<Fact>]
    member _.``Writable POSIX result retains the complete fd buffer count call and separate current claims``() =
        let revision=ForeignCases.publishedWritablePosix.Value
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let row=Assert.Single revision.Emission.Boundary.WritableBufferUses.Values
        let call=revision.Emission.Boundary.Calls[row.Call]
        let imported=revision.Emission.Boundary.Imports[call.Import]
        Assert.Equal(1,row.Parameter)
        Assert.Equal(2,row.CountParameter)
        Assert.Equal<Fidelity.PSG.BoundaryScalar list>([Fidelity.PSG.BoundaryScalar.Integer(32,true);Fidelity.PSG.BoundaryScalar.WritableBytes row.Declaration;Fidelity.PSG.BoundaryScalar.Integer(64,false)],call.Arguments |> List.map _.Abi)
        Assert.Equal(Some(Fidelity.PSG.BoundaryScalar.Integer(64,true)),call.Result)
        Assert.Equal<(Fidelity.PSG.NodeId*Fidelity.PSG.BoundaryScalar) list>(imported.Parameters,call.Arguments |> List.map(fun argument->argument.Formal,argument.Abi))
        let resultUse=revision.Emission.Numeric.ForeignResultUses |> List.filter(fun account->account.Application.Call=row.Call) |> Assert.Single
        Assert.Equal<Fidelity.PSG.NodeId list>(call.Arguments |> List.map _.Actual,resultUse.Application.Arguments |> List.map _.Node)
        Assert.Equal(Fidelity.PSG.ForeignResultBound.Argument 2,resultUse.Application.Hypothesis.Value.Upper)
        Assert.Equal(Fidelity.PSG.ValueRange.Bounded(-1I,3I),revision.Emission.Numeric.Values[row.Call].Range)
        let fd,count=call.Arguments[0],call.Arguments[2]
        Assert.Equal(Fidelity.PSG.ValueRange.Bounded(0I,0I),revision.Emission.Numeric.Values[fd.Actual].Range)
        for argument,target in [fd,32;count,64] do
            let meet=revision.Codata.Meets[call.Site] |> List.filter(fun meet->meet.Operand=argument.Actual) |> List.distinct |> Assert.Single
            Assert.Equal(Some meet,argument.Adaptation)
            Assert.Equal(call.Site,meet.Consumer)
            Assert.Equal(target,meet.To)
        Assert.True(call.ResultAdaptation.IsSome)
        let citizens=row.CountCoverage::row.StorageCoverage::(resultUse.Claims |> List.map snd)
        Assert.Equal(4,citizens |> List.distinct |> List.length)
        Assert.Equal<Fidelity.PSG.ForeignResultProofRole list>([Fidelity.PSG.ForeignResultProofRole.LogicalCoverage;Fidelity.PSG.ForeignResultProofRole.AbiNarrowing],resultUse.Claims |> List.map fst)
        for citizen in citizens do
            Assert.Contains(citizen,row.Participants)
            Assert.Contains(revision.CurrentClaims[citizen],revision.Obligations)
        Assert.Contains(fd.Actual,row.Participants)
        let limits:Fidelity.PSG.Binary.Limits={MaxBytes=16000000;MaxCollectionLength=100000;MaxDepth=128;MaxStringBytes=1000000;MaxBigIntegerBytes=4096;MaxValues=4000000}
        let copy=Fidelity.PSG.Binary.encode limits revision |> Result.defaultWith(fun error->failwithf "%A" error)
                 |> Fidelity.PSG.Binary.decode limits |> Result.defaultWith(fun error->failwithf "%A" error)
        Assert.Empty(Fidelity.PSG.Integrity.check copy)
        Assert.Equal(revision.Emission.Boundary,copy.Emission.Boundary)

    [<Theory>]
    [<InlineData("Integer (Unsigned, 32)")>]
    [<InlineData("Integer (Signed, 64)")>]
    member _.``Writable POSIX fd requires its exact signed32 ABI profile``(abi:string) =
        let source=ForeignCases.writablePosixSource.Replace("Name = \"fd\"; Type = Integer (Signed, 32)","Name = \"fd\"; Type = "+abi)
        Assert.NotEqual<string>(ForeignCases.writablePosixSource,source)
        let result=ForeignCases.writableVoidApplication source ForeignCases.writablePosixBody
        Assert.DoesNotContain(result.CheckResult.Graph.Edges,fun edge->match edge.Role with EdgeRole.BoundaryCall _->true | _->false)
        Assert.Contains(Clef.Compiler.Project.ProjectChecker.getErrorMessages result,fun message->message.Contains "or signed-32 fd0/buffer1/count2 unsigned-64 with signed-64 result.")

    [<Theory>]
    [<InlineData("missing")>]
    [<InlineData("upper")>]
    [<InlineData("lower")>]
    [<InlineData("zero")>]
    member _.``Writable POSIX result requires its current declared count relation``(shape:string) =
        let source,body,reason=
            match shape with
            | "missing" ->
                let source=ForeignCases.writablePosixSource
                source.Substring(0,source.IndexOf("let readResultRange",System.StringComparison.Ordinal)),ForeignCases.writablePosixBody,"The writable result requires its current declared -1..count behavior hypothesis."
            | "zero" -> ForeignCases.writablePosixSource,"    let buffer = Array.zeroCreate 4\n    Test.Native.read 0 buffer 0\n","The relational writable adapter requires one exact positive count within its initialized byte capacity."
            | _ ->
                let before,after=if shape="upper" then "Upper = Argument 2","Upper = Argument 0" else "Lower = Constant (-1)","Lower = Constant 0"
                let body=if shape="upper" then ForeignCases.writablePosixBody.Replace("Test.Native.read 0 buffer 3","Test.Native.read 4 buffer 3") else ForeignCases.writablePosixBody
                ForeignCases.writablePosixSource.Replace(before,after),body,"The writable result hypothesis or ordered actuals differ from this call's exact -1..count relation."
        let graph=(ForeignCases.writableVoidApplication source body).CheckResult.Graph
        Assert.DoesNotContain(graph.Edges,fun edge->match edge.Role with EdgeRole.BoundaryWritableBufferUse _->true | _->false)
        Assert.Contains(graph.Nodes.Values,fun node->
            match node.Kind with
            | SemanticKind.Obligation info when info.Kind="foreign-writable-buffer-adapter" ->
                match info.Body with ObligationBody.Pending reasons->List.contains reason reasons | _->false
            | _->false)

    [<Fact>]
    member _.``Writable POSIX held account withdraws a changed fd premise``() =
        let graph=ForeignCases.writablePosix.Value.CheckResult.Graph
        let application=Clef.Compiler.Baker.Recipes.StringByteStorageRecipes.writableApplications graph |> Map.toList |> Assert.Single |> snd |> Result.defaultWith(fun failure->failwith failure.Reason)
        let fd=graph.Nodes[application.Arguments.Head]
        let kind=match fd.Kind with SemanticKind.Literal(NativeLiteral.Int(_,kind))->kind | _->failwith "Expected the fd0 actual"
        let changed={graph with Nodes=graph.Nodes.Add(fd.Id,{fd with Kind=SemanticKind.Literal(NativeLiteral.Int(1L,kind))})}
        match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project changed with
        | Error failures->Assert.Contains(failures,fun failure->failure.Reason.Contains "A source boundary premise, membership, scope, type, range, platform claim or numeric meet changed")
        | Ok _->failwith "A changed fd retained the held writable boundary account"

    [<Theory>]
    [<InlineData("missing")>]
    [<InlineData("substituted")>]
    [<InlineData("ambiguous")>]
    member _.``Writable POSIX public fd adaptation replays its own current scalar meet``(shape:string) =
        let revision=ForeignCases.publishedWritablePosix.Value
        let boundary=revision.Emission.Boundary
        let row=Assert.Single boundary.WritableBufferUses.Values
        let call=boundary.Calls[row.Call]
        let fd=call.Arguments.Head
        Assert.True(fd.Adaptation.IsSome)
        let changed=
            if shape="ambiguous" then
                let current=revision.Codata.Meets[call.Site]
                let original=fd.Adaptation.Value
                let ambiguous=current@[{original with To=64}]
                Assert.Equal(2,ambiguous |> List.filter(fun meet->meet.Operand=fd.Actual) |> List.distinct |> List.length)
                {revision with Codata={revision.Codata with Meets=revision.Codata.Meets.Add(call.Site,ambiguous)}}
            else
                let adaptation=if shape="missing" then None else call.Arguments[2].Adaptation
                let changedCall={call with Arguments={fd with Adaptation=adaptation}::call.Arguments.Tail}
                {revision with Emission={revision.Emission with Boundary={boundary with Calls=boundary.Calls.Add(call.Site,changedCall)}}}
        Assert.Contains(Fidelity.PSG.Integrity.check changed,fun issue->issue.Node=Some call.Site && issue.Part="Emission.Boundary.Calls.Arguments.Adaptation" && issue.Reason="The boundary argument adaptation differs from its exact current source numeric meet.")

    [<Theory>]
    [<InlineData("order")>]
    [<InlineData("arity")>]
    [<InlineData("formal")>]
    [<InlineData("abi")>]
    [<InlineData("support")>]
    [<InlineData("claim")>]
    [<InlineData("hypothesis")>]
    member _.``Writable POSIX public replay requires the exact three actual profile and result account``(shape:string) =
        let revision=ForeignCases.publishedWritablePosix.Value
        let boundary=revision.Emission.Boundary
        let key,row=boundary.WritableBufferUses |> Map.toList |> Assert.Single
        let call=boundary.Calls[row.Call]
        let fd,count=call.Arguments[0],call.Arguments[2]
        let resultUse=revision.Emission.Numeric.ForeignResultUses |> List.filter(fun account->account.Application.Call=row.Call) |> Assert.Single
        let changed=
            match shape with
            | "support" -> {revision with Emission={revision.Emission with Boundary={boundary with WritableBufferUses=boundary.WritableBufferUses.Add(key,{row with Participants=row.Participants.Remove fd.Actual})}}}
            | "claim" -> {revision with CurrentClaims=revision.CurrentClaims.Remove(snd resultUse.Claims.Head)}
            | "hypothesis" -> {revision with Emission={revision.Emission with Boundary={boundary with ResultHypotheses=[]}}}
            | _ ->
                let arguments=match shape with
                              | "order" -> [{fd with Actual=count.Actual};call.Arguments[1];{count with Actual=fd.Actual}]
                              | "arity" -> call.Arguments.Tail
                              | "formal" -> {fd with Formal=count.Formal}::call.Arguments.Tail
                              | _ -> {fd with Abi=Fidelity.PSG.BoundaryScalar.Integer(64,true)}::call.Arguments.Tail
                let imported=boundary.Imports[call.Import]
                let imports=if shape="abi" then boundary.Imports.Add(imported.Identity,{imported with Parameters=(fd.Formal,Fidelity.PSG.BoundaryScalar.Integer(64,true))::imported.Parameters.Tail}) else boundary.Imports
                {revision with Emission={revision.Emission with Boundary={boundary with Imports=imports;Calls=boundary.Calls.Add(call.Site,{call with Arguments=arguments})}}}
        Assert.Contains(Fidelity.PSG.Integrity.check changed,fun issue->issue.Part="Emission.Boundary.WritableBufferUses.Account")

    [<Fact>]
    member _.``Writable relational equal arguments retain distinct original calls and result claims``() =
        let result=ForeignCases.writableVoidApplication ForeignCases.writableRelationalSource "    let buffer = Array.zeroCreate 4\n    let first = Test.Native.read buffer 3\n    let second = Test.Native.read buffer 3\n    if first < 0 then first elif second = 0 then 0 else second\n"
        Assert.False(Clef.Compiler.Project.ProjectChecker.hasErrors result,String.concat "\n" (Clef.Compiler.Project.ProjectChecker.getErrorMessages result))
        let revision=Clef.Compiler.Project.ProjectChecker.publish result |> Result.defaultWith failwith
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let uses=revision.Emission.Boundary.WritableBufferUses.Values |> Seq.toList
        Assert.Equal(2,uses.Length)
        Assert.NotEqual(uses[0].Call,uses[1].Call)
        let accounts=uses |> List.map(fun row->revision.Emission.Numeric.ForeignResultUses |> List.filter(fun account->account.Application.Call=row.Call) |> Assert.Single)
        let citizens=accounts |> List.collect(fun account->account.Claims |> List.map snd)
        Assert.Equal(4,citizens |> List.distinct |> List.length)
        Assert.Equal(uses[0].Allocation,uses[1].Allocation)

    [<Theory>]
    [<InlineData("count","Account")>]
    [<InlineData("allocation","Storage")>]
    [<InlineData("format","Storage")>]
    [<InlineData("claim","Claims")>]
    [<InlineData("withdrawal","Account")>]
    member _.``Writable native public replay refuses substituted per use incidence``(shape:string,part:string) =
        let revision=ForeignCases.publishedWritableNative.Value
        let boundary=revision.Emission.Boundary
        let key,row=boundary.WritableBufferUses |> Map.toList |> Assert.Single
        let changedRow=
            match shape with
            | "count" -> {row with Count=row.Capacity}
            | "allocation" -> {row with Allocation=row.Buffer}
            | "format" -> {row with ByteFormat=row.Declaration}
            | "claim" -> {row with CountCoverage=row.StorageCoverage}
            | _ -> row
        let uses=if shape="withdrawal" then Map.empty else boundary.WritableBufferUses.Add(key,changedRow)
        let changed={revision with Emission={revision.Emission with Boundary={boundary with WritableBufferUses=uses}}}
        let expected=if shape="withdrawal" then "Emission.Boundary.Calls.WritableBuffer" else "Emission.Boundary.WritableBufferUses."+part
        Assert.Contains(Fidelity.PSG.Integrity.check changed,fun issue->issue.Part=expected)

    [<Theory>]
    [<InlineData("hypothesis")>]
    [<InlineData("ordinal")>]
    member _.``Writable native lifetime requires exact current no retain hypothesis and actual ordinal``(shape:string) =
        let graph=ForeignCases.writableNative.Value.CheckResult.Graph
        let application=Clef.Compiler.Baker.Recipes.StringByteStorageRecipes.writableApplications graph |> Map.toList |> Assert.Single |> snd |> Result.defaultWith(fun failure->failwith failure.Reason)
        let _,closed,_=Clef.Compiler.Baker.Recipes.MemoryAccessRecipes.arrayUses graph application.Allocation
        Assert.True(closed)
        let changed=
            if shape="hypothesis" then
                let quote=graph.Nodes[application.Declaration.Quote]
                {graph with Nodes=graph.Nodes.Add(quote.Id,{quote with Kind=SemanticKind.Literal NativeLiteral.Unit;Children=[]})}
            else
                let site=graph.Nodes[application.Site]
                let arguments=List.rev application.Arguments
                {graph with Nodes=graph.Nodes.Add(site.Id,{site with Kind=SemanticKind.Application(application.Callee,arguments);Children=application.Callee::arguments})}
        let _,retained,_=Clef.Compiler.Baker.Recipes.MemoryAccessRecipes.arrayUses changed application.Allocation
        Assert.False(retained)

    [<Fact>]
    member _.``Resource application retains exact finite conversion and cleanup models without discharging them``() =
        let result = ForeignCases.resourceApplication "    match Foreign.mallocFirst 8 with\n    | Some handle -> Foreign.freeFirst handle; 0\n    | None -> 0\n"
        let graph = result.CheckResult.Graph
        let requirements = ForeignCases.resourceRequirements graph
        Assert.Equal(2,requirements.Length)
        Assert.Equal<string list>(["foreign-resource-cleanup";"foreign-resource-nullable-conversion"],requirements |> List.map(fun (_,info) -> info.Kind) |> List.sort)
        let resource = (ForeignDeclarations.readDescriptors graph).Resources |> List.find(fun row -> row.Contract.Hypothesis.Identity="fixture-owned-First")
        let selected = (ForeignDeclarations.read graph).Platform |> Option.get
        for id,info in requirements do
            Assert.Equal("QF_LIA",info.Logic)
            match info.Body with
            | ObligationBody.ResourceConversion model ->
                Assert.Equal(resource.Quote,model.Declaration)
                Assert.Equal(resource.PointerBits,model.SelectedPointerBits)
                Assert.Equal<bool list>([false;true],model.Arms |> List.map _.NativeNonNull)
                Assert.Equal(None,model.Arms.Head.PayloadOrigin)
                Assert.Equal(Some model.Acquisition,model.Arms.Tail.Head.PayloadOrigin)
            | ObligationBody.ResourceCleanup model ->
                Assert.Equal(resource.Release.Binding,model.Release)
                let conversionId,conversion = requirements |> List.pick(fun (id,info)->
                    match info.Body with ObligationBody.ResourceConversion value -> Some(id,value) | _ -> None)
                Assert.Equal(conversionId,model.Conversion)
                Assert.Equal(conversion,model.ConversionModel)
                Assert.NotEmpty(model.Relations)
                Assert.Contains(model.Points,fun point->point.Port=EvaluationPort.FailureExit)
                Assert.Contains(model.Points,fun point->point.Port=EvaluationPort.Exit && point.Event=Some ResourceFlowEvent.Acquisition)
                let sharedSubject = model.Cases |> List.groupBy _.Subject |> List.find(fun (_,cases)->cases.Length>1) |> fst
                let contexts = model.Points |> List.filter(fun point->point.Site=sharedSubject && point.Port=EvaluationPort.Entry) |> List.map _.Context |> List.distinct
                Assert.True(contexts.Length>1,"Shared Option subjects must retain their distinct operand-demand contexts.")
            | other -> failwithf "The finite resource account was not authored: %A" other
            Assert.Contains(resource.Contract.Hypothesis.Identity,String.concat "\n" info.Refs)
            Assert.Contains(resource.Contract.Hypothesis.Version,String.concat "\n" info.Refs)
            Assert.Contains(resource.Contract.Hypothesis.Source,String.concat "\n" info.Refs)
            let support = ForeignCases.resourceRequirementSupport graph id
            for required in [resource.Quote;resource.Acquisition.Binding;resource.Release.Binding;resource.ReleaseFormal;selected.Node;selected.Core.Value.Node] do
                Assert.Contains(required,support)
        let dispatch = Clef.Compiler.Baker.Recipes.ProofDispatchRecipes.materialize graph |> Result.defaultWith(fun errors -> failwithf "%A" errors)
        let ledger = Clef.Compiler.Nanopass.ObligationDischarge.ledgerJson (dispatch.Required |> List.map snd)
        for _,info in requirements do
            Assert.Contains(info.Kind,ledger)
            let row = Clef.Compiler.Nanopass.ObligationDischarge.ledgerJson [info]
            Assert.DoesNotContain("\"state\": \"pending\"",row)
        match dispatch.Query with
        | Error unavailable -> failwithf "A finite resource model was not materialized: %A" unavailable
        | Ok query -> for _,info in requirements do Assert.Contains(info.Id,query)
        Assert.True(Clef.Compiler.Baker.Ingredients.NumericValues.rangeContextCurrent graph graph.RangeContextFacts.Value)
        let resources=(ForeignDeclarations.readDescriptors graph).Resources
        let foreignImplementations=resources |> List.collect(fun row->[List.last row.Acquisition.Path;List.last row.Release.Path]) |> Set.ofList
        Assert.DoesNotContain(graph.Codata.Value.CallableContracts.Values,fun contract ->
            contract.Kind=CallableKind.OrdinaryFlatClosure &&
            (contract.Participants |> List.exists(fun participant->participant.Role=ParticipantRole.CallableImplementation && foreignImplementations.Contains participant.Node)))
        match Clef.Compiler.Project.ProjectChecker.publish result with
        | Error reason -> failwithf "A complete source resource model could not publish: %s" reason
        | Ok revision -> Assert.Empty(Fidelity.PSG.Integrity.check revision)

    [<Fact>]
    member _.``Resource handle tuple containment refuses before cleanup authority``() =
        let result=ForeignCases.resourceApplication "    match Foreign.mallocFirst 8 with\n    | Some handle ->\n        let boxed = (handle, 1)\n        let (_, value) = boxed\n        Foreign.freeFirst handle\n        value\n    | None -> 0\n"
        Assert.True(Clef.Compiler.Project.ProjectChecker.hasErrors result)
        Assert.Contains(Clef.Compiler.Project.ProjectChecker.getErrorMessages result,fun message->
            message.Contains("A resource Option or handle cannot enter a tuple, record, collection, storage, or unsupported value consumer.",System.StringComparison.Ordinal))

    [<Fact>]
    member _.``Ordinary handle callable is refused by local resource flow rather than foreign stub identity``() =
        let result=ForeignCases.resourceApplication "    let ordinary handle = 0\n    match Foreign.mallocFirst 8 with\n    | Some handle -> ordinary handle\n    | None -> 0\n"
        Assert.True(Clef.Compiler.Project.ProjectChecker.hasErrors result)
        Assert.Contains(Clef.Compiler.Project.ProjectChecker.getErrorMessages result,fun message->
            message.Contains("Interprocedural resource use is outside the admitted local profile.",System.StringComparison.Ordinal))

    [<Theory>]
    [<InlineData("mallocFirst")>]
    [<InlineData("mallocSecond")>]
    member _.``Resource application requirements keep equal actual calls and same symbol twins independent``(second:string) =
        let body =
            "    match Foreign.mallocFirst 8 with\n"
            + "    | Some first ->\n"
            + "        match Foreign."+second+" 8 with\n"
            + "        | Some second -> Foreign.freeFirst first; 0\n"
            + "        | None -> Foreign.freeFirst first; 0\n"
            + "    | None -> 0\n"
        let graph = (ForeignCases.resourceApplication body).CheckResult.Graph
        let requirements = ForeignCases.resourceRequirements graph
        Assert.Equal(4,requirements.Length)
        Assert.Equal(4,requirements |> List.map(fun (_,info) -> info.Id) |> List.distinct |> List.length)
        let declarations = (ForeignDeclarations.readDescriptors graph).Resources
        let sites = requirements |> List.map(fun (id,_) ->
            ForeignCases.resourceRequirementSupport graph id |> List.filter(fun site ->
                match graph.Nodes[site].Kind with SemanticKind.Application _ -> true | _ -> false) |> List.head)
        Assert.Equal(2,sites |> List.distinct |> List.length)
        let supportedQuotes =
            requirements |> List.map(fun (id,_) ->
                let support = ForeignCases.resourceRequirementSupport graph id
                let quotes = declarations |> List.filter(fun declaration -> List.contains declaration.Quote support)
                Assert.Single quotes |> ignore
                let quote = quotes.Head
                Assert.Contains(quote.Release.Binding,support)
                Assert.Contains(quote.ReleaseFormal,support)
                quote.Quote) |> Set.ofList
        Assert.Equal((if second="mallocFirst" then 1 else 2),supportedQuotes.Count)

    [<Fact>]
    member _.``Resource application requirements renew claim roles without retaining old obligation nodes``() =
        let graph = (ForeignCases.resourceApplication "    match Foreign.mallocFirst 8 with\n    | Some handle -> Foreign.freeFirst handle; 0\n    | None -> 0\n").CheckResult.Graph
        let original = ForeignCases.resourceRequirements graph
        let renewed = Clef.Compiler.Nanopass.BoundarySettlement.normalize graph
        let current = ForeignCases.resourceRequirements renewed
        Assert.Equal<string list>(original |> List.map(fun (_,info) -> info.Id) |> List.sort,current |> List.map(fun (_,info) -> info.Id) |> List.sort)
        Assert.Equal(2,current.Length)
        for id,_ in original do Assert.False(renewed.Nodes.ContainsKey id)

    [<Fact>]
    member _.``Resource application requirements invalidate changed quote target and repeated actual incidence``() =
        let graph = (ForeignCases.resourceApplication "    match Foreign.mallocFirst 8 with\n    | Some handle -> Foreign.freeFirst handle; 0\n    | None -> 0\n").CheckResult.Graph
        let declaration = (ForeignDeclarations.readDescriptors graph).Resources |> List.find(fun row -> row.Contract.Hypothesis.Identity="fixture-owned-First")
        let _,fields = ForeignDeclarations.recordOf graph declaration.Node |> Option.get
        let _,hypothesis = ForeignDeclarations.field "Hypothesis" fields |> Option.bind(ForeignDeclarations.recordOf graph) |> Option.get
        let literal,_ = ForeignDeclarations.field "Version" hypothesis |> Option.bind(ForeignDeclarations.valuePath graph) |> Option.get
        let site =
            let id,_ = ForeignCases.resourceRequirements graph |> List.head
            ForeignCases.resourceRequirementSupport graph id |> List.find(fun id ->
                match graph.Nodes[id].Kind with SemanticKind.Application _ -> true | _ -> false)
        let application = graph.Nodes[site]
        let repeated =
            match application.Kind with
            | SemanticKind.Application(callee,[actual]) -> {application with Kind=SemanticKind.Application(callee,[actual;actual]);Children=[callee;actual;actual]}
            | other -> failwithf "Unexpected source acquisition: %A" other
        let changed =
            [ {graph with Nodes=graph.Nodes.Add(literal.Id,{literal with Kind=SemanticKind.Literal(NativeLiteral.String "changed-version")})}
              {graph with Nodes=graph.Nodes.Remove declaration.Quote}
              {graph with Nodes=graph.Nodes.Add(site,repeated)}
              {graph with Platform=graph.Platform |> Option.map(fun platform -> {platform with PlatformArchitecture=Some "changed-target"})} ]
        for current in changed do
            match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project current with
            | Error failures -> Assert.Contains(failures,fun failure -> failure.Reason="BoundaryEmission: A source boundary premise, membership, scope, type, range, platform claim or numeric meet changed; Baker must settle the new source graph.")
            | Ok _ -> failwith "Changed exact resource support retained an old boundary account."
        let renewed = Clef.Compiler.Nanopass.BoundarySettlement.normalize changed.Head
        Assert.Equal<string list>(ForeignCases.resourceRequirements graph |> List.map(fun (_,info) -> info.Id) |> List.sort,
                                  ForeignCases.resourceRequirements renewed |> List.map(fun (_,info) -> info.Id) |> List.sort)

    [<Fact>]
    member _.``Resource declaration replay separates actual qualified scopes with identical module leaves``() =
        let source ns =
            let body = ForeignCases.resourceSource.Split('\n') |> Array.skip 1
            "namespace " + ns + "\n\nmodule Foreign =\n"
            + (body |> Array.map(fun line -> "    " + line) |> String.concat "\n")
                  .Replace("Binding=\"Foreign.", "Binding=\"" + ns + ".Foreign.")
        let graph = ForeignCases.resourceGraphFor [source "Alpha","alpha.clef";source "Beta","beta.clef"]
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph
            |> Result.defaultWith(fun errors -> failwithf "%A" errors)
        let defects = Fidelity.PSG.Integrity.check revision
        Assert.True(defects.IsEmpty,Fidelity.PSG.Integrity.describe defects)
        let declarations = (ForeignDeclarations.readDescriptors graph).Resources
        Assert.Equal(4,declarations.Length)
        let first = declarations |> List.find(fun row -> row.Contract.Resource = BAREWire.Descriptors.ResourceProtocol.OwnedNullableReturn {Binding="Alpha.Foreign.freeFirst";Parameter=0})
        let second = declarations |> List.find(fun row -> row.Contract.Resource = BAREWire.Descriptors.ResourceProtocol.OwnedNullableReturn {Binding="Beta.Foreign.freeFirst";Parameter=0})
        for declaration in [first;second] do
            let releaseName = ForeignDeclarations.qualifiedExportName graph graph.Nodes[declaration.Release.Binding] |> Option.get
            let row = revision.Emission.Boundary.ResourceDeclarations[Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId declaration.Quote]
            let scope = row.DeclarationFacts[row.Release].Parent |> Option.get
            let header = revision.SourceReadings.ContextHeaders[scope]
            Assert.Equal(releaseName,header.Name+".freeFirst")
            Assert.Contains(header.Name,["Alpha.Foreign";"Beta.Foreign"])
        let boundary = revision.Emission.Boundary
        let first = boundary.ResourceDeclarations[Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId first.Quote]
        let second = boundary.ResourceDeclarations[Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId second.Quote]
        Assert.Equal(first.HandleType,second.HandleType)
        let facts = Map.fold(fun current id value -> Map.add id value current) first.DeclarationFacts second.DeclarationFacts
        let swapped = {first with Release=second.Release;ReleaseBody=second.ReleaseBody;ReleaseDescriptor=second.ReleaseDescriptor;ReleaseFormal=second.ReleaseFormal;DeclarationFacts=facts;Participants=facts.Keys |> Set.ofSeq}
        let changed = {revision with Emission={revision.Emission with Boundary={boundary with ResourceDeclarations=boundary.ResourceDeclarations.Add(first.Identity,swapped)}}}
        Assert.Contains(Fidelity.PSG.Integrity.check changed,fun issue ->
            issue.Part="Emission.Boundary.ResourceDeclarations.Context" &&
            issue.Reason="The resource declaration lacks its exact current module context or qualified release binding.")

    [<Fact>]
    member _.``Resource declaration replay retains exact metadata contexts and twins without executable bodies``() =
        let revision = ForeignCases.publishedResources.Value
        let rows = revision.Emission.Boundary.ResourceDeclarations.Values |> Seq.toList
        Assert.Equal(2, rows.Length)
        Assert.Equal(2, rows |> List.map _.Acquisition |> List.distinct |> List.length)
        Assert.Equal(2, rows |> List.map _.Release |> List.distinct |> List.length)
        Assert.True(rows[0].HandleType=rows[1].HandleType && rows[0].ResultType=rows[1].ResultType)
        for row in rows do
            for declaration in [row.Acquisition;row.Release] do
                Assert.False(revision.Nodes.ContainsKey declaration)
                let scope = row.DeclarationFacts[declaration].Parent |> Option.get
                let header = revision.SourceReadings.ContextHeaders[scope]
                Assert.Equal("Foreign", header.Name)
                let port = header.Ports[Fidelity.PSG.OccurrencePort.ModuleDeclaration]
                Assert.True(port.Extent>0 && not(System.String.IsNullOrWhiteSpace port.Stamp))
                Assert.DoesNotContain(declaration, port.Positions.Values)
        let defects = Fidelity.PSG.Integrity.check revision
        Assert.True(defects.IsEmpty, Fidelity.PSG.Integrity.describe defects)
        let limits: Fidelity.PSG.Binary.Limits =
            { MaxBytes=8*1024*1024;MaxCollectionLength=10000;MaxDepth=128;MaxStringBytes=1024*1024;MaxBigIntegerBytes=4096;MaxValues=2000000 }
        let bytes = Fidelity.PSG.Binary.encode limits revision |> Result.defaultWith (fun error -> failwithf "%A" error)
        let copy = Fidelity.PSG.Binary.decode limits bytes |> Result.defaultWith (fun error -> failwithf "%A" error)
        Assert.True(copy.Emission.Boundary.ResourceDeclarations=revision.Emission.Boundary.ResourceDeclarations)

    [<Theory>]
    [<InlineData("missing-wrapper", "Declaration")>]
    [<InlineData("wrong-sibling", "Declaration")>]
    [<InlineData("wrong-formal", "Incidence")>]
    [<InlineData("wrong-acquisition-body", "Incidence")>]
    [<InlineData("wrong-release-body", "Incidence")>]
    [<InlineData("missing-context", "Context")>]
    [<InlineData("same-leaf-wrong-module", "Context")>]
    member _.``Resource declaration replay refuses same-typed substituted identities and missing support``(shape:string, part:string) =
        let revision = ForeignCases.publishedResources.Value
        let boundary = revision.Emission.Boundary
        let first,second = match boundary.ResourceDeclarations.Values |> Seq.toList with [first;second] -> first,second | _ -> failwith "Expected resource twins."
        let union = Map.fold (fun all id fact -> Map.add id fact all) first.DeclarationFacts second.DeclarationFacts
        let supported (row:Fidelity.PSG.BoundaryResourceDeclaration) facts = {row with DeclarationFacts=facts;Participants=facts.Keys |> Set.ofSeq}
        let replace row = {revision with Emission={revision.Emission with Boundary={boundary with ResourceDeclarations=boundary.ResourceDeclarations.Add(first.Identity,row)}}}
        let changed =
            match shape with
            | "missing-wrapper" -> supported first (first.DeclarationFacts.Remove(first.DeclarationFacts[first.ReleaseDescriptor].Parent |> Option.get)) |> replace
            | "wrong-sibling" -> supported {first with Acquisition=second.Acquisition;AcquisitionBody=second.AcquisitionBody;AcquisitionDescriptor=second.AcquisitionDescriptor;AcquisitionType=second.AcquisitionType} union |> replace
            | "wrong-formal" -> supported {first with ReleaseFormal=second.ReleaseFormal} union |> replace
            | "wrong-acquisition-body" -> supported {first with AcquisitionBody=second.AcquisitionBody} union |> replace
            | "wrong-release-body" -> supported {first with ReleaseBody=second.ReleaseBody} union |> replace
            | "missing-context" ->
                let scope=first.DeclarationFacts[first.Release].Parent |> Option.get
                {revision with SourceReadings={revision.SourceReadings with ContextHeaders=revision.SourceReadings.ContextHeaders.Remove scope}}
            | "same-leaf-wrong-module" ->
                let scope=first.DeclarationFacts[first.Release].Parent |> Option.get
                let header=revision.SourceReadings.ContextHeaders[scope]
                {revision with SourceReadings={revision.SourceReadings with ContextHeaders=revision.SourceReadings.ContextHeaders.Add(scope,{header with Name="Other.Namespace"})}}
            | _ -> failwithf "Unknown resource shape %s" shape
        let reason =
            match part with
            | "Declaration" -> "The resource account differs from its exact sibling acquisition or release declaration."
            | "Incidence" -> "The resource declaration differs from its exact original acquisition/release body or ordinal-zero release formal."
            | "Context" -> "The resource declaration lacks its exact current module context or qualified release binding."
            | _ -> failwithf "Unknown resource refusal part %s" part
        Assert.Contains(Fidelity.PSG.Integrity.check changed, fun issue -> issue.Part="Emission.Boundary.ResourceDeclarations."+part && issue.Reason=reason)

    [<Fact>]
    member _.``Resource declaration replay refuses changed hypothesis and withdrawn source account``() =
        let graph = ForeignCases.resourceGraph ()
        let declaration = (ForeignDeclarations.readDescriptors graph).Resources.Head
        let _,fields = ForeignDeclarations.recordOf graph declaration.Node |> Option.get
        let _,hypothesis = ForeignDeclarations.field "Hypothesis" fields |> Option.bind (ForeignDeclarations.recordOf graph) |> Option.get
        let literal,_ = ForeignDeclarations.field "Version" hypothesis |> Option.bind (ForeignDeclarations.valuePath graph) |> Option.get
        let changed = {graph with Nodes=graph.Nodes.Add(literal.Id,{literal with Kind=SemanticKind.Literal(NativeLiteral.String "changed-after-issue")})}
        let expected = "BoundaryEmission: A source boundary premise, membership, scope, type, range, platform claim or numeric meet changed; Baker must settle the new source graph."
        match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project changed with
        | Error failures -> Assert.Contains(failures, fun failure -> failure.Reason=expected)
        | Ok _ -> failwith "Changed resource hypothesis retained an old account."
        let withdrawn =
            { graph with
                Edges =
                    graph.Edges
                    |> List.filter(fun edge ->
                        match edge.Role with
                        | EdgeRole.BoundaryResourceDeclaration row when row.Identity=declaration.Quote -> false
                        | _ -> true) }
        match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project withdrawn with
        | Error failures -> Assert.Contains(failures, fun failure -> failure.Reason="BoundaryEmission: The source resource declaration account was withdrawn or duplicated.")
        | Ok _ -> failwith "Withdrawing a resource declaration retained an old account."

    [<Fact>]
    member _.``Published conditional foreign result keeps metadata identities without executable bodies``() =
        let revision = ForeignCases.publishedLabs.Value
        Assert.Empty(revision.Emission.Boundary.ResourceDeclarations)

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

        let limits: Fidelity.PSG.Binary.Limits =
            { MaxBytes = 4 * 1024 * 1024; MaxCollectionLength = 10000; MaxDepth = 128
              MaxStringBytes = 1024 * 1024; MaxBigIntegerBytes = 4096; MaxValues = 1000000 }
        let roundTrip current =
            let bytes = Fidelity.PSG.Binary.encode limits current |> Result.defaultWith (fun error -> failwithf "%A" error)
            let copy = Fidelity.PSG.Binary.decode limits bytes |> Result.defaultWith (fun error -> failwithf "%A" error)
            Assert.True(current.Emission.Numeric.ForeignResultUses = copy.Emission.Numeric.ForeignResultUses)
            Assert.True(current.CurrentClaims = copy.CurrentClaims)
        roundTrip revision
        let call = revision.Emission.Boundary.Calls[revision.Emission.Numeric.ForeignResultUses.Head.Application.Call]
        let withdrawn =
            { revision with Emission = { revision.Emission with Boundary = { revision.Emission.Boundary with Imports = revision.Emission.Boundary.Imports.Remove call.Import } } }
        Assert.Contains(Fidelity.PSG.Integrity.check withdrawn, fun issue ->
            issue.Part = "Emission.Numeric.ForeignResultUses.Abi"
            && issue.Reason = "A conditional ABI premise lacks its own call's imported declaration fact.")

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
            AvailableMemorySpaces=[]; DefaultMemorySpace=None; ClockFrequencyMhz=None; NsPerWeightUnit=None; ProjectMemoryPolicy=None }
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
    member _.``Missing foreign result behavior retains only its complete declared ABI domain``() =
        let graph =
            ForeignCases.resultPlatformGraph
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
                Assert.Equal(ValueRange.Bounded(-(1I <<< 63), (1I <<< 63) - 1I), row.ResultRange)
        )
        let revision=
            Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare graph
            |> Result.defaultWith(fun errors->failwithf "%A" errors)
            |> Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish
            |> Result.defaultWith(fun errors->failwithf "%A" errors)
        let call=Assert.Single revision.Emission.Boundary.Calls.Values
        Assert.Equal(Some(Fidelity.PSG.BoundaryScalar.Integer(64,true)),call.Result)
        Assert.True(call.ResultAdaptation.IsNone)
        let resultMeets=revision.Codata.Meets.TryFind call.Site |> Option.defaultValue [] |> List.filter(fun meet->meet.Operand=call.Site)
        Assert.Empty resultMeets
        Assert.Empty(Fidelity.PSG.Integrity.check revision)

    [<Fact>]
    member _.``Foreign result contract consumes the complete declared ABI domain of an unknown actual``() =
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
                Assert.True(row.Application.Hypothesis.IsSome)
                Assert.True(row.Abi.IsSome)
                Assert.Equal(ValueRange.Bounded(0I, (1I <<< 32) - 1I), row.Application.Arguments.Head.Enclosure)
                Assert.Equal(ValueRange.Bounded(-1I, (1I <<< 32) - 1I), row.ResultRange)
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
    member _.``Duplicate foreign result contracts refuse behavior authority while retaining declared ABI domain``() =
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
                Assert.True(row.Application.Hypothesis.IsNone)
                Assert.Equal(ValueRange.Bounded(-(1I <<< 63), (1I <<< 63) - 1I), row.ResultRange)
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
