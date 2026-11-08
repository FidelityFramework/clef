namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module BoundaryEmission = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission

module private BoundaryValuesFixture =
    let check source =
        match parseAndCheck ("module BoundaryValues\n" + source) "boundary-values.clef" with
        | Success result | CheckFailure result -> result
        | ParseFailure errors -> failwithf "Boundary value source did not parse: %A" errors
    let nativeGraph pointerBits =
        let source = """module BoundaryValues
type Listener = { Entry: FnPtr<bool -> bool> }
let callback (enabled: bool) : bool = enabled
[<EntryPoint>]
let main _ =
    let listener = { Entry = FnPtr.ofFunction callback }
    if FnPtr.invoke listener.Entry true then 0 else 1
"""
        SourcePlatformFixture.check pointerBits "boundary-values.clef" source

    let publish graph =
        match Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph with
        | Result.Ok revision -> revision
        | Result.Error failures -> failwithf "Native component publication refused: %A" failures

    let nativeContract (graph: SemanticGraph) =
        graph.Codata.Value.CallableContracts.Values
        |> Seq.filter (fun contract -> contract.Kind = CallableKind.NativeEntry)
        |> Assert.Single

    let library source concreteRoot =
        let path = System.IO.Path.GetFullPath "library-native.clef"
        let parse text file =
            match parseStringWithDefaults text file with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Library native source did not parse: %A" errors
        let inputs =
            [ parse SourcePlatformFixture.authority "write-authority.clef"
              parse ("module LibraryNative\n" + source) path ]
        let inputs =
            if concreteRoot then
                inputs @ [parse "module Program\n[<EntryPoint>]\nlet main _ = 0\n" "native-program.clef"]
            else inputs
        checkParsedInputsWithDeclarations inputs (Some SourcePlatformFixture.platform)
            Set.empty (Some(Set.singleton path)) None

    let exported name (graph: SemanticGraph) =
        graph.DeclarationRoots |> List.choose (fun (id, purpose) ->
            match purpose, graph.Nodes[id].Kind with
            | DeclRoot.LibraryExport, SemanticKind.Binding(name = actual) when actual = name -> Some graph.Nodes[id]
            | _ -> None) |> Assert.Single

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "BoundaryValues")>]
type BoundaryValueCases() =
    [<Theory>]
    [<InlineData("let exported (pointer: FnPtr<bool -> bool>) = true\n", "parameter")>]
    [<InlineData("let exported (flag: bool) (pointer: FnPtr<bool -> bool>) = flag\n", "result.parameter")>]
    [<InlineData("let private callback (flag: bool) = flag\nlet exported (flag: bool) : FnPtr<bool -> bool> = FnPtr.ofFunction callback\n", "result")>]
    [<InlineData("type Listener = { Entry: FnPtr<bool -> bool> }\nlet exported (listener: Listener) = true\n", "parameter.Entry")>]
    [<InlineData("type Entry = { Invoke: FnPtr<option<CHandle<unit>> -> option<CHandle<unit>>> }\nlet exported (first: int) (second: int) (entry: Entry) (arg: CHandle<unit>) = 0\n", "result.result.parameter.Invoke")>]
    [<InlineData("let exported (pair: bool * FnPtr<bool -> bool>) = true\n", "parameter.Item2")>]
    [<InlineData("let exported (candidate: option<FnPtr<bool -> bool>>) = true\n", "parameter.Some")>]
    [<InlineData("let exported (entries: FnPtr<bool -> bool> array) = true\n", "parameter.element")>]
    [<InlineData("type Inner = { Entry: FnPtr<bool -> bool> }\ntype Outer = { Nested: option<Inner> }\nlet exported (value: Outer) = true\n", "Nested.Some")>]
    [<InlineData("let private callback (flag: bool) = flag\nlet mutable exported : FnPtr<bool -> bool> = FnPtr.ofFunction callback\n", "public interface")>]
    member _.``Library native public shapes retain the typed host loading refusal``(source: string, slot: string) =
        let result = BoundaryValuesFixture.library source false
        let declaration = BoundaryValuesFixture.exported "exported" result.Graph
        let failures = BoundaryEmission.exportedInterfaceFailures result.Graph
        let failure = Assert.Single failures
        Assert.Equal(WitnessProjectionFailureKind.LibraryNativeInterfaceLoading, failure.Kind)
        Assert.Equal(Some declaration.Id, failure.Occurrence)
        Assert.Contains(slot, failure.Reason)
        Assert.Contains(result.Diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8416" && diagnostic.Severity = NativeDiagnosticSeverity.Error &&
            diagnostic.Range = declaration.Range && List.contains declaration.Id diagnostic.RelatedNodes)
        Assert.True(Result.isError(Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph))

    [<Fact>]
    member _.``Callback entry export requires its descriptor and forwarding extern``() =
        let declarations = """type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Pointer of int
type Passing = Value | Reference
type CallingConvention = CDecl | StdCall
type Ownership = Undeclared | Owned
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: Passing }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallingConvention; OwnershipTransfer: Ownership }
type CallbackDescriptor = { Record: string; Field: string; Signature: FunctionDescriptor }
type Entry = { Invoke: FnPtr<option<CHandle<unit>> -> option<CHandle<unit>>> }
"""
        let callback = """let EntryDescriptor : Expr<CallbackDescriptor> =
    <@ { Record = "Entry"; Field = "Invoke"; Signature = { CName = "callback"; Parameters = [| { Name = "arg"; Type = Pointer 64; PassBy = Value } |]; ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Undeclared } } @>
"""
        let wrapper = """[<FidelityExtern("c", "pthread_create")>]
let private native (first: int) (second: int) (entry: FnPtr<option<CHandle<unit>> -> option<CHandle<unit>>>) (arg: CHandle<unit>) : int = NativeDefault.zeroed ()
let nativeDescriptor : Expr<FunctionDescriptor> =
    <@ { CName = "pthread_create"; Parameters = [| { Name = "first"; Type = Integer (Signed, 32); PassBy = Value }; { Name = "second"; Type = Integer (Signed, 32); PassBy = Value }; { Name = "entry"; Type = Pointer 64; PassBy = Value }; { Name = "arg"; Type = Pointer 64; PassBy = Value } |]; ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let exported (first: int) (second: int) (entry: Entry) (arg: CHandle<unit>) : int = native first second entry.Invoke arg
"""
        let positive = BoundaryValuesFixture.library (declarations + callback + wrapper) false
        DimensionalCases.noErrors positive
        Assert.Empty(BoundaryEmission.exportedInterfaceFailures positive.Graph)
        Assert.DoesNotContain(positive.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8416")

        let pthreadResult = Clef.Compiler.Project.ProjectChecker.checkProject "/home/hhh/repos/Fidelity.Platform/Environments/Linux/x86_64/Fidelity.Pthread.fidproj"
        Assert.True(Result.isOk pthreadResult)
        let pthread = Result.defaultWith (fun error -> failwithf "Pthread project check failed: %A" error) pthreadResult
        Assert.False(Clef.Compiler.Project.ProjectChecker.hasErrors pthread)
        Assert.Empty(BoundaryEmission.exportedInterfaceFailures pthread.CheckResult.Graph)
        Assert.DoesNotContain(pthread.CheckResult.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8416")

        let invalidSources =
            [ declarations + wrapper
              declarations + callback.Replace("Field = \"Invoke\"", "Field = \"Wrong\"") + wrapper
              declarations + callback.Replace("CallingConvention = CDecl", "CallingConvention = StdCall") + wrapper
              declarations + callback.Replace("Parameters = [| { Name = \"arg\"; Type = Pointer 64; PassBy = Value } |]", "Parameters = [||]") + wrapper
              declarations + callback.Replace("Type = Pointer 64; PassBy = Value", "Type = Integer (Signed, 32); PassBy = Value") + wrapper
              declarations + callback.Replace("Type = Pointer 64; PassBy = Value", "Type = Pointer 64; PassBy = Reference") + wrapper
              declarations + callback.Replace("ReturnType = Pointer 64", "ReturnType = Integer (Signed, 32)") + wrapper
              declarations + callback + wrapper.Replace("[<FidelityExtern(\"c\", \"pthread_create\")>]\n", "")
              declarations + callback + wrapper.Replace("native first second entry.Invoke arg", "0") ]
        for index, source in List.indexed invalidSources do
            let result = BoundaryValuesFixture.library source false
            let failures = BoundaryEmission.exportedInterfaceFailures result.Graph
            Assert.True(not failures.IsEmpty, $"Invalid source {index} was admitted")
            let failure = Assert.Single failures
            Assert.Equal(WitnessProjectionFailureKind.LibraryNativeInterfaceLoading, failure.Kind)
            Assert.Contains("result.result.parameter.Invoke", failure.Reason)
            Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8416")

        let concreteLibrary = """module LibraryNative
type Signedness = Signed | Unsigned
type TypeRef = Void | Integer of Signedness * int | Pointer of int | Entry of string
type Passing = Value | Reference
type CallingConvention = CDecl | StdCall
type Ownership = Undeclared | Owned
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: Passing }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallingConvention; OwnershipTransfer: Ownership }
type CallbackDescriptor = { Record: string; Field: string; Signature: FunctionDescriptor }
type EntrySignature = { Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallingConvention }
type ExternalExecutionHypothesis = { Identity: string; Version: string; Source: string }
type ScopedCallbackDescriptor = { Binding: string; Parameter: string }
type CallbackInvocationContract = { Binding: string; Parameter: int; Scope: string; Signature: EntrySignature; Hypothesis: ExternalExecutionHypothesis }
type CallbackEntry = { Invoke: FnPtr<unit -> unit> }
let CallbackEntryDescriptor : Expr<CallbackDescriptor> =
    <@ { Record = "CallbackEntry"; Field = "Invoke"; Signature = { CName = "callback"; Parameters = [||]; ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared } } @>
[<FidelityExtern("c", "pthread_create")>]
let private native (entry: FnPtr<unit -> unit>) : unit = ()
let nativeDescriptor : Expr<FunctionDescriptor> =
    <@ { CName = "pthread_create"; Parameters = [| { Name = "entry"; Type = TypeRef.Entry "LibraryNative.nativeInvocation"; PassBy = Value } |]; ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let nativeScope : Expr<ScopedCallbackDescriptor> =
    <@ { Binding = "LibraryNative.native"; Parameter = "entry" } @>
let nativeInvocation : Expr<CallbackInvocationContract> =
    <@ { Binding = "LibraryNative.native"; Parameter = 0; Scope = "LibraryNative.nativeScope"; Signature = { Parameters = [||]; ReturnType = Void; CallingConvention = CDecl }; Hypothesis = { Identity = "test"; Version = "1"; Source = "test" } } @>
let exported (entry: CallbackEntry) : unit = native entry.Invoke
"""
        let concreteConsumer = """module Program
let callback () = ()
[<EntryPoint>]
let main _ =
    LibraryNative.exported { Invoke = FnPtr.ofFunction callback }
    0
"""
        let libraryPath = System.IO.Path.GetFullPath "library-native.clef"
        let authorityPath = System.IO.Path.GetFullPath "write-authority.clef"
        let parse text file =
            match parseStringWithDefaults text file with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Library native source did not parse: %A" errors
        let libcAuthority = SourcePlatformFixture.authority.Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")
        let libcPlatform =
            { SourcePlatformFixture.platform with
                RuntimeModel = Some RuntimeModel.Libc
                PlatformDescription = Some "WriteAuthority.description"
                PlatformSourcePaths = Set.singleton authorityPath }
        let concreteResult =
            checkParsedInputsWithDeclarations
                [ parse libcAuthority authorityPath
                  parse concreteLibrary libraryPath
                  parse concreteConsumer "native-program.clef" ]
                (Some libcPlatform)
                Set.empty
                (Some(Set.singleton libraryPath))
                None
        DimensionalCases.noErrors concreteResult
        Assert.Contains(concreteResult.Graph.DeclarationRoots, fun (_, purpose) -> purpose = DeclRoot.LibraryExport)
        Assert.Contains(concreteResult.Graph.DeclarationRoots, fun (_, purpose) -> purpose = DeclRoot.EntryPoint)
        let revision = BoundaryValuesFixture.publish concreteResult.Graph
        let nodes = revision.Nodes.Values |> Seq.map (sprintf "%A") |> String.concat "\n"
        Assert.Contains("exported", nodes)
        Assert.Contains("native", nodes)
        Assert.Contains("callback", nodes)

    [<Fact>]
    member _.``A public boolean function does not export its private native implementation``() =
        let source = "let private callback (flag: bool) = flag\nlet exported (flag: bool) : bool =\n    let pointer = FnPtr.ofFunction callback\n    FnPtr.invoke pointer flag\n"
        let result = BoundaryValuesFixture.library source false
        DimensionalCases.noErrors result
        let declaration = BoundaryValuesFixture.exported "exported" result.Graph
        Assert.Equal<NativeType>(NativeType.TFun(Types.boolType, Types.boolType), declaration.Type)
        Assert.Contains(result.Graph.Nodes.Values, fun node -> Types.tryGetNTUKind node.Type = Some NTUKind.NTUfnptr)
        Assert.Empty(BoundaryEmission.exportedInterfaceFailures result.Graph)
        Assert.DoesNotContain(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8416")

    [<Fact>]
    member _.``An opaque handle phantom argument is not an exported native callable slot``() =
        let result = BoundaryValuesFixture.library "let exported (handle: CHandle<FnPtr<bool -> bool>>) = true\n" false
        DimensionalCases.noErrors result
        BoundaryValuesFixture.exported "exported" result.Graph |> ignore
        Assert.Empty(BoundaryEmission.exportedInterfaceFailures result.Graph)
        Assert.DoesNotContain(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8416")

    [<Fact>]
    member _.``A concrete root does not suppress a retained native interface diagnostic``() =
        let result = BoundaryValuesFixture.library "let exported (pointer: FnPtr<bool -> bool>) = true\n" true
        let declaration = BoundaryValuesFixture.exported "exported" result.Graph
        Assert.Contains(result.Graph.DeclarationRoots, fun (_, purpose) -> purpose = DeclRoot.EntryPoint)
        Assert.DoesNotContain(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8417")
        Assert.Contains(result.Diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8416" && List.contains declaration.Id diagnostic.RelatedNodes)

    [<Fact>]
    member _.``Native interface refusal survives an independently invalid ordinary demand proof``() =
        let result = BoundaryValuesFixture.library "let exported (pointer: FnPtr<bool -> bool>) = true\n" false
        let declaration = BoundaryValuesFixture.exported "exported" result.Graph
        let invalidDemand =
            { Class = EdgeClass.Demand; Target = declaration.Id; Ordinal = 0; Sources = []
              Role = EdgeRole.OrdinaryBindingDemandPending("invalid demand fixture", { Participants = []; SourceTypes = Map.empty }) }
        let graph = { result.Graph with Edges = invalidDemand :: result.Graph.Edges }
        Assert.True(Result.isError(Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.projectValidated graph))
        match BoundaryEmission.prepare graph with
        | Result.Ok _ -> failwith "Invalid ordinary demand and native export were admitted"
        | Result.Error failures ->
            Assert.Contains(failures, fun failure -> failure.Kind = WitnessProjectionFailureKind.LibraryNativeInterfaceLoading)
            Assert.Contains(failures, fun failure ->
                failure.Kind = WitnessProjectionFailureKind.Settlement && failure.Reason.Contains("OrdinaryBindingDemand"))

    [<Fact>]
    member _.``Program image residence and diagnostic prose cannot establish host loading``() =
        let graph = BoundaryValuesFixture.nativeGraph 64
        let contract = BoundaryValuesFixture.nativeContract graph
        match contract.Convention with
        | CallableConvention.CompilerOwnedPortable convention ->
            Assert.True(graph.Nodes.ContainsKey convention.CodeLifetime.Implementation)
        | other -> failwithf "Expected valid program image residence, got %A" other
        let listener = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Binding(name = "listener") -> true | _ -> false) |> Assert.Single
        let exported = { graph with DeclarationRoots = (listener.Id, DeclRoot.LibraryExport) :: graph.DeclarationRoots }
        let failure = BoundaryEmission.exportedInterfaceFailures exported |> Assert.Single
        let diagnostic = BoundaryEmission.diagnostics exported [{ failure with Reason = "An unrelated explanatory sentence." }] |> Assert.Single
        Assert.Equal("CCS8416", diagnostic.Code)
        Assert.Equal(listener.Range, diagnostic.Range)
        Assert.Contains(listener.Id, diagnostic.RelatedNodes)
        Assert.True(Result.isError(BoundaryEmission.prepare exported))

    [<Theory>]
    [<InlineData("[<EntryPoint>]\nlet main _ = let mutable value = true in let address = &&value in 0")>]
    [<InlineData("let raw (value: bool) = &&value\n[<EntryPoint>]\nlet main _ = 0")>]
    [<InlineData("let raw (value: bool byref) = &&value\n[<EntryPoint>]\nlet main _ = 0")>]
    member _.``A source raw address is rejected even when its result is unused`` source =
        let result = BoundaryValuesFixture.check source
        Assert.Contains(result.Diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8401" && diagnostic.Severity = NativeDiagnosticSeverity.Error && diagnostic.Message.Contains("Raw addresses"))
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8401" && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            match node.Type with NativeType.TNativePtr _ -> true | _ -> false)

    [<Theory>]
    [<InlineData("Sys.stackArgv")>]
    [<InlineData("Arena.fromPointer")>]
    [<InlineData("Arena.alloc")>]
    [<InlineData("Arena.allocAligned")>]
    member _.``Internal address ingredients are unavailable through source lookup`` name =
        let result = BoundaryValuesFixture.check ($"let unavailable () = {name}\n[<EntryPoint>]\nlet main _ = 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8401" && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            match node.Kind with
            | SemanticKind.Intrinsic info -> info.FullName = name
            | _ -> false)

    [<Theory>]
    [<InlineData("let handle: CHandle<unit> = NativeDefault.zeroed ()", "if handle = handle then 0 else 1")>]
    [<InlineData("let zero = NativeDefault.zeroed\nlet handle: CHandle<unit> = zero ()", "if handle = handle then 0 else 1")>]
    [<InlineData("let forge () : CHandle<unit> = NativeDefault.zeroed ()", "let handle = forge () in if handle = handle then 0 else 1")>]
    [<InlineData("let construct factory : CHandle<unit> = factory ()", "let handle = construct NativeDefault.zeroed in if handle = handle then 0 else 1")>]
    [<InlineData("type Holder<'T> = Entry of 'T\nlet construct holder : CHandle<unit> = match holder with Entry factory -> factory ()", "let handle = construct (Entry NativeDefault.zeroed) in if handle = handle then 0 else 1")>]
    [<InlineData("let construct candidate : option<CHandle<unit>> = match candidate with Some factory -> Some (factory ()) | None -> None", "match construct (Some NativeDefault.zeroed) with Some handle -> (if handle = handle then 0 else 1) | None -> 0")>]
    [<InlineData("let construct candidate : voption<CHandle<unit>> = match candidate with ValueSome factory -> ValueSome (factory ()) | ValueNone -> ValueNone", "match construct (ValueSome NativeDefault.zeroed) with ValueSome handle -> (if handle = handle then 0 else 1) | ValueNone -> 0")>]
    [<InlineData("let construct candidate : Result<CHandle<unit>, bool> = match candidate with Ok factory -> Ok (factory ()) | Error flag -> Error flag", "match construct (Ok NativeDefault.zeroed) with Ok handle -> (if handle = handle then 0 else 1) | Error flag -> if flag then 1 else 0")>]
    [<InlineData("type Holder<'T> = { Value: 'T }\nlet holder: Holder<CHandle<unit>> = NativeDefault.zeroed ()", "if holder.Value = holder.Value then 0 else 1")>]
    [<InlineData("type Inner = { Value: CHandle<unit> }\ntype Outer = { Nested: Inner }\nlet holder: Outer = NativeDefault.zeroed ()", "if holder.Nested.Value = holder.Nested.Value then 0 else 1")>]
    [<InlineData("let pair: CHandle<unit> * bool = NativeDefault.zeroed ()", "let handle, _ = pair in if handle = handle then 0 else 1")>]
    [<InlineData("type Wrapped = Wrapped of CHandle<unit>\nlet wrapped: Wrapped = NativeDefault.zeroed ()", "match wrapped with Wrapped handle -> if handle = handle then 0 else 1")>]
    [<InlineData("let wrapped: Result<CHandle<unit>, bool> = NativeDefault.zeroed ()", "match wrapped with Ok handle -> (if handle = handle then 0 else 1) | Error flag -> if flag then 1 else 0")>]
    [<InlineData("type Holder<'T> = { Value: 'T }\nlet holder: Holder<unit -> CHandle<unit>> = NativeDefault.zeroed ()", "let handle = holder.Value () in if handle = handle then 0 else 1")>]
    [<InlineData("type option = Wrapped of CHandle<unit>\nlet wrapped: option = NativeDefault.zeroed ()", "match wrapped with Wrapped handle -> if handle = handle then 0 else 1")>]
    [<InlineData("type voption = Wrapped of CHandle<unit>\nlet wrapped: voption = NativeDefault.zeroed ()", "match wrapped with Wrapped handle -> if handle = handle then 0 else 1")>]
    [<InlineData("let handle: CHandle<unit> = NativeDefault.zeroed ()", "let closure () = handle in let captured = closure () in if captured = captured then 0 else 1")>]
    [<InlineData("let pointer: FnPtr<unit -> unit> = NativeDefault.zeroed ()", "FnPtr.invoke pointer (); 0")>]
    [<InlineData("type Listener = { Entry: FnPtr<unit -> unit> }\nlet listener: Listener = NativeDefault.zeroed ()", "FnPtr.invoke listener.Entry (); 0")>]
    member _.``Zero initialization cannot forge a demanded non-null boundary value``(declarations: string, body: string) =
        let result = BoundaryValuesFixture.check (declarations + "\n[<EntryPoint>]\nlet main _ = " + body + "\n")
        Assert.Contains(result.Diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8010" && diagnostic.Severity = NativeDiagnosticSeverity.Error &&
            Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error && diagnostic.Message.Contains("NativeDefault.zeroed"))

    [<Theory>]
    [<InlineData("int")>]
    [<InlineData("CHandle<unit>")>]
    [<InlineData("option<CHandle<unit>>")>]
    [<InlineData("FnPtr<unit -> unit>")>]
    [<InlineData("int * int")>]
    member _.``FnPtr rejects a concrete payload without a function signature`` payload =
        let result = BoundaryValuesFixture.check ($"let invalid (pointer: FnPtr<{payload}>) = pointer\n[<EntryPoint>]\nlet main _ = 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096" && diagnostic.Message.Contains("requires a function signature"))
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096" && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)

    [<Theory>]
    [<InlineData("type Alias<'T> = FnPtr<'T>\nlet invalid (pointer: Alias<int>) = pointer")>]
    [<InlineData("type Holder<'T> = { Entry: FnPtr<'T> }\nlet invalid (pointer: Holder<int>) = pointer")>]
    [<InlineData("type Holder<'T> = Entry of FnPtr<'T>\nlet invalid (pointer: Holder<int>) = pointer")>]
    member _.``Concrete instantiation cannot hide a non-function native signature`` source =
        let result = BoundaryValuesFixture.check (source + "\n[<EntryPoint>]\nlet main _ = 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8096" && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)

    [<Fact>]
    member _.``Absence and ordinary scalar records remain explicitly constructible``() =
        let result = BoundaryValuesFixture.check """
type Flags = { Enabled: bool }
let flags: Flags = NativeDefault.zeroed ()
let absent: option<CHandle<unit>> = None
[<EntryPoint>]
let main _ =
    match absent with
    | None -> if flags.Enabled then 1 else 0
    | Some handle -> if handle = handle then 1 else 0
"""
        DimensionalCases.noErrors result

    [<Theory>]
    [<InlineData(32)>]
    [<InlineData(64)>]
    member _.``Native entry records use the declared platform pointer width`` pointerBits =
        let graph = BoundaryValuesFixture.nativeGraph pointerBits
        let layout = graph.Layouts.Value.Values |> Seq.choose (function
            | SettledLayout.Record([field], Some bytes, Some alignment) when field.Name = "Entry" -> Some(field, bytes, alignment)
            | _ -> None) |> Assert.Single
        let field, bytes, alignment = layout
        // FFI §3.6.1 items 1/2: "A single-entry family needs no code storage"
        // and each inhabited slot retains its receiving contract and lifetime.
        // Closure Representation §2.4 keeps native entries distinct and
        // explicitly without an ordinary closure environment.
        Assert.Equal(0, bytes)
        Assert.Equal(1, alignment)
        Assert.Equal(Some 0, field.Size)
        Assert.Equal(SettledSlot.InlineBytes(0, 1), field.Slot)
        let contract = BoundaryValuesFixture.nativeContract graph
        let convention =
            match contract.Convention with
            | CallableConvention.CompilerOwnedPortable convention -> convention
            | other -> failwithf "Expected compiler-owned portable convention: %A" other
        Assert.True(contract.EnvironmentBytes.IsNone)
        Assert.Empty contract.OmittedParameters
        Assert.Equal(Clef.Compiler.Baker.Ingredients.Boundaries.platformPremise graph.Platform, Some convention.Target)
        let lifetime = convention.CodeLifetime
        let expectedLifetime = [lifetime.Module; lifetime.Binding; lifetime.Implementation]
        let carriers = graph.Codata.Value.CallableCarriers.Values |> Seq.filter (fun carrier -> carrier.Kind = CallableKind.NativeEntry)
        Assert.NotEmpty carriers
        for carrier in carriers do
            Assert.Equal(Ok contract.Identity, carrier.Contract)
            Assert.True(carrier.Environment.IsNone)
            Assert.True(carrier.EnvironmentValue.IsNone)
            Assert.Equal<NodeId list>(expectedLifetime, carrier.Lifetime |> List.sortBy _.Ordinal |> List.map _.Node)
            Assert.All(carrier.Lifetime, fun participant ->
                Assert.Equal(ParticipantRole.CallableLifetime, participant.Role)
                Assert.Equal(contract.Identity, participant.Group))
        let revision = BoundaryValuesFixture.publish graph
        Assert.Empty(Fidelity.PSG.Integrity.callableAggregates revision)
        Assert.NotEmpty revision.Emission.Callable.AggregateDependencies
        // Standalone boundary carrier layout remains a separate assertion.
        Assert.Equal(TypeLayout.PlatformWord, layoutOf (NativeType.TApp(Types.fnPtrTyCon, [NativeType.TFun(Types.boolType, Types.boolType)])))

    [<Fact>]
    member _.``A native component without code residence is refused by its owning recipe`` () =
        let graph = BoundaryValuesFixture.nativeGraph 64
        let facts = graph.Codata.Value
        let carriers = facts.CallableCarriers |> Map.map (fun _ carrier ->
            if carrier.Kind = CallableKind.NativeEntry then { carrier with Lifetime = [] } else carrier)
        let settled =
            Clef.Compiler.Baker.Recipes.CallableAggregateRecipes.settle
                (Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolveCallableBranches graph)
                { Carriers = carriers; Contracts = facts.CallableContracts
                  Flows = facts.CallableFlows; Joins = facts.CallableJoins
                  PreviousSlots = facts.CallableAggregateSlots } graph
        Assert.Contains(settled.Residuals, fun failure -> failure.Code = "CCS8101")
        Assert.Empty settled.Values

    [<Fact>]
    member _.``A nonempty forged native lifetime cannot authorize an aggregate component`` () =
        let graph = BoundaryValuesFixture.nativeGraph 64
        let facts = graph.Codata.Value
        let unrelated = graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.TypeDef _ -> true | _ -> false)
        let carriers = facts.CallableCarriers |> Map.map (fun _ carrier ->
            if carrier.Kind <> CallableKind.NativeEntry then carrier else
            Assert.NotEmpty carrier.Lifetime
            let lifetime = carrier.Lifetime |> List.map (fun participant -> { participant with Node = unrelated.Id })
            { carrier with Lifetime = lifetime })
        let settled =
            Clef.Compiler.Baker.Recipes.CallableAggregateRecipes.settle
                (Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolveCallableBranches graph)
                { Carriers = carriers; Contracts = facts.CallableContracts
                  Flows = facts.CallableFlows; Joins = facts.CallableJoins
                  PreviousSlots = facts.CallableAggregateSlots } graph
        Assert.Contains(settled.Residuals, fun failure -> failure.Code = "CCS8101")
        Assert.Empty settled.Values
        let codata = { facts with CallableCarriers = carriers }
        let forged = { graph with Codata = lazy codata }
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare forged |> Result.isError)
        Assert.True(Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish forged |> Result.isError)

    [<Fact>]
    member _.``An extern-tagged binding cannot acquire compiler-owned code residence`` () =
        let graph = BoundaryValuesFixture.nativeGraph 64
        let contract = BoundaryValuesFixture.nativeContract graph
        let lifetime =
            match contract.Convention with
            | CallableConvention.CompilerOwnedPortable convention -> convention.CodeLifetime
            | other -> failwithf "Expected compiler-owned convention: %A" other
        let binding = graph.Nodes[lifetime.Binding]
        let externBinding =
            { binding with Metadata = binding.Metadata.Add("FidelityExtern.Library", MetadataValue.String "foreign-library") }
        let changed = { graph with Nodes = graph.Nodes.Add(binding.Id, externBinding) }
        Assert.True(Clef.Compiler.Baker.Ingredients.CompilerOwnedEntries.tryImplementation graph lifetime.Implementation |> Option.isSome)
        Assert.True(Clef.Compiler.Baker.Ingredients.CompilerOwnedEntries.tryImplementation changed lifetime.Implementation |> Option.isNone)
        Assert.True(Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish changed |> Result.isError)

    [<Theory>]
    [<InlineData(true)>]
    [<InlineData(false)>]
    member _.``Same identity native residence corruption withdraws the earlier account`` changeParent =
        let graph = BoundaryValuesFixture.nativeGraph 64
        let before = BoundaryValuesFixture.publish graph
        let contract = BoundaryValuesFixture.nativeContract graph
        let lifetime =
            match contract.Convention with
            | CallableConvention.CompilerOwnedPortable convention -> convention.CodeLifetime
            | other -> failwithf "Expected compiler-owned convention: %A" other
        let changed =
            if changeParent then
                let binding = graph.Nodes[lifetime.Binding]
                { graph with Nodes = graph.Nodes.Add(binding.Id, { binding with Parent = None }) }
            else
                let moduleNode = graph.Nodes[lifetime.Module]
                let kind =
                    match moduleNode.Kind with
                    | SemanticKind.ModuleDef(name, members) -> SemanticKind.ModuleDef(name, members |> List.filter ((<>) lifetime.Binding))
                    | other -> failwithf "Expected program module: %A" other
                { graph with Nodes = graph.Nodes.Add(moduleNode.Id, { moduleNode with Kind = kind }) }
        Assert.NotEmpty before.Emission.Callable.AggregateDependencies
        let sites = graph.Codata.Value.CallableAggregateDependencies.Keys |> Seq.toList
        Assert.NotEmpty sites
        for site in sites do
            Assert.True(Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.current changed site |> Result.isError)
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare changed |> Result.isError)
        Assert.True(Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish changed |> Result.isError)

    [<Fact>]
    member _.``Native value option annotations and helper returns share the source constructor``() =
        for value in ["ValueSome 7"; "ValueNone"] do
            let result = BoundaryValuesFixture.check ("let choose () : voption<int> = " + value + "\n[<EntryPoint>]\nlet main _ =\n    let selected: voption<int> = choose ()\n    match selected with | ValueSome payload -> payload | ValueNone -> 0\n")
            DimensionalCases.noErrors result
            let selected = result.Graph.Nodes.Values |> Seq.filter(fun node -> match node.Kind with SemanticKind.Binding("selected",_,_,_) -> true | _ -> false) |> Assert.Single
            DimensionalCases.same (NativeType.TApp(Types.voptionTyCon,[Types.intType])) selected.Type
            let payloads=result.Graph.Nodes.Values |> Seq.choose(fun node -> match node.Kind with SemanticKind.DUEliminate(_,1,"ValueSome",payload) -> Some payload | _ -> None) |> Seq.toList
            Assert.NotEmpty payloads
            for payload in payloads do DimensionalCases.same Types.intType payload
