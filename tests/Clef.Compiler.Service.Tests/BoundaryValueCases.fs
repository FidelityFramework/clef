namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private BoundaryValuesFixture =
    let check source =
        match parseAndCheck ("module BoundaryValues\n" + source) "boundary-values.clef" with
        | Success result | CheckFailure result -> result
        | ParseFailure errors -> failwithf "Boundary value source did not parse: %A" errors
    let context pointerBits : PlatformContext =
        { PlatformId = "native-entry-layout"; Dimensions = Map.ofList ["Pointer", pointerBits; "Register", 64]
          Representations = Map.empty; EndpointReturns = Map.empty; PlatformLibraryPath = None
          PlatformDescription = None; PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.empty
          Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
          AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None }

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "BoundaryValues")>]
type BoundaryValueCases() =
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
        let result = BoundaryValuesFixture.check """
type Listener = { Entry: FnPtr<bool -> bool> }
let callback (enabled: bool) : bool = enabled
[<EntryPoint>]
let main _ =
    let listener = { Entry = FnPtr.ofFunction callback }
    if FnPtr.invoke listener.Entry true then 0 else 1
"""
        DimensionalCases.noErrors result
        let context = BoundaryValuesFixture.context pointerBits
        let graph = Clef.Compiler.PSGSaturation.SemanticGraph.Placement.settle (Some context) { result.Graph with Platform = Some context }
        let layout = graph.Layouts.Value.Values |> Seq.choose (function
            | SettledLayout.Record([field], Some bytes, Some alignment) when field.Name = "Entry" -> Some(field, bytes, alignment)
            | _ -> None) |> Assert.Single
        let field, bytes, alignment = layout
        Assert.Equal(pointerBits / 8, bytes)
        Assert.Equal(pointerBits / 8, alignment)
        Assert.Equal(Some(pointerBits / 8), field.Size)
        Assert.Equal(TypeLayout.PlatformWord, layoutOf (NativeType.TApp(Types.fnPtrTyCon, [NativeType.TFun(Types.boolType, Types.boolType)])))
