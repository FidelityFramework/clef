namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeService
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations

module private ClosedCallbackCases =
    let declarations = """
module ClosedCallbacks
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Pointer of int | Void
type PassBy = | Value
type CallConv = | CDecl
type Transfer = | Borrowed
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type CallbackDescriptor = { Record: string; Field: string; Signature: FunctionDescriptor }
type ClosedCallbackDescriptor = { Binding: string; Adapter: string; Record: string; Field: string }
type NativeEntry = { Invoke: FnPtr<int -> CHandle<unit> -> unit> }
let entryDescriptor: Expr<CallbackDescriptor> = <@ { Record = "NativeEntry"; Field = "Invoke"; Signature = { CName = "Test::message"; Parameters = [| { Name = "value"; Type = Integer (Signed, 32); PassBy = Value }; { Name = "data"; Type = Pointer 64; PassBy = Value } |]; ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Borrowed } } @>
let private adapter (handler: int -> unit) (value: int) (_data: CHandle<unit>) : unit = handler value
let private makeEntry (handler: int -> unit) : NativeEntry = NativeDefault.zeroed ()
let closedDescriptor: Expr<ClosedCallbackDescriptor> = <@ { Binding = "ClosedCallbacks.makeEntry"; Adapter = "ClosedCallbacks.adapter"; Record = "NativeEntry"; Field = "Invoke" } @>
let inline listener handler = makeEntry handler
"""
    let check (source: string) =
        let marker = "let inline listener handler = makeEntry handler\n"
        let split = source.IndexOf(marker) + marker.Length
        let library = source.Substring(0, split)
        let application = "module Application\nopen ClosedCallbacks\n" + source.Substring(split)
        let parsed =
            [library, "closed-bindings.clef"; application, "closed-application.clef"]
            |> List.map (fun (text, path) ->
                match parseStringWithDefaults text path with
                | ParseSuccess input -> input
                | ParseError errors -> failwithf "Parse failed: %A" errors)
        checkParsedInputs parsed
    let entries graph = (read graph).Callbacks
    let handlerReferences (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.choose (fun node ->
            if not node.IsReachable then None else
            match node.Kind with
            | SemanticKind.VarRef (_, Some target) ->
                match graph.Nodes[target].Kind with
                | SemanticKind.Binding (name, _, _, _) when name.StartsWith("handler") -> Some name
                | _ -> None
            | _ -> None) |> Set.ofSeq

    // This source fixture stipulates a receiving C contract. It executes no C.
    let receivingGraph () =
        let source =
            """
module ReceivingCallback
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Void | Entry of string
type PassBy = | Value
type CallConv = | CDecl
type Transfer = | Undeclared
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type EntrySignature = { Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv }
type ExternalExecutionHypothesis = { Identity: string; Version: string; Source: string }
type ScopedCallbackDescriptor = { Binding: string; Parameter: string }
type CallbackInvocationContract = { Binding: string; Parameter: int; Signature: EntrySignature; Hypothesis: ExternalExecutionHypothesis; Scope: string }
[<FidelityExtern("c", "consume_callback")>]
let private receive (callback: FnPtr<int -> int>) : unit = NativeDefault.zeroed ()
let receiveDescriptor: Expr<FunctionDescriptor> = <@ { CName = "consume_callback"; Parameters = [| { Name = "callback"; Type = Entry "ReceivingCallback.invocation"; PassBy = Value } |]; ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>
let scope: Expr<ScopedCallbackDescriptor> = <@ { Binding = "ReceivingCallback.receive"; Parameter = "callback" } @>
let invocation: Expr<CallbackInvocationContract> = <@ { Binding = "ReceivingCallback.receive"; Parameter = 0; Signature = { Parameters = [| { Name = "arg0"; Type = Integer (Signed, 64); PassBy = Value } |]; ReturnType = Integer (Signed, 64); CallingConvention = CDecl }; Hypothesis = { Identity = "receiving-test"; Version = "v1"; Source = "declared-source-fixture" }; Scope = "ReceivingCallback.scope" } @>
let callback (_unused: int) = 7
[<EntryPoint>]
let main _ =
    receive (FnPtr.ofFunction callback)
    0
"""

        let parse source path =
            match parseStringWithDefaults source path with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Parse failed: %A" errors

        let platform = SourcePlatformFixture.platform

        let authority =
            SourcePlatformFixture.authority.Replace("Runtime = \"freestanding\"", "Runtime = \"libc\"")

        let result =
            checkParsedInputsWithPlatform
                [
                    parse authority "write-authority.clef"
                    parse source "receiving-callback.clef"
                ]
                (Some platform)

        DimensionalCases.noErrors result
        result.Graph

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ClosedCallbacks")>]
type ClosedCallbackTests() =
    [<Fact>]
    member _.``A binding adapter hides native arguments from a closed application handler``() =
        let body = """
let handler (value: int) : unit = ()
[<EntryPoint>]
let main _ = let entry = listener handler in 0
"""
        let result = ClosedCallbackCases.check (ClosedCallbackCases.declarations + body)
        DimensionalCases.noErrors result
        let entry = ClosedCallbackCases.entries result.Graph |> Assert.Single
        match result.Graph.Nodes[entry.Lambda].Kind with
        | SemanticKind.Lambda (parameters, _, captures, _, _) ->
            Assert.Equal(2, parameters.Length)
            Assert.Empty captures
        | kind -> failwithf "Expected native module entry, got %A" kind
        Assert.Contains("handler", ClosedCallbackCases.handlerReferences result.Graph)
        Assert.True(entry.ReturnsVoid)
        Assert.Contains(result.Graph.Codata.Value.FunctionPointers |> Map.values, function
            | FunctionPointerPlan.Address (symbol, target) -> target = entry.Lambda && symbol.StartsWith("__clef_callback_")
            | _ -> false)

    [<Fact>]
    member _.``Different closed handlers retain distinct native entries``() =
        let body = """
let handlerOne (value: int) : unit = ()
let handlerTwo (value: int) : unit = ()
[<EntryPoint>]
let main _ =
    let first = listener handlerOne
    let second = listener handlerTwo
    0
"""
        let result = ClosedCallbackCases.check (ClosedCallbackCases.declarations + body)
        DimensionalCases.noErrors result
        let entries = ClosedCallbackCases.entries result.Graph
        Assert.Equal(2, entries.Length)
        Assert.Equal(2, entries |> List.map (fun entry -> entry.Lambda) |> List.distinct |> List.length)
        Assert.Contains("handlerOne", ClosedCallbackCases.handlerReferences result.Graph)
        Assert.Contains("handlerTwo", ClosedCallbackCases.handlerReferences result.Graph)

    [<Theory>]
    [<InlineData("let captured (value: int) = if value = limit then () else ()\n    let entry = listener captured\n    0")>]
    [<InlineData("let entry = listener (fun value -> if value = limit then () else ())\n    0")>]
    member _.``A captured handler is rejected before any C address is created``(body: string) =
        let result = ClosedCallbackCases.check (ClosedCallbackCases.declarations + "\n[<EntryPoint>]\nlet main _ =\n    let limit = 7\n    " + body + "\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096")
        Assert.Empty(ClosedCallbackCases.entries result.Graph)

    [<Fact>]
    member _.``The adapter requires a declared native ABI``() =
        let source = ClosedCallbackCases.declarations.Split('\n') |> Array.filter (fun line -> not (line.StartsWith("let entryDescriptor:"))) |> String.concat "\n"
        let result = ClosedCallbackCases.check (source + "\nlet handler (value: int) = ()\n[<EntryPoint>]\nlet main _ = let entry = listener handler in 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096" && diagnostic.Message.Contains("CallbackDescriptor"))

    [<Fact>]
    member _.``Native scalar mismatches remain errors after specialization``() =
        let source = ClosedCallbackCases.declarations.Replace("Type = Integer (Signed, 32)", "Type = Pointer 64")
        let result = ClosedCallbackCases.check (source + "\nlet handler (value: int) = ()\n[<EntryPoint>]\nlet main _ = let entry = listener handler in 0\n")
        Assert.Contains((read result.Graph).Findings, fun finding -> finding.Defect = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.DeclarationDefect.Invalid)

    [<Theory>]
    [<InlineData("let private adapter (handler: int -> unit) (value: int) (_data: CHandle<unit>) : unit = handler value", "let mutable adapter = fun (handler: int -> unit) (value: int) (_data: CHandle<unit>) -> handler value")>]
    [<InlineData("let private makeEntry (handler: int -> unit) : NativeEntry = NativeDefault.zeroed ()", "let mutable makeEntry = fun (handler: int -> unit) -> (NativeDefault.zeroed () : NativeEntry)")>]
    member _.``Mutable template declarations cannot be statically substituted``(original: string, replacement: string) =
        let source = ClosedCallbackCases.declarations.Replace(original, replacement)
        let result = ClosedCallbackCases.check (source + "\nlet handler (value: int) = ()\n[<EntryPoint>]\nlet main _ = let entry = listener handler in 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096")
        Assert.Empty(ClosedCallbackCases.entries result.Graph)

    [<Fact>]
    member _.``A nested closure cannot retain the removed handler formal``() =
        let source = ClosedCallbackCases.declarations.Replace("= handler value", "= let later () = handler value in later ()")
        let result = ClosedCallbackCases.check (source + "\nlet handler (value: int) = ()\n[<EntryPoint>]\nlet main _ = let entry = listener handler in 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096" && diagnostic.Message.Contains("nested closure"))

    [<Fact>]
    member _.``A local descriptor cannot declare the native ABI``() =
        let source = ClosedCallbackCases.declarations.Replace("let entryDescriptor:", "let localDeclaration () =\n    let entryDescriptor:").Replace("let private adapter", "    ()\nlet private adapter")
        let result = ClosedCallbackCases.check (source + "\nlet handler (value: int) = ()\n[<EntryPoint>]\nlet main _ = let entry = listener handler in 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096" && diagnostic.Message.Contains("CallbackDescriptor"))

    [<Fact>]
    member _.``A saturated inline call checks even an unused argument's declared type``() =
        let result =
            match parseAndCheck "module InlineCheck\nlet inline keep (x: int) (y: int) = x\n[<EntryPoint>]\nlet main _ = keep 1 \"bad\"" "inline-check.clef" with
            | Success result | CheckFailure result -> result
            | ParseFailure errors -> failwithf "%A" errors
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Severity = NativeDiagnosticSeverity.Error)

    [<Fact>]
    member _.``Inline names resolve at the definition even when the caller shadows them``() =
        let library = "module Library\nlet helper (x: int) = x + 1\nlet inline apply (first: int) (second: int) = helper (first + second)"
        let application = "module Application\nlet helper (x: string) = x\n[<EntryPoint>]\nlet main _ = Library.apply 3 4"
        let inputs =
            [library, "inline-library.clef"; application, "inline-caller.clef"]
            |> List.map (fun (text, path) ->
                match parseStringWithDefaults text path with
                | ParseSuccess input -> input
                | ParseError errors -> failwithf "%A" errors)
        let result = checkParsedInputs inputs
        DimensionalCases.noErrors result
        Assert.Contains(result.Graph.Nodes.Values, fun node ->
            node.IsReachable && node.Range.File = "inline-library.clef"
            && match node.Kind with SemanticKind.Binding ("helper", _, _, _) -> true | _ -> false)

    [<Fact>]
    member _.``A declared factory cannot escape through an ordinary function alias``() =
        let source = ClosedCallbackCases.declarations
        let result = ClosedCallbackCases.check (source + "\nlet handler (value: int) = ()\n[<EntryPoint>]\nlet main _ =\n    let factory = ClosedCallbacks.makeEntry\n    let entry = factory handler\n    0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096" && diagnostic.Message.Contains("escape"))

    [<Fact>]
    member _.``Inline annotation parameters are fresh at each use``() =
        let source = "module GenericInline\nlet inline keep<'T> (x: 'T) (_y: 'T) =\n    let result: 'T = x\n    result\n[<EntryPoint>]\nlet main _ =\n    let count = keep 1 2\n    let text = keep \"a\" \"b\"\n    count"
        let result =
            match parseAndCheck source "generic-inline.clef" with
            | Success result | CheckFailure result -> result
            | ParseFailure errors -> failwithf "%A" errors
        DimensionalCases.noErrors result

    [<Fact>]
    member _.``Inline measure annotations are fresh at each use``() =
        let source = "module MeasuredInline\n[<Measure>] type m\n[<Measure>] type s\nlet inline keep (x: int<'u>) (_y: int<'u>) =\n    let result: int<'u> = x\n    result\n[<EntryPoint>]\nlet main _ =\n    let length = keep 1<m> 2<m>\n    let time = keep 1<s> 2<s>\n    0"
        let result =
            match parseAndCheck source "measured-inline.clef" with
            | Success result | CheckFailure result -> result
            | ParseFailure errors -> failwithf "%A" errors
        DimensionalCases.noErrors result

    [<Fact>]
    member _.``Specialization cannot discard effects in a factory body``() =
        let source = ClosedCallbackCases.declarations.Replace("NativeEntry = NativeDefault.zeroed ()", "NativeEntry = handler 1; NativeDefault.zeroed ()")
        let result = ClosedCallbackCases.check (source + "\nlet handler (value: int) = ()\n[<EntryPoint>]\nlet main _ = let entry = listener handler in 0\n")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8096" && diagnostic.Message.Contains("exactly NativeDefault.zeroed"))

    [<Fact>]
    member _.``Receiving callback unused native formal preserves ABI64``() =
        let graph = ClosedCallbackCases.receivingGraph ()
        let entry = (read graph).Receiving |> Assert.Single
        let formal, declared = entry.Signature.Parameters |> Assert.Single
        Assert.Equal(64, declared.Value.Bits)
        Assert.Equal(Some(ValueRange.twosComplement 64), graph.Nodes[formal].ValueRange)

        match graph.Nodes[entry.Lambda].Kind with
        | SemanticKind.Lambda(parameters, _, captures, _, _) ->
            Assert.Equal(formal, parameters |> List.exactlyOne |> fun (_, _, id) -> id)
            Assert.Empty captures
        | kind -> failwithf "Expected full callback lambda: %A" kind

        Assert.DoesNotContain(
            graph.Nodes.Values,
            fun node ->
                match node.Kind with
                | SemanticKind.VarRef(_, Some target) -> target = formal
                | _ -> false
        )

        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph with
        | Ok numeric -> Assert.Equal(ValueRange.twosComplement 64, numeric.Values[formal].Range)
        | Result.Error failures -> failwithf "Current incoming numeric evidence refused: %A" failures

    [<Fact>]
    member _.``Receiving callback changed hypothesis invalidates numeric premises``() =
        let graph = ClosedCallbackCases.receivingGraph ()

        let declarations =
            Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.readDescriptors graph

        let invocation = declarations.CallbackInvocations |> Assert.Single

        let _, fields =
            Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.recordOf graph invocation.Node
            |> Option.get

        let _, hypothesis =
            Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.field "Hypothesis" fields
            |> Option.bind (Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.recordOf graph)
            |> Option.get

        let version, _ =
            Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.field "Version" hypothesis
            |> Option.bind (Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.valuePath graph)
            |> Option.get

        let changed =
            { graph with
                Nodes =
                    graph.Nodes.Add(
                        version.Id,
                        { version with
                            Kind = SemanticKind.Literal(NativeLiteral.String "v2")
                        }
                    )
            }

        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project changed with
        | Result.Error failures ->
            Assert.Contains(
                failures,
                fun failure ->
                    failure.Reason =
                        "NumericPublication: Invocation-context range premises changed or the producer receipt is absent; source range settlement is required."
            )
        | Ok _ -> failwith "Changed receiving hypothesis retained old numeric evidence"
