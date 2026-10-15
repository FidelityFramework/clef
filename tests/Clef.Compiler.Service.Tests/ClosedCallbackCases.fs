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
    let receivingCheckWith wrapper transform =
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

        let source =
            if wrapper then
                let record =
                    "type NativeRecord = { Handler: FnPtr<int -> int> }\nlet receiveRecord (callback: NativeRecord) = receive callback.Handler\nlet callback (_unused: int) = 7"

                let wrapped = source.Replace("let callback (_unused: int) = 7", record)
                wrapped.Replace("    receive (FnPtr.ofFunction callback)", "    receiveRecord { Handler = FnPtr.ofFunction callback }")
            else
                source

        let source = transform source

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

        result

    let receivingGraphWith wrapper =
        let result = receivingCheckWith wrapper id
        DimensionalCases.noErrors result
        result.Graph

    let pairSource callback (source: string) =
        source
            .Replace("FnPtr<int -> int>", "FnPtr<int -> int -> int>")
            .Replace("Parameters = [| { Name = \"arg0\"; Type = Integer (Signed, 64); PassBy = Value } |]", "Parameters = [| { Name = \"arg0\"; Type = Integer (Signed, 64); PassBy = Value }; { Name = \"arg1\"; Type = Integer (Signed, 64); PassBy = Value } |]")
            .Replace("let callback (_unused: int) = 7", callback)

    let receivingPairGraph useSecond =
        let callback = if useSecond then "let callback (_first: int) (second: int) = second" else "let callback (_first: int) (_second: int) = 7"
        let result = receivingCheckWith false (pairSource callback)
        DimensionalCases.noErrors result
        result.Graph

    let receivingUnitGraph mixed =
        let result =
            receivingCheckWith true (fun source ->
                let source =
                    (pairSource "let callback (_first: int) (_second: int) : unit =\n    let marker = 7\n    ()" source)
                        .Replace("FnPtr<int -> int -> int>", "FnPtr<int -> int -> unit>")
                        .Replace("ReturnType = Integer (Signed, 64); CallingConvention", "ReturnType = Void; CallingConvention")

                if mixed then
                    source
                        .Replace("{ Name = \"arg0\"; Type = Integer (Signed, 64)", "{ Name = \"arg0\"; Type = Integer (Signed, 32)")
                        .Replace("{ Name = \"arg1\"; Type = Integer (Signed, 64)", "{ Name = \"arg1\"; Type = Integer (Unsigned, 64)")
                else
                    source)

        DimensionalCases.noErrors result
        result.Graph

    let receivingZeroCheckWith signature callback =
        receivingCheckWith true (fun source ->
            source
                .Replace("FnPtr<int -> int>", "FnPtr<" + signature + ">")
                .Replace("type EntrySignature =", "type CallbackDescriptor = { Record: string; Field: string; Signature: FunctionDescriptor }\ntype EntrySignature =")
                .Replace("let receiveRecord (callback: NativeRecord)", "let legacyEntry: Expr<CallbackDescriptor> = <@ { Record = \"NativeRecord\"; Field = \"Handler\"; Signature = { CName = \"callback\"; Parameters = [||]; ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared } } @>\nlet receiveRecord (callback: NativeRecord)")
                .Replace("Parameters = [| { Name = \"arg0\"; Type = Integer (Signed, 64); PassBy = Value } |]", "Parameters = [||]")
                .Replace("ReturnType = Integer (Signed, 64); CallingConvention", "ReturnType = Void; CallingConvention")
                .Replace("let callback (_unused: int) = 7", callback))

    let receivingZeroCheck callback =
        receivingZeroCheckWith "unit -> unit" callback

    let receivingGraph () = receivingGraphWith false
    let receivingWrapperGraph () = receivingGraphWith true

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


    [<Fact>]
    member _.``Receiving record projection retains original native callback account``() =
        let graph = ClosedCallbackCases.receivingWrapperGraph ()
        let association = (read graph).Receiving |> Assert.Single

        let boundary =
            match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project graph with
            | Ok boundary -> boundary
            | Result.Error errors -> failwithf "Projected callback source publication refused: %A" errors

        let closed = boundary.ClosedEntries.Values |> Assert.Single
        Assert.Equal(association.Address, closed.Formation)
        Assert.Contains(association.Operand, closed.Transport)

        let projection =
            graph.Codata.Value.CallableAggregateValues[association.Operand] |> Assert.Single

        Assert.Equal(CallableAggregateOperation.Project, projection.Operation)
        Assert.Equal(closed.Formation, projection.Alternatives.Head.Formation)
        let formal = closed.Formals |> Assert.Single
        Assert.Equal(Some(ValueRange.twosComplement 64), graph.Nodes[formal].ValueRange)

        match graph.Nodes[association.Operand].Kind with
        | SemanticKind.FieldGet(_, "Handler") -> ()
        | kind -> failwithf "The generic declared record field was not retained: %A" kind

    [<Fact>]
    member _.``Receiving record projection refuses coherently withdrawn supplier``() =
        let graph = ClosedCallbackCases.receivingWrapperGraph ()
        let association = (read graph).Receiving |> Assert.Single
        let facts = graph.Codata.Value
        let projection = facts.CallableAggregateValues[association.Operand] |> Assert.Single
        let construction = projection.FormationInputs.Head

        let withdrawn =
            { graph with
                Codata =
                    lazy
                        { facts with
                            CallableAggregateValues = facts.CallableAggregateValues.Remove construction
                        }
            }
        // Renew only the held aggregate account. The source Project and native
        // signature remain intact, so an old-account mismatch cannot kill this test.
        let account =
            match Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.author withdrawn association.Operand with
            | Ok account -> account
            | Result.Error reason -> failwith reason

        let renewed =
            { withdrawn.Codata.Value with
                CallableAggregateDependencies = facts.CallableAggregateDependencies.Add(association.Operand, account)
            }

        let changed = { withdrawn with Codata = lazy renewed }

        match Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.current changed association.Operand with
        | Ok _ -> ()
        | Result.Error reason -> failwithf "Coherent account renewal failed: %s" reason

        match Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project changed with
        | Result.Error failures ->
            Assert.Contains(
                failures,
                fun failure -> failure.Reason = "BoundaryEmission: The receiving projection has no exact admitted supplying construction."
            )
        | Ok _ -> failwith "The receiving projection survived withdrawal of its supplying construction"


    [<Fact>]
    member _.``Receiving record account retains ordinary body but excludes foreign placeholder``() =
        let graph = ClosedCallbackCases.receivingWrapperGraph ()
        let association = (read graph).Receiving |> Assert.Single
        let account = graph.Codata.Value.CallableAggregateDependencies[association.Operand]

        let _, wrapper =
            graph.Nodes
            |> Map.toSeq
            |> Seq.find (fun (_, node) ->
                match node.Kind with
                | SemanticKind.Binding("receiveRecord", _, _, _) -> true
                | _ -> false)

        let implementation = graph.Nodes[wrapper.Children |> List.exactlyOne]

        let body =
            match implementation.Kind with
            | SemanticKind.Lambda(_, body, _, _, _) -> body
            | kind -> failwithf "Expected exact ordinary wrapper declaration: %A" kind

        Assert.Contains(account.Sources, fun source -> source.Node = body)

        let foreignBodies =
            graph.Edges
            |> List.choose (fun edge ->
                match edge.Role with
                | EdgeRole.BoundaryDeclaration declaration -> Some declaration.Body
                | _ -> None)

        Assert.NotEmpty foreignBodies

        for placeholder in foreignBodies do
            Assert.DoesNotContain(account.Sources, fun source -> source.Node = placeholder)

        let changed =
            { graph with
                Nodes = graph.Nodes.Remove body
            }

        match Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.current changed association.Operand with
        | Result.Error reason ->
            Assert.Equal("Callable aggregate source support changed after its dependency account was authored (CCS8414).", reason)
        | Ok _ -> failwith "Withdrawing an ordinary wrapper body retained its old dependency account"


    [<Fact>]
    member _.``Receiving record public replay refuses withdrawn projection account``() =
        let graph = ClosedCallbackCases.receivingWrapperGraph ()

        let revision =
            match Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph with
            | Ok revision -> revision
            | Result.Error failures -> failwithf "Source callback revision refused: %A" failures

        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let call = revision.Emission.Boundary.Calls.Values |> Assert.Single

        let operand =
            call.Arguments
            |> List.filter (fun operand ->
                match operand.Abi with
                | Fidelity.PSG.BoundaryScalar.Entry _ -> true
                | _ -> false)
            |> Assert.Single

        let callable = revision.Emission.Callable

        let withdrawn =
            { callable with
                AggregateValues = callable.AggregateValues.Remove operand.Actual
                AggregateDependencies = callable.AggregateDependencies.Remove operand.Actual
            }

        let changed =
            { revision with
                Codata =
                    { revision.Codata with
                        CallableAggregateValues = withdrawn.AggregateValues
                        CallableAggregateDependencies = withdrawn.AggregateDependencies
                    }
                Emission =
                    { revision.Emission with
                        Callable = withdrawn
                    }
            }

        Assert.Contains(
            Fidelity.PSG.Integrity.check changed,
            fun failure ->
                failure.Part = "Emission.Boundary.Calls.CallbackProjection"
                && failure.Reason = "The projected callback argument lacks its exact original closed-entry aggregate account."
        )

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Receiving integer pair preserves every ordered native formal and codec``(useSecond: bool) =
        let graph = ClosedCallbackCases.receivingPairGraph useSecond
        let receiving = (read graph).Receiving |> Assert.Single
        let formals = receiving.Signature.Parameters |> List.map fst
        Assert.Equal(2, formals.Length)
        for formal, declared in receiving.Signature.Parameters do
            Assert.Equal(64, declared.Value.Bits)
            Assert.Equal(Some(ValueRange.twosComplement 64), graph.Nodes[formal].ValueRange)
        match graph.Nodes[receiving.Lambda].Kind with
        | SemanticKind.Lambda(parameters, _, captures, _, _) ->
            Assert.True((parameters |> List.map (fun (_, _, id) -> id)) = formals)
            Assert.Empty captures
        | kind -> failwithf "Expected complete two-formal native lambda: %A" kind
        let uses formal =
            graph.Nodes.Values |> Seq.exists (fun node ->
                match node.Kind with SemanticKind.VarRef(_, Some target) -> target = formal | _ -> false)
        Assert.False(uses formals.Head)
        Assert.Equal(useSecond, uses formals[1])
        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph with
        | Ok numeric ->
            for formal in formals do Assert.Equal(ValueRange.twosComplement 64, numeric.Values[formal].Range)
        | Result.Error failures -> failwithf "Complete incoming pair domains refused: %A" failures
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph
            |> Result.defaultWith (fun errors -> failwithf "Pair source publication refused: %A" errors)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let entry = revision.Emission.Boundary.ClosedEntries.Values |> Assert.Single
        let invocation = revision.Emission.Boundary.CallbackInvocations[entry.Invocation]
        Assert.Equal(2, entry.Formals.Length)
        Assert.Equal(2, entry.ParameterAdaptations.Length)
        Assert.True(invocation.Signature.Parameters = [Fidelity.PSG.BoundaryScalar.Integer(64, true); Fidelity.PSG.BoundaryScalar.Integer(64, true)])
        let limits: Fidelity.PSG.Binary.Limits =
            { MaxBytes = 8 * 1024 * 1024; MaxCollectionLength = 100000; MaxDepth = 128
              MaxStringBytes = 1024 * 1024; MaxBigIntegerBytes = 4096; MaxValues = 2000000 }
        let bytes =
            Fidelity.PSG.Binary.encode limits revision
            |> Result.defaultWith (fun error -> failwithf "Pair codec refused: %A" error)
        let copy =
            Fidelity.PSG.Binary.decode limits bytes
            |> Result.defaultWith (fun error -> failwithf "Pair codec refused: %A" error)
        Assert.True(copy.Emission.Boundary.CallbackInvocations = revision.Emission.Boundary.CallbackInvocations)
        Assert.True(copy.Emission.Boundary.ClosedEntries = revision.Emission.Boundary.ClosedEntries)

    [<Theory>]
    [<InlineData("missing-formal")>]
    [<InlineData("arity")>]
    [<InlineData("order")>]
    [<InlineData("boolean")>]
    [<InlineData("empty")>]
    member _.``Receiving integer pair public account refuses exact withdrawal``(shape: string) =
        let graph = ClosedCallbackCases.receivingPairGraph false
        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph
            |> Result.defaultWith (fun errors -> failwithf "Pair source publication refused: %A" errors)
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let boundary = revision.Emission.Boundary
        let entry = boundary.ClosedEntries.Values |> Assert.Single
        let invocation = boundary.CallbackInvocations[entry.Invocation]
        let changed, part =
            match shape with
            | "missing-formal" ->
                { boundary with ClosedEntries = boundary.ClosedEntries.Add(entry.Formation, {entry with Formals = entry.Formals.Tail; ParameterAdaptations = entry.ParameterAdaptations.Tail}) }, "Emission.Boundary.ClosedEntries.Declaration"
            | "order" ->
                { boundary with ClosedEntries = boundary.ClosedEntries.Add(entry.Formation, {entry with Formals = List.rev entry.Formals; ParameterAdaptations = List.rev entry.ParameterAdaptations}) }, "Emission.Boundary.ClosedEntries.Declaration"
            | "arity" ->
                let invocation = { invocation with Signature = { invocation.Signature with Parameters = invocation.Signature.Parameters.Tail } }
                { boundary with CallbackInvocations = boundary.CallbackInvocations.Add(invocation.Identity, invocation) }, "Emission.Boundary.CallbackInvocations.Signature"
            | "boolean" ->
                let parameters = Array.copy invocation.Contract.Signature.Parameters
                parameters[0] <- { parameters[0] with Type = BAREWire.Descriptors.TypeRef.Bool }
                let invocation =
                    { invocation with
                        Signature = { invocation.Signature with Parameters = Fidelity.PSG.BoundaryScalar.Boolean :: invocation.Signature.Parameters.Tail }
                        Contract = { invocation.Contract with Signature = { invocation.Contract.Signature with Parameters = parameters } } }
                { boundary with CallbackInvocations = boundary.CallbackInvocations.Add(invocation.Identity, invocation) }, "Emission.Boundary.CallbackInvocations.Signature"
            | "empty" ->
                let invocation =
                    { invocation with
                        Signature = { invocation.Signature with Parameters = [] }
                        Contract = { invocation.Contract with Signature = { invocation.Contract.Signature with Parameters = [||] } } }
                { boundary with CallbackInvocations = boundary.CallbackInvocations.Add(invocation.Identity, invocation) }, "Emission.Boundary.CallbackInvocations.Signature"
            | _ -> failwithf "Unknown withdrawal %s" shape
        let changed = { revision with Emission = { revision.Emission with Boundary = changed } }
        let reason =
            if part = "Emission.Boundary.ClosedEntries.Declaration" then
                "The closed entry differs from its original capture-free implementation, body or complete ordered native formals."
            else
                "The callback signature differs from its complete nonempty integer-formal CDecl receiving quotation and exact integer or void result."
        Assert.Contains(Fidelity.PSG.Integrity.check changed, fun error -> error.Part = part && error.Reason = reason)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Receiving unit result preserves full integer domains and an empty native result through codec``(mixed: bool) =
        let graph = ClosedCallbackCases.receivingUnitGraph mixed
        let receiving = (read graph).Receiving |> Assert.Single
        Assert.Equal(2, receiving.Signature.Parameters.Length)
        Assert.True receiving.Signature.Return.IsNone
        let body = receiving.Signature.Body.Value
        Assert.Equal(Some NTUKind.NTUunit, Types.tryGetNTUKind graph.Nodes[body].Type)
        Assert.False(graph.Codata.Value.ReturnMeets.ContainsKey receiving.Lambda)

        let expected =
            if mixed then
                [ ValueRange.twosComplement 32; ValueRange.unsignedOf 64 ]
            else
                [ ValueRange.twosComplement 64; ValueRange.twosComplement 64 ]

        let numeric =
            Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph
            |> Result.defaultWith (fun errors -> failwithf "Unit incoming domains refused: %A" errors)

        for (formal, declared), domain in List.zip receiving.Signature.Parameters expected do
            Assert.Equal(domain, declared.Value.Range)
            Assert.Equal(domain, numeric.Values[formal].Range)

        Assert.False(numeric.Values.ContainsKey body)

        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph
            |> Result.defaultWith (fun errors -> failwithf "Unit source publication refused: %A" errors)

        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let entry = revision.Emission.Boundary.ClosedEntries.Values |> Assert.Single
        let invocation = revision.Emission.Boundary.CallbackInvocations[entry.Invocation]
        Assert.Equal(BAREWire.Descriptors.TypeRef.Void, invocation.Contract.Signature.ReturnType)
        Assert.True(invocation.Signature.Result.IsNone && entry.ResultAdaptation.IsNone)
        Assert.True(Fidelity.PSG.TypeIdentity.isUnit revision.Nodes[entry.Body].Type)
        Assert.Contains(entry.Body, revision.Emission.Callable.UnitNodes)
        Assert.Equal(2, entry.Formals.Length)
        Assert.False(revision.Emission.Numeric.Values.ContainsKey entry.Body)

        let limits: Fidelity.PSG.Binary.Limits =
            {
                MaxBytes = 8 * 1024 * 1024
                MaxCollectionLength = 100000
                MaxDepth = 128
                MaxStringBytes = 1024 * 1024
                MaxBigIntegerBytes = 4096
                MaxValues = 2000000
            }

        let bytes =
            Fidelity.PSG.Binary.encode limits revision
            |> Result.defaultWith (fun error -> failwithf "%A" error)

        let copy =
            Fidelity.PSG.Binary.decode limits bytes
            |> Result.defaultWith (fun error -> failwithf "%A" error)

        Assert.True(revision.Emission.Boundary = copy.Emission.Boundary)

    [<Theory>]
    [<InlineData("missing-void")>]
    [<InlineData("body")>]
    [<InlineData("unit-fact")>]
    [<InlineData("result")>]
    member _.``Receiving unit public account refuses missing void or actual unit evidence``(shape: string) =
        let revision =
            ClosedCallbackCases.receivingUnitGraph false
            |> Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish
            |> Result.defaultWith (fun errors -> failwithf "Unit source publication refused: %A" errors)

        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let boundary = revision.Emission.Boundary
        let entry = boundary.ClosedEntries.Values |> Assert.Single
        let invocation = boundary.CallbackInvocations[entry.Invocation]

        let withInvocation (invocation: Fidelity.PSG.BoundaryCallbackInvocation) =
            { revision with
                Emission =
                    { revision.Emission with
                        Boundary =
                            { boundary with
                                CallbackInvocations = boundary.CallbackInvocations.Add(invocation.Identity, invocation)
                            }
                    }
            }

        let changed, part, reason =
            if shape = "missing-void" || shape = "result" then
                let invocation =
                    if shape = "missing-void" then
                        { invocation with
                            Contract =
                                { invocation.Contract with
                                    Signature =
                                        { invocation.Contract.Signature with
                                            ReturnType = BAREWire.Descriptors.TypeRef.Pointer 64
                                        }
                                }
                        }
                    else
                        { invocation with
                            Signature =
                                { invocation.Signature with
                                    Result = Some(Fidelity.PSG.BoundaryScalar.Integer(64, true))
                                }
                        }

                withInvocation invocation,
                "Emission.Boundary.CallbackInvocations.Signature",
                "The callback signature differs from its complete nonempty integer-formal CDecl receiving quotation and exact integer or void result."
            else
                let changed =
                    if shape = "unit-fact" then
                        { revision with
                            Emission =
                                { revision.Emission with
                                    Callable =
                                        { revision.Emission.Callable with
                                            UnitNodes = revision.Emission.Callable.UnitNodes.Remove entry.Body
                                        }
                                }
                        }
                    else
                        let body = revision.Nodes[entry.Body]

                        let wrongType =
                            match body.Type with
                            | Fidelity.PSG.TypeIdentity.Application(constructor, arguments) ->
                                Fidelity.PSG.TypeIdentity.Application(
                                    { constructor with
                                        NativeKind = Some Fidelity.PSG.NTUKind.NTUbool
                                    },
                                    arguments
                                )
                            | _ -> failwith "Expected the actual source unit type."

                        { revision with
                            Nodes = revision.Nodes.Add(entry.Body, { body with Type = wrongType })
                        }

                changed,
                "Emission.Boundary.ClosedEntries.UnitResult",
                "A void native callback requires its actual unit source body and no numeric result or return adaptation."

        let failures = Fidelity.PSG.Integrity.check changed
        Assert.Contains(failures, fun error -> error.Part = part && error.Reason = reason)
        if shape = "missing-void" then Assert.Single failures |> ignore

    [<Fact>]
    member _.``Receiving integer pair refuses source callback with missing native formal``() =
        let result =
            ClosedCallbackCases.receivingCheckWith false
                (ClosedCallbackCases.pairSource "let callback (_first: int) = 7")
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8207" && diagnostic.Message.Contains("declares 2 parameters; the binding takes 1"))
        Assert.Empty(result.Graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryClosedEntry entry -> Some entry | _ -> None))

    [<Fact>]
    member _.``Mixed receiving callback blocks publish immediate meets without a duplicate return cast``() =
        let callback =
            """let callback (first: int) (second: int) =
    let marker = second
    if first < 0 then
        if second > 9223372036854775807 then 4294967295 else 0
    else 0"""

        let result =
            ClosedCallbackCases.receivingCheckWith false (fun source ->
                let paired = ClosedCallbackCases.pairSource callback source

                paired
                    .Replace("{ Name = \"arg0\"; Type = Integer (Signed, 64)", "{ Name = \"arg0\"; Type = Integer (Signed, 32)")
                    .Replace("{ Name = \"arg1\"; Type = Integer (Signed, 64)", "{ Name = \"arg1\"; Type = Integer (Unsigned, 64)")
                    .Replace("ReturnType = Integer (Signed, 64)", "ReturnType = Integer (Unsigned, 32)"))

        DimensionalCases.noErrors result
        let graph = result.Graph
        let receiving = (read graph).Receiving |> Assert.Single
        let body = receiving.Signature.Body.Value

        let child =
            match graph.Nodes[body].Kind with
            | SemanticKind.Sequential values -> List.last values
            | kind -> failwithf "Expected source block, got %A" kind

        let bodyMeet = graph.Codata.Value.Meets[body] |> Assert.Single
        Assert.Equal(body, bodyMeet.Consumer)
        Assert.Equal(child, bodyMeet.Operand)
        Assert.Equal(64, bodyMeet.From)
        Assert.Equal(32, bodyMeet.To)
        Assert.Equal(MeetKind.Truncate, bodyMeet.Adapt)
        Assert.False(graph.Codata.Value.ReturnMeets.ContainsKey receiving.Lambda)

        let numeric =
            Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph
            |> Result.defaultWith (sprintf "%A" >> failwith)

        Assert.Equal(ValueRange.Bounded(0I, 4294967295I), numeric.Values[body].Range)
        Assert.Equal(SettledSlot.Integer(32, Some "unsigned32"), numeric.Values[body].Slot)
        Assert.NotEmpty numeric.Values[body].Obligations

        for formal, declared in receiving.Signature.Parameters do
            Assert.Equal(Some declared.Value.Range, graph.Nodes[formal].ValueRange)

        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph
            |> Result.defaultWith (sprintf "%A" >> failwith)

        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let native = revision.Emission.Boundary.ClosedEntries.Values |> Assert.Single
        Assert.True(native.ResultAdaptation.IsNone)

        Assert.Equal(
            [ 32; 64 ],
            revision.Emission.Boundary.CallbackInvocations[native.Invocation].Signature.Parameters
            |> List.map (function
                | Fidelity.PSG.BoundaryScalar.Integer(bits, _) -> bits
                | value -> failwithf "%A" value)
        )

        let publishedMeet = revision.Codata.Meets[Fidelity.PSG.NodeId(NodeId.value body)] |> Assert.Single
        Assert.Equal(Fidelity.PSG.NodeId(NodeId.value bodyMeet.Consumer), publishedMeet.Consumer)
        Assert.Equal(Fidelity.PSG.NodeId(NodeId.value bodyMeet.Operand), publishedMeet.Operand)
        Assert.Equal(bodyMeet.From, publishedMeet.From)
        Assert.Equal(bodyMeet.To, publishedMeet.To)
        let withdrawn = { graph with Platform = None }

        let derives =
            Clef.Compiler.PSGSaturation.SemanticGraph.Meets.derive None withdrawn withdrawn.Codata.Value.Curry

        Assert.False(derives.ContainsKey body)

        match Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project withdrawn with
        | Result.Error failures ->
            Assert.Contains(failures, fun failure -> failure.Reason = "NumericPublication: Invocation-context range premises changed or the producer receipt is absent; source range settlement is required.")
        | Ok _ -> failwith "Withdrawn selected platform retained current mixed carrier evidence"

    [<Fact>]
    member _.``Equal native block carrier does not fabricate a forwarding or return meet``() =
        let graph =
            ClosedCallbackCases.receivingCheckWith false (fun source ->
                source.Replace("let callback (_unused: int) = 7", "let callback (_unused: int) =\n    let value = _unused\n    value"))

        DimensionalCases.noErrors graph
        let receiving = (read graph.Graph).Receiving |> Assert.Single
        let body = receiving.Signature.Body.Value
        Assert.False(graph.Graph.Codata.Value.Meets.ContainsKey body)
        Assert.False(graph.Graph.Codata.Value.ReturnMeets.ContainsKey receiving.Lambda)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Sole source unit formal is retained while its native vector is empty``(used: bool) =
        let callback =
            if used then
                "let callback (value: unit) : unit =\n    let marker = 7\n    value"
            else
                "let callback (_unused: unit) : unit = ()"

        let result = ClosedCallbackCases.receivingZeroCheck callback
        DimensionalCases.noErrors result

        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph
            |> Result.defaultWith (fun errors -> failwithf "Sole unit publication refused: %A" errors)

        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let entry = revision.Emission.Boundary.ClosedEntries.Values |> Assert.Single
        let formal = entry.Formals |> Assert.Single
        let invocation = revision.Emission.Boundary.CallbackInvocations[entry.Invocation]
        let carrier = revision.Emission.Callable.Carriers[entry.Formation]

        let contract =
            carrier.Contract
            |> Result.defaultWith failwith
            |> fun identity -> revision.Emission.Callable.Contracts[identity]

        Assert.Empty invocation.Contract.Signature.Parameters
        Assert.Empty invocation.Signature.Parameters
        Assert.Equal(BAREWire.Descriptors.TypeRef.Void, invocation.Contract.Signature.ReturnType)
        Assert.True invocation.Signature.Result.IsNone
        Assert.True(Set.singleton formal = carrier.OmittedParameters)
        Assert.Equal<int list>([ 0 ], contract.OmittedParameters)
        Assert.Empty contract.ParameterRepresentations
        Assert.True(Fidelity.PSG.TypeIdentity.isUnit revision.Nodes[formal].Type)
        Assert.Contains(formal, revision.Emission.Callable.UnitNodes)
        Assert.Equal<Fidelity.PSG.Meet option list>([ None ], entry.ParameterAdaptations)
        Assert.True(entry.ResultAdaptation.IsNone)
        Assert.False(revision.Emission.Numeric.Values.ContainsKey formal)
        Assert.False(revision.Emission.Numeric.Values.ContainsKey entry.Body)

        let limits: Fidelity.PSG.Binary.Limits =
            {
                MaxBytes = 8 * 1024 * 1024
                MaxCollectionLength = 100000
                MaxDepth = 128
                MaxStringBytes = 1024 * 1024
                MaxBigIntegerBytes = 4096
                MaxValues = 2000000
            }

        let bytes =
            Fidelity.PSG.Binary.encode limits revision
            |> Result.defaultWith (fun error -> failwithf "%A" error)

        let copy =
            Fidelity.PSG.Binary.decode limits bytes
            |> Result.defaultWith (fun error -> failwithf "%A" error)

        Assert.Equal(revision.Emission.Boundary, copy.Emission.Boundary)
        Assert.True(carrier.OmittedParameters = copy.Emission.Callable.Carriers[entry.Formation].OmittedParameters)

    [<Theory>]
    [<InlineData("let callback (_unused: int) : unit = ()")>]
    [<InlineData("let callback (_first: unit) (_second: unit) : unit = ()")>]
    member _.``Empty native vector refuses a source formal vector without exact sole unit``(callback: string) =
        let signature =
            if callback.Contains("_first") then
                "unit -> unit -> unit"
            else
                "int -> unit"

        let result = ClosedCallbackCases.receivingZeroCheckWith signature callback

        Assert.Contains(
            result.Diagnostics,
            fun diagnostic ->
                diagnostic.Code = "CCS8413"
                && diagnostic.Message = "Callable receiving convention has not been settled by its source recipe."
        )

    [<Theory>]
    [<InlineData("type")>]
    [<InlineData("representation")>]
    [<InlineData("unit-fact")>]
    [<InlineData("convention")>]
    member _.``Sole unit public erasure refuses withdrawn exact formal premises``(shape: string) =
        let result =
            ClosedCallbackCases.receivingZeroCheck "let callback (value: unit) : unit = value"

        DimensionalCases.noErrors result

        let revision =
            Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph
            |> Result.defaultWith (fun errors -> failwithf "%A" errors)

        let entry = revision.Emission.Boundary.ClosedEntries.Values |> Assert.Single
        let formal = entry.Formals |> Assert.Single

        let changed =
            match shape with
            | "convention" ->
                let boundary = revision.Emission.Boundary
                let invocation = boundary.CallbackInvocations[entry.Invocation]

                let invocation =
                    { invocation with
                        Signature =
                            { invocation.Signature with
                                CallingConvention = "not-CDecl"
                            }
                    }

                { revision with
                    Emission =
                        { revision.Emission with
                            Boundary =
                                { boundary with
                                    CallbackInvocations = boundary.CallbackInvocations.Add(entry.Invocation, invocation)
                                }
                        }
                }
            | "type" ->
                let body = revision.Nodes[formal]

                let integer =
                    revision.Nodes.Values
                    |> Seq.find (fun node ->
                        not (Fidelity.PSG.TypeIdentity.isUnit node.Type)
                        && revision.Emission.Numeric.Values.ContainsKey node.Id)

                { revision with
                    Nodes = revision.Nodes.Add(formal, { body with Type = integer.Type })
                }
            | "representation" ->
                { revision with
                    Emission =
                        { revision.Emission with
                            Numeric =
                                { revision.Emission.Numeric with
                                    OccurrenceRepresentations = revision.Emission.Numeric.OccurrenceRepresentations.Remove formal
                                }
                        }
                }
            | _ ->
                { revision with
                    Emission =
                        { revision.Emission with
                            Callable =
                                { revision.Emission.Callable with
                                    UnitNodes = revision.Emission.Callable.UnitNodes.Remove formal
                                }
                        }
                }

        let part, reason =
            if shape = "convention" then
                "Emission.Boundary.CallbackInvocations.Signature",
                "The callback signature differs from its complete nonempty integer-formal CDecl receiving quotation and exact integer or void result."
            else
                "Emission.Boundary.ClosedEntries.UnitParameters",
                "A zero-argument void callback requires its exact sole source unit formal and current unit representation."

        Assert.Contains(Fidelity.PSG.Integrity.check changed, fun issue -> issue.Part = part && issue.Reason = reason)
