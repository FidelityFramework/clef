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
    let receivingGraphWith wrapper =
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
