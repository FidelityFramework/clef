namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeService
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private ClosureValues =
    let check source =
        match parseAndCheck ("module ClosureValues\n" + source) "closure-values.clef" with
        | Success result | CheckFailure result ->
            DimensionalCases.noErrors result
            result
        | ParseFailure errors -> failwithf "Parse failed: %A" errors
    let bindingNamed name (result: CheckResult) =
        result.Graph.Nodes |> Map.values |> Seq.find (fun node ->
            node.IsReachable && match node.Kind with
                                | SemanticKind.Binding (bindingName, _, _, _) -> bindingName = name || bindingName.EndsWith("." + name)
                                | _ -> false)
    let rec valueNode (result: CheckResult) id =
        let node = result.Graph.Nodes[id]
        match node.Kind with
        | SemanticKind.TypeAnnotation (child, _) -> valueNode result child
        | _ -> node
    let assertAlias sourceName (result: CheckResult) =
        let saved = bindingNamed "saved" result
        let value = valueNode result saved.Children.Head
        match value.Kind with
        | SemanticKind.VarRef (name, Some _) -> Assert.True(name = sourceName || name.EndsWith("." + sourceName))
        | kind -> failwithf "A function alias must snapshot the referenced value, got %A" kind
        let calls = result.Graph.Nodes |> Map.values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Application (funcId, args) when node.IsReachable ->
                match (valueNode result funcId).Kind with
                | SemanticKind.VarRef (_, Some bindingId) when bindingId = saved.Id -> Some args
                | _ -> None
            | _ -> None) |> Seq.toList
        Assert.Single calls |> ignore
        Assert.Equal(2, calls.Head.Length)
    let expressionLambdas (result: CheckResult) =
        result.Graph.Nodes |> Map.values |> Seq.filter (fun node ->
            node.IsReachable && (node.Metadata |> Map.tryFind ClosureMetadata.LambdaExpression = Some (MetadataValue.Bool true))) |> Seq.toList
    let context: PlatformContext = {
            PlatformId = "closure-test"; Dimensions = Map.ofList ["Pointer", 64; "Register", 64]
            Representations = Map.empty; EndpointReturns = Map.empty; PlatformLibraryPath = None
            PlatformDescription = None; PlatformArchitecture = None; PlatformOS = None
            PlatformSourcePaths = Set.empty
            Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
            AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None }
    let assertPairs (result: CheckResult) =
        let layouts = Clef.Compiler.PSGSaturation.SemanticGraph.Placement.closures (Some context) result.Graph
        let lambdas = expressionLambdas result
        Assert.NotEmpty lambdas
        for node in lambdas do
            Assert.True(layouts.ContainsKey node.Id, $"Anonymous function {node.Id} has no closure placement")
            Assert.Equal(EscapeKind.EscapesViaReturn, result.Graph.Codata.Value.Escapes[node.Id])

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ClosureValues")>]
type ClosureValueTests() =
    [<Fact>]
    member _.``Listener descriptors govern native callback entry scalar width and void result``() =
        let source = """
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Pointer of int | Float of int | Void
type PassBy = Value | Reference
type CallConv = | CDecl
type Transfer = | Borrowed
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type CallbackDescriptor = { Record: string; Field: string; Signature: FunctionDescriptor }
type Listener = { Done: FnPtr<CHandle<unit> -> int -> unit>; Marker: bool }
let mutable observed = 0
let onDone (_data: CHandle<unit>) (serial: int) : unit = observed <- serial
let DoneDescriptor: Expr<CallbackDescriptor> = <@ {
    Record = "Listener"; Field = "Done"
    Signature = { CName = "listener.done"
                  Parameters = [| { Name = "data"; Type = Pointer 64; PassBy = Value }
                                  { Name = "serial"; Type = Integer (Unsigned, 32); PassBy = Value } |]
                  ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Borrowed } } @>
[<EntryPoint>]
let main _ =
    let listener = { Done = FnPtr.ofFunction onDone; Marker = true }
    if listener.Marker then 0 else 1
"""
        let result = ClosureValues.check source
        let declarations = Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations.read result.Graph
        Assert.Empty declarations.Findings
        let callback = Assert.Single declarations.Callbacks
        Assert.True callback.ReturnsVoid
        let serialId, serial = callback.Function.Parameters |> List.pick (fun (id, p) ->
            p |> Option.filter (fun p -> p.Name = "serial") |> Option.map (fun p -> id, p))
        Assert.Equal(32, serial.Bits)
        Assert.Equal(ValueRange.unsignedOf 32, serial.Range)
        Assert.Equal(Some serial.Range, result.Graph.Nodes[serialId].ValueRange)
        let graph = { result.Graph with Platform = Some ClosureValues.context }
        Assert.Equal(Some 32, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth graph serialId)
        let invalid = ClosureValues.check (source.Replace("ReturnType = Void", "ReturnType = Integer (Signed, 32)"))
        let invalidDeclarations = Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations.read invalid.Graph
        Assert.Contains(invalidDeclarations.Findings, fun finding -> finding.Message.Contains("Void result"))
        let wrongPointer = ClosureValues.check (source.Replace("Type = Pointer 64", "Type = Float 64"))
        Assert.Contains((Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations.read wrongPointer.Graph).Findings,
                        fun finding -> finding.Message.Contains("matching Pointer"))
        let otherPlatform = { graph with Platform = Some { ClosureValues.context with Dimensions = Map.ofList ["Pointer", 32; "Register", 64] } }
        Assert.Contains((Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations.read otherPlatform).Findings,
                        fun finding -> finding.Message.Contains("Pointer dimension"))

    [<Fact>]
    member _.``Declared callback ABI follows another address and its indirect scalar results``() =
        let source = """
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Pointer of int | Float of int | Void
type PassBy = Value | Reference
type CallConv = | CDecl
type Transfer = | Borrowed
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
type CallbackDescriptor = { Record: string; Field: string; Signature: FunctionDescriptor }
type Listener = { Apply: FnPtr<int -> int> }
let identity (value: int) : int = value
let ApplyDescriptor: Expr<CallbackDescriptor> = <@ {
    Record = "Listener"; Field = "Apply"
    Signature = { CName = "listener.apply"
                  Parameters = [| { Name = "value"; Type = Integer (Signed, 32); PassBy = Value } |]
                  ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Borrowed } } @>
[<EntryPoint>]
let main _ =
    let listener = { Apply = FnPtr.ofFunction identity }
    let again = FnPtr.ofFunction identity
    let first = FnPtr.invoke listener.Apply -1
    let second = FnPtr.invoke again -2
    if first = -1 && second = -2 then 0 else 1
"""
        let result = ClosureValues.check source
        let graph = { result.Graph with Platform = Some ClosureValues.context }
        let callbacks = Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations.read graph
        Assert.Empty callbacks.Findings
        let calls = graph.Codata.Value.FunctionPointers |> Map.toList |> List.choose (function
            | call, FunctionPointerPlan.Invoke (pointer, _, _, _) -> Some (call, pointer)
            | _ -> None)
        Assert.Equal(2, calls.Length)
        for call, pointer in calls do
            Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations.forPointer graph pointer |> Option.isSome)
            Assert.Equal(Some (ValueRange.twosComplement 32), graph.Nodes[call].ValueRange)
            Assert.Equal(Some 32, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth graph call)
        let wrongResult = ClosureValues.check (source.Replace("ReturnType = Integer (Signed, 32)", "ReturnType = Float 32"))
        Assert.Contains((Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations.read wrongResult.Graph).Findings,
                        fun finding -> finding.Message.Contains("callback result needs a matching scalar"))

    [<Theory>]
    [<InlineData(32)>]
    [<InlineData(64)>]
    member _.``Aggregate function fields retain the entire settled view descriptor``(pointerBits: int) =
        let result = ClosureValues.check """
type Holder = { Work: int -> int -> int; Tail: bool }
[<EntryPoint>]
let main _ =
    let holder = { Work = (fun a b -> a + b); Tail = true }
    if holder.Tail then holder.Work 1 2 else 0
"""
        let context = { ClosureValues.context with Dimensions = Map.ofList ["Pointer", pointerBits; "Register", 64] }
        let graph = Clef.Compiler.PSGSaturation.SemanticGraph.Placement.settle (Some context) result.Graph
        let layout = graph.Layouts.Value |> Map.toSeq |> Seq.pick (fun (name, layout) ->
            if name = "Holder" || name.EndsWith(".Holder") then Some layout else None)
        match layout with
        | SettledLayout.Record ([work; tail], Some size, Some alignment) ->
            let descriptorBytes = 5 * (pointerBits / 8)
            Assert.Equal(SettledSlot.Pointer 5, work.Slot)
            Assert.Equal(Some descriptorBytes, work.Size)
            Assert.Equal(Some descriptorBytes, tail.Offset)
            Assert.True(size >= descriptorBytes + 1)
            Assert.Equal(pointerBits / 8, alignment)
        | other -> failwithf "Expected a fully placed function/boolean record, got %A" other

    [<Fact>]
    member _.``Annotated zero-capture function values receive closure pairs``() =
        let result = ClosureValues.check """
let emptyWork: int -> int -> int = fun _lo _hi -> 0
let emptyRetirement: unit -> unit = fun () -> ()
[<EntryPoint>]
let main _ =
    emptyRetirement ()
    emptyWork 0 1
"""
        ClosureValues.assertPairs result

    [<Fact>]
    member _.``Locally bound anonymous values are not mistaken for nested declarations``() =
        let result = ClosureValues.check """
[<EntryPoint>]
let main _ =
    let failWork = fun (_lo: int) (_hi: int) -> 77
    failWork 0 1
"""
        ClosureValues.assertPairs result

    [<Fact>]
    member _.``Returned zero-capture lambdas retain a live pair``() =
        let result = ClosureValues.check """
let make (choose: bool) =
    if choose then (fun (value: int) -> value)
    else (fun (value: int) -> value + 1)
[<EntryPoint>]
let main _ =
    let callback = make true
    callback 0
"""
        ClosureValues.assertPairs result

    [<Fact>]
    member _.``Named native callback declarations stay direct``() =
        let result = ClosureValues.check """
let identity (value: int) : int = value
[<EntryPoint>]
let main _ = FnPtr.invoke (FnPtr.ofFunction identity) 0
"""
        let symbol, lambda =
            result.Graph.Codata.Value.FunctionPointers |> Map.values |> Seq.pick (function FunctionPointerPlan.Address(symbol, lambda) -> Some(symbol, lambda) | _ -> None)
        Assert.Equal("ClosureValues.identity", symbol)
        Assert.False(result.Graph.Codata.Value.Closures.ContainsKey lambda)

    [<Fact>]
    member _.``A function parameter alias remains a value and receives all arguments together``() =
        let result = ClosureValues.check """
let apply (callback: int -> int -> int) (lo: int) (hi: int) =
    let saved = callback
    saved lo hi
[<EntryPoint>]
let main _ = apply (fun a b -> a + b) 40 2
"""
        ClosureValues.assertAlias "callback" result

    [<Fact>]
    member _.``A mutable function alias snapshots before subsequent assignment``() =
        let result = ClosureValues.check """
let add (a: int) (b: int) = a + b
let subtract (a: int) (b: int) = a - b
let mutable selected: int -> int -> int = add
[<EntryPoint>]
let main _ =
    let saved = selected
    selected <- subtract
    saved 40 2
"""
        ClosureValues.assertAlias "selected" result

    [<Fact>]
    member _.``An anonymous function alias reuses the existing closure value``() =
        let result = ClosureValues.check """
[<EntryPoint>]
let main _ =
    let callback = fun (a: int) (b: int) -> a + b
    let saved = callback
    saved 40 2
"""
        ClosureValues.assertAlias "callback" result

    [<Fact>]
    member _.``A named declaration alias gets a pair with a saturated direct call``() =
        let result = ClosureValues.check """
let add (a: int) (b: int) = a + b
[<EntryPoint>]
let main _ =
    let saved = add
    saved 40 2
"""
        let saved = ClosureValues.bindingNamed "saved" result
        let value = ClosureValues.valueNode result saved.Children.Head
        Assert.Equal(Some (MetadataValue.Bool true), Map.tryFind ClosureMetadata.RequiresClosurePair value.Metadata)
        match value.Kind with
        | SemanticKind.Lambda (parameters, body, captures, _, _) ->
            Assert.Equal(2, parameters.Length)
            Assert.Empty captures
            match (ClosureValues.valueNode result body).Kind with
            | SemanticKind.Application (_, arguments) -> Assert.Equal(2, arguments.Length)
            | kind -> failwithf "Expected saturated declaration call, got %A" kind
        | kind -> failwithf "Expected declaration closure pair, got %A" kind

    [<Fact>]
    member _.``Indirect curried callbacks receive actual argument ranges through a mutable slot``() =
        let result = ClosureValues.check """
let mutable published: int -> int -> int = fun _lo _hi -> 0
let call () =
    let work = published
    work 224 257
let run (work: int -> int -> int) =
    published <- work
    call ()
[<EntryPoint>]
let main _ =
    let output: int array = Array.zeroCreate 258
    let work: int -> int -> int = fun lo hi ->
        let mutable index = lo
        while index < hi do
            Array.set output index 1
            index <- index + 1
        0
    let nested: int -> int -> int = fun lo hi -> work lo hi
    run work + run nested
"""
        let parameters = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.PatternBinding "lo" | SemanticKind.PatternBinding "hi" -> true | _ -> false) |> Seq.toList
        Assert.Equal(4, parameters.Length)
        for parameter in parameters do
            let expected = match parameter.Kind with SemanticKind.PatternBinding "lo" -> 224I | _ -> 257I
            Assert.Equal(Some (ValueRange.point expected), parameter.ValueRange)
        let index = ClosureValues.bindingNamed "index" result
        Assert.NotEqual(Some ValueRange.Empty, index.ValueRange)
        Assert.True(index.ValueRange |> Option.exists (fun range -> ValueRange.contains range (ValueRange.point 224I)))

    [<Fact>]
    member _.``A callback with no observed argument flow keeps the declared register width``() =
        let result = ClosureValues.check """
let keep (callback: int -> int -> int) = 0
[<EntryPoint>]
let main _ =
    let work: int -> int -> int = fun lo hi ->
        let saved = lo
        saved + hi
    keep work
"""
        let saved = ClosureValues.bindingNamed "saved" result
        Assert.Equal(Some ValueRange.Unbounded, saved.ValueRange)
        let graph = { result.Graph with Platform = Some ClosureValues.context }
        Assert.Equal(Some 64, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth graph saved.Id)

    [<Fact>]
    member _.``Immutable binding adapts a uniform callback result before a narrow store``() =
        let result = ClosureValues.check """
let apply (callback: int -> int -> int) =
    let status = callback 0 1
    let mutable failure = 0
    failure <- status
    failure
[<EntryPoint>]
let main _ = apply (fun _lo _hi -> 0)
"""
        let representations = [
            { Name = "int8"; Capability = "native"; Family = "int"; Bits = 8
              MinMagnitude = "-128"; MaxMagnitude = "127"; Boundary = "wrap" }
            { Name = "int64"; Capability = "native"; Family = "int"; Bits = 64
              MinMagnitude = "-9223372036854775808"; MaxMagnitude = "9223372036854775807"; Boundary = "wrap" } ]
        let context = { ClosureValues.context with Representations = representations |> List.map (fun r -> r.Name, r) |> Map.ofList }
        let graph = { result.Graph with Platform = Some context }
        let status = ClosureValues.bindingNamed "status" result
        let call = ClosureValues.valueNode result status.Children.Head
        let width = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth graph
        Assert.Equal(Some 64, width call.Id)
        Assert.Equal(Some 8, width status.Id)
        let meets = Clef.Compiler.PSGSaturation.SemanticGraph.Meets.derive (Some context) graph result.Graph.Codata.Value.Curry
        Assert.True(meets.ContainsKey status.Id, "The immutable alias needs its ABI-to-binding representation meet")
        let conversion = Assert.Single meets[status.Id]
        Assert.Equal(call.Id, conversion.Operand)
        Assert.Equal(64, conversion.From)
        Assert.Equal(8, conversion.To)
        Assert.Equal(MeetKind.Truncate, conversion.Adapt)
