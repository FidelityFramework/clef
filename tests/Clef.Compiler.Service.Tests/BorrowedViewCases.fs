namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeService
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph

module private BorrowedViewCases =
    let prefix = """module BorrowedViewTests
type Pixel = private | Pixel
type Repr = string
type Access = string
type ViewLayoutDescriptor = { Schema: string; Element: Repr; Alignment: int; Access: Access }
type ScopedCallbackDescriptor = { Binding: string; Parameter: string }
let pixelLayout: Expr<ViewLayoutDescriptor> = <@ { Schema = "BorrowedViewTests.Pixel"; Element = "u32"; Alignment = 4; Access = "rw" } @>
let withView (work: BorrowedView<Pixel> -> int) : int = NativeDefault.zeroed ()
let viewScope: Expr<ScopedCallbackDescriptor> = <@ { Binding = "BorrowedViewTests.withView"; Parameter = "work" } @>
"""
    let check text =
        match parseAndCheck text "borrowed-view.clef" with
        | Success result | CheckFailure result ->
            DimensionalCases.noErrors result
            result
        | ParseFailure errors -> failwithf "Parse failed: %A" errors
    let source body = check (prefix + body)
    let context: PlatformContext = {
        PlatformId = "borrowed-test"; Dimensions = Map.ofList ["Pointer", 64; "Register", 64]
        Representations = Map.empty; EndpointReturns = Map.empty; PlatformLibraryPath = None
        PlatformDescription = None; PlatformArchitecture = None; PlatformOS = None
        PlatformSourcePaths = Set.empty
        Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
        AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None }

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "BorrowedViews")>]
type BorrowedViewTests() =
    [<Fact>]
    member _.``Nominal schema governs physical loads and synchronous capture placement``() =
        let result = BorrowedViewCases.source """
let consume (store: int -> int -> unit) =
    store 0 4294967295
    0
let render (view: BorrowedView<Pixel>) =
    let store = fun (index: int) (value: int) -> BorrowedView.set view index value
    let value = BorrowedView.get view 0
    if value <= 4294967295 then consume store else 1
[<EntryPoint>]
let main _ = withView (fun view -> render view)
"""
        let graph = { result.Graph with Platform = Some BorrowedViewCases.context }
        let scopes = ScopedCallbacks.read graph
        Assert.Empty scopes.Findings
        Assert.True(scopes.StackLambdas.Count >= 2)
        let loads = graph.Nodes.Values |> Seq.filter (fun n ->
            n.IsReachable && (BorrowedViews.operation graph n.Id |> Option.exists (fun (op, _, _, _) -> op = "get"))) |> Seq.toList
        let load = Assert.Single loads
        Assert.Equal(Some (ValueRange.unsignedOf 32), load.ValueRange)
        Assert.Equal(Some 32, RangeAnalysis.heldWidth graph load.Id)
        let escapes = Escape.analyze graph
        for lambda in scopes.StackLambdas do
            if escapes.ContainsKey lambda then Assert.Equal(EscapeKind.StackScoped, escapes[lambda])

    [<Fact>]
    member _.``Borrowed view cannot be stored in an optional global``() =
        let result = BorrowedViewCases.source """
let mutable escaped: option<BorrowedView<Pixel>> = None
[<EntryPoint>]
let main _ = withView (fun view -> escaped <- Some view; 0)
"""
        Assert.Contains((ScopedCallbacks.read result.Graph).Findings, fun f -> f.Message.Contains("escapes its mapping scope"))

    [<Fact>]
    member _.``Closure capturing a view cannot enter a retaining callback consumer``() =
        let result = BorrowedViewCases.source """
let mutable saved: unit -> int = fun () -> 0
let retain callback = saved <- callback; 0
[<EntryPoint>]
let main _ = withView (fun view -> retain (fun () -> BorrowedView.length view))
"""
        Assert.Contains((ScopedCallbacks.read result.Graph).Findings, fun f -> f.Message.Contains("escapes its mapping scope"))

    [<Fact>]
    member _.``A callable stored by a startup initializer after its slot is ordered by its formation phase``() =
        // The storing closure is formed inside `primed`'s initializer, which runs after `saved`'s
        // (static initializers run in compilation order), and again inside the entry, which runs
        // after every initializer. Neither needs the boundary to declare an invocation: the
        // formation phase bounds the invocation phase from below.
        let result = BorrowedViewCases.source """
let mutable saved: unit -> int = fun () -> 0
let retain callback = saved <- callback; 0
let primed = retain (fun () -> 1)
[<EntryPoint>]
let main _ = withView (fun view -> retain (fun () -> BorrowedView.length view)) + primed
"""
        Assert.Contains((ScopedCallbacks.read result.Graph).Findings, fun f -> f.Message.Contains("escapes its mapping scope"))

    [<Fact>]
    member _.``Borrowed view cannot be manufactured with a default value``() =
        let result = BorrowedViewCases.source """
[<EntryPoint>]
let main _ =
    let view: BorrowedView<Pixel> = NativeDefault.zeroed ()
    ignore view
    0
"""
        // The finding is about the view's origin. Committing its length would add an
        // unobservable integer on a context declaring no Pointer width (CCS8011), which is
        // not what this case guards.
        Assert.Contains((ScopedCallbacks.read result.Graph).Findings, fun f -> f.Message.Contains("no source constructor"))

    [<Fact>]
    member _.``A borrowed view's length is a length bounded by the platform's pointer width``() =
        // Positive control for `BorrowedViews.numericBoundary`: on a context declaring a Pointer width a
        // committed view length is the declared extent `[0, 2^(Pointer-1) - 1]`.
        let views =
            BorrowedViewCases.prefix.Replace("module BorrowedViewTests\n", "").Replace("BorrowedViewTests.", "SequenceProgram.")
        let source = SequenceProgramFixture.header + views + "[<EntryPoint>]\nlet main _ = withView (fun view -> if BorrowedView.length view >= 0 then 0 else 1)\n"
        let input =
            match parseStringWithDefaults source SequenceProgramFixture.file with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Parse failed: %A" errors
        let result = checkParsedInputsWithPlatform [input] (Some SequenceProgramFixture.context)
        DimensionalCases.noErrors result
        let length =
            result.Graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable &&
                match node.Kind with
                | SemanticKind.Application(callee, _) ->
                    match result.Graph.Nodes.TryFind callee with
                    | Some { Kind = SemanticKind.Intrinsic info } -> info.Module = IntrinsicModule.BorrowedView && info.Operation = "length"
                    | _ -> false
                | _ -> false) |> Assert.Single
        Assert.Equal(Some(ValueRange.Bounded(0I, bigint.Pow(2I, 63) - 1I)), length.ValueRange)

    [<Fact>]
    member _.``A committed view length is unobservable on a context declaring no pointer width``() =
        // Negative control: without a platform there is no declared extent and no length range, so a
        // length the entry commits refuses at the length's own commitment. The view is manufactured
        // here because a callback handed to the `withView` stub is never invoked and commits nothing.
        let result =
            match parseAndCheck (BorrowedViewCases.prefix + "[<EntryPoint>]\nlet main _ =\n    let view: BorrowedView<Pixel> = NativeDefault.zeroed ()\n    BorrowedView.length view\n") "borrowed-view.clef" with
            | Success result | CheckFailure result -> result
            | ParseFailure errors -> failwithf "Parse failed: %A" errors
        let errors = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.CheckResult.errors result
        Assert.NotEmpty errors
        Assert.All(errors, fun diagnostic -> Assert.Equal("CCS8011", diagnostic.Code))
        Assert.Contains(errors, fun diagnostic -> diagnostic.Message.Contains "'length'")

    [<Fact>]
    member _.``Read-only view rejects a store``() =
        let text = BorrowedViewCases.prefix.Replace("Access = \"rw\"", "Access = \"ro\"") + """
[<EntryPoint>]
let main _ = withView (fun view -> BorrowedView.set view 0 1; 0)
"""
        let result = BorrowedViewCases.check text
        Assert.Contains((ScopedCallbacks.read result.Graph).Findings, fun f -> f.Message.Contains("does not declare write access"))

    [<Fact>]
    member _.``Returned closure cannot carry a borrowed view out of a helper``() =
        let result = BorrowedViewCases.source """
let retain view = fun () -> BorrowedView.length view
[<EntryPoint>]
let main _ = withView (fun view -> let saved = retain view in saved ())
"""
        let scopes = ScopedCallbacks.read result.Graph
        Assert.Contains(scopes.Findings, fun f -> f.Message.Contains("escapes its mapping scope"))

    [<Fact>]
    member _.``Exactly resolved synchronous consumer retains borrowed capture scope``() =
        let result = BorrowedViewCases.source """
let forward (unknown: (unit -> int) -> int) (view: BorrowedView<Pixel>) =
    unknown (fun () -> BorrowedView.length view)
[<EntryPoint>]
let main _ = withView (fun view -> forward (fun callback -> callback ()) view)
"""
        Assert.Empty((ScopedCallbacks.read result.Graph).Findings)

    [<Theory>]
    [<InlineData("declaration")>]
    [<InlineData("parameter")>]
    [<InlineData("root")>]
    [<InlineData("external")>]
    member _.``Synchronous callback activation retracts when its declaring or incoming authority changes`` defect =
        let result = BorrowedViewCases.source """
let forward (unknown: (unit -> int) -> int) (view: BorrowedView<Pixel>) =
    unknown (fun () -> BorrowedView.length view)
[<EntryPoint>]
let main _ = withView (fun view -> forward (fun callback -> callback ()) view)
"""
        let graph = result.Graph
        Assert.Empty((ScopedCallbacks.read graph).Findings)
        let forward = graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.Binding("forward", _, _, _) -> true | _ -> false)
        let contract = graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.Binding("viewScope", _, _, _) -> true | _ -> false)
        let formal = graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.PatternBinding "unknown" -> true | _ -> false)
        let proof = CallableIngress.tryEvidence (CallableIngress.analyze graph) formal.Id |> Option.get
        Assert.Contains(contract.Id, proof.Participants)
        let changed =
            match defect with
            | "declaration" ->
                { graph with Nodes = graph.Nodes.Add(contract.Id, { contract with Kind = SemanticKind.PatternBinding "removedContract"; Children = [] }) }
            | "parameter" ->
                let parameterName = graph.Nodes.Values |> Seq.find (fun node ->
                    match node.Kind with SemanticKind.Literal(NativeLiteral.String "work") -> true | _ -> false)
                { graph with Nodes = graph.Nodes.Add(parameterName.Id, { parameterName with Kind = SemanticKind.Literal(NativeLiteral.String "missing") }) }
            | "root" ->
                { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramInitialization) }
            | _ ->
                { graph with DeclarationRoots = (forward.Id, DeclRoot.KernelModule) :: graph.DeclarationRoots }
        Assert.False(CallableIngress.allowsOccurrence (CallableIngress.analyze changed) formal.Id)
        Assert.Contains((ScopedCallbacks.read changed).Findings, fun finding -> finding.Message.Contains("escapes its mapping scope"))
        Assert.True(CallableIngress.allowsOccurrence (CallableIngress.analyze graph) formal.Id)

    [<Fact>]
    member _.``A factory declaration cannot grant scope to a returned function parameter``() =
        let text = BorrowedViewCases.prefix + """
let factory seed = fun (callback: int -> int) -> callback seed
let returnedScope: Expr<ScopedCallbackDescriptor> = <@ { Binding = "BorrowedViewTests.factory"; Parameter = "callback" } @>
[<EntryPoint>]
let main _ = factory 0 (fun value -> value)
"""
        let result =
            match parseAndCheck text "borrowed-returned-contract.clef" with
            | Success result | CheckFailure result -> result
            | ParseFailure errors -> failwithf "Parse failed: %A" errors
        let reading = ScopedDeclarations.read result.Graph
        Assert.Contains(reading.Findings, fun finding -> finding.Message.Contains("missing from the declared callable boundary"))
        for node in result.Graph.Nodes.Values do
            match node.Kind with
            | SemanticKind.PatternBinding "callback" -> Assert.DoesNotContain(node.Id, reading.Parameters)
            | _ -> ()

    [<Fact>]
    member _.``Unknown function consumer cannot receive a borrowed capture``() =
        let result = BorrowedViewCases.source """
let opaque () : (unit -> int) -> int = NativeDefault.zeroed ()
let forward (unknown: (unit -> int) -> int) (view: BorrowedView<Pixel>) =
    unknown (fun () -> BorrowedView.length view)
[<EntryPoint>]
let main _ = withView (fun view -> forward (opaque ()) view)
"""
        Assert.Contains((ScopedCallbacks.read result.Graph).Findings, fun f -> f.Message.Contains("escapes its mapping scope"))

    [<Fact>]
    member _.``One synchronous actual does not hide a retaining consumer alternative``() =
        let result = BorrowedViewCases.source """
let mutable saved: unit -> int = fun () -> 0
let retain callback = saved <- callback; 0
let forward (unknown: (unit -> int) -> int) (view: BorrowedView<Pixel>) =
    unknown (fun () -> BorrowedView.length view)
[<EntryPoint>]
let main _ = withView (fun view -> forward (fun callback -> callback ()) view; forward retain view)
"""
        Assert.Contains((ScopedCallbacks.read result.Graph).Findings, fun f -> f.Message.Contains("escapes its mapping scope"))

    [<Fact>]
    member _.``Write-only view rejects a load``() =
        let text = BorrowedViewCases.prefix.Replace("Access = \"rw\"", "Access = \"wo\"") + """
[<EntryPoint>]
let main _ = withView (fun view -> BorrowedView.get view 0)
"""
        let result = BorrowedViewCases.check text
        Assert.Contains((ScopedCallbacks.read result.Graph).Findings, fun f -> f.Message.Contains("does not declare read access"))

    [<Fact>]
    member _.``Match branches cannot hide an escaping closure``() =
        let result = BorrowedViewCases.source """
let retain view = match 0 with | 0 -> (fun () -> BorrowedView.length view) | _ -> (fun () -> 0)
[<EntryPoint>]
let main _ = withView (fun view -> let saved = retain view in saved ())
"""
        Assert.Contains((ScopedCallbacks.read result.Graph).Findings, fun f -> f.Message.Contains("escapes its mapping scope"))

    [<Fact>]
    member _.``Partially applied view getter cannot be retained``() =
        let result = BorrowedViewCases.source """
let mutable getter: int -> int = fun _ -> 0
[<EntryPoint>]
let main _ = withView (fun view -> getter <- BorrowedView.get view; 0)
"""
        Assert.Contains((ScopedCallbacks.read result.Graph).Findings, fun f -> f.Message.Contains("escapes its mapping scope"))

    [<Fact>]
    member _.``Fully saturated helper remains a synchronous borrower``() =
        let result = BorrowedViewCases.source """
let readAt (view: BorrowedView<Pixel>) = fun (index: int) -> BorrowedView.get view index
[<EntryPoint>]
let main _ = withView (fun view -> readAt view 0)
"""
        Assert.Empty((ScopedCallbacks.read result.Graph).Findings)
        // The lifetime proof must span the two actual callable boundaries;
        // flattening away the returned function is not its justification.
        Assert.Contains(result.Graph.Nodes.Values, fun node ->
            node.IsReachable && match node.Kind with
                                | SemanticKind.Application (callee, [_]) ->
                                    match Core.SemanticGraph.tryGetNode callee result.Graph with
                                    | Some { Kind = SemanticKind.Application (_, [_]); Type = NativeType.TFun _ } -> true
                                    | _ -> false
                                | _ -> false)

    [<Fact>]
    member _.``Immediately completed unit closure remains a synchronous borrower``() =
        let result = BorrowedViewCases.source """
let readLength (view: BorrowedView<Pixel>) = fun () -> BorrowedView.length view
[<EntryPoint>]
let main _ = withView (fun view -> readLength view ())
"""
        let scopes = ScopedCallbacks.read result.Graph
        Assert.Empty scopes.Findings
        let returned = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with
                                | SemanticKind.Lambda ([(_, NativeType.TApp ({ NTUKind = Some NTUKind.NTUunit }, []), _)], _, captures, _, _) -> not captures.IsEmpty
                                | _ -> false) |> Assert.Single
        // Synchronous borrowing does not permit allocating this environment in
        // the helper frame that has already returned before the unit call.
        Assert.False(scopes.StackLambdas.Contains returned.Id)
        Assert.Equal(EscapeKind.EscapesViaReturn, (Escape.analyze result.Graph)[returned.Id])

    [<Fact>]
    member _.``One saturated use does not authorize retaining the same helper result``() =
        let result = BorrowedViewCases.source """
let readAt (view: BorrowedView<Pixel>) = fun (index: int) -> BorrowedView.get view index
[<EntryPoint>]
let main _ = withView (fun view ->
    let immediate = readAt view 0
    let retained = readAt view
    immediate + retained 0)
"""
        Assert.Contains((ScopedCallbacks.read result.Graph).Findings, fun f -> f.Message.Contains("escapes its mapping scope"))

    [<Fact>]
    member _.``Returned helper closure cannot be forwarded through an unknown consumer``() =
        let result = BorrowedViewCases.source """
let readAt (view: BorrowedView<Pixel>) = fun (index: int) -> BorrowedView.get view index
let forward (unknown: (int -> int) -> int) (view: BorrowedView<Pixel>) =
    unknown (readAt view)
[<EntryPoint>]
let main _ = withView (fun view -> forward (fun callback -> callback 0) view)
"""
        Assert.Contains((ScopedCallbacks.read result.Graph).Findings, fun f -> f.Message.Contains("escapes its mapping scope"))

    [<Fact>]
    member _.``Default record cannot manufacture a nested view``() =
        let result = BorrowedViewCases.source """
type Holder = { Pixels: BorrowedView<Pixel> }
[<EntryPoint>]
let main _ =
    let holder: Holder = NativeDefault.zeroed ()
    ignore holder.Pixels
    0
"""
        Assert.Contains((ScopedCallbacks.read result.Graph).Findings, fun f -> f.Message.Contains("no source constructor"))

    [<Fact>]
    member _.``Malformed unreachable scoped quotation cannot silently lose its contract``() =
        let source = """module MalformedScope
module Vocabulary =
    type ScopedCallbackDescriptor = { Binding: string; Parameter: string }
let call (work: unit -> int) = work ()
let contract: Expr<Vocabulary.ScopedCallbackDescriptor> = <@ { Binding = "MalformedScope.call"; Parameter = "work" } @>
[<EntryPoint>]
let main _ = call (fun () -> 0)
"""
        let result =
            match parseAndCheck source "malformed-scoped-quote.clef" with
            | Success result | CheckFailure result -> result
            | ParseFailure errors -> failwithf "%A" errors
        Assert.Contains((ScopedCallbacks.read result.Graph).Findings, fun f -> f.Message.Contains("well-typed quoted record"))

    [<Fact>]
    member _.``A callback handed to a boundary that lets it escape leaves its stores unordered``() =
        // Negative control for the scoped-parameter account: `keep` stores `work`, so the
        // parameter is neither declared nor inferred scoped (a parameter a body never uses is
        // inferred scoped, since nothing can invoke or hold it), and nothing accounts for the
        // callback: the store it reaches stays pending with that specific reason, naming both
        // the storing callable and the callback. Dropping the scoped-parameter test on the
        // formal's own edge in ProgramActivation would order it wrongly.
        let text = BorrowedViewCases.prefix + """
let mutable saved: unit -> int = fun () -> 0
let mutable held: (unit -> int) option = None
let keep (work: unit -> int) : int = held <- Some work; 0
let retain callback = saved <- callback; 0
[<EntryPoint>]
let main _ = keep (fun () -> retain (fun () -> 1))
"""
        let result =
            match parseAndCheck text "borrowed-view.clef" with
            | Success result | CheckFailure result -> result
            | ParseFailure errors -> failwithf "Parse failed: %A" errors
        let pending = result.Diagnostics |> List.filter (fun d -> d.Code = "CCS8403")
        Assert.NotEmpty pending
        Assert.All(pending, fun d -> Assert.Contains("Complete ordinary invocation scope is unavailable", d.Message))
        // Both facts are owed and both are reported: the storing callable's own scope is
        // incomplete, and the callback through which it is reached is unaccounted for.
        let reasons = pending |> List.map _.Message |> List.distinct
        Assert.True(reasons.Length >= 2, sprintf "expected the storing callable and the callback each named: %A" reasons)

    [<Fact>]
    member _.``A callable that is formed but never applied in source is ordered by its formation``() =
        // Every use of `later` is accounted for and none applies it: its body can only run after
        // its formation inside the entry, so the store it reaches is ordered without any claim
        // about an invocation (Program Structure and Execution, Execution of Static Initializers).
        let text = BorrowedViewCases.prefix + """
let mutable saved: unit -> int = fun () -> 0
[<EntryPoint>]
let main _ =
    let later = fun () -> saved <- (fun () -> 1); 0
    let kept = later
    0
"""
        let result =
            match parseAndCheck text "borrowed-view.clef" with
            | Success result | CheckFailure result -> result
            | ParseFailure errors -> failwithf "Parse failed: %A" errors
        Assert.Empty(result.Diagnostics |> List.filter (fun d -> d.Code = "CCS8403"))
