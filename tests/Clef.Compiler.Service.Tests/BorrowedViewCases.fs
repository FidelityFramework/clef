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
    member _.``Borrowed view cannot be manufactured with a default value``() =
        let result = BorrowedViewCases.source """
[<EntryPoint>]
let main _ =
    let view: BorrowedView<Pixel> = NativeDefault.zeroed ()
    BorrowedView.length view
"""
        Assert.Contains((ScopedCallbacks.read result.Graph).Findings, fun f -> f.Message.Contains("no source constructor"))

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
    member _.``Unknown function consumer cannot receive a borrowed capture``() =
        let result = BorrowedViewCases.source """
let forward (unknown: (unit -> int) -> int) (view: BorrowedView<Pixel>) =
    unknown (fun () -> BorrowedView.length view)
[<EntryPoint>]
let main _ = withView (fun view -> forward (fun callback -> callback ()) view)
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

    [<Fact>]
    member _.``Default record cannot manufacture a nested view``() =
        let result = BorrowedViewCases.source """
type Holder = { Pixels: BorrowedView<Pixel> }
[<EntryPoint>]
let main _ =
    let holder: Holder = NativeDefault.zeroed ()
    BorrowedView.length holder.Pixels
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
