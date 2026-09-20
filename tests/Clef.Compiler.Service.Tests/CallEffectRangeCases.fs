namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module RangeAnalysis = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis

module private CallEffectRanges =
    let check source =
        match parseAndCheck ("module CallEffects\n" + source) "call-effects.clef" with
        | Success result ->
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Error _ -> true | _ -> false)
            result.Graph
        | CheckFailure result -> failwithf "Source did not reach a checked graph: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Parse failed: %A" errors

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable &&
            match node.Kind with SemanticKind.Binding (actual, _, _, _) -> actual = name | _ -> false)

    let range name lo hi graph =
        let node = binding name graph
        Assert.Equal(Some (ValueRange.Bounded(lo, hi)), node.ValueRange)
        let value = graph.Nodes[node.Children.Head]
        match node.Kind with
        | SemanticKind.Binding (_, true, _, _) -> () // The cell joins all writes; its initializer does not.
        | _ -> Assert.Equal(Some (ValueRange.Bounded(lo, hi)), value.ValueRange)
        Assert.Equal("call-effects.clef", value.Range.File)
        Assert.True(value.Range.Start.Line > 0)

[<Trait("Category", "NTU"); Trait("Subcategory", "CallEffectRanges")>]
type CallEffectRangeCases() =
    [<Theory>]
    [<InlineData("let change = fun () -> state <- 300", "change ()")>]
    [<InlineData("let change = fun () -> state <- 300\n    let relay = fun () -> change ()", "relay ()")>]
    [<InlineData("let rec change count = if count = 0 then state <- 300 else change (count - 1)", "change 2")>]
    [<InlineData("let change = fun () -> state <- 300\n    let invoke work = work ()", "invoke change")>]
    member _.``Direct transitive recursive and known value calls invalidate only later observations``(declarations: string, call: string) =
        let graph = CallEffectRanges.check $"""
[<EntryPoint>]
let main _ =
    let mutable state: int = 1
    {declarations}
    if state < 10 then
        let before = state
        {call}
        let after = state
        if before < 10 && after = 300 then 0 else 1
    else 2
"""
        CallEffectRanges.range "state" 1I 300I graph
        CallEffectRanges.range "before" 1I 9I graph
        CallEffectRanges.range "after" 1I 300I graph

    [<Fact>]
    member _.``Earlier effectful arguments invalidate later reads without changing earlier snapshots``() =
        let graph = CallEffectRanges.check """
let takeFirst (left: int) (_: unit) = left
let takeSecond (_: unit) (right: int) = right
[<EntryPoint>]
let main _ =
    let mutable state: int = 1
    let change = fun () -> state <- 300
    if state < 10 then
        let snapshot = takeFirst state (change ())
        state <- 1
        if state < 10 then
            let after = takeSecond (change ()) state
            if snapshot < 10 && after = 300 then 0 else 1
        else 2
    else 3
"""
        CallEffectRanges.range "snapshot" 1I 9I graph
        CallEffectRanges.range "after" 1I 300I graph

    [<Fact>]
    member _.``A write to another cell and a pure recursive call retain the guarded range``() =
        let graph = CallEffectRanges.check """
let rec pure count = if count = 0 then () else pure (count - 1)
[<EntryPoint>]
let main _ =
    let mutable state: int = 1
    let mutable other: int = 0
    let changeOther = fun () -> other <- 300
    if state < 10 then
        changeOther ()
        pure 2
        let retained = state
        if retained < 10 && other = 300 then 0 else 1
    else
        state <- 300
        2
"""
        CallEffectRanges.range "retained" 1I 9I graph

    [<Fact>]
    member _.``Constructing a closure does not execute its mutation``() =
        let graph = CallEffectRanges.check """
[<EntryPoint>]
let main _ =
    let mutable state: int = 1
    if state < 10 then
        let delayed = fun () -> state <- 300
        let before = state
        delayed ()
        let after = state
        if before < 10 && after = 300 then 0 else 1
    else 2
"""
        CallEffectRanges.range "before" 1I 9I graph
        CallEffectRanges.range "after" 1I 300I graph

    [<Fact>]
    member _.``Loop summaries include transitive writes before the first body observation``() =
        let graph = CallEffectRanges.check """
[<EntryPoint>]
let main _ =
    let mutable state: int = 1
    let change = fun () -> state <- 300
    let relay = fun () -> change ()
    if state < 10 then
        let mutable count: int = 0
        while count < 2 do
            let observed = state
            ignore observed
            relay ()
            count <- count + 1
        if state = 300 then 0 else 1
    else 2
"""
        CallEffectRanges.range "observed" 1I 300I graph

    [<Theory>]
    [<InlineData("let wasSmall = state < 10", "wasSmall")>]
    [<InlineData("let wasSmall = state < 10\n    let saved = wasSmall && state = 1", "saved")>]
    member _.``Saved predicates do not replay old mutable observations as current bounds``(predicate: string, guard: string) =
        let graph = CallEffectRanges.check $"""
[<EntryPoint>]
let main _ =
    let mutable state: int = 1
    {predicate}
    state <- 300
    if {guard} then
        let afterPredicate = state
        if afterPredicate = 300 then 0 else 1
    else 2
"""
        CallEffectRanges.range "afterPredicate" 1I 300I graph

    [<Fact>]
    member _.``Saved predicates over immutable values still refine their observations``() =
        let graph = CallEffectRanges.check """
let inspect (value: int) =
    let wasSmall = value < 10
    if wasSmall then
        let retained = value
        retained
    else 0
[<EntryPoint>]
let main _ = inspect 1 + inspect 300
"""
        CallEffectRanges.range "retained" 1I 9I graph

    [<Fact>]
    member _.``Saved successful checks may be combined after different writes to the same cell``() =
        let graph = CallEffectRanges.check """
[<EntryPoint>]
let main _ =
    let mutable trace: int = 1245
    let firstOk = trace = 1245
    trace <- 12345
    let secondOk = trace = 12345
    trace <- 1246
    if firstOk && secondOk then
        let finalTrace = trace
        if finalTrace = 1246 then 0 else 1
    else 2
"""
        CallEffectRanges.range "finalTrace" 1245I 12345I graph

    [<Fact>]
    member _.``A later guard operand that writes the cell cannot validate its earlier read``() =
        let graph = CallEffectRanges.check """
[<EntryPoint>]
let main _ =
    let mutable state: int = 1
    let limit = fun () -> state <- 300; 10
    if state < limit () then
        let observed = state
        if observed = 300 then 0 else 1
    else 2
"""
        CallEffectRanges.range "observed" 1I 300I graph

    [<Fact>]
    member _.``A predicate call cannot map an old argument value onto storage it writes``() =
        let graph = CallEffectRanges.check """
let mutable state: int = 1
let isSmall (value: int) =
    state <- 300
    value < 10
[<EntryPoint>]
let main _ =
    if isSmall state then
        let observed = state
        if observed = 300 then 0 else 1
    else 2
"""
        CallEffectRanges.range "observed" 1I 300I graph

    [<Fact>]
    member _.``Backward arithmetic refinement cannot outlive a write inside the compared expression``() =
        let graph = CallEffectRanges.check """
[<EntryPoint>]
let main _ =
    let mutable state: int = 1
    let change = fun () -> state <- 300; 0
    if state + change () < 10 then
        let observed = state
        if observed = 300 then 0 else 1
    else 2
"""
        CallEffectRanges.range "observed" 1I 300I graph

    [<Fact>]
    member _.``A partial application does not run the remaining function body``() =
        let graph = CallEffectRanges.check """
[<EntryPoint>]
let main _ =
    let mutable state: int = 1
    let change (_: unit) (_: unit) = state <- 300
    if state < 10 then
        let delayed = change ()
        let before = state
        delayed ()
        let after = state
        if before < 10 && after = 300 then 0 else 1
    else 2
"""
        CallEffectRanges.range "before" 1I 9I graph
        CallEffectRanges.range "after" 1I 300I graph

    [<Fact>]
    member _.``A mutable callback argument cannot inherit its initial lambda's pure effects``() =
        let graph = CallEffectRanges.check """
[<EntryPoint>]
let main _ =
    let mutable state: int = 1
    let mutable initialize: int -> int = fun _ -> 1
    initialize <- fun _ -> state <- 300; 1
    if state < 10 then
        let values = Array.init 1 initialize
        let observed = state
        if observed = 300 && values.[0] = 1 then 0 else 1
    else 2
"""
        CallEffectRanges.range "observed" 1I 300I graph

    [<Fact>]
    member _.``An unresolved callable cannot preserve mutable guards``() =
        let graph = CallEffectRanges.check """
[<EntryPoint>]
let main _ =
    let mutable state: int = 1
    let known = fun () -> ()
    if state < 10 then
        known ()
        let observed = state
        if observed < 10 then 0 else 1
    else
        state <- 300
        2
"""
        CallEffectRanges.range "observed" 1I 9I graph
        let nodes = graph.Nodes |> Map.map (fun _ node ->
            match node.Kind with
            | SemanticKind.VarRef ("known", _) -> { node with Kind = SemanticKind.VarRef ("unknown", None) }
            | _ -> node)
        let unknown, _ = RangeAnalysis.run None { graph with Nodes = nodes }
        CallEffectRanges.range "observed" 1I 300I unknown
