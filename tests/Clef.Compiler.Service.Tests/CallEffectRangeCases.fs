namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module RangeAnalysis = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis

module private CallEffectRanges =
    let mutableCallback = """
[<EntryPoint>]
let main _ =
    let mutable state: int = 1
    let mutable initialize: int -> int = fun _ -> 1
    initialize <- fun _ -> state <- 300; 1
    if state < 10 then
        let values = Array.init 1 initialize
        if values.[0] = 1 then
            let observed = state
            if observed = 300 then 0 else 1
        else 1
    else 2
"""

    let check source =
        match parseAndCheck ("module CallEffects\n" + source) "call-effects.clef" with
        | Success result ->
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Error _ -> true | _ -> false)
            result.Graph
        | CheckFailure result -> failwithf "Source did not reach a checked graph: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Parse failed: %A" errors

    /// Current owner facts are inspected even for deliberately rejected premises.
    let checkResult source =
        match parseAndCheck ("module CallEffects\n" + source) "call-effects.clef" with
        | Success result | CheckFailure result -> result
        | ParseFailure errors -> failwithf "Parse failed: %A" errors

    /// The diagnostics of a source that may not reach a checked graph.
    let diagnostics source = (checkResult source).Diagnostics

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
    [<InlineData(0, 1, 10)>]
    [<InlineData(10, 0, 9)>]
    [<InlineData(5, 0, 10)>]
    member _.``Inequality removes only an established interval endpoint`` (excluded: int, lower: int, upper: int) =
        let graph = CallEffectRanges.check $"""
let observe flag =
    let value = if flag then 0 else 10
    if value <> {excluded} then
        let retained = value
        retained
    else 0
[<EntryPoint>]
let main _ = observe true + observe false
"""
        CallEffectRanges.range "retained" (bigint lower) (bigint upper) graph

    [<Fact>]
    member _.``Inequality against a non-singleton value cannot remove either endpoint`` () =
        let graph = CallEffectRanges.check """
let observe flag =
    let value = if flag then 0 else 10
    let excluded = if flag then 0 else 10
    if value <> excluded then
        let retained = value
        retained
    else 0
[<EntryPoint>]
let main _ = observe true + observe false
"""
        CallEffectRanges.range "retained" 0I 10I graph

    // These range fixtures request lexical cell observations explicitly: an ordinary
    // binding first observes at demand and cannot stand for a pre-write snapshot.
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
        let before = eager state
        {call}
        let after = eager state
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
        let delayed = eager (fun () -> state <- 300)
        let before = eager state
        delayed ()
        let after = eager state
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
            let observed = eager state
            ignore observed
            relay ()
            count <- count + 1
        if state = 300 then 0 else 1
    else 2
"""
        CallEffectRanges.range "observed" 1I 300I graph

    [<Theory>]
    [<InlineData("let wasSmall = eager (state < 10)", "wasSmall")>]
    [<InlineData("let wasSmall = eager (state < 10)\n    let saved = eager (wasSmall && state = 1)", "saved")>]
    member _.``Saved predicates do not replay old mutable observations as current bounds``(predicate: string, guard: string) =
        let graph = CallEffectRanges.check $"""
[<EntryPoint>]
let main _ =
    let mutable state: int = 1
    {predicate}
    state <- 300
    if {guard} then
        let afterPredicate = eager state
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
    member _.``Eager saved predicates over immutable values still refine their observations``() =
        let graph = CallEffectRanges.check """
let inspect (value: int) =
    let wasSmall = eager (value < 10)
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
    let firstOk = eager (trace = 1245)
    trace <- 12345
    let secondOk = eager (trace = 12345)
    trace <- 1246
    if firstOk && secondOk then
        let finalTrace = eager trace
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
        let observed = eager state
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
        let observed = eager state
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
        let observed = eager state
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
        let delayed = eager (change ())
        let before = eager state
        delayed ()
        let after = eager state
        if before < 10 && after = 300 then 0 else 1
    else 2
"""
        CallEffectRanges.range "before" 1I 9I graph
        CallEffectRanges.range "after" 1I 300I graph

    [<Fact>]
    member _.``A mutable callback argument cannot inherit its initial lambda's pure effects``() =
        let graph = CallEffectRanges.check CallEffectRanges.mutableCallback
        // The write reaches `state` only when `values` is demanded (the reassigned callback runs
        // inside Array.init); ordinary bindings are deferred, so the guard that demands `values`
        // precedes the observation and the arm that observes `state` is entered after the write.
        CallEffectRanges.range "observed" 1I 300I graph

    [<Fact>]
    member _.``An unconditional overwrite defers only the initial callable value and preserves its index declaration``() =
        let graph = CallEffectRanges.check CallEffectRanges.mutableCallback
        let cell = CallEffectRanges.binding "initialize" graph
        let reading = Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.read graph
        let proof = reading.Initializers[cell.Id]
        Assert.False(proof.ExcludesBinding)
        Assert.True(proof.InitializerUse.IsSome)
        let deferred = Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.deferredOnly graph
        Assert.DoesNotContain(cell.Id, deferred)
        Assert.Contains(proof.Initializer, deferred)
        let initialCode =
            match graph.Nodes[proof.Initializer].Kind with
            | SemanticKind.TypeAnnotation(inner, _) -> graph.Nodes[inner]
            | _ -> graph.Nodes[proof.Initializer]
        match initialCode.Kind with
        | SemanticKind.Lambda([(_, _, formal)], _, [], _, _) ->
            Assert.Contains(formal, deferred)
            Assert.False(reading.Formals.ContainsKey formal)
            Assert.True(graph.Nodes.ContainsKey formal)
        | _ -> failwith "The retained initializer lost its logical index declaration"
        let sourceCells = Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.sourceFamilies graph |> fst
        for _, _, written in sourceCells[cell.Id].Writes do
            match graph.Nodes[written].Kind with
            | SemanticKind.Lambda(parameters, _, _, _, _) -> Assert.Single parameters |> ignore
            | _ -> failwith "Expected the retained replacement implementation"
        CallEffectRanges.range "observed" 1I 300I graph

    [<Theory>]
    [<InlineData("read before write")>]
    [<InlineData("eager snapshot")>]
    [<InlineData("conditional write")>]
    [<InlineData("captured cell")>]
    [<InlineData("captured initializer")>]
    member _.``Mutable initializer exclusion requires complete unconditional overwrite premises``(defect: string) =
        let statements =
            match defect with
            | "read before write" -> "let before = eager (initialize 0)\n    initialize <- fun index -> index + 1\n    before + initialize 0"
            | "eager snapshot" -> "let saved = eager initialize\n    initialize <- fun index -> index + 1\n    saved 0 + initialize 0"
            | "conditional write" -> "if flag then initialize <- fun index -> index + 1\n    initialize 0"
            | "captured cell" -> "let saved () = initialize 0\n    initialize <- fun index -> index + 1\n    saved ()"
            | "captured initializer" -> "initialize <- fun index -> index + 1\n    initialize 0"
            | other -> failwithf "Unknown overwrite premise: %s" other
        let initial = if defect = "captured initializer" then "fun index -> captured + index" else "fun _ -> 1"
        let result = CallEffectRanges.checkResult $"""
let run flag =
    let captured = 1
    let mutable initialize: int -> int = {initial}
    {statements}
[<EntryPoint>]
let main _ = run true + run false
"""
        let cell = CallEffectRanges.binding "initialize" result.Graph
        let reading = Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.analyze result.Graph
        Assert.False(reading.Initializers.ContainsKey cell.Id, sprintf "Excluded the initializer with %s" defect)
        Assert.False(reading.Formals.Values |> Seq.exists (fun proof ->
            result.Graph.Nodes[proof.Implementation].Parent = Some cell.Children.Head))

    [<Theory>]
    [<InlineData("exported cell")>]
    [<InlineData("exported initializer")>]
    [<InlineData("duplicated initializer incidence")>]
    [<InlineData("read moved before write")>]
    member _.``Changed mutable initializer support refuses and retracts its previous demand row``(change: string) =
        let graph = CallEffectRanges.check CallEffectRanges.mutableCallback
        let cell = CallEffectRanges.binding "initialize" graph
        let proof = (Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.read graph).Initializers[cell.Id]
        let changed =
            match change with
            | "exported cell" -> { graph with DeclarationRoots = (cell.Id, DeclRoot.LibraryExport) :: graph.DeclarationRoots }
            | "exported initializer" -> { graph with DeclarationRoots = (proof.Initializer, DeclRoot.LibraryExport) :: graph.DeclarationRoots }
            | "duplicated initializer incidence" -> { graph with Edges = proof.InitializerUse.Value :: proof.InitializerUse.Value :: graph.Edges }
            | "read moved before write" ->
                let sourceCell = (Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.sourceFamilies graph |> fst)[cell.Id]
                let writer, _, _ = sourceCell.Writes |> Assert.Single
                let scope = graph.Nodes[graph.Nodes[writer].Parent.Value]
                let statements = match scope.Kind with SemanticKind.Sequential statements -> statements | _ -> failwith "Expected the replacing write's ordered scope"
                let at = statements |> List.findIndex ((=) writer)
                let following = statements[at + 1]
                let reordered = statements |> List.map (fun id -> if id = writer then following elif id = following then writer else id)
                { graph with
                    Nodes = graph.Nodes.Add(scope.Id, { scope with Kind = SemanticKind.Sequential reordered; Children = reordered })
                    Edges = graph.Edges |> List.map (fun edge ->
                        match edge.Target, edge.Class, edge.Sources with
                        | target, EdgeClass.Structural, [source] when target = scope.Id && List.contains source reordered ->
                            { edge with Ordinal = reordered |> List.findIndex ((=) source) }
                        | _ -> edge) }
            | other -> failwithf "Unknown current premise change: %s" other
        match Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.tryRead changed with
        | Result.Error failures -> Assert.Contains(failures, fun failure -> failure.Occurrence = Some cell.Id)
        | Result.Ok _ -> failwith "The stale initializer cut was accepted"
        let renewed = Clef.Compiler.Nanopass.OrdinaryDemand.normalize changed
        let reading = Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.read renewed
        Assert.False(reading.Initializers.ContainsKey cell.Id)
        Assert.DoesNotContain(proof.Initializer, Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.deferredOnly renewed)

    [<Fact>]
    member _.``A branch-local snapshot observes the writes before its first demand and shares that value afterwards``() =
        // The snapshot is an ordinary deferred binding: it reads the cell at its first demand, after
        // the write of 257 and before the write of 300, and the second demand shares that value. The
        // cell's range at the read joins the writes that precede it (a sound enclosure, not a
        // strong update), so the proof is that 300 never reaches either demand and both agree.
        let graph = CallEffectRanges.check """
[<EntryPoint>]
let main _ =
    let mutable current = 1
    if current < 10 then
        let snapshot = current
        current <- 257
        let first = eager snapshot
        current <- 300
        let second = eager snapshot
        first + second
    else 2
"""
        // The schedule is the ingredient's own proof: the activation's statements in realized order
        // place the snapshot's read after the write of 257 and before the write of 300, immediately
        // ahead of its first demand, and both demands share the one binding. (The cell's numeric
        // range still joins every write in scope, so the range alone cannot separate the two
        // writes; the statement order can.)
        let snapshot = CallEffectRanges.binding "snapshot" graph
        let schedule =
            Clef.Compiler.Baker.Ingredients.BindingDemand.analyze graph
            |> List.find (fun schedule -> schedule.Binding = snapshot.Id)
        Assert.Equal<string option>(None, schedule.Pending)
        let statements = schedule.Slots |> List.map (fun slot -> slot.Statement)
        Assert.Equal<NodeId list>(schedule.Desired, statements)
        let position id = statements |> List.findIndex ((=) id)
        let writeOf (value: int64) =
            graph.Nodes.Values |> Seq.find (fun node ->
                node.IsReachable &&
                match node.Kind with
                | SemanticKind.Set (_, written) ->
                    match graph.Nodes[written].Kind with
                    | SemanticKind.Literal (NativeLiteral.Int (actual, _)) -> actual = value
                    | _ -> false
                | _ -> false)
        Assert.True(position (writeOf 257L).Id < position snapshot.Id, "the read is scheduled after the write of 257")
        Assert.True(position snapshot.Id < position (writeOf 300L).Id, "the read is scheduled before the write of 300")
        Assert.True(position snapshot.Id + 1 = position (CallEffectRanges.binding "first" graph).Id, "the read sits immediately ahead of its first demand")
        Assert.Empty(Clef.Compiler.Baker.Ingredients.BindingDemand.failures graph)
        Assert.Equal((CallEffectRanges.binding "first" graph).ValueRange, (CallEffectRanges.binding "second" graph).ValueRange)

    [<Fact>]
    member _.``A changed conditional entry retracts a branch-local demand schedule``() =
        // The arm taken is a premise of the schedule: swapping the arms of the decision that
        // admitted the snapshot must refuse the retained rows before settlement can recreate them.
        let graph = CallEffectRanges.check """
[<EntryPoint>]
let main _ =
    let mutable current = 1
    if current < 10 then
        let snapshot = current
        current <- 257
        let first = eager snapshot
        first
    else 2
"""
        let decision =
            graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && node.Range.Start.Line = 6 &&
                match node.Kind with SemanticKind.IfThenElse(_, _, Some _) -> true | _ -> false) |> Seq.exactlyOne
        let swapped =
            match decision.Kind with
            | SemanticKind.IfThenElse(condition, thenArm, Some elseArm) -> { decision with Kind = SemanticKind.IfThenElse(condition, elseArm, Some thenArm) }
            | _ -> failwith "not a two-armed decision"
        let mutated = { graph with Nodes = graph.Nodes |> Map.add decision.Id swapped }
        let failures = Clef.Compiler.Baker.Ingredients.BindingDemand.failures mutated
        Assert.NotEmpty failures
        Assert.Contains(failures, fun failure -> failure.Reason.Contains "OrdinaryBindingDemand")
        Assert.Empty(Clef.Compiler.Baker.Ingredients.BindingDemand.failures graph)

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
        // The probe replaces the callee with an unresolved reference; its definition edge goes
        // with it so the recorded incidence still describes the mutated node and the settled
        // demand schedule stays valid for the renewed numeric analysis.
        let unresolved =
            graph.Nodes.Values |> Seq.filter (fun node -> match node.Kind with SemanticKind.VarRef ("known", _) -> true | _ -> false)
            |> Seq.map (fun node -> node.Id) |> Set.ofSeq
        let nodes = graph.Nodes |> Map.map (fun _ node ->
            match node.Kind with
            | SemanticKind.VarRef ("known", _) -> { node with Kind = SemanticKind.VarRef ("unknown", None) }
            | _ -> node)
        let edges = graph.Edges |> List.filter (fun edge -> not (edge.Class = EdgeClass.Reference && unresolved.Contains edge.Target))
        let unknown, _ = RangeAnalysis.run None { graph with Nodes = nodes; Edges = edges }
        CallEffectRanges.range "observed" 1I 300I unknown


    [<Fact>]
    member _.``The retained branch-local schedule names its decision and guard, so a swapped arm retracts it for that reason``() =
        // The conditional entry path is recorded on the schedule's edge: a mutation that stops
        // recording the decision and guard would pass the generic retraction check but fail here.
        let graph = CallEffectRanges.check """
[<EntryPoint>]
let main _ =
    let mutable current = 1
    if current < 10 then
        let snapshot = current
        current <- 257
        let first = eager snapshot
        first
    else 2
"""
        let snapshot = CallEffectRanges.binding "snapshot" graph
        let decision =
            graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && node.Range.Start.Line = 6 &&
                match node.Kind with SemanticKind.IfThenElse(_, _, Some _) -> true | _ -> false) |> Seq.exactlyOne
        let guard = match decision.Kind with SemanticKind.IfThenElse(condition, _, _) -> condition | _ -> failwith "unreachable"
        let retained =
            graph.Edges |> List.filter (fun edge ->
                edge.Target = snapshot.Id && (match edge.Role with EdgeRole.OrdinaryBindingDemand _ -> true | _ -> false))
            |> List.exactlyOne
        Assert.Contains(decision.Id, retained.Sources)
        Assert.Contains(guard, retained.Sources)
        let swapped =
            match decision.Kind with
            | SemanticKind.IfThenElse(condition, thenArm, Some elseArm) -> { decision with Kind = SemanticKind.IfThenElse(condition, elseArm, Some thenArm) }
            | _ -> failwith "not a two-armed decision"
        let failures = Clef.Compiler.Baker.Ingredients.BindingDemand.failures { graph with Nodes = graph.Nodes |> Map.add decision.Id swapped }
        let failure = Assert.Single failures
        Assert.Contains("differs from its complete typed scope/use proof", failure.Reason)
        Assert.Contains(decision.Id, failure.Participants)

    [<Fact>]
    member _.``A snapshot demanded only in the right operand of a conjunction stays pending for that reason``() =
        // `&&` demands its left operand first and keeps the right conditional (Expressions, logical
        // operators): the read in the right operand is not an unconditional first demand.
        let pending = CallEffectRanges.diagnostics """
[<EntryPoint>]
let main _ =
    let mutable current = 1
    let mutable other = 2
    if current < 10 then
        let snapshot = current
        current <- 257
        if other < 5 && snapshot = 1 then 0 else 1
    else 2
"""
        Assert.Contains(pending, fun d -> d.Code = "CCS8403" && d.Message.Contains "Every use requires one unconditional first-demand path")
        // The mirror image, demanded in the left operand, is scheduled.
        let scheduled = CallEffectRanges.check """
[<EntryPoint>]
let main _ =
    let mutable current = 1
    let mutable other = 2
    if current < 10 then
        let snapshot = current
        current <- 257
        if snapshot = 1 && other < 5 then 0 else 1
    else 2
"""
        Assert.Empty(Clef.Compiler.Baker.Ingredients.BindingDemand.failures scheduled)

    [<Fact>]
    member _.``A snapshot referenced from a nested closure in the arm stays pending for that reason``() =
        // A deferred demand inside a closure is not a first demand of the arm.
        let pending = CallEffectRanges.diagnostics """
[<EntryPoint>]
let main _ =
    let mutable current = 1
    if current < 10 then
        let snapshot = current
        current <- 257
        let later = fun () -> snapshot
        later ()
    else 2
"""
        // The reference from inside the closure is a family use the ingredient does not
        // schedule: it is neither a first demand of the arm nor a supported contract.
        Assert.Contains(pending, fun d -> d.Code = "CCS8403" && d.Message.Contains "family use has no supported demand contract")
