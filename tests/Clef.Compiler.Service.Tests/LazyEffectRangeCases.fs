namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module EffectRanges = Clef.Compiler.PSGSaturation.SemanticGraph.LazyEffectRanges
module EffectRangeAnalysis = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis
module EffectLazyValues = Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues

module private LazyEffects =
    let check source =
        match parseAndCheck ("module LazyEffects\n" + source) "lazy-effects.clef" with
        | Success result | CheckFailure result ->
            Assert.Empty(result.Diagnostics |> List.filter (fun diagnostic -> Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error))
            result.Graph
        | ParseFailure errors -> failwithf "%A" errors

    let twoFactories = """
let mutable executions = 0
let make value = lazy (executions <- executions + 1; value)
[<EntryPoint>]
let main _ =
    let first = make true
    let second = make false
    let alias = first
    let both = Lazy.force first && not (Lazy.force second) && Lazy.force alias
    if both then executions else 9
"""
    let cell (graph: SemanticGraph) = graph.Nodes.Values |> Seq.filter (fun node ->
        node.IsReachable && match node.Kind with SemanticKind.Binding("executions", true, _, _) -> true | _ -> false) |> Assert.Single
    let proof graph = EffectRanges.recognize graph |> Assert.Single
    let analyze graph = EffectRangeAnalysis.run graph.Platform graph |> fst
    let obligations (graph: SemanticGraph) = graph.Nodes.Values |> Seq.filter (fun node ->
        match node.Kind with SemanticKind.Obligation { Body = ObligationBody.FiniteAdditiveEffects _ } -> true | _ -> false) |> Seq.toList

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "LazyEffectRanges")>]
type LazyEffectRangeCases() =
    [<Fact>]
    member _.``Two factory activations count two instances while an alias retains the first cache`` () =
        let graph = LazyEffects.check LazyEffects.twoFactories
        let bound = LazyEffects.proof graph
        Assert.Equal(0I, bound.Lower)
        Assert.Equal(2I, bound.Upper)
        Assert.Equal(2I, (Assert.Single bound.Contributions).Count)
        Assert.Equal(Some(ValueRange.Bounded(0I, 2I)), (LazyEffects.cell graph).ValueRange)
        for contribution in bound.Contributions do
            Assert.Equal(Some(ValueRange.Bounded(1I, 2I)), graph.Nodes[contribution.Value].ValueRange)
        let protocol = EffectLazyValues.settle graph
        Assert.Equal(3, protocol.Forces.Count)
        Assert.Single protocol.Instances |> ignore
        let required = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LazyMemoization)
        for edge in required do
            for participant in edge.Target :: edge.Sources do Assert.Contains(participant, bound.Participants)

    [<Fact>]
    member _.``Unit factories retain their distinct invocation count`` () =
        let graph = LazyEffects.check """
let mutable executions = 0
let make () = lazy (executions <- executions + 1; "value")
[<EntryPoint>]
let main _ =
    let first = make ()
    let second = make ()
    let alias = first
    let a = Lazy.force first
    let b = Lazy.force second
    let c = Lazy.force alias
    if a = b && b = c then executions else 9
"""
        Assert.Equal(2I, (LazyEffects.proof graph).Upper)

    [<Fact>]
    member _.``Signed contributions enclose every ordering prefix and final store`` () =
        let graph = LazyEffects.check """
let mutable executions = 10
[<EntryPoint>]
let main _ =
    let up = lazy (executions <- executions + 5; executions)
    let down = lazy (executions <- executions - 3; executions)
    let mixed = lazy (executions <- executions + 2; executions <- executions - 7; executions)
    Lazy.force down + Lazy.force up + Lazy.force mixed
"""
        let bound = LazyEffects.proof graph
        Assert.Equal(0I, bound.Lower)
        Assert.Equal(17I, bound.Upper)
        Assert.Equal<bigint list>([-7I; -3I; 2I; 5I], bound.Contributions |> List.map _.Delta |> List.sort)
        Assert.Equal(Some(ValueRange.Bounded(0I, 17I)), (LazyEffects.cell graph).ValueRange)

    [<Fact>]
    member _.``An unbounded force loop reuses an already formed memo instance`` () =
        let graph = LazyEffects.check """
let mutable executions = 0
[<EntryPoint>]
let main _ =
    let value = lazy (executions <- executions + 1)
    while true do
        Lazy.force value
    executions
"""
        let bound = LazyEffects.proof graph
        Assert.Equal(1I, bound.Upper)

    [<Theory>]
    [<InlineData("loop")>]
    [<InlineData("extra-store")>]
    [<InlineData("mutable-alias")>]
    [<InlineData("library")>]
    [<InlineData("recursive")>]
    member _.``Unbounded formation or unaccounted mutable access retains no finite permission`` defect =
        let source =
            match defect with
            | "loop" -> """
let mutable executions = 0
let make () = lazy (executions <- executions + 1)
[<EntryPoint>]
let main _ =
    while true do
        let value = make ()
        Lazy.force value
    executions
"""
            | "extra-store" -> """
let mutable executions = 0
[<EntryPoint>]
let main _ =
    let value = lazy (executions <- executions + 1)
    executions <- executions + 1
    Lazy.force value
    executions
"""
            | "mutable-alias" -> """
let mutable executions = 0
[<EntryPoint>]
let main _ =
    let value = lazy (executions <- executions + 1)
    let mutable escaped = value
    Lazy.force escaped
    executions
"""
            | "recursive" -> """
let mutable executions = 0
let make () = lazy (executions <- executions + 1)
let rec drive running =
    let value = make ()
    Lazy.force value
    if running then drive running else 0
[<EntryPoint>]
let main _ = drive true; executions
"""
            | _ -> """
let mutable executions = 0
let make () = lazy (executions <- executions + 1)
let useValue () = Lazy.force (make ()); executions
"""
        let graph = LazyEffects.check source
        Assert.Empty(EffectRanges.recognize graph)
        Assert.Empty(LazyEffects.obligations graph)

    [<Theory>]
    [<InlineData("startup")>]
    [<InlineData("memoization")>]
    [<InlineData("cell-type")>]
    [<InlineData("delta-type")>]
    [<InlineData("delta-dimension")>]
    [<InlineData("store-children")>]
    [<InlineData("unknown-call")>]
    [<InlineData("naked-thunk-call")>]
    member _.``Changed typed activation and cache premises retract stale finite bounds`` defect =
        let original = LazyEffects.check LazyEffects.twoFactories
        let bound = LazyEffects.proof original
        let store = Assert.Single bound.Contributions
        let protocol = EffectLazyValues.settle original
        let force = protocol.Forces.Values |> Seq.head
        let update id transform graph = { graph with Nodes = graph.Nodes.Add(id, transform graph.Nodes[id]) }
        let changed =
            match defect with
            | "startup" -> { original with Edges = original.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramInitialization) }
            | "memoization" -> { original with Edges = original.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.LazyMemoization) }
            | "cell-type" -> original |> update bound.Cell (fun node -> { node with Type = Types.boolType })
            | "delta-type" | "delta-dimension" ->
                let delta = match original.Nodes[store.Value].Kind with SemanticKind.Application(_, [_; right]) -> right | _ -> failwith "Expected additive store"
                original |> update delta (fun node ->
                    let ty =
                        if defect = "delta-type" then Types.boolType else
                        match node.Type with
                        | NativeType.TNum(carrier, dimension) -> NativeType.TNum(carrier, { dimension with Bases = Map.ofList [({ Name = "different"; Module = [] }, 1)] })
                        | _ -> failwith "Expected a dimensional source number"
                    { node with Type = ty })
            | "store-children" -> original |> update store.Store (fun node -> { node with Children = [] })
            | "unknown-call" ->
                let call = original.Nodes.Values |> Seq.find (fun node ->
                    match node.Kind with
                    | SemanticKind.Application(_, _) ->
                        bound.Participants.Contains node.Id && node.Id <> store.Value && node.Id <> force.Invocation &&
                        (match node.Type with NativeType.TLazy _ -> true | _ -> false)
                    | _ -> false)
                let callee = match call.Kind with SemanticKind.Application(callee, _) -> callee | _ -> failwith "Expected factory call"
                original |> update callee (fun node -> { node with Kind = SemanticKind.VarRef("opaque", None); Children = [] })
            | _ ->
                let extra = { original.Nodes[force.Invocation] with Id = NodeId.fresh() }
                let entry = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read original |> Option.get
                let spine = original.Nodes[entry.Spine]
                let values = match spine.Kind with SemanticKind.Sequential values -> values | _ -> failwith "Expected startup spine"
                { original with Nodes = original.Nodes.Add(extra.Id, extra).Add(spine.Id, { spine with Kind = SemanticKind.Sequential(extra.Id :: values); Children = extra.Id :: values }) }
        Assert.Empty(EffectRanges.recognize changed)
        let analyzed = LazyEffects.analyze changed
        Assert.Empty(LazyEffects.obligations analyzed)
        Assert.Empty(analyzed.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LazyEffectRange))
        Assert.NotEqual(Some(ValueRange.Bounded(bound.Lower, bound.Upper)), analyzed.Nodes[bound.Cell].ValueRange)
        Assert.Single(EffectRanges.recognize original) |> ignore

    [<Fact>]
    member _.``Unchanged analysis preserves joint obligation identity and proof participants`` () =
        let first = LazyEffects.check LazyEffects.twoFactories |> LazyEffects.analyze
        let second = LazyEffects.analyze first
        let oldProof, newProof = Assert.Single(LazyEffects.obligations first), Assert.Single(LazyEffects.obligations second)
        Assert.Equal(oldProof.Id, newProof.Id)
        let participants graph proof = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.Constrains && edge.Target = proof.Id) |> Assert.Single |> _.Sources
        Assert.Equal<NodeId list>(participants first oldProof, participants second newProof)
