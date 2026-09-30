namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module EffectRanges = Clef.Compiler.PSGSaturation.SemanticGraph.LazyEffectRanges
module EffectRangeAnalysis = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis
module EffectLazyValues = Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues
module EffectDemand = Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand
module EffectDemandPass = Clef.Compiler.Nanopass.OrdinaryDemand

module private LazyEffects =
    let private parse source =
        parseAndCheck ("module LazyEffects\n" + source) "lazy-effects.clef"

    let check source =
        match parse source with
        | Success result | CheckFailure result ->
            Assert.Empty(result.Diagnostics |> List.filter (fun diagnostic -> Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error))
            result.Graph
        | ParseFailure errors -> failwithf "%A" errors

    let unobservable subject owner =
        sprintf "The range of '%s' in '%s' cannot be observed; bound it with a comparison, a modulus or a clamp" subject owner

    let rejected expectedSites source =
        match parse source with
        | CheckFailure result ->
            let actual = CheckResult.errors result |> List.map (fun diagnostic ->
                Assert.Equal("CCS8011", diagnostic.Code)
                Assert.Equal("lazy-effects.clef", diagnostic.Range.File)
                let node = result.Graph.Nodes[Assert.Single diagnostic.RelatedNodes]
                Assert.True(node.IsReachable)
                Assert.True((node.Range = diagnostic.Range), "The refusal must identify its actual source node")
                Assert.True(node.ValueRange |> Option.exists (ValueRange.isObservable >> not), "The rejected lazy-effect source node must remain nonobservable")
                diagnostic.Message, diagnostic.Range.Start.Line, diagnostic.Range.Start.Column,
                diagnostic.Range.End.Line, diagnostic.Range.End.Column)
            Assert.Equal<(string * int * int * int * int) list>(List.sort expectedSites, List.sort actual)
            result.Graph
        | result -> failwithf "Expected the exact located lazy-effect source refusals: %A" result

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
    let ordinaryFunction localCell =
        let declaration = "let mutable executions = 0\n"
        (if localCell then "let observe () =\n    " + declaration else declaration + "let observe () =\n") + """
    let value = lazy (executions <- executions + 1; true)
    let alias = value
    let first = Lazy.force alias
    let second = Lazy.force value
    if first && second then executions else 9
[<EntryPoint>]
let main _ = observe ()
"""
    let cell (graph: SemanticGraph) = graph.Nodes.Values |> Seq.filter (fun node ->
        node.IsReachable && match node.Kind with SemanticKind.Binding("executions", true, _, _) -> true | _ -> false) |> Assert.Single
    let proof graph = EffectRanges.recognize graph |> Assert.Single
    let analyze graph = EffectRangeAnalysis.run graph.Platform graph |> fst
    let renewDemand graph =
        let failures =
            match EffectDemand.tryRead graph with
            | Result.Error failures -> Assert.NotEmpty failures; failures
            | Result.Ok _ -> failwith "Removing startup authority must invalidate the retained demand support"
        let untouched, diagnostics = EffectRangeAnalysis.run graph.Platform graph
        Assert.Same(graph, untouched)
        Assert.Equal<Diagnostic list>(EffectDemand.diagnostics graph failures, diagnostics)
        let current = EffectDemandPass.normalize graph
        Assert.True(EffectDemand.tryRead current |> Result.isOk)
        current

    let analyzeChanged graph =
        // The changed structural census also invalidates ordinary-demand rows.
        // Renew that owning prerequisite before asking range analysis to settle.
        let current = Clef.Compiler.Nanopass.OrdinaryDemand.normalize graph
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.tryRead current |> Result.isOk)
        Assert.Empty(EffectRanges.recognize current)
        analyze current
    let withChildren (graph: SemanticGraph) id children =
        let node = { graph.Nodes[id] with Children = children }
        let retained = graph.Edges |> List.filter (fun edge ->
            edge.Target <> id || (edge.Class <> EdgeClass.Structural && edge.Class <> EdgeClass.Reference))
        let incidence =
            Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence node
            |> List.filter (fun edge -> edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference)
        { graph with Nodes = graph.Nodes.Add(id, node); Edges = incidence @ retained }
    let obligations (graph: SemanticGraph) = graph.Nodes.Values |> Seq.filter (fun node ->
        match node.Kind with SemanticKind.Obligation { Body = ObligationBody.FiniteAdditiveEffects _ } -> true | _ -> false) |> Seq.toList

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "LazyEffectRanges")>]
type LazyEffectRangeCases() =
    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``An ordinary function retains one memo instance for a module or locally captured counter`` localCell =
        let graph = LazyEffects.ordinaryFunction localCell |> LazyEffects.check
        let bound = LazyEffects.proof graph
        Assert.Equal(0I, bound.Lower)
        Assert.Equal(1I, bound.Upper)
        let contribution = Assert.Single bound.Contributions
        Assert.Equal(1I, contribution.Count)
        Assert.Equal(Some(ValueRange.Bounded(0I, 1I)), (LazyEffects.cell graph).ValueRange)
        Assert.Equal(Some(ValueRange.Bounded(1I, 1I)), graph.Nodes[contribution.Value].ValueRange)
        let protocol = EffectLazyValues.settle graph
        Assert.Single protocol.Instances |> ignore
        Assert.Equal(2, protocol.Forces.Count)
        let required = graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.LazyMemoization || match edge.Role with EdgeRole.LazyCapture _ -> true | _ -> false)
        for edge in required do
            for participant in edge.Target :: edge.Sources do Assert.Contains(participant, bound.Participants)

    [<Fact>]
    member _.``Distinct lazy formations share a local captured counter without counting its alias again`` () =
        let graph = LazyEffects.check """
let observe () =
    let mutable executions = 0
    let first = lazy (executions <- executions + 1; true)
    let second = lazy (executions <- executions + 1; false)
    let alias = first
    let both = Lazy.force first && not (Lazy.force second) && Lazy.force alias
    if both then executions else 9
[<EntryPoint>]
let main _ = observe ()
"""
        let bound = LazyEffects.proof graph
        Assert.Equal(0I, bound.Lower)
        Assert.Equal(2I, bound.Upper)
        Assert.Equal(2, bound.Contributions.Length)
        Assert.Equal(2, bound.Contributions |> List.map _.Formation |> Set.ofList |> Set.count)
        Assert.All(bound.Contributions, fun contribution -> Assert.Equal(1I, contribution.Count))
        Assert.Equal(Some(ValueRange.Bounded(0I, 2I)), (LazyEffects.cell graph).ValueRange)
        let protocol = EffectLazyValues.settle graph
        Assert.Equal(2, protocol.Instances.Count)
        Assert.Equal(3, protocol.Forces.Count)

    [<Theory>]
    [<InlineData("missing-initializer-child")>]
    [<InlineData("captured-binding-child")>]
    [<InlineData("duplicate-initializer-incidence")>]
    [<InlineData("missing-capture-premise")>]
    [<InlineData("computed-already-true")>]
    [<InlineData("computed-literal-with-child")>]
    member _.``Local capture formation requires its exact initialization and capture premises`` defect =
        let original = LazyEffects.ordinaryFunction true |> LazyEffects.check
        let bound = LazyEffects.proof original
        let instance = (EffectLazyValues.settle original).Instances.Values |> Assert.Single
        let environment = original.Nodes[instance.Environment]
        Assert.Equal<NodeId list>([instance.InitialComputed], environment.Children)
        let changed =
            match defect with
            | "missing-initializer-child" | "captured-binding-child" ->
                let children = if defect = "missing-initializer-child" then [] else [instance.InitialComputed; bound.Cell]
                LazyEffects.withChildren original environment.Id children
            | "duplicate-initializer-incidence" ->
                let row = original.Edges |> List.find (fun edge ->
                    edge.Target = environment.Id && edge.Role = EdgeRole.EnvironmentInitializer && edge.Ordinal = 1)
                { original with Edges = row :: original.Edges }
            | "missing-capture-premise" ->
                let edges = original.Edges |> List.filter (fun edge ->
                    edge.Target <> environment.Id || match edge.Role with EdgeRole.LazyCapture _ -> false | _ -> true)
                { original with Edges = edges }
            | "computed-literal-with-child" ->
                LazyEffects.withChildren original instance.InitialComputed [bound.Initializer]
            | _ ->
                let initial = original.Nodes[instance.InitialComputed]
                { original with Nodes = original.Nodes.Add(initial.Id, { initial with Kind = SemanticKind.Literal(NativeLiteral.Bool true) }) }
        Assert.Empty(EffectRanges.recognize changed)
        let analyzed = LazyEffects.analyzeChanged changed
        Assert.Empty(LazyEffects.obligations analyzed)
        Assert.Empty(analyzed.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LazyEffectRange))
        Assert.NotEqual(Some(ValueRange.Bounded(bound.Lower, bound.Upper)), analyzed.Nodes[bound.Cell].ValueRange)
        Assert.Single(EffectRanges.recognize original) |> ignore

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``A module counter still requires the exact memo environment initialization`` malformedLiteral =
        let original = LazyEffects.ordinaryFunction false |> LazyEffects.check
        let bound = LazyEffects.proof original
        let instance = (EffectLazyValues.settle original).Instances.Values |> Assert.Single
        let changed =
            if malformedLiteral then LazyEffects.withChildren original instance.InitialComputed [bound.Initializer]
            else LazyEffects.withChildren original instance.Environment []
        Assert.Empty(EffectRanges.recognize changed)
        let analyzed = LazyEffects.analyzeChanged changed
        Assert.Empty(LazyEffects.obligations analyzed)
        Assert.Empty(analyzed.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LazyEffectRange))
        Assert.NotEqual(Some(ValueRange.Bounded(bound.Lower, bound.Upper)), analyzed.Nodes[bound.Cell].ValueRange)
        Assert.Single(EffectRanges.recognize original) |> ignore

    [<Fact>]
    member _.``A cyclic computed initializer loses its instance before recursive formation validation`` () =
        let original = LazyEffects.ordinaryFunction true |> LazyEffects.check
        let instance = (EffectLazyValues.settle original).Instances.Values |> Assert.Single
        let initial = original.Nodes[instance.InitialComputed]
        let cycle =
            { initial with
                Kind = SemanticKind.LazyEnvironment(instance.Formation, [instance.Computed, instance.Environment])
                Type = original.Nodes[instance.Environment].Type
                Children = [instance.Environment] }
        let changed = { original with Nodes = original.Nodes.Add(cycle.Id, cycle) }
        Assert.Empty((EffectLazyValues.settle changed).Instances)
        Assert.Empty(EffectRanges.recognize changed)
        Assert.Single(EffectRanges.recognize original) |> ignore

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
        let graph =
            if defect = "library" then LazyEffects.check source
            else
                let message = LazyEffects.unobservable
                let changedSites =
                    match defect with
                    | "loop" ->
                        [ message "the result of '+'" "make", 4, 34, 4, 48
                          message "main" "main", 7, 4, 10, 14
                          message "main …" "__clef_program_entry", 5, 0, 5, 0 ]
                    | "extra-store" ->
                        [ message "the result of '+'" "main", 6, 36, 6, 50
                          message "the result of '+'" "main", 7, 18, 7, 32
                          message "main …" "__clef_program_entry", 4, 0, 4, 0 ]
                    | "mutable-alias" ->
                        [ message "the result of '+'" "main", 6, 36, 6, 50
                          message "main" "main", 8, 4, 9, 14
                          message "main …" "__clef_program_entry", 4, 0, 4, 0 ]
                    | "recursive" ->
                        [ message "the result of '+'" "make", 4, 34, 4, 48
                          message "main" "main", 10, 13, 10, 35
                          message "main …" "__clef_program_entry", 9, 0, 9, 0 ]
                    | _ -> failwithf "Unknown rejected lazy-effect fixture: %s" defect
                let sites = (message "executions" "__clef_program_entry", 3, 12, 3, 22) :: changedSites
                LazyEffects.rejected sites source
        Assert.Empty(EffectRanges.recognize graph)
        Assert.Empty(LazyEffects.obligations graph)
        if defect <> "library" then
            Assert.True((LazyEffects.cell graph).ValueRange |> Option.exists (ValueRange.isObservable >> not))

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
        let current = if defect = "startup" then LazyEffects.renewDemand changed else changed
        // Demand settlement must leave the old effect proof and annotation
        // resident; range analysis owns their subsequent withdrawal.
        let oldProofIds = LazyEffects.obligations changed |> List.map _.Id
        let currentProofIds = LazyEffects.obligations current |> List.map _.Id
        Assert.NotEmpty oldProofIds
        Assert.Equal<NodeId list>(oldProofIds, currentProofIds)
        Assert.Equal(changed.Nodes[bound.Cell].ValueRange, current.Nodes[bound.Cell].ValueRange)
        Assert.Empty(EffectRanges.recognize current)
        let analyzed, diagnostics = EffectRangeAnalysis.run current.Platform current
        Assert.All(diagnostics, fun diagnostic -> Assert.Equal("CCS8011", diagnostic.Code))
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

module BorrowExtentShapes = Clef.Compiler.Baker.Ingredients.ArrayShapes
module BorrowExtentOrigins = Clef.Compiler.Baker.Recipes.StringComparisonRecipes

module private BorrowExtentFixture =
    let admitted text count =
        let source =
            "let make () = lazy \"" + text + "\"\n" +
            "[<EntryPoint>]\nlet main _ =\n" +
            "    let delayed = make ()\n    let alias = delayed\n" +
            "    let value = Lazy.force alias\n    let bytes = value.Bytes\n    Array.length bytes\n"
        let graph = LazyEffects.check source
        Assert.True(graph.Platform.IsNone)
        let view = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.StringByteBorrow _ -> true | _ -> false) |> Assert.Single
        let source = match view.Kind with SemanticKind.StringByteBorrow source -> source | _ -> failwith "Missing logical view"
        let flow = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
        let identity,origins,participants =
            match BorrowExtentOrigins.stringOrigin graph flow view.Id source with
            | Ok(Some value) -> value
            | other -> failwithf "The owning source origin did not settle: %A" other
        Assert.NotEmpty origins
        Assert.All(origins.Values, fun length -> Assert.Equal<bigint>(count,length))
        Assert.Contains(participants, fun participant -> participant.Role=ParticipantRole.LazyStringOrigin)
        let extent = BorrowExtentShapes.reader graph view.Id |> Option.defaultWith (fun () -> failwith "Missing logical borrowed extent")
        Assert.Equal<BorrowExtentShapes.Length list>(origins.Values |> Seq.map BorrowExtentShapes.Length.Constant |> Seq.toList,extent.Sources)
        Assert.Equal<Set<NodeId>>(origins.Keys |> Set.ofSeq,extent.StringSources)
        for id in view.Id::source::identity::(participants |> List.collect (fun participant -> [participant.Node;participant.Group])) do
            Assert.Contains(id,extent.Participants)
        let lengths = BorrowExtentShapes.observations graph
        Assert.NotEmpty lengths
        for KeyValue(site,_) in lengths do Assert.Equal<ValueRange option>(Some(ValueRange.point count),graph.Nodes[site].ValueRange)
        Assert.DoesNotContain(graph.Edges, fun edge -> match edge.Role with EdgeRole.StringByteView _ | EdgeRole.StringByteStorage _ -> true | _ -> false)
        let lazyFacts = EffectLazyValues.settle graph
        Assert.Empty lazyFacts.Residuals
        Assert.NotEmpty lazyFacts.Forces
        graph,view

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "LazyEffectRange")>]
type LazyBorrowExtentCases() =
    [<Theory>]
    [<InlineData("é",2)>]
    [<InlineData("value",5)>]
    member _.``Lazy borrowed byte length reuses exact source origin evidence``(text:string,count:int) =
        BorrowExtentFixture.admitted text (bigint count) |> ignore

    [<Theory>]
    [<InlineData("view-children")>]
    [<InlineData("unexpected-view-incidence")>]
    [<InlineData("duplicate-view-incidence")>]
    [<InlineData("missing-memoization")>]
    [<InlineData("memoization-ordinal")>]
    [<InlineData("memoization-class")>]
    member _.``Borrowed logical extent refuses damaged view or lazy protocol``(mutation:string) =
        let graph,view = BorrowExtentFixture.admitted "é" 2I
        let memoization = graph.Edges |> List.filter (fun edge -> edge.Role=EdgeRole.LazyMemoization)
        Assert.NotEmpty memoization
        let changed =
            match mutation with
            | "view-children" -> {graph with Nodes=graph.Nodes.Add(view.Id,{view with Children=[]})}
            | "unexpected-view-incidence" ->
                let edge = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence view |> Assert.Single
                {graph with Edges={edge with Ordinal=edge.Ordinal+1}::graph.Edges}
            | "duplicate-view-incidence" ->
                let edge = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence view |> Assert.Single
                {graph with Edges=edge::edge::graph.Edges}
            | "missing-memoization" ->
                let edges = graph.Edges |> List.filter (fun edge -> edge.Role<>EdgeRole.LazyMemoization)
                {graph with Edges=edges}
            | "memoization-ordinal" ->
                let edges = graph.Edges |> List.map (fun edge ->
                    if edge.Role=EdgeRole.LazyMemoization then {edge with Ordinal=edge.Ordinal+1} else edge)
                {graph with Edges=edges}
            | "memoization-class" ->
                let edges = graph.Edges |> List.map (fun edge ->
                    if edge.Role=EdgeRole.LazyMemoization then {edge with Class=EdgeClass.Structural} else edge)
                {graph with Edges=edges}
            | other -> failwithf "Unknown mutation: %s" other
        // Renew the separate demand owner, without repairing the lazy relation.
        let current = EffectDemandPass.normalize changed
        Assert.True(EffectDemand.tryRead current |> Result.isOk)
        if mutation.Contains("memoization") then Assert.NotEmpty((EffectLazyValues.settle current).Residuals)
        Assert.True((BorrowExtentShapes.reader current view.Id).IsNone,mutation)
