namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Activation = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramActivation
module Startup = Clef.Compiler.Nanopass.ProgramInitialization
module StartupFacts = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization
module EntryResidence = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence
module EntryEnvironments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments

module private ActivationFixture =
    let source recursive =
        "let input = seq { yield 1; yield 2 }\n" +
        (if recursive then
            "let rec read again =\n    for value in input do ignore value\n    if again then read false else 0\nlet invoke () = read true\n"
         else
            "let read () =\n    for value in input do ignore value\n    0\nlet invoke () = read ()\n") +
        "[<EntryPoint>]\nlet main _ = invoke ()\n"

    let check source =
        let result =
            match parseAndCheck ("module ActivationFixture\n" + source) "program-activation.clef" with
            | Success result -> DimensionalCases.noErrors result; result
            | CheckFailure result -> failwithf "Expected admitted source: %A" result.Diagnostics
            | ParseFailure errors -> failwithf "Expected parsed source: %A" errors
        let moduleId = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.ModuleDef("ActivationFixture", _) -> true | _ -> false) |> Assert.Single |> _.Id
        let graph, diagnostics = Startup.normalize [moduleId] result.Graph
        Assert.Empty diagnostics
        Assert.True((StartupFacts.read graph).IsSome)
        Clef.Compiler.PSGSaturation.SemanticGraph.Reachability.markUnreachable graph

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false) |> Assert.Single

    let lambda name graph = (binding name graph).Children |> Assert.Single

    let sequence (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false) |> Assert.Single

    let residence graph = EntryResidence.analyzeWithRegions graph Map.empty Map.empty

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ProgramActivation")>]
type ProgramActivationCases() =
    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Wrapper backing covers complete transitive calls and rooted recursion`` recursive =
        let graph = ActivationFixture.check (ActivationFixture.source recursive)
        // The source Parent projection remains lexical and is not proof.
        let graph = { graph with Nodes = graph.Nodes |> Map.map (fun _ node -> { node with Parent = None }) }
        let plan = (StartupFacts.read graph).Value
        let read = ActivationFixture.lambda "read" graph
        let covered = Activation.coverage (Activation.analyze graph) plan.EntryLambda read |> Option.get
        Assert.Empty covered.Dependencies
        let callEdges = covered.Evidence |> List.filter (fun edge -> edge.Role = EdgeRole.ProgramActivationCall)
        Assert.True(callEdges.Length >= 3)
        for edge in callEdges do
            match edge.Sources, graph.Nodes[edge.Target].Kind with
            | [wrapper; caller; callee; implementation], SemanticKind.Application(actual, arguments) ->
                Assert.Equal(plan.EntryLambda, wrapper)
                Assert.Equal(actual, callee)
                Assert.True(graph.Nodes.ContainsKey caller)
                Assert.Equal(Some implementation, EntryEnvironments.tryImplementation graph actual)
                match graph.Nodes[implementation].Kind with
                | SemanticKind.Lambda(parameters, _, _, _, _) -> Assert.Equal(parameters.Length, arguments.Length)
                | _ -> failwith "Coverage lost its actual callable boundary"
            | other -> failwithf "Incomplete activation incidence: %A" other
        let reading = ActivationFixture.residence graph
        Assert.Empty reading.Unresolved
        Assert.Equal(Some EscapeKind.StackScoped, reading.Sites.TryFind (ActivationFixture.sequence graph).Id)
        Assert.DoesNotContain(reading.Sites.Values, fun lifetime -> lifetime <> EscapeKind.StackScoped)
        Assert.Contains(reading.Evidence, fun edge -> edge.Role = EdgeRole.ProgramActivationCoverage && edge.Target = read)

    [<Fact>]
    member _.``Program formed callback retains its private cell and deferred owner prerequisites``() =
        let graph = ActivationFixture.check """
let input = seq { yield 1; yield 2 }
let mapper =
    let mutable calls = 0
    fun value -> calls <- value; value
let mapped = Seq.map mapper input
[<EntryPoint>]
let main _ =
    for value in mapped do ignore value
    0
"""
        let plan = (StartupFacts.read graph).Value
        let owner = graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && match node.Kind with SemanticKind.ClosureValue _ -> true | _ -> false) |> Assert.Single
        let implementation, environment = match owner.Kind with SemanticKind.ClosureValue(code, env) -> code, env | _ -> failwith "Expected callback"
        let cell = ActivationFixture.binding "calls" graph
        Assert.Contains(EntryEnvironments.captures graph owner.Id, fun capture -> capture.SourceNodeId = Some cell.Id && capture.IsMutable)
        let coverage = Activation.coverage (Activation.analyze graph) plan.EntryLambda implementation |> Option.get
        Assert.NotEmpty coverage.Dependencies
        for dependency in coverage.Dependencies do
            match graph.Nodes[dependency].Kind with
            | SemanticKind.Lambda(_, _, _, _, LambdaContext.SeqGenerator) -> ()
            | _ -> failwith "Ordinary coverage fabricated a deferred execution root"
        let reading = EntryResidence.analyzeEnvironments graph
        Assert.Empty reading.Unresolved
        Assert.Equal(Some EscapeKind.StackScoped, reading.Sites.TryFind environment)
        Assert.Contains(reading.Evidence, fun edge -> edge.Role = EdgeRole.EnvironmentResidence && List.contains cell.Id edge.Sources)
        let projection = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.EnvironmentReference _ -> true | _ -> false) |> Assert.Single
        let escaped =
            { graph with Edges = { Sources = [projection.Id]; Target = plan.SourceBinding
                                   Class = EdgeClass.Reference; Role = EdgeRole.Symbol; Ordinal = 0 } :: graph.Edges }
        Assert.True((Activation.coverage (Activation.analyze escaped) plan.EntryLambda implementation).IsNone)

    [<Theory>]
    [<InlineData("opaque-reference")>]
    [<InlineData("partial-call")>]
    [<InlineData("unowned-call")>]
    [<InlineData("external-root")>]
    [<InlineData("missing-startup")>]
    member _.``Unknown invocation or escape evidence cannot inherit wrapper residence`` damage =
        let graph = ActivationFixture.check (ActivationFixture.source false)
        let plan = (StartupFacts.read graph).Value
        let readBinding = ActivationFixture.binding "read" graph
        let implementation = Assert.Single readBinding.Children
        let call = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Application(callee, _) -> EntryEnvironments.tryImplementation graph callee = Some implementation | _ -> false) |> Assert.Single
        let damaged =
            match damage with
            | "opaque-reference" ->
                { graph with Edges = { Sources = [readBinding.Id]; Target = plan.SourceBinding
                                       Class = EdgeClass.Reference; Role = EdgeRole.Symbol; Ordinal = 0 } :: graph.Edges }
            | "partial-call" ->
                let callee = match call.Kind with SemanticKind.Application(callee, _) -> callee | _ -> failwith "Expected call"
                let changed = { call with Kind = SemanticKind.Application(callee, []); Children = [callee] }
                { graph with Nodes = graph.Nodes.Add(changed.Id, changed) }
            | "unowned-call" ->
                let extra = { call with Id = NodeId.fresh(); Parent = None }
                { graph with Nodes = graph.Nodes.Add(extra.Id, extra) }
            | "external-root" -> { graph with DeclarationRoots = (readBinding.Id, DeclRoot.EntryPoint) :: graph.DeclarationRoots }
            | "missing-startup" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramInitialization) }
            | _ -> failwith "Unexpected damage"
        Assert.True((Activation.coverage (Activation.analyze damaged) plan.EntryLambda implementation).IsNone)
        let reading = ActivationFixture.residence damaged
        let input = ActivationFixture.sequence damaged
        Assert.False(reading.Sites.ContainsKey input.Id)
        Assert.Contains(reading.Unresolved, fun failure -> failure.Site = input.Id)

    [<Fact>]
    member _.``An unrooted recursive call cycle supplies no coverage proof``() =
        let graph = ActivationFixture.check (ActivationFixture.source true)
        let plan = (StartupFacts.read graph).Value
        let implementation = ActivationFixture.lambda "read" graph
        let invoke = ActivationFixture.lambda "invoke" graph
        let invokeBody = match graph.Nodes[invoke].Kind with SemanticKind.Lambda(_, body, _, _, _) -> body | _ -> failwith "Expected invoke"
        let rec calls id =
            let node = graph.Nodes[id]
            match node.Kind with
            | SemanticKind.Application(callee, _) when EntryEnvironments.tryImplementation graph callee = Some implementation -> [id]
            | _ -> node.Children |> List.collect calls
        let outside = calls invokeBody |> List.distinct |> Assert.Single
        let old = graph.Nodes[outside]
        let changed = { old with Kind = SemanticKind.Literal(NativeLiteral.Int(0L, Types.tryGetNTUKind old.Type |> Option.get)); Children = [] }
        let damaged = { graph with Nodes = graph.Nodes.Add(outside, changed) }
        Assert.True((Activation.coverage (Activation.analyze damaged) plan.EntryLambda implementation).IsNone)

    [<Fact>]
    member _.``A returning factory cannot retain activation local sequence storage``() =
        let graph = ActivationFixture.check """
let produce () = seq { yield 1 }
[<EntryPoint>]
let main _ =
    for value in produce () do ignore value
    0
"""
        let reading = ActivationFixture.residence graph
        let local = ActivationFixture.sequence graph
        Assert.False(reading.Sites.ContainsKey local.Id)
        Assert.Contains(reading.Unresolved, fun failure ->
            failure.Site = local.Id && match failure.Reason with EntryResidence.ResidualReason.ReturnsFrom _ -> true | _ -> false)
