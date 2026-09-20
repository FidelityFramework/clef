namespace Clef.Compiler.Service.Tests

open System.Collections.Generic
open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module MatchRecipes = Clef.Compiler.Baker.Recipes.MatchRecipes
module MatchContext = Clef.Compiler.Baker.Recipes.Decomposition

module private NestedMatch =
    let check source =
        match parseAndCheck ("module Nested\n[<Measure>] type m\n" + source + "\n[<EntryPoint>]\nlet main _ = ignore observed; 0\n") "nested-match.clef" with
        | Success result -> DimensionalCases.noErrors result; result.Graph
        | CheckFailure result -> failwithf "Expected admitted nested match: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed nested match: %A" errors

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false) |> Assert.Single

    // A small evaluator for the emitted decision algebra. Invalid payload reads
    // fail immediately, so None paths cannot pass by reading a different case.
    type Value = Number of int64 | Boolean of bool | Union of int * Value option
    let evaluate (graph: SemanticGraph) root =
        let bound = Dictionary<NodeId, Value>()
        let rec value id =
            match graph.Nodes[id].Kind with
            | SemanticKind.Literal(NativeLiteral.Int(number, _)) -> Number number
            | SemanticKind.Literal(NativeLiteral.Bool boolean) -> Boolean boolean
            | SemanticKind.DUConstruct(_, tag, payload, _) | SemanticKind.UnionCase(_, tag, payload) -> Union(tag, Option.map value payload)
            | SemanticKind.Binding _ ->
                let result = value (Assert.Single graph.Nodes[id].Children)
                bound[id] <- result
                result
            | SemanticKind.VarRef(_, Some source) ->
                match bound.TryGetValue source with true, result -> result | _ -> value source
            | SemanticKind.TypeAnnotation(input, _) -> value input
            | SemanticKind.Sequential expressions -> expressions |> List.map value |> List.last
            | SemanticKind.IfThenElse(condition, yes, Some no) ->
                match value condition with Boolean true -> value yes | Boolean false -> value no | actual -> failwithf "Nonboolean guard %A" actual
            | SemanticKind.DUEliminate(input, expected, _, _) ->
                match value input with Union(actual, Some payload) when actual = expected -> payload | actual -> failwithf "Unguarded payload read for tag %d from %A" expected actual
            | SemanticKind.CaseElimination(input, arms) ->
                let observed = value input
                let matches = function
                    | Pattern.Wildcard -> true
                    | Pattern.Union(_, expected, _, _) -> match observed with Union(actual, _) -> expected = actual | _ -> false
                    | other -> failwithf "Unexpected decision pattern %A" other
                let arm = arms |> List.find (fun arm -> matches arm.Pattern)
                Assert.Empty arm.Bindings
                Assert.True(Option.isNone arm.Guard, "Source guards belong in the admitted branch body")
                value arm.Body
            | kind -> failwithf "Unexpected decision operation %A" kind
        value root

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "NestedMatch")>]
type NestedMatchCases() =
    [<Theory>]
    [<InlineData("None", 0L)>]
    [<InlineData("Some None", 1L)>]
    [<InlineData("Some (Some 5<m>)", 2L)>]
    member _.``Nested constructor decisions preserve all three cases``(input: string, expected: int64) =
        let graph = NestedMatch.check ("let input: int<m> option option = " + input + "\nlet observed =\n    match input with\n    | Some None -> 1\n    | Some (Some value) -> 2\n    | _ -> 0\n")
        Assert.Equal(NestedMatch.Number expected, NestedMatch.evaluate graph (NestedMatch.binding "observed" graph).Id)
        let decisions = graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && match node.Kind with SemanticKind.CaseElimination _ -> true | _ -> false) |> Seq.toList
        Assert.True(decisions.Length >= 3)
        for decision in decisions do
            match decision.Kind with
            | SemanticKind.CaseElimination(_, arms) ->
                for arm in arms do
                    match arm.Pattern with
                    | Pattern.Union(_, _, Some Pattern.Wildcard, _) | Pattern.Union(_, _, None, _) | Pattern.Wildcard -> ()
                    | pattern -> failwithf "A refutable payload pattern was left for the witness: %A" pattern
            | _ -> ()

    [<Theory>]
    [<InlineData("None", "true", 7L)>]
    [<InlineData("Some None", "true", 4L)>]
    [<InlineData("Some (Some 3<m>)", "false", 7L)>]
    [<InlineData("Some (Some 3<m>)", "true", 3L)>]
    member _.``Source guards run after nested selection and retain later cases``(input: string, guard: string, expected: int64) =
        let graph = NestedMatch.check ("let input: int<m> option option = " + input + "\nlet observed =\n    match input with\n    | Some (Some value) when " + guard + " -> value\n    | Some None -> 4<m>\n    | _ -> 7<m>\n")
        Assert.Equal(NestedMatch.Number expected, NestedMatch.evaluate graph (NestedMatch.binding "observed" graph).Id)
        let source = NestedMatch.binding "value" graph
        Assert.Equal<NativeType>((NestedMatch.binding "observed" graph).Type, source.Type)
        Assert.Contains(graph.Nodes.Values, fun node -> match node.Kind with SemanticKind.VarRef("value", Some id) -> id = source.Id && node.Range = source.Range | _ -> false)

    [<Fact>]
    member _.``Nested match forms one eager scrutinee snapshot``() =
        let graph = NestedMatch.check "let mutable calls = 0\nlet make () = calls <- 1; (Some None: int<m> option option)\nlet observed = match make () with Some None -> true | _ -> false\n"
        let root = graph.Nodes[Assert.Single (NestedMatch.binding "observed" graph).Children]
        let snapshot, decision = match root.Kind with SemanticKind.Sequential [snapshot; decision] -> snapshot, decision | kind -> failwithf "Lost eager scrutinee: %A" kind
        let call = graph.Nodes[Assert.Single graph.Nodes[snapshot].Children]
        Assert.True(match call.Kind with SemanticKind.Application _ -> true | _ -> false)
        let input = match graph.Nodes[decision].Kind with SemanticKind.CaseElimination(input, _) -> input | kind -> failwithf "Missing first decision: %A" kind
        Assert.True(match graph.Nodes[input].Kind with SemanticKind.VarRef(_, Some source) -> source = snapshot | _ -> false)
        let owners = graph.Nodes.Values |> Seq.filter (fun node -> List.contains call.Id node.Children) |> Seq.toList
        Assert.Equal<NodeId list>([snapshot], owners |> List.map _.Id)

    [<Fact>]
    member _.``Nested extraction preserves original source binding identity range and metadata``() =
        let builder = NodeBuilder()
        let range: SourceRange = { File = "binding-origin.clef"; Start = { Line = 4; Column = 10 }; End = { Line = 4; Column = 17 } }
        let inner = NativeType.TApp(Types.optionTyCon, [Types.boolType])
        let outer = NativeType.TApp(Types.optionTyCon, [inner])
        let input = builder.Create(SemanticKind.PatternBinding "input", outer, range)
        let source = builder.Create(SemanticKind.PatternBinding "payload", Types.boolType, range)
        let body = builder.Create(SemanticKind.VarRef("payload", Some source.Id), Types.boolType, range)
        let other = builder.Create(SemanticKind.Literal(NativeLiteral.Bool false), Types.boolType, range)
        let original = { source with Metadata = Map.ofList ["SourceTest", MetadataValue.String "retained"] }
        let graph = builder.Build []
        let graph = { graph with Nodes = Map.add source.Id original graph.Nodes }
        let pattern = Pattern.Union("Some", 1, Some(Pattern.Tuple [Pattern.Union("Some", 1, Some(Pattern.Tuple [Pattern.Var("payload", Types.boolType)]), inner)]), outer)
        let cases = [{ Pattern = pattern; PatternBindings = [source.Id]; Guard = None; Body = body.Id }; { Pattern = Pattern.Wildcard; PatternBindings = []; Guard = None; Body = other.Id }]
        let operationRange = { range with Start = { Line = 3; Column = 0 } }
        let context = MatchContext.mkContext operationRange Types.boolType None "Match" input.Id
        let result = MatchRecipes.enrichMatch graph context input.Id cases Types.boolType
        let emitted = result.NewNodes |> List.filter (fun node -> node.Id = source.Id) |> Assert.Single
        Assert.Equal(range, emitted.Range)
        Assert.Equal(original.Metadata["SourceTest"], emitted.Metadata["SourceTest"])
        Assert.Equal(SemanticKind.Binding("payload", false, false, None), emitted.Kind)
        Assert.Equal(SemanticKind.VarRef("payload", Some source.Id), graph.Nodes[body.Id].Kind)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "BranchOccurrences")>]
type BranchOccurrenceCases() =
    [<Fact>]
    member _.``Nested fallthroughs have separate occurrences with exact source provenance``() =
        let graph = NestedMatch.check "let input: int option option = Some None\nlet observed = match input with Some None -> true | _ -> false\n"
        let fallthroughs = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && node.Kind = SemanticKind.Literal(NativeLiteral.Bool false)) |> Seq.toList
        Assert.Equal(2, fallthroughs.Length)
        let incidence = graph.Nodes.Values |> Seq.collect (fun node -> kindEdges node.Id node.Kind)
                        |> Seq.filter (fun edge -> edge.Class = EdgeClass.Structural && edge.Role = EdgeRole.CaseBody) |> Seq.toList
        for body in fallthroughs do
            incidence |> List.filter (fun edge -> edge.Sources = [body.Id]) |> Assert.Single |> ignore
        let origin = graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.BranchOccurrence && (fallthroughs |> List.exists (fun node -> node.Id = edge.Target))) |> Assert.Single
        Assert.Contains(origin.Target, fallthroughs |> List.map _.Id)
        Assert.Contains(Assert.Single origin.Sources, fallthroughs |> List.map _.Id)
        Assert.Equal(NestedMatch.Boolean true, NestedMatch.evaluate graph (NestedMatch.binding "observed" graph).Id)

    [<Fact>]
    member _.``Independent sequential decisions do not establish exclusive occurrences``() =
        let builder = NodeBuilder()
        let guard = builder.Create(SemanticKind.Literal(NativeLiteral.Bool true), Types.boolType, dummyRange)
        let body = builder.Create(SemanticKind.Literal(NativeLiteral.Bool false), Types.boolType, dummyRange)
        let left = builder.Create(SemanticKind.IfThenElse(guard.Id, body.Id, None), Types.unitType, dummyRange)
        let right = builder.Create(SemanticKind.IfThenElse(guard.Id, body.Id, None), Types.unitType, dummyRange)
        let sequence = builder.Create(SemanticKind.Sequential [left.Id; right.Id], Types.unitType, dummyRange)
        let graph = builder.Build [sequence.Id, DeclRoot.EntryPoint]
        let normalized = Clef.Compiler.Nanopass.BranchOccurrences.normalize graph
        Assert.Equal(graph.Nodes.Count, normalized.Nodes.Count)
        Assert.DoesNotContain(normalized.Edges, fun edge -> edge.Role = EdgeRole.BranchOccurrence)

    [<Fact>]
    member _.``Case arm incidence retains the actual arm ordinal``() =
        let builder = NodeBuilder()
        let source = builder.Create(SemanticKind.PatternBinding "input", Types.boolType, dummyRange)
        let left = builder.Create(SemanticKind.Literal(NativeLiteral.Bool true), Types.boolType, dummyRange)
        let right = builder.Create(SemanticKind.Literal(NativeLiteral.Bool false), Types.boolType, dummyRange)
        let arm body = { Pattern = Pattern.Wildcard; Bindings = []; Guard = None; Body = body }
        let decision = builder.Create(SemanticKind.CaseElimination(source.Id, [arm left.Id; arm right.Id]), Types.boolType, dummyRange)
        let bodies = kindEdges decision.Id decision.Kind |> List.filter (fun edge -> edge.Role = EdgeRole.CaseBody)
        Assert.Equal<(NodeId * int) list>([(left.Id, 0); (right.Id, 1)], bodies |> List.map (fun edge -> Hyperedge.soleSource edge, edge.Ordinal))
