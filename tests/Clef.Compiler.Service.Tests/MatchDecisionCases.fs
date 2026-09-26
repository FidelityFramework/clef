namespace Clef.Compiler.Service.Tests

open System.Collections.Generic
open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

module private SelectedMatch =
    exception RequirementFailed of diagnostic: string * trace: int64 list
    let check source =
        let text = "module SelectedMatch\n" + source + "\n[<EntryPoint>]\nlet main _ = ignore observed; 0\n"
        match parseAndCheck text "selected-match.clef" with
        | Success result -> DimensionalCases.noErrors result; result.Graph
        | CheckFailure result -> failwithf "Match source rejected: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Match source did not parse: %A" errors

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false) |> Assert.Single

    type Value = Number of int64 | Real of float | Text of string | Character of char | Boolean of bool | Unit | Union of int * Value option | Tuple of Value list | Record of Map<string, Value>

    // Interpret the admitted primitive decision algebra, recording observable
    // source assignments. A payload read from a different active case fails;
    // this oracle does not implement source patterns or guard fallthrough.
    let evaluate (graph: SemanticGraph) root =
        let values = Dictionary<NodeId, Value>()
        let trace = ResizeArray<int64>()
        let literal = function
            | NativeLiteral.Int(number, _) -> Number number
            | NativeLiteral.Float(number, _) -> Real number
            | NativeLiteral.String text -> Text text
            | NativeLiteral.Char character -> Character character
            | NativeLiteral.Bool boolean -> Boolean boolean
            | NativeLiteral.Unit -> Unit
            | other -> failwithf "Unsupported oracle literal: %A" other
        let rec value id =
            let node = graph.Nodes[id]
            match node.Kind with
            | SemanticKind.Literal source -> literal source
            | SemanticKind.Binding _ ->
                let result = value (Assert.Single node.Children)
                values[id] <- result
                result
            | SemanticKind.VarRef(_, Some source) ->
                match values.TryGetValue source with true, actual -> actual | _ -> value source
            | SemanticKind.TypeAnnotation(source, _) -> value source
            | SemanticKind.Sequential elements -> elements |> List.map value |> List.last
            | SemanticKind.TupleExpr elements -> Tuple(List.map value elements)
            | SemanticKind.TupleGet(source, ordinal) ->
                match value source with Tuple fields -> fields[ordinal] | other -> failwithf "Invalid tuple projection: %A" other
            | SemanticKind.RecordExpr(fields, _) -> Record(fields |> List.map (fun (name, source) -> name, value source) |> Map.ofList)
            | SemanticKind.FieldGet(source, name) ->
                match value source with Record fields -> fields[name] | other -> failwithf "Invalid field projection: %A" other
            | SemanticKind.DUConstruct(_, tag, payload, _) | SemanticKind.UnionCase(_, tag, payload) -> Union(tag, Option.map value payload)
            | SemanticKind.DUEliminate(source, expected, _, _) ->
                match value source with
                | Union(actual, Some payload) when actual = expected -> payload
                | other -> failwithf "Payload read preceded case %d selection: %A" expected other
            | SemanticKind.Set(target, source) ->
                let actual = value source
                match graph.Nodes[target].Kind, actual with
                | SemanticKind.VarRef(_, Some declaration), Number event -> values[declaration] <- actual; trace.Add event; Unit
                | _ -> failwith "Unexpected assignment in guard oracle"
            | SemanticKind.IfThenElse(condition, yes, Some no) ->
                match value condition with Boolean true -> value yes | Boolean false -> value no | other -> failwithf "Invalid guard %A" other
            | SemanticKind.Application(callee, [left; right]) ->
                match graph.Nodes[callee].Kind with
                | SemanticKind.Intrinsic info when info.Module = IntrinsicModule.Operators && info.Operation = "op_Equality" ->
                    match value left, value right with
                    | Real left, Real right -> Boolean(left = right)
                    | left, right -> Boolean(left = right)
                | other -> failwithf "Unexpected operation in decision oracle: %A" other
            | SemanticKind.Require(condition, diagnostic) ->
                Clef.Compiler.PSGSaturation.SemanticGraph.Requirements.tryRequirement graph id
                |> Option.defaultWith (fun () -> failwith "Requirement lost its source authority") |> ignore
                match value condition with
                | Boolean true -> Unit
                | Boolean false -> raise (RequirementFailed(diagnostic, List.ofSeq trace))
                | other -> failwithf "Invalid requirement condition %A" other
            | SemanticKind.CaseElimination(source, arms) ->
                let actual = value source
                let matches = function
                    | Pattern.Wildcard -> true
                    | Pattern.Const constant -> literal constant = actual
                    | Pattern.Union(_, expected, _, _) -> match actual with Union(tag, _) -> tag = expected | _ -> false
                    | other -> failwithf "Witness-facing decision is not shallow: %A" other
                let selected = arms |> List.find (fun arm -> matches arm.Pattern)
                Assert.Empty selected.Bindings
                Assert.True(selected.Guard.IsNone, "Baker must own source guard execution")
                value selected.Body
            | other -> failwithf "Unexpected decision operation: %A" other
        let result = value root
        result, List.ofSeq trace

    let assertSelected expected events source =
        let graph = check source
        let result, actualEvents = evaluate graph (binding "observed" graph).Id
        Assert.Equal(Number expected, result)
        Assert.Equal<int64 list>(events, actualEvents)
        for node in graph.Nodes.Values do
            if node.IsReachable then
                match node.Kind with
                | SemanticKind.CaseElimination(_, arms) ->
                    for arm in arms do
                        Assert.Empty arm.Bindings
                        Assert.True(arm.Guard.IsNone)
                | _ -> ()
        graph

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "MatchDecision")>]
type MatchDecisionCases() =
    [<Theory>]
    [<InlineData("char", "'\u03a9'", "'\u03bb'", "'\u03a9'")>]
    [<InlineData("float", "1.5", "0.25", "1.5")>]
    [<InlineData("string", "\"same\"", "\"lame\"", "\"same\"")>]
    [<InlineData("string", "\"\"", "\"x\"", "\"\"")>]
    member _.``Literal decisions retain typed equality and source guard fallthrough`` (ty: string, input: string, wrong: string, right: string) =
        let source = sprintf "let mutable trace = 0\nlet input: %s = %s\nlet observed =\n    match input with\n    | %s when (trace <- 1; true) -> 10\n    | %s when (trace <- 2; false) -> 20\n    | %s when (trace <- 3; true) -> 30\n    | _ -> 40\n" ty input wrong right right
        let graph = SelectedMatch.assertSelected 30L [2L; 3L] source
        let rec descendants pending visited =
            match pending with
            | [] -> visited
            | id :: rest when Set.contains id visited -> descendants rest visited
            | id :: rest -> descendants (graph.Nodes[id].Children @ rest) (Set.add id visited)
        let actual = descendants [(SelectedMatch.binding "observed" graph).Id] Set.empty
        let equalities = actual |> Seq.choose (fun id ->
            match graph.Nodes[id].Kind with
            | SemanticKind.Application(callee, [left; right]) ->
                match graph.Nodes[callee].Kind with
                | SemanticKind.Intrinsic info when info.Module = IntrinsicModule.Operators && info.Operation = "op_Equality" -> Some(callee, left, right)
                | _ -> None
            | _ -> None)
        let inputBinding = SelectedMatch.binding "input" graph
        let rec reachesInput seen id =
            if id = inputBinding.Id then true
            elif Set.contains id seen then false
            else
                let seen = Set.add id seen
                match graph.Nodes[id].Kind, graph.Nodes[id].Children with
                | SemanticKind.VarRef(_, Some source), _ -> reachesInput seen source
                | SemanticKind.Binding(_, false, false, _), [source]
                | SemanticKind.TypeAnnotation(source, _), _ -> reachesInput seen source
                | _ -> false
        let expectedLiteral (text: string) =
            match ty with
            | "char" -> NativeLiteral.Char text[1]
            | "float" -> NativeLiteral.Float(System.Double.Parse(text, System.Globalization.CultureInfo.InvariantCulture), NTUKind.NTUfloat(NTUWidth.Fixed 64))
            | _ -> NativeLiteral.String(text.Substring(1, text.Length - 2))
        let expected = [expectedLiteral wrong; expectedLiteral right]
        let actualLiterals =
            equalities |> Seq.map (fun (_, _, right) ->
                match graph.Nodes[right].Kind with SemanticKind.Literal literal -> literal | other -> failwithf "Comparison lost its source literal: %A" other)
            |> Seq.distinct |> Seq.toList
        Assert.Equal(expected.Length, actualLiterals.Length)
        for literal in expected do Assert.Contains(literal, actualLiterals)
        for callee, left, right in equalities do
            Assert.True(reachesInput Set.empty left, "Every repeated decision must retain the original shared match input")
            DimensionalCases.same graph.Nodes[left].Type graph.Nodes[right].Type
            DimensionalCases.same inputBinding.Type graph.Nodes[right].Type
            DimensionalCases.same (NativeType.TFun(graph.Nodes[left].Type, NativeType.TFun(graph.Nodes[right].Type, Types.boolType))) graph.Nodes[callee].Type
        Assert.DoesNotContain(graph.Nodes.Values, fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.CaseElimination(_, arms) -> arms |> List.exists (fun arm -> match arm.Pattern with Pattern.Const _ -> true | _ -> false)
            | _ -> false)

    [<Fact>]
    member _.``Unit literal still selects guards in order through typed semantic equality`` () =
        SelectedMatch.assertSelected 30L [2L; 3L] "let mutable trace = 0\nlet input = ()\nlet observed = match input with () when (trace <- 2; false) -> 20 | () when (trace <- 3; true) -> 30\n" |> ignore

    [<Fact>]
    member _.``A measured literal comparison keeps its source dimension`` () =
        let graph = SelectedMatch.assertSelected 7L [] "[<Measure>] type m\nlet input = 1.5<m>\nlet observed = match input with 1.5<m> -> 7 | _ -> 8\n"
        let comparisons = graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Application(callee, [left; right]) when node.IsReachable ->
                match graph.Nodes[callee].Kind with
                | SemanticKind.Intrinsic info when info.Operation = "op_Equality" -> Some(left, right)
                | _ -> None
            | _ -> None)
        let left, right = Assert.Single comparisons
        DimensionalCases.same graph.Nodes[left].Type graph.Nodes[right].Type
        match graph.Nodes[right].Type with
        | NativeType.TNum(_, dimension) -> Assert.False(dimension.Bases.IsEmpty)
        | other -> failwithf "Measured pattern literal lost its dimension: %A" other

    [<Fact>]
    member _.``A terminal refutable case returns a result only after its actual pattern requirement succeeds`` () =
        let graph = SelectedMatch.assertSelected 7L [] "let input: int option = Some 7\nlet observed = match input with Some selected -> selected\n"
        let requirement = graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && match node.Kind with SemanticKind.Require _ -> true | _ -> false) |> Assert.Single
        let proof = Clef.Compiler.PSGSaturation.SemanticGraph.Requirements.tryRequirement graph requirement.Id |> Option.get
        Assert.True(proof.PatternTest.IsSome)
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.Requirements.tryPatternRequirement graph proof.Continuation |> Option.isSome)

    [<Theory>]
    [<InlineData("None", "true", "")>]
    [<InlineData("Some 7", "false", "1")>]
    member _.``A failed final pattern or final guard terminates before an unselected result`` (input: string, guard: string, trace: string) =
        let source = "let mutable trace = 0\nlet input: int option = " + input + "\nlet observed = match input with Some selected when (trace <- 1; " + guard + ") -> selected\n"
        let graph = SelectedMatch.check source
        try
            SelectedMatch.evaluate graph (SelectedMatch.binding "observed" graph).Id |> ignore
            failwith "A failed requirement returned a match result"
        with SelectedMatch.RequirementFailed(diagnostic, actual) ->
            Assert.StartsWith("Pattern match failed at selected-match.clef:", diagnostic)
            Assert.Equal<int64 list>((if trace = "" then [] else [1L]), actual)

    [<Fact>]
    member _.``Null pattern uses the existing null-free source diagnostic`` () =
        let result =
            match parseAndCheck "module NullPattern\nlet choose (value: string) = match value with null -> false | _ -> true\n" "null-pattern.clef" with
            | Success result | CheckFailure result -> result
            | ParseFailure errors -> failwithf "Null pattern parse failed: %A" errors
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8010")

    [<Fact>]
    member _.``Wrong constructor skips both its payload read and guard`` () =
        SelectedMatch.assertSelected 20L [2L] """
let mutable trace = 0
let input: int option = None
let observed =
    match input with
    | Some value when (trace <- 1; true) -> value
    | None when (trace <- 2; true) -> 20
    | _ -> 30
        """ |> ignore

    [<Theory>]
    [<InlineData("false", 7L, "1,2")>]
    [<InlineData("true", 11L, "1")>]
    member _.``Matching guards preserve same-tag fallthrough and stop after success`` (guard: string, expected: int64, events: string) =
        let source = """
let mutable trace = 0
let input = Some 7
let observed =
    match input with
    | Some first when (trace <- 1; GUARD) -> 11
    | Some second when (trace <- 2; true) -> second
    | _ -> 30
        """
        let source = source.Replace("GUARD", guard)
        SelectedMatch.assertSelected expected (events.Split(',') |> Array.map int64 |> Array.toList) source |> ignore

    [<Fact>]
    member _.``Wrong constant does not execute its guard`` () =
        SelectedMatch.assertSelected 20L [2L] """
let mutable trace = 0
let input = 2
let observed =
    match input with
    | 1 when (trace <- 1; true) -> 10
    | 2 when (trace <- 2; true) -> 20
    | _ -> 30
        """ |> ignore

    [<Theory>]
    [<InlineData("(None, Some 7)", 7L, "2")>]
    [<InlineData("(Some 3, Some 7)", 7L, "1,2")>]
    [<InlineData("(Some 3, None)", 30L, "")>]
    member _.``Tuple components select payloads and bindings before their guard`` (input: string, expected: int64, events: string) =
        let source = """
let mutable trace = 0
let input: int option * int option = INPUT
let observed =
    match input with
    | (Some left, Some right) when (trace <- 1; false) -> left
    | (_, Some selected) when (trace <- 2; true) -> selected
    | _ -> 30
        """
        let source = source.Replace("INPUT", input)
        let events = if events = "" then [] else events.Split(',') |> Array.map int64 |> Array.toList
        SelectedMatch.assertSelected expected events source |> ignore

    [<Fact>]
    member _.``Record component failure bypasses later extraction and the source guard`` () =
        SelectedMatch.assertSelected 8L [2L] """
type Pair = { Left: int option; Right: int option }
let mutable trace = 0
let input = { Left = None; Right = Some 8 }
let observed =
    match input with
    | { Left = Some left; Right = Some right } when (trace <- 1; true) -> left
    | { Right = Some selected } when (trace <- 2; true) -> selected
    | _ -> 30
        """ |> ignore

    [<Fact>]
    member _.``Generic union tuple payload retains wildcard field type and exact source binding`` () =
        let graph = SelectedMatch.assertSelected 7L [] """
type Pair<'a, 'b> = Pair of 'a * 'b | Empty
let input = Pair (true, Some 7)
let observed = match input with Pair (_, Some selected) -> selected | _ -> 30
        """
        let selected = SelectedMatch.binding "selected" graph
        Assert.Equal<NativeType>((SelectedMatch.binding "observed" graph).Type, selected.Type)
        Assert.Contains(graph.Nodes.Values, fun node ->
            match node.Kind, node.Type with
            | SemanticKind.DUEliminate(_, _, _, _), NativeType.TTuple([first; _], _) -> first = Types.boolType
            | _ -> false)
