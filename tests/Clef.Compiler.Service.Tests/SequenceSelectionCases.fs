namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module SelectionCurrent = Clef.Compiler.Nanopass.SequenceCurrentAdmission

module private SequenceSelection =
    let prelude = "module Dimensions\n[<Measure>] type m\n[<Measure>] type s\n"
    let check source =
        match parseAndCheck (prelude + source + "\n[<EntryPoint>]\nlet main _ = ignore observed; 0\n") "sequence-selection.clef" with
        | Success result ->
            DimensionalCases.noErrors result
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node -> match node.Kind with SemanticKind.Error _ -> true | _ -> false)
            result
        | CheckFailure result -> failwithf "Expected admitted selection: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed selection: %A" errors

    let binding prefix (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(name, _, _, _) -> name.StartsWith(prefix: string) | _ -> false) |> Assert.Single

    let operation (graph: SemanticGraph) id =
        match graph.Nodes[id].Kind with
        | SemanticKind.Application(callee, arguments) ->
            match graph.Nodes[callee].Kind with SemanticKind.Intrinsic info -> info.Operation, arguments | _ -> failwith "Expected an intrinsic operation"
        | _ -> failwith "Expected an application"

    let assignment (graph: SemanticGraph) id =
        match graph.Nodes[id].Kind with
        | SemanticKind.Set(target, value) ->
            match graph.Nodes[target].Kind with SemanticKind.VarRef(_, Some binding) -> binding, value | _ -> failwith "Assignment lost its declaration"
        | _ -> failwith "Expected an assignment"

    let rec callName (graph: SemanticGraph) id =
        match graph.Nodes[id].Kind with
        | SemanticKind.Application(callee, _) | SemanticKind.TypeAnnotation(callee, _) -> callName graph callee
        | SemanticKind.VarRef(name, _) -> name
        | _ -> failwith "Expected source factory identity"

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceSelection")>]
type SequenceSelectionCases() =
    [<Theory>]
    [<InlineData("Seq.tryPick (fun (_: int<m>) -> Some 2<s>) (seq { yield 1<m> })", "int<s> option")>]
    [<InlineData("Seq.tryPick (fun (_: int<m>) -> Some (None: bool option)) (seq { yield 1<m> })", "bool option option")>]
    [<InlineData("Seq.tryPick (fun (_: int<m>) -> Some (Ok 2<s>: Result<int<s>,bool>)) (seq { yield 1<m> })", "Result<int<s>,bool> option")>]
    [<InlineData("Seq.tryHead<int<m> option> (seq { yield Some 1<m> })", "int<m> option option")>]
    member _.``Selection retains complete optional result independently from the input payload`` (expression, resultType) =
        let result = SequenceSelection.check ("let expected: " + resultType + " = None\nlet observed = " + expression)
        let expected = DimensionalCases.bindingType "expected" result
        DimensionalCases.same expected (DimensionalCases.bindingType "observed" result)
        DimensionalCases.same expected (SequenceSelection.binding "__seq_selection_" result.Graph).Type
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            node.IsReachable && match node.Kind with SemanticKind.VarRef(_, None) -> true | _ -> false)

    [<Theory>]
    [<InlineData("tryHead")>]
    [<InlineData("tryPick")>]
    member _.``Selection snapshots eager operand factories once before acquiring an iterator`` operation =
        let factories = if operation = "tryHead" then ["inputFactory"] else ["chooserFactory"; "inputFactory"]
        let expression = "Seq." + operation + (if operation = "tryHead" then " (inputFactory ())" else " (chooserFactory ()) (inputFactory ())")
        let source =
            "let mutable trace = 0\nlet chooserFactory () = trace <- 1; fun (_: int<m>) -> Some 2<s>\n" +
            "let inputFactory () = trace <- 2; seq { yield 1<m> }\nlet observed = " + expression
        let graph = (SequenceSelection.check source).Graph
        let root = graph.Nodes[Assert.Single (SequenceSelection.binding "observed" graph).Children]
        let actions = match root.Kind with SemanticKind.Sequential actions -> actions | _ -> failwith "Selection lost eager sequencing"
        Assert.Equal(factories.Length + 1, actions.Length)
        let snapshots = actions |> List.take factories.Length |> List.map (fun id -> graph.Nodes[id])
        let calls = snapshots |> List.map (fun node -> Assert.Single node.Children)
        Assert.Equal<string list>(factories, calls |> List.map (SequenceSelection.callName graph))
        for call in calls do
            graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && List.contains call node.Children) |> Assert.Single |> ignore
        let certificate = SelectionCurrent.certify graph |> snd |> Assert.Single
        let enumerator = graph.Nodes[certificate.Sources.Head]
        let _, inputs = SequenceSelection.operation graph (Assert.Single enumerator.Children)
        match graph.Nodes[Assert.Single inputs].Kind with
        | SemanticKind.VarRef(_, Some input) -> Assert.Equal((List.last snapshots).Id, input)
        | _ -> failwith "Iterator reacquires the unevaluated input expression"

    [<Theory>]
    [<InlineData("tryHead", false)>]
    [<InlineData("tryHead", true)>]
    [<InlineData("tryPick", false)>]
    [<InlineData("tryPick", true)>]
    member _.``Empty result and stopping decision share exact current and one candidate snapshot`` (operation, empty) =
        let input = if empty then "(seq { () }: seq<int<m>>)" else "(seq { yield 1<m>; yield 2<m> })"
        let chooser = if operation = "tryHead" then "" else " (fun value -> if value > 1<m> then Some 3<s> else None)"
        let graph = (SequenceSelection.check ("let observed = Seq." + operation + chooser + " " + input)).Graph
        let result, found = SequenceSelection.binding "__seq_selection_" graph, SequenceSelection.binding "__seq_selected_" graph
        match graph.Nodes[Assert.Single result.Children].Kind with
        | SemanticKind.DUConstruct("None", 0, None, None) ->
            Assert.Equal<NativeType>(result.Type, graph.Nodes[Assert.Single result.Children].Type)
        | kind -> failwithf "Empty selection does not start at None: %A" kind
        Assert.Equal(SemanticKind.Literal(NativeLiteral.Bool false), graph.Nodes[Assert.Single found.Children].Kind)
        let proof = SelectionCurrent.certify graph |> snd |> Assert.Single
        let guard, loop = proof.Sources[1], proof.Sources[2]
        let demand, pull, stopped = match graph.Nodes[guard].Kind with SemanticKind.IfThenElse(d, p, Some n) -> d, p, n | _ -> failwith "Missing pre-pull stopping guard"
        Assert.Equal(SemanticKind.Literal(NativeLiteral.Bool false), graph.Nodes[stopped].Kind)
        let decision =
            match graph.Nodes[demand].Kind with
            | SemanticKind.IfThenElse(decision, whenSelected, Some whenSearching) ->
                Assert.Equal(SemanticKind.Literal(NativeLiteral.Bool false), graph.Nodes[whenSelected].Kind)
                Assert.Equal(SemanticKind.Literal(NativeLiteral.Bool true), graph.Nodes[whenSearching].Kind)
                decision
            | kind -> failwithf "Selection guard lost its stopping polarity: %A" kind
        match graph.Nodes[decision].Kind with SemanticKind.VarRef(_, Some flag) -> Assert.Equal(found.Id, flag) | _ -> failwith "Guard lost retained decision"
        Assert.Equal("moveNext", fst (SequenceSelection.operation graph pull))
        let body = match graph.Nodes[loop].Kind with SemanticKind.WhileLoop(actual, body) -> Assert.Equal(guard, actual); body | _ -> failwith "Missing shared iterator loop"
        let current, action = match graph.Nodes[body].Kind with SemanticKind.Sequential [_; current; action] -> current, action | _ -> failwith "Missing current prefix"
        let snapshot, save, stop = match graph.Nodes[action].Kind with SemanticKind.Sequential [snapshot; save; stop] -> snapshot, save, stop | _ -> failwith "Candidate is not evaluated once before both writes"
        let candidate = graph.Nodes[snapshot]
        let chosen = graph.Nodes[Assert.Single candidate.Children]
        match operation, chosen.Kind with
        | "tryHead", SemanticKind.DUConstruct("Some", 1, Some argument, None)
        | "tryPick", SemanticKind.Application(_, [argument]) -> Assert.Equal(current, argument)
        | _, kind -> failwithf "Chooser lost the current snapshot: %A" kind
        Assert.DoesNotContain(graph.Nodes.Values, fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Intrinsic { Module = IntrinsicModule.Option } -> true | _ -> false)
        let resultTarget, savedValue = SequenceSelection.assignment graph save
        Assert.Equal(result.Id, resultTarget)
        match graph.Nodes[savedValue].Kind with SemanticKind.VarRef(_, Some definition) -> Assert.Equal(snapshot, definition) | _ -> failwith "Selected value was recomputed"
        Assert.Equal(found.Id, fst (SequenceSelection.assignment graph stop))
        graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && List.contains chosen.Id node.Children) |> Assert.Single |> ignore

    [<Theory>]
    [<InlineData("Seq.tryPick (fun (_: int<m>) -> Some 1<s>) (seq { yield 1<s> })", "CCS8040")>]
    [<InlineData("Seq.tryHead 42", "CCS8003")>]
    member _.``Invalid selection operands remain checking failures with located compiler diagnostics`` (expression, code) =
        let source = SequenceSelection.prelude + "let wrong = " + expression + "\n[<EntryPoint>]\nlet main _ = ignore wrong; 0\n"
        match parseAndCheck source "selection-negative.clef" with
        | CheckFailure result ->
            let diagnostic = result.Diagnostics |> List.filter (fun d -> d.Code = code && Diagnostic.effectiveSeverity d = NativeDiagnosticSeverity.Error) |> Assert.Single
            let expected = { File = "selection-negative.clef"; Start = { Line = 4; Column = 12 }; End = { Line = 4; Column = 12 + expression.Length } }
            Assert.Equal<SourceRange>(expected, diagnostic.Range)
        | other -> failwithf "Expected located %s checking failure: %A" code other
