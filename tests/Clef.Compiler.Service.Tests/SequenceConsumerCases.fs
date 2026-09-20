namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module ConsumerCurrent = Clef.Compiler.Nanopass.SequenceCurrentAdmission

module private SequenceConsumers =
    let check source =
        let result = DimensionalCases.check (source + "\n[<EntryPoint>]\nlet main _ = ignore observed; 0\n")
        DimensionalCases.noErrors result
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node -> node.IsReachable && match node.Kind with SemanticKind.Error _ -> true | _ -> false)
        result

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false) |> Assert.Single

    let value name (graph: SemanticGraph) = graph.Nodes[Assert.Single (binding name graph).Children]
    let operation (graph: SemanticGraph) id =
        match graph.Nodes[id].Kind with
        | SemanticKind.Application(callee, _) ->
            match graph.Nodes[callee].Kind with SemanticKind.Intrinsic info -> Some(info.Module, info.Operation) | _ -> None
        | _ -> None

    let rec callName (graph: SemanticGraph) id =
        match graph.Nodes[id].Kind with
        | SemanticKind.Application(callee, _) | SemanticKind.TypeAnnotation(callee, _) -> callName graph callee
        | SemanticKind.VarRef(name, _) -> name
        | kind -> failwithf "Expected a resolved source factory call: %A" kind

    let take count = check ("let observed = Seq.take " + string count + " (seq { yield 1<m>; yield 2<m> })")
    let protocol (graph: SemanticGraph) =
        let _, evidence = ConsumerCurrent.certify graph
        let proof = evidence |> List.filter (fun edge ->
            match edge.Sources with
            | [_; guard; _] -> match graph.Nodes[guard].Kind with SemanticKind.IfThenElse _ -> true | _ -> false
            | _ -> false) |> Assert.Single
        match proof.Sources with
        | [enumerator; guard; loop] ->
            let demand, pull, exhausted = match graph.Nodes[guard].Kind with SemanticKind.IfThenElse(demand, pull, Some exhausted) -> demand, pull, exhausted | _ -> failwith "No bounded guard"
            let body = match graph.Nodes[loop].Kind with SemanticKind.WhileLoop(_, body) -> body | _ -> failwith "No iterator loop"
            proof, enumerator, guard, loop, demand, pull, exhausted, body
        | _ -> failwith "Missing exact iterator proof"

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceConsumers")>]
type SequenceConsumerCases() =
    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Fold keeps accumulator dimensions and representation independent from its input element`` realState =
        let initial, folder, expected =
            if realState then "0.0<1/s>", "fun (state: float<1/s>) (_: int<m>) -> state + 0.25<1/s>", DimensionalCases.measured (DimensionalCases.power DimensionalCases.second -1I)
            else "0<s>", "fun (state: int<s>) (_: int<m>) -> state + 1<s>", DimensionalCases.measuredInt DimensionalCases.second
        let result = SequenceConsumers.check ("let observed = Seq.fold (" + folder + ") " + initial + " (seq { yield 1<m>; yield 2<m> })")
        DimensionalCases.same expected (DimensionalCases.bindingType "observed" result)
        let graph = result.Graph
        let accumulator = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(name, true, false, _) -> name.StartsWith "__seq_accumulator_" | _ -> false) |> Assert.Single
        DimensionalCases.same expected accumulator.Type
        let proof = ConsumerCurrent.certify graph |> snd |> Assert.Single
        DimensionalCases.same (DimensionalCases.measuredInt DimensionalCases.metre) graph.Nodes[proof.Target].Type
        Assert.DoesNotContain(graph.Nodes.Values, fun node ->
            node.IsReachable && match node.Kind with SemanticKind.VarRef(_, None) -> true | _ -> false)
        let assignments = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && (match node.Kind with
                                 | SemanticKind.Set(target, _) -> match graph.Nodes[target].Kind with SemanticKind.VarRef(_, Some source) -> source = accumulator.Id | _ -> false
                                 | _ -> false)) |> Seq.toList
        let assignment = Assert.Single assignments
        match assignment.Kind with SemanticKind.Set(_, value) -> DimensionalCases.same expected graph.Nodes[value].Type | _ -> failwith "No accumulator update"

    [<Theory>]
    [<InlineData("fold")>]
    [<InlineData("iter")>]
    [<InlineData("exists")>]
    [<InlineData("forall")>]
    member _.``Eager consumer snapshots each supplied factory once before enumeration`` operation =
        let prelude = """
let mutable trace = 0
let folderFactory () = trace <- 1; fun (state: int<s>) (_: int<m>) -> state + 1<s>
let actionFactory () = trace <- 1; fun (_: int<m>) -> trace <- 4
let predicateFactory () = trace <- 1; fun (value: int<m>) -> value > 0<m>
let stateFactory () = trace <- 2; 0<s>
let inputFactory () = trace <- 3; seq { yield 1<m> }
"""
        let expression, factories =
            match operation with
            | "fold" -> "Seq.fold (folderFactory ()) (stateFactory ()) (inputFactory ())", ["folderFactory"; "stateFactory"; "inputFactory"]
            | "iter" -> "Seq.iter (actionFactory ()) (inputFactory ())", ["actionFactory"; "inputFactory"]
            | predicate -> "Seq." + predicate + " (predicateFactory ()) (inputFactory ())", ["predicateFactory"; "inputFactory"]
        let graph = (SequenceConsumers.check (prelude + "let observed = " + expression)).Graph
        let root = SequenceConsumers.value "observed" graph
        let actions = match root.Kind with SemanticKind.Sequential actions -> actions | _ -> failwith "Consumer lost eager operands"
        Assert.Equal(factories.Length + 1, actions.Length)
        let snapshots = actions |> List.take factories.Length |> List.map (fun id -> graph.Nodes[id])
        let calls = snapshots |> List.map (fun node ->
            match node.Kind with SemanticKind.Binding(_, false, false, _) -> Assert.Single node.Children | _ -> failwith "Missing immutable operand snapshot")
        Assert.Equal<string list>(factories, calls |> List.map (SequenceConsumers.callName graph))
        let evidence = ConsumerCurrent.certify graph |> snd |> Assert.Single
        let enumerator = graph.Nodes[evidence.Sources.Head]
        let initialization = graph.Nodes[Assert.Single enumerator.Children]
        match initialization.Kind with
        | SemanticKind.Application(_, [input]) ->
            match graph.Nodes[input].Kind with
            | SemanticKind.VarRef(_, Some definition) -> Assert.Equal((List.last snapshots).Id, definition)
            | _ -> failwith "Input initializer would be repeated in the loop"
        | _ -> failwith "Enumerator is not initialized once"
        for call in calls do
            let incoming = graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && List.contains call node.Children) |> Seq.toList
            Assert.Single incoming |> ignore

    [<Theory>]
    [<InlineData(-2)>]
    [<InlineData(0)>]
    [<InlineData(3)>]
    member _.``Take forms operands eagerly but places the positive count guard before every upstream pull`` count =
        let result = SequenceConsumers.take count
        let graph = result.Graph
        DimensionalCases.same (Types.mkSeqType (DimensionalCases.measuredInt DimensionalCases.metre)) (DimensionalCases.bindingType "observed" result)
        let proof, _, guard, loop, demand, pull, exhausted, body = SequenceConsumers.protocol graph
        let literalAt operation =
            match graph.Nodes[operation].Kind with
            | SemanticKind.Application(_, [_; value]) ->
                let literal = graph.Nodes[value]
                match literal.Kind with
                | SemanticKind.Literal(NativeLiteral.Int(_, kind)) ->
                    Assert.Equal(Types.tryGetNTUKind literal.Type, Some kind)
                | kind -> failwithf "Expected the operation's integer literal: %A" kind
            | kind -> failwithf "Expected a binary integer operation: %A" kind
        Assert.Equal(Some(IntrinsicModule.Operators, "op_GreaterThan"), SequenceConsumers.operation graph demand)
        // These constants may live in continuation scratch slots. Their
        // embedded kind must agree with the type used to settle those slots.
        literalAt demand
        Assert.Equal(Some(IntrinsicModule.SeqEnumerator, "moveNext"), SequenceConsumers.operation graph pull)
        Assert.Equal(SemanticKind.Literal(NativeLiteral.Bool false), graph.Nodes[exhausted].Kind)
        let consumers = Clef.Compiler.Baker.Recipes.SequenceCurrentRecipes.structuralConsumers graph
        Assert.Equal<NodeId list>([guard], consumers[pull])
        Assert.Equal<NodeId list>([loop], consumers[guard])
        let currentBinding, action = match graph.Nodes[body].Kind with SemanticKind.Sequential [binding; _; action] -> binding, action | _ -> failwith "Missing immediate current prefix"
        Assert.Equal<NodeId list>([proof.Target], graph.Nodes[currentBinding].Children)
        let decrement, yielded = match graph.Nodes[action].Kind with SemanticKind.Sequential [decrement; yielded] -> decrement, yielded | _ -> failwith "Take has no decrement-before-yield boundary"
        match graph.Nodes[decrement].Kind with
        | SemanticKind.Set(target, next) ->
            Assert.Equal(Some(IntrinsicModule.Operators, "op_Subtraction"), SequenceConsumers.operation graph next)
            literalAt next
            match graph.Nodes[target].Kind with
            | SemanticKind.VarRef(_, Some remaining) ->
                match graph.Nodes[remaining].Kind with SemanticKind.Binding(_, true, false, _) -> () | _ -> failwith "Counter is not per enumeration"
            | _ -> failwith "Counter update lost its identity"
        | _ -> failwith "Take does not consume its successful demand"
        match graph.Nodes[yielded].Kind with SemanticKind.Yield _ -> () | _ -> failwith "No owner-local yield"
        let formed = SequenceConsumers.value "observed" graph
        match formed.Kind with
        | SemanticKind.Sequential [countSnapshot; inputSnapshot; owner] ->
            match graph.Nodes[owner].Kind with
            | SemanticKind.SeqExpr(_, captures) -> Assert.Equal<Set<NodeId>>(Set.ofList [countSnapshot; inputSnapshot], captures |> List.choose _.SourceNodeId |> Set.ofList)
            | _ -> failwith "Missing deferred result"
        | _ -> failwith "Take lost count/input formation"

    [<Theory>]
    [<InlineData("true-fallback")>]
    [<InlineData("different-iterator")>]
    [<InlineData("shared-pull")>]
    [<InlineData("shared-guard")>]
    [<InlineData("intervening-pull")>]
    member _.``Bounded current admission rejects broken successful-pull premises`` defect =
        let graph = (SequenceConsumers.take 2).Graph
        let proof, enumerator, guard, _, _, pull, exhausted, body = SequenceConsumers.protocol graph
        let update id kind children nodes = nodes |> Map.add id { graph.Nodes[id] with Kind = kind; Children = children }
        let nodes =
            match defect with
            | "true-fallback" -> update exhausted (SemanticKind.Literal(NativeLiteral.Bool true)) [] graph.Nodes
            | "different-iterator" ->
                let other = { graph.Nodes[enumerator] with Id = NodeId.fresh() }
                let argument = match graph.Nodes[pull].Kind with SemanticKind.Application(_, [argument]) -> argument | _ -> failwith "No guarded pull"
                graph.Nodes.Add(other.Id, other) |> update argument (SemanticKind.VarRef("other", Some other.Id)) []
            | "shared-pull" | "shared-guard" ->
                let shared = if defect = "shared-pull" then pull else guard
                let additional = { graph.Nodes[shared] with Id = NodeId.fresh(); Kind = SemanticKind.Sequential [shared]; Children = [shared]; Parent = None }
                graph.Nodes.Add(additional.Id, additional)
            | _ ->
                let inserted = match graph.Nodes[body].Kind with SemanticKind.Sequential actions -> pull :: actions | _ -> failwith "No guarded body"
                update body (SemanticKind.Sequential inserted) inserted graph.Nodes
        let admitted, evidence = ConsumerCurrent.certify { graph with Nodes = nodes }
        Assert.DoesNotContain(proof.Target, admitted)
        Assert.DoesNotContain(evidence, fun edge -> edge.Target = proof.Target)
