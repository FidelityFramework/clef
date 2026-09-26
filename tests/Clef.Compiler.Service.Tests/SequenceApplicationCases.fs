namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module SequenceApplicationEnvironments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments

module private SequenceApplications =
    let prelude = "module Dimensions\n[<Measure>] type m\n[<Measure>] type s\n"
    let option payload = NativeType.TApp(Types.optionTyCon, [payload])
    let distance = DimensionalCases.measuredInt DimensionalCases.metre
    let inverseTime = DimensionalCases.measured (DimensionalCases.power DimensionalCases.second -1I)
    let input = NativeType.TSeq distance
    let coreOperations =
        Set.ofList ["map"; "filter"; "collect"; "append"; "take"; "iter"; "fold"; "exists"; "forall"; "tryPick"; "tryHead"]

    let check source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Error _ -> true
            | SemanticKind.Intrinsic info -> info.Module = IntrinsicModule.Seq && coreOperations.Contains info.Operation
            | _ -> false)
        result

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Binding (actual, _, _, _) ->
                let local = actual.Substring(actual.LastIndexOf('.') + 1)
                local = name || local.StartsWith(name + "__mono")
            | _ -> false) |> Assert.Single

    let rec value (graph: SemanticGraph) id =
        let node = graph.Nodes[id]
        match node.Kind with
        | SemanticKind.Binding _ -> value graph (List.last node.Children)
        | SemanticKind.TypeAnnotation (inner, _) -> value graph inner
        | SemanticKind.Sequential items -> value graph (List.last items)
        | _ -> node

    let concrete expected actual =
        let actual = applySubst actual
        Assert.False(hasUnboundVars actual, formatType actual)
        Assert.Empty(freeMeasureVars actual)
        Assert.Equal(formatType expected, formatType actual)

    let descendants (graph: SemanticGraph) root =
        let rec visit seen id =
            if Set.contains id seen then seen
            else graph.Nodes[id].Children |> List.fold visit (Set.add id seen)
        visit Set.empty root |> Set.toList |> List.map (fun id -> graph.Nodes[id])

    // The supplied values precede the residual callable. Looking only at its
    // final function type would miss a callback/state read deferred until use.
    let frontier name (graph: SemanticGraph) =
        let binding = binding name graph
        let formation = graph.Nodes[List.last binding.Children]
        match formation.Kind with
        | SemanticKind.Sequential items ->
            let snapshots = items |> List.take (items.Length - 1)
            let closure = value graph (List.last items)
            let implementation = SequenceApplicationEnvironments.tryImplementation graph closure.Id |> Option.get
            match graph.Nodes[implementation].Kind with
            | SemanticKind.Lambda (parameters, body, captures, _, _) ->
                let environmentFormals = graph.Edges |> List.filter (fun edge ->
                    edge.Role = EdgeRole.EnvironmentFormal && List.contains implementation edge.Sources) |> List.map _.Target |> Set.ofList
                parameters |> List.filter (fun (_, _, formal) -> not (environmentFormals.Contains formal)) |> Assert.Single |> ignore
                let captures =
                    match closure.Kind with
                    | SemanticKind.ClosureValue _ -> SequenceApplicationEnvironments.captures graph closure.Id
                    | _ -> captures
                let stored = captures |> List.choose _.SourceNodeId
                for snapshot in snapshots do
                    if not (List.contains snapshot stored) then
                        // An immutable stateless callback still evaluates at
                        // formation, but needs no runtime environment slot.
                        let code = SequenceApplicationEnvironments.tryImplementation graph snapshot |> Option.get
                        match graph.Nodes[code].Kind with
                        | SemanticKind.Lambda (_, _, [], _, _) -> ()
                        | kind -> failwithf "Dropped a runtime capture at %s: %A" name kind
                Assert.All(stored, fun capture -> Assert.Contains(capture, snapshots))
                for capture in captures do Assert.False capture.IsMutable
                for snapshot in snapshots do
                    match graph.Nodes[snapshot].Kind with
                    | SemanticKind.Binding (_, false, false, _) -> ()
                    | kind -> failwithf "Supplied value was not snapshotted immutably: %A" kind
                snapshots, closure, body
            | kind -> failwithf "Missing residual callable at %s: %A" name kind
        | kind -> failwithf "Missing formation frontier at %s: %A" name kind

    let reject code (marked: string) =
        let first, last = marked.IndexOf('«'), marked.IndexOf('»')
        Assert.True(first >= 0 && last > first)
        let before, selected = marked.Substring(0, first), marked.Substring(first + 1, last - first - 1)
        let position (text: string) =
            let lines = text.Split('\n')
            { Line = lines.Length; Column = (Array.last lines).Length }
        let file = "sequence-application-negative.clef"
        let expected = { File = file; Start = position (prelude + before); End = position (prelude + before + selected) }
        let source = prelude + marked.Replace("«", "").Replace("»", "") + "\n[<EntryPoint>]\nlet main _ = ignore wrong; 0\n"
        match parseAndCheck source file with
        | CheckFailure result ->
            let diagnostic = result.Diagnostics |> List.filter (fun diagnostic ->
                diagnostic.Code = code && Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error) |> Assert.Single
            Assert.Equal<SourceRange>(expected, diagnostic.Range)
        | other -> failwithf "Expected located %s checking failure, got %A" code other

/// Source/graph acceptance for the existing eleven-operation C-07 contract.
/// Native 16h separately checks execution, restart and stopping behavior;
/// these checks do not grant escaping environments or factory-result residence.
[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceApplications")>]
type SequenceApplicationCases() =
    [<Theory>]
    [<InlineData("map")>]
    [<InlineData("filter")>]
    [<InlineData("collect")>]
    [<InlineData("append")>]
    [<InlineData("take")>]
    [<InlineData("iter")>]
    [<InlineData("fold")>]
    [<InlineData("exists")>]
    [<InlineData("forall")>]
    [<InlineData("tryPick")>]
    [<InlineData("tryHead")>]
    member _.``Stored and bare core operations retain their source residual and result types``(operation: string) =
        let input = SequenceApplications.input
        let resultType, first, rest =
            match operation with
            | "map" -> NativeType.TSeq SequenceApplications.inverseTime, "(fun (_: int<m>) -> 0.5<1/s>)", ""
            | "collect" -> NativeType.TSeq SequenceApplications.inverseTime, "(fun (_: int<m>) -> seq { yield 0.5<1/s> })", ""
            | "filter" -> input, "(fun (value: int<m>) -> value > 0<m>)", ""
            | "append" -> input, "(seq { yield 0<m> })", ""
            | "take" -> input, "1", ""
            | "iter" -> Types.unitType, "(fun (_: int<m>) -> ())", ""
            | "fold" -> SequenceApplications.inverseTime, "(fun (state: float<1/s>) (_: int<m>) -> state + 0.25<1/s>)", "1.0<1/s> "
            | "exists" | "forall" -> Types.boolType, "(fun (value: int<m>) -> value > 0<m>)", ""
            | "tryPick" -> SequenceApplications.option SequenceApplications.inverseTime, "(fun (_: int<m>) -> Some 0.5<1/s>)", ""
            | "tryHead" -> SequenceApplications.option SequenceApplications.distance, "", ""
            | name -> failwith name
        let residual = NativeType.TFun(input, resultType)
        let storedType = if operation = "fold" then NativeType.TFun(SequenceApplications.inverseTime, residual) else residual
        for bare in [false; true] do
            let alias = if bare then $"    let operation = Seq.{operation}\n" else ""
            let callee = if bare then "operation" else "Seq." + operation
            let result = SequenceApplications.check $"""
[<EntryPoint>]
let main _ =
{alias}    let stored = {callee} {first}
    let observed = stored {rest}(seq {{ yield 1<m>; yield 2<m> }})
    ignore observed
    0
"""
            let graph = result.Graph
            let stored = SequenceApplications.binding "stored" graph
            let observed = SequenceApplications.binding "observed" graph
            SequenceApplications.concrete storedType stored.Type
            SequenceApplications.concrete resultType observed.Type
            if bare then
                let operationBinding = SequenceApplications.binding "operation" graph
                let implementation = SequenceApplicationEnvironments.tryImplementation graph operationBinding.Id |> Option.get
                match graph.Nodes[implementation].Kind with
                | SemanticKind.Lambda (parameters, _, [], _, _) ->
                    Assert.Single parameters |> ignore
                    SequenceApplications.concrete operationBinding.Type graph.Nodes[implementation].Type
                | kind -> failwithf "Bare %s has no resident callable boundary: %A" operation kind

    [<Fact>]
    member _.``A fully supplied bare map invokes its returned callable at a separate boundary``() =
        let result = SequenceApplications.check """
[<EntryPoint>]
let main _ =
    let offset = 0.5<1/s>
    let callback = fun (_: int<m>) -> offset
    let callbackAlias = callback
    let operation: (int<m> -> float<1/s>) -> seq<int<m>> -> seq<float<1/s>> = Seq.map
    let observed = operation callbackAlias (seq { yield 1<m> })
    ignore observed
    0
"""
        let graph = result.Graph
        let observed = SequenceApplications.binding "observed" graph
        let output = NativeType.TSeq SequenceApplications.inverseTime
        let invocation = SequenceApplications.value graph observed.Id
        match invocation.Kind with
        | SemanticKind.Application (_, finalArguments) ->
            let ordinal, environment = (SequenceApplicationEnvironments.callEnvironments graph)[invocation.Id]
            Assert.Equal(0, ordinal)
            let input = finalArguments |> List.indexed |> List.choose (fun (index, argument) -> if index = ordinal then None else Some argument) |> Assert.Single
            SequenceApplications.concrete SequenceApplications.input graph.Nodes[input].Type
            let intermediate =
                match graph.Nodes[environment].Kind with
                | SemanticKind.EnvironmentReference source -> source
                | kind -> failwithf "Returned map lost its actual environment: %A" kind
            let intermediate = SequenceApplications.value graph intermediate
            SequenceApplications.concrete (NativeType.TFun(SequenceApplications.input, output)) intermediate.Type
            match intermediate.Kind with
            | SemanticKind.Application (original, initialArguments) ->
                let callback = Assert.Single initialArguments
                SequenceApplications.concrete (NativeType.TFun(SequenceApplications.distance, SequenceApplications.inverseTime)) graph.Nodes[callback].Type
                let implementation = SequenceApplicationEnvironments.tryImplementation graph
                let source = implementation (SequenceApplications.binding "operation" graph).Id |> Option.get
                Assert.Equal(Some source, implementation original)
            | kind -> failwithf "No distinct call produces the residual map: %A" kind
        | kind -> failwithf "No call invokes the returned map: %A" kind
        SequenceApplications.concrete output observed.Type

    [<Fact>]
    member _.``Both fold frontiers snapshot supplied values while retaining the callback's shared cell``() =
        let result = SequenceApplications.check """
[<EntryPoint>]
let main _ =
    let mutable calls = 0
    let mutable callback = fun (state: float<1/s>) (_: int<m>) -> calls <- calls + 1; state + 0.25<1/s>
    let mutable supplied = 1.0<1/s>
    let firstFrontier = Seq.fold callback
    let secondFrontier = Seq.fold callback supplied
    callback <- fun (state: float<1/s>) (_: int<m>) -> state + 10.0<1/s>
    supplied <- 9.0<1/s>
    let staged = firstFrontier supplied
    let observed = secondFrontier (seq { yield 1<m>; yield 2<m> })
    let empty = staged (seq { if false then yield 1<m> })
    if observed = 1.5<1/s> && empty = 9.0<1/s> && calls = 2 then 0 else 1
"""
        let graph = result.Graph
        let callback = SequenceApplications.binding "callback" graph
        let supplied = SequenceApplications.binding "supplied" graph
        for name, definitions in ["firstFrontier", [callback.Id]; "secondFrontier", [callback.Id; supplied.Id]] do
            let snapshots, closure, body = SequenceApplications.frontier name graph
            Assert.Equal(definitions.Length, snapshots.Length)
            List.iter2 (fun snapshot definition ->
                let initial = Assert.Single graph.Nodes[snapshot].Children
                match graph.Nodes[initial].Kind with
                | SemanticKind.VarRef (_, Some source) -> Assert.Equal(definition, source)
                | kind -> failwithf "Supplied value lost its source read: %A" kind) snapshots definitions
            let bodyNodes = SequenceApplications.descendants graph body
            for definition in definitions do
                Assert.DoesNotContain(bodyNodes, fun node ->
                    match node.Kind with SemanticKind.VarRef (_, Some source) -> source = definition | _ -> false)
            SequenceApplications.concrete (SequenceApplications.binding name graph).Type closure.Type
        for name in ["observed"; "empty"] do
            SequenceApplications.concrete SequenceApplications.inverseTime (SequenceApplications.binding name graph).Type
        let calls = SequenceApplications.binding "calls" graph
        Assert.Contains(graph.Nodes.Values, fun node ->
            match node.Kind with
            | SemanticKind.Lambda (_, _, captures, _, _) ->
                captures |> List.exists (fun capture -> capture.IsMutable && capture.SourceNodeId = Some calls.Id)
            | _ -> false)

    [<Fact>]
    member _.``Effectful operands run once at their written fold frontier before deferred consumption``() =
        let result = SequenceApplications.check """
let mutable trace = 0
let makeFolder () =
    trace <- trace * 10 + 1
    fun (state: float<1/s>) (_: int<m>) -> state + 0.25<1/s>
let makeState () =
    trace <- trace * 10 + 2
    1.0<1/s>
[<EntryPoint>]
let main _ =
    let firstFrontier = Seq.fold (makeFolder ())
    let secondFrontier = Seq.fold (makeFolder ()) (makeState ())
    let first = firstFrontier 1.0<1/s> (seq { yield 1<m> })
    let second = secondFrontier (seq { yield 2<m> })
    if first = 1.25<1/s> && second = 1.25<1/s> && trace = 112 then 0 else 1
"""
        let graph = result.Graph
        for name, factories in ["firstFrontier", ["makeFolder"]; "secondFrontier", ["makeFolder"; "makeState"]] do
            let snapshots, _, body = SequenceApplications.frontier name graph
            Assert.Equal(factories.Length, snapshots.Length)
            List.iter2 (fun snapshot factory ->
                let call = SequenceApplications.value graph (Assert.Single graph.Nodes[snapshot].Children)
                match call.Kind with
                | SemanticKind.Application (callee, _) ->
                    match (SequenceApplications.value graph callee).Kind with
                    | SemanticKind.VarRef (_, Some source) -> Assert.Equal((SequenceApplications.binding factory graph).Id, source)
                    | kind -> failwithf "Snapshot lost its exact factory: %A" kind
                | kind -> failwithf "Snapshot lost its effectful call: %A" kind
                Assert.DoesNotContain(SequenceApplications.descendants graph body, fun node -> node.Id = call.Id)
                let parents = graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && List.contains call.Id node.Children)
                Assert.Equal(snapshot, (Assert.Single parents).Id)) snapshots factories

    [<Theory>]
    [<InlineData("let stored = Seq.map (fun (value: int<m>) -> value)\nlet wrong = «stored (seq { yield 1<s> })»", "CCS8040")>]
    [<InlineData("let stored = Seq.fold (fun (state: float<1/s>) (_: int<m>) -> state)\nlet wrong = «stored 1.0<m>»", "CCS8040")>]
    [<InlineData("let operation = Seq.tryHead\nlet wrong = «operation 42»", "CCS8003")>]
    member _.``Stored and bare operations reject a mismatched residual argument at its source span``(source: string, code: string) =
        SequenceApplications.reject code source
