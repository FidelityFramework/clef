namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module Requirements = Clef.Compiler.PSGSaturation.SemanticGraph.Requirements

module private RequirementFixture =
    let createFor inputType pattern =
        let builder = NodeBuilder()
        let boolean value = builder.Create(SemanticKind.Literal(NativeLiteral.Bool value), Types.boolType, dummyRange)
        let original = builder.Create(SemanticKind.PatternBinding "input", inputType, dummyRange)
        let yes, no, body = boolean true, boolean false, boolean true
        let input = builder.Create(SemanticKind.TypeAnnotation(original.Id, inputType), inputType, dummyRange, children = [original.Id])
        let arm pattern body : CaseArm = { Pattern = pattern; Bindings = []; Guard = None; Body = body }
        let test = builder.Create(SemanticKind.CaseElimination(input.Id, [arm pattern yes.Id; arm Pattern.Wildcard no.Id]), Types.boolType, dummyRange, children = [input.Id; yes.Id; no.Id])
        let selected = builder.Create(SemanticKind.CaseElimination(input.Id, [arm pattern body.Id]), Types.boolType, dummyRange, children = [input.Id; body.Id])
        let site = builder.Create(SemanticKind.Require(test.Id, "Pattern match failed"), Types.unitType, dummyRange, children = [test.Id])
        let frontier = builder.Create(SemanticKind.Sequential [site.Id; selected.Id], Types.boolType, dummyRange, children = [site.Id; selected.Id])
        let row = { Class = EdgeClass.Provenance; Role = EdgeRole.MatchRequirement; Ordinal = 0
                    Sources = [site.Id; test.Id; selected.Id; input.Id; yes.Id; no.Id; body.Id; original.Id]; Target = frontier.Id }
        let graph = builder.Build []
        { graph with Edges = row :: graph.Edges; Codata = lazy (failwith "Requirement reader forced codata") }, site.Id, test.Id, selected.Id, frontier.Id, body.Id

    let create () = createFor Types.boolType (Pattern.Const(NativeLiteral.Bool true))

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "Requirement")>]
type RequirementCases() =
    [<Theory>]
    [<InlineData("char")>]
    [<InlineData("float")>]
    [<InlineData("int")>]
    [<InlineData("union")>]
    member _.``Pattern applicability retains checked carrier and dimension rather than hosted literal width`` kind =
        let metre = DimensionalCases.metre
        let ty, pattern =
            match kind with
            | "char" -> Types.charType, Pattern.Const(NativeLiteral.Char 'a')
            | "int" -> DimensionalCases.measuredInt metre, Pattern.Const(NativeLiteral.Int(1L, NTUKind.NTUint(NTUWidth.Fixed 64)))
            | "float" -> DimensionalCases.measured metre, Pattern.Const(NativeLiteral.Float(1.0, NTUKind.NTUfloat(NTUWidth.Fixed 64)))
            | _ ->
                let ty = NativeType.TApp(Types.optionTyCon, [DimensionalCases.measured metre])
                ty, Pattern.Union("Some", 1, Some Pattern.Wildcard, ty)
        let graph, site, test, selected, _, _ = RequirementFixture.createFor ty pattern
        Assert.True(Requirements.tryRequirement graph site |> Option.isSome)
        let input = match graph.Nodes[test].Kind with SemanticKind.CaseElimination(input, _) -> input | _ -> failwith "Missing test"
        let altered =
            match kind with
            | "int" -> DimensionalCases.measuredInt DimensionalCases.second
            | "float" -> DimensionalCases.measured DimensionalCases.second
            | "union" -> NativeType.TApp(Types.optionTyCon, [DimensionalCases.measured DimensionalCases.second])
            | _ -> Types.boolType
        let changed = { graph with Nodes = graph.Nodes.Add(input, { graph.Nodes[input] with Type = altered }) }
        Assert.True(Requirements.tryRequirement changed site |> Option.isNone)
        Assert.True(Requirements.tryPatternRequirement changed selected |> Option.isNone)

    [<Fact>]
    member _.``Pattern requirement retains complete ordered source participants without codata`` () =
        let graph, site, test, selected, frontier, body = RequirementFixture.create ()
        let contract = Requirements.tryRequirement graph site |> Option.get
        Assert.Equal(frontier, contract.Frontier)
        Assert.Equal(Some test, contract.PatternTest)
        Assert.Equal(selected, contract.Continuation)
        Assert.Contains(body, contract.Participants)
        Assert.Equal(Some contract, Requirements.tryPatternRequirement graph selected)

    [<Theory>]
    [<InlineData("require-children")>]
    [<InlineData("frontier-children")>]
    [<InlineData("test-children")>]
    [<InlineData("selected-children")>]
    [<InlineData("frontier-order")>]
    [<InlineData("missing-row")>]
    [<InlineData("duplicate-row")>]
    [<InlineData("wrong-body")>]
    [<InlineData("wrong-pattern")>]
    [<InlineData("wrong-condition-type")>]
    [<InlineData("dead-selected-body")>]
    [<InlineData("input-type")>]
    [<InlineData("original-input-type")>]
    [<InlineData("input-children")>]
    [<InlineData("wrong-constant-category")>]
    member _.``Changed requirement premises retract both assertion and single-case authority`` defect =
        let graph, site, test, selected, frontier, body = RequirementFixture.create ()
        let change id update = { graph with Nodes = graph.Nodes.Add(id, update graph.Nodes[id]) }
        let changed =
            let input = match graph.Nodes[test].Kind with SemanticKind.CaseElimination(input, _) -> input | _ -> failwith "Missing test"
            let original = match graph.Nodes[input].Kind with SemanticKind.TypeAnnotation(original, _) -> original | _ -> failwith "Missing typed input"
            match defect with
            | "input-type" -> change input (fun node -> { node with Type = Types.intType })
            | "original-input-type" -> change original (fun node -> { node with Type = Types.intType })
            | "input-children" -> change input (fun node -> { node with Children = [] })
            | "wrong-constant-category" ->
                let nodes =
                    graph.Nodes |> Map.map (fun id node ->
                        match node.Kind with
                        | SemanticKind.CaseElimination(input, first :: rest) when id = test || id = selected ->
                            { node with Kind = SemanticKind.CaseElimination(input, { first with Pattern = Pattern.Const(NativeLiteral.Char 'a') } :: rest) }
                        | _ -> node)
                { graph with Nodes = nodes }
            | "require-children" -> change site (fun node -> { node with Children = [] })
            | "frontier-children" -> change frontier (fun node -> { node with Children = [selected; site] })
            | "test-children" -> change test (fun node -> { node with Children = List.rev node.Children })
            | "selected-children" -> change selected (fun node -> { node with Children = [] })
            | "frontier-order" -> change frontier (fun node -> { node with Kind = SemanticKind.Sequential [selected; site]; Children = [selected; site] })
            | "wrong-condition-type" -> change test (fun node -> { node with Type = Types.unitType })
            | "dead-selected-body" -> change body (fun node -> { node with IsReachable = false })
            | "wrong-pattern" ->
                change selected (fun node ->
                    match node.Kind with
                    | SemanticKind.CaseElimination(input, [arm]) -> { node with Kind = SemanticKind.CaseElimination(input, [{ arm with Pattern = Pattern.Const(NativeLiteral.Bool false) }]) }
                    | _ -> failwith "Missing selected decision")
            | "missing-row" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.MatchRequirement) }
            | "duplicate-row" ->
                let row = graph.Edges |> List.find (fun edge -> edge.Role = EdgeRole.MatchRequirement)
                { graph with Edges = row :: graph.Edges }
            | _ ->
                let edges = graph.Edges |> List.map (fun edge ->
                    if edge.Role = EdgeRole.MatchRequirement then { edge with Sources = List.take 6 edge.Sources @ [test; original] } else edge)
                { graph with Edges = edges }
        Assert.True(Requirements.tryRequirement changed site |> Option.isNone)
        Assert.True(Requirements.tryPatternRequirement changed selected |> Option.isNone)
        Assert.True(Requirements.tryRequirement graph site |> Option.isSome)
