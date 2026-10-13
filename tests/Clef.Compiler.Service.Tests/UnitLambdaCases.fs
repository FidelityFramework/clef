namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.Syntax
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module ExpressionTypes = Clef.Compiler.NativeTypedTree.Expressions.Types
module Applications = Clef.Compiler.NativeTypedTree.Expressions.Applications
module Bindings = Clef.Compiler.NativeTypedTree.Expressions.Bindings
module Literals = Clef.Compiler.NativeTypedTree.Expressions.Literals
module UnitEnvironments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments

module private UnitLambdas =
    let check source =
        match parseAndCheck ("module UnitLambdas\n" + source) "unit-lambdas.clef" with
        | Success result ->
            DimensionalCases.noErrors result
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Error _ -> true | _ -> false)
            result
        | CheckFailure result -> failwithf "Unit callable failed checking: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Unit callable failed parsing: %A" errors

    let binding name (result: CheckResult) =
        result.Graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Binding (actual, _, _, _) -> actual = name || actual.EndsWith("." + name)
            | _ -> false)

    let rec value (result: CheckResult) id =
        let node = result.Graph.Nodes[id]
        match node.Kind with
        | SemanticKind.Binding _ -> value result (List.last node.Children)
        | SemanticKind.TypeAnnotation (inner, _) -> value result inner
        | SemanticKind.Sequential children -> value result (List.last children)
        | _ -> node

    let same expected actual = Assert.Equal(formatType (applySubst expected), formatType (applySubst actual))

    /// Inspect the settled implementation while retaining the source boundary.
    /// A materialized environment adds one physical formal, never a source unit
    /// argument. Captures are read from the owning formation's provenance.
    let callable (result: CheckResult) (value: SemanticNode) =
        let implementation =
            UnitEnvironments.tryImplementation result.Graph value.Id
            |> Option.defaultWith (fun () -> failwithf "No callable implementation for %A" value.Kind)
        let node = result.Graph.Nodes[implementation]
        match node.Kind with
        | SemanticKind.Lambda(parameters, body, captures, _, _) ->
            match (UnitEnvironments.knownCallables result.Graph).TryFind value.Id with
            | Some carrier ->
                let _, _, formal = List.head parameters
                Assert.Equal(Some carrier.EnvironmentOwner, UnitEnvironments.tryEnvironmentOwner result.Graph formal)
                Assert.Empty captures
                node, List.tail parameters, body, UnitEnvironments.captures result.Graph carrier.EnvironmentOwner
            | None -> node, parameters, body, captures
        | kind -> failwithf "Callable implementation is not a lambda: %A" kind

    /// A logical formal is an actual graph participant. Consuming exactly those
    /// formals from the callable type must leave the body's type, even for unit.
    let assertArity (nodes: Map<NodeId, SemanticNode>) (node: SemanticNode) =
        match node.Kind with
        | SemanticKind.Lambda (parameters, body, _, _, _) ->
            Assert.NotEmpty parameters
            let resultType = parameters |> List.fold (fun signature (name, parameterType, parameterId) ->
                Assert.Contains(parameterId, node.Children)
                match nodes[parameterId].Kind with
                | SemanticKind.PatternBinding actual -> Assert.Equal(name, actual)
                | kind -> failwithf "A formal is not a resident parameter: %A" kind
                same parameterType nodes[parameterId].Type
                match applySubst signature with
                | NativeType.TFun (domain, result) -> same domain parameterType; result
                | ty -> failwithf "The graph has more formals than its function type: %A" ty) node.Type
            same nodes[body].Type resultType
        | kind -> failwithf "Expected a lambda, got %A" kind

    let assertSettled (result: CheckResult) =
        for node in result.Graph.Nodes.Values do
            if node.IsReachable then
                match node.Kind with
                | SemanticKind.Lambda (parameters, _, _, _, _) ->
                    assertArity result.Graph.Nodes node
                    for _, _, parameter in parameters do
                        Assert.Equal(Some node.Id, result.Graph.Nodes[parameter].Parent)
                | _ -> ()

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "UnitLambdas")>]
type UnitLambdaCases() =
    [<Fact>]
    member _.``Parsed unit lambda has a resident logical formal before saturation``() =
        let expression =
            match parseStringWithDefaults "module UnitLambdas\nlet work = fun () -> ()" "unit-lambda-raw.clef" with
            | ParseSuccess (ParsedInput.ImplFile implementation) ->
                let (SynModuleOrNamespace(decls = declarations)) = Assert.Single implementation.Contents
                let binding = declarations |> List.pick (function SynModuleDecl.Let(bindings = [binding]) -> Some binding | _ -> None)
                let (SynBinding(expr = expression)) = binding
                expression
            | parsed -> failwithf "Expected one parsed lambda: %A" parsed
        match expression with
        | SynExpr.Lambda(_, inLambdaSeq, args, body, _, range, _) ->
            let builder = NodeBuilder()
            let env = ExpressionTypes.createTypeEnv ()
            let checkLiteral env (builder: NodeBuilder) = function
                | SynExpr.Const(constant, literalRange) ->
                    match Literals.checkConst env constant with
                    | Result.Ok (ty, value) ->
                        builder.Create(SemanticKind.Literal value, ty, ExpressionTypes.rangeToSourceRange literalRange)
                    | Result.Error error -> failwithf "Literal failed: %A" error
                | other -> failwithf "Expected the source unit body, got %A" other
            let lambda = Applications.checkLambda checkLiteral Bindings.extractLambdaParams
                            env builder inLambdaSeq args body (ExpressionTypes.rangeToSourceRange range)
            UnitLambdas.assertArity builder.Nodes lambda
            match lambda.Kind with
            | SemanticKind.Lambda (parameters, _, _, _, _) ->
                let _, parameterType, _ = Assert.Single parameters
                UnitLambdas.same Types.unitType parameterType
            | _ -> failwith "Source lambda was not elaborated as a callable"
        | other -> failwithf "Expected the parsed function expression, got %A" other

    [<Fact>]
    member _.``Assignment-bodied unit lambda retains one formal and the original unit body``() =
        let result = UnitLambdas.check """
let mutable calls: int = 0
let work = fun () -> calls <- calls + 1
[<EntryPoint>]
let main _ = work (); calls - 1
"""
        UnitLambdas.assertSettled result
        let work = UnitLambdas.value result (UnitLambdas.binding "work" result).Id
        let _, parameters, body, captures = UnitLambdas.callable result work
        let _, parameterType, _ = Assert.Single parameters
        UnitLambdas.same Types.unitType parameterType
        Assert.Empty captures
        match result.Graph.Nodes[body].Kind with
        | SemanticKind.Set _ -> UnitLambdas.same Types.unitType result.Graph.Nodes[body].Type
        | kind -> failwithf "Unit body was replaced rather than retaining the assignment: %A" kind

    [<Fact>]
    member _.``Captured unit lambda distinguishes its formal from shared mutable storage``() =
        let result = UnitLambdas.check """
[<EntryPoint>]
let main _ =
    let mutable calls: int = 0
    let work = fun () -> calls <- calls + 1
    work ()
    calls - 1
"""
        UnitLambdas.assertSettled result
        let work = UnitLambdas.value result (UnitLambdas.binding "work" result).Id
        let _, parameters, _, captures = UnitLambdas.callable result work
        let _, parameterType, parameter = Assert.Single parameters
        UnitLambdas.same Types.unitType parameterType
        let capture = Assert.Single captures
        Assert.True capture.IsMutable
        Assert.Equal(Some (UnitLambdas.binding "calls" result).Id, capture.SourceNodeId)
        Assert.NotEqual(Some parameter, capture.SourceNodeId)

    [<Fact>]
    member _.``Named explicit and pattern unit parameters agree on logical arity``() =
        let result = UnitLambdas.check """
let named () = ()
let anonymous = fun () -> ()
let typed = fun (_: unit) -> ()
let combined = fun () () -> ()
[<EntryPoint>]
let main _ = named (); anonymous (); typed (); combined () (); 0
"""
        UnitLambdas.assertSettled result
        for name, arity in ["named", 1; "anonymous", 1; "typed", 1; "combined", 2] do
            let lambda = UnitLambdas.value result (UnitLambdas.binding name result).Id
            let _, parameters, _, _ = UnitLambdas.callable result lambda
            Assert.Equal(arity, parameters.Length)
            for _, parameterType, _ in parameters do UnitLambdas.same Types.unitType parameterType

    [<Fact>]
    member _.``A unit callable returning another unit callable preserves both boundaries``() =
        let result = UnitLambdas.check """
let mutable calls: int = 0
let make = fun () ->
    calls <- calls * 10 + 1
    fun () -> calls <- calls * 10 + 2
let work = make ()
[<EntryPoint>]
let main _ = work (); if calls = 12 then 0 else 1
"""
        UnitLambdas.assertSettled result
        let make = UnitLambdas.value result (UnitLambdas.binding "make" result).Id
        let residual = NativeType.TFun(Types.unitType, Types.unitType)
        UnitLambdas.same (NativeType.TFun(Types.unitType, residual)) make.Type
        let _, parameters, body, _ = UnitLambdas.callable result make
        Assert.Single parameters |> ignore
        let returned = UnitLambdas.value result body
        UnitLambdas.same residual returned.Type
        let _, parameters, _, _ = UnitLambdas.callable result returned
        Assert.Single parameters |> ignore
        Assert.False(result.Graph.Codata.Value.Curry.AbsorbedLambdas.Contains returned.Id)
        let work = UnitLambdas.value result (UnitLambdas.binding "work" result).Id
        UnitLambdas.same residual work.Type
        match work.Kind with
        | SemanticKind.Application (_, arguments) -> Assert.Single arguments |> ignore
        | kind -> failwithf "Factory invocation lost its own boundary: %A" kind

    [<Fact>]
    member _.``Curry refresh retains source absorption and recomputes current arguments without another shape rewrite``() =
        let builder = NodeBuilder()
        let curry = Clef.Compiler.PSGSaturation.SemanticGraph.Curry.normalize
        let refresh = Clef.Compiler.PSGSaturation.SemanticGraph.Curry.refresh

        let parameter =
            builder.Create(SemanticKind.PatternBinding "flag", Types.boolType, dummyRange)

        let unitParameter =
            builder.Create(SemanticKind.PatternBinding "unit", Types.unitType, dummyRange)

        let body =
            builder.Create(SemanticKind.Literal(NativeLiteral.Bool true), Types.boolType, dummyRange)

        let residualType = NativeType.TFun(Types.unitType, Types.boolType)

        let inner =
            builder.Create(
                SemanticKind.Lambda([ "unit", Types.unitType, unitParameter.Id ], body.Id, [], None, LambdaContext.RegularClosure),
                residualType,
                dummyRange
            )

        let sourceType = NativeType.TFun(Types.boolType, residualType)

        let outer =
            builder.Create(
                SemanticKind.Lambda([ "flag", Types.boolType, parameter.Id ], inner.Id, [], None, LambdaContext.RegularClosure),
                sourceType,
                dummyRange
            )

        let declaration =
            builder.Create(SemanticKind.Binding("choose", false, false, None), sourceType, dummyRange, children = [ outer.Id ])

        let callee =
            builder.Create(SemanticKind.VarRef("choose", Some declaration.Id), sourceType, dummyRange)

        let supplied =
            builder.Create(SemanticKind.Literal(NativeLiteral.Bool true), Types.boolType, dummyRange)

        let replacement =
            builder.Create(SemanticKind.Literal(NativeLiteral.Bool false), Types.boolType, dummyRange)

        let partial =
            builder.Create(SemanticKind.Application(callee.Id, [ supplied.Id ]), residualType, dummyRange)

        let saved =
            builder.Create(SemanticKind.Binding("saved", false, false, None), residualType, dummyRange, children = [ partial.Id ])

        builder.SetParent(partial.Id, saved.Id)

        let savedRead =
            builder.Create(SemanticKind.VarRef("saved", Some saved.Id), residualType, dummyRange)

        let unitArgument =
            builder.Create(SemanticKind.Literal NativeLiteral.Unit, Types.unitType, dummyRange)

        let completed =
            builder.Create(SemanticKind.Application(savedRead.Id, [ unitArgument.Id ]), Types.boolType, dummyRange)

        let mutableCell =
            builder.Create(SemanticKind.Binding("selected", true, false, None), sourceType, dummyRange, children = [ outer.Id ])

        let raw = builder.Build []
        let incidence = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence

        let independent =
            {
                Class = EdgeClass.Reference
                Role = EdgeRole.Argument
                Sources = [ body.Id ]
                Target = outer.Id
                Ordinal = 99
            }

        let provenance =
            {
                Class = EdgeClass.Provenance
                Role = EdgeRole.FiniteCellRange
                Sources = [ outer.Id; inner.Id ]
                Target = body.Id
                Ordinal = 0
            }

        let raw =
            { raw with
                Edges =
                    incidence raw.Nodes[outer.Id]
                    @ incidence raw.Nodes[inner.Id]
                    @ [ independent; provenance ]
            }

        let enrichment, retiredSources, absorbed =
            Clef.Compiler.PSGSaturation.SemanticGraph.Curry.elaborate raw

        let annotated = enrichment.Annotated |> List.map _.Id |> Set.ofList
        Assert.True(Set.isSubset retiredSources (Set.union annotated absorbed))
        let source, held = curry raw
        Assert.Contains(inner.Id, held.AbsorbedLambdas)
        Assert.False(source.Nodes[inner.Id].IsReachable)

        let sourceFamilies =
            Clef.Compiler.PSGSaturation.SemanticGraph.MutableCallableStorage.sourceFamilies

        // Independent incidence survives for its existing owner to judge.
        // The callable control uses the separately declared mutable cell graph.
        let cellGraph =
            { source with Edges = source.Edges |> List.filter (fun edge -> not (obj.ReferenceEquals(edge, independent))) }

        let families, refusals = sourceFamilies cellGraph
        Assert.True(families.ContainsKey mutableCell.Id, refusals |> List.map _.Reason |> String.concat "; ")
        Assert.Empty refusals

        let edgeKey (edge: Hyperedge) =
            edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target

        let retiredKeys =
            retiredSources
            |> Set.toList
            |> List.collect (fun id -> incidence raw.Nodes[id])
            |> List.map edgeKey
            |> Set.ofList

        let preserved =
            raw.Edges |> List.filter (fun edge -> not (retiredKeys.Contains(edgeKey edge)))

        Assert.All(preserved, fun prior -> Assert.Contains(source.Edges, fun edge -> obj.ReferenceEquals(prior, edge)))

        let expectedKeys =
            (preserved @ enrichment.NewEdges) |> List.map edgeKey |> Set.ofList

        Assert.Equal(expectedKeys.Count, source.Edges.Length)
        Assert.Equal<Set<_>>(expectedKeys, source.Edges |> List.map edgeKey |> Set.ofList)
        Assert.Contains(source.Edges, fun edge -> edgeKey edge = edgeKey independent)
        Assert.Contains(source.Edges, fun edge -> edgeKey edge = edgeKey provenance)

        let currentDeclared =
            incidence source.Nodes[outer.Id] |> List.map edgeKey |> Set.ofList

        let actualDeclared =
            source.Edges
            |> List.filter (fun edge ->
                edge.Target = outer.Id
                && (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference)
                && edgeKey edge <> edgeKey independent)
            |> List.map edgeKey

        Assert.Equal(currentDeclared.Count, actualDeclared.Length)
        Assert.Equal<Set<_>>(currentDeclared, Set.ofList actualDeclared)

        Assert.DoesNotContain(
            source.Edges,
            fun edge ->
                edge.Target = inner.Id
                && (edge.Class = EdgeClass.Structural || edge.Class = EdgeClass.Reference)
        )
        // Freshly constructed ownership of the same source parameter group.
        let expectedOuter =
            { raw.Nodes[outer.Id] with
                Kind =
                    SemanticKind.Lambda(
                        [
                            "flag", Types.boolType, parameter.Id
                            "unit", Types.unitType, unitParameter.Id
                        ],
                        body.Id,
                        [],
                        None,
                        LambdaContext.RegularClosure
                    )
                Children = [ parameter.Id; unitParameter.Id; body.Id ]
            }

        Assert.Equal(expectedOuter.Kind, source.Nodes[outer.Id].Kind)
        Assert.Equal<NodeId list>(expectedOuter.Children, source.Nodes[outer.Id].Children)
        Assert.Equal(Some outer.Id, source.Nodes[unitParameter.Id].Parent)
        Assert.Equal(Some outer.Id, source.Nodes[body.Id].Parent)
        Assert.True(source.Nodes[unitParameter.Id].IsReachable)
        Assert.True(source.Nodes[body.Id].IsReachable)
        let fresh = NodeBuilder()

        let freshFlag =
            fresh.Create(SemanticKind.PatternBinding "flag", Types.boolType, dummyRange)

        let freshUnit =
            fresh.Create(SemanticKind.PatternBinding "unit", Types.unitType, dummyRange)

        let freshBody =
            fresh.Create(SemanticKind.Literal(NativeLiteral.Bool true), Types.boolType, dummyRange)

        let freshOuter =
            fresh.Create(
                SemanticKind.Lambda(
                    [ "flag", Types.boolType, freshFlag.Id; "unit", Types.unitType, freshUnit.Id ],
                    freshBody.Id,
                    [],
                    None,
                    LambdaContext.RegularClosure
                ),
                sourceType,
                dummyRange
            )

        fresh.SetParent(freshUnit.Id, freshOuter.Id)
        fresh.SetParent(freshBody.Id, freshOuter.Id)
        let freshlyConstructed = fresh.Build []

        for currentId, freshId in [ unitParameter.Id, freshUnit.Id; body.Id, freshBody.Id ] do
            Assert.Equal(freshlyConstructed.Nodes[freshId].Parent = Some freshOuter.Id, source.Nodes[currentId].Parent = Some outer.Id)
            Assert.Equal(freshlyConstructed.Nodes[freshId].IsReachable, source.Nodes[currentId].IsReachable)

        let stale =
            { cellGraph with
                Edges = cellGraph.Edges @ incidence raw.Nodes[outer.Id]
            }

        let staleFamilies, staleRefusals = sourceFamilies stale
        Assert.False(staleFamilies.ContainsKey mutableCell.Id)

        Assert.Contains(
            staleRefusals,
            fun refusal ->
                refusal.Binding = mutableCell.Id
                && refusal.Reason = "The mutable callable cell has inconsistent current source incidence."
        )

        Assert.Equal<NodeId list>([ supplied.Id; unitArgument.Id ], held.SaturatedCalls[completed.Id].AllArgNodes)
        let again, newlyAbsorbed = curry source
        Assert.Same(source, again)
        Assert.Empty newlyAbsorbed.AbsorbedLambdas
        let sourceRefresh = refresh held.AbsorbedLambdas source
        Assert.Equal(held, sourceRefresh)
        // A later source-preserving rewrite replaces an actual occurrence.
        // Refresh reads that current correspondence while retaining the original
        // synthetic lambda identities; it must never flatten a second time.
        let currentPartial =
            { source.Nodes[partial.Id] with
                Kind = SemanticKind.Application(callee.Id, [ replacement.Id ])
                Children = [ callee.Id; replacement.Id ]
            }

        let postTransform =
            { source with
                Nodes = source.Nodes.Add(partial.Id, currentPartial)
                Edges = source.Edges @ incidence currentPartial
            }

        let current = refresh held.AbsorbedLambdas postTransform
        Assert.Equal(held.AbsorbedLambdas, current.AbsorbedLambdas)
        Assert.Equal<NodeId list>([ replacement.Id ], current.PartialApplications[partial.Id].SuppliedArgNodes)
        Assert.Equal<NodeId list>([ replacement.Id; unitArgument.Id ], current.SaturatedCalls[completed.Id].AllArgNodes)
        Assert.Equal(held.PartialAppBindings, current.PartialAppBindings)
        let finalGraph, finalNormalization = curry postTransform
        Assert.Same(postTransform, finalGraph)
        Assert.Empty finalNormalization.AbsorbedLambdas
        Assert.Equal<Map<_, _>>(current.PartialApplications, finalNormalization.PartialApplications)
        Assert.Equal<Map<_, _>>(current.SaturatedCalls, finalNormalization.SaturatedCalls)
