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
        match work.Kind with
        | SemanticKind.Lambda (parameters, body, captures, _, _) ->
            let _, parameterType, _ = Assert.Single parameters
            UnitLambdas.same Types.unitType parameterType
            Assert.Empty captures
            match result.Graph.Nodes[body].Kind with
            | SemanticKind.Set _ -> UnitLambdas.same Types.unitType result.Graph.Nodes[body].Type
            | kind -> failwithf "Unit body was replaced rather than retaining the assignment: %A" kind
        | kind -> failwithf "Unit function value lost its lambda: %A" kind

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
        match work.Kind with
        | SemanticKind.Lambda (parameters, _, captures, _, _) ->
            let _, parameterType, parameter = Assert.Single parameters
            UnitLambdas.same Types.unitType parameterType
            let capture = Assert.Single captures
            Assert.True capture.IsMutable
            Assert.Equal(Some (UnitLambdas.binding "calls" result).Id, capture.SourceNodeId)
            Assert.NotEqual(Some parameter, capture.SourceNodeId)
        | kind -> failwithf "Captured unit function lost its lambda: %A" kind

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
            match lambda.Kind with
            | SemanticKind.Lambda (parameters, _, _, _, _) ->
                Assert.Equal(arity, parameters.Length)
                for _, parameterType, _ in parameters do UnitLambdas.same Types.unitType parameterType
            | kind -> failwithf "Unit callable lost its lambda: %A" kind

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
        match make.Kind with
        | SemanticKind.Lambda (parameters, body, _, _, _) ->
            Assert.Single parameters |> ignore
            let returned = UnitLambdas.value result body
            UnitLambdas.same residual returned.Type
            match returned.Kind with
            | SemanticKind.Lambda (parameters, _, _, _, _) -> Assert.Single parameters |> ignore
            | kind -> failwithf "Returned unit callable was absorbed: %A" kind
            Assert.False(result.Graph.Codata.Value.Curry.AbsorbedLambdas.Contains returned.Id)
        | kind -> failwithf "Factory lost its unit callable: %A" kind
        let work = UnitLambdas.value result (UnitLambdas.binding "work" result).Id
        UnitLambdas.same residual work.Type
        match work.Kind with
        | SemanticKind.Application (_, arguments) -> Assert.Single arguments |> ignore
        | kind -> failwithf "Factory invocation lost its own boundary: %A" kind
