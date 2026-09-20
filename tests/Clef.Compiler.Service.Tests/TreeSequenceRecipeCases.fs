namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
module TreePatterns = Clef.Compiler.Baker.Ingredients.Patterns
module TreePrimitives = Clef.Compiler.Baker.Ingredients.Primitives
// Shared sequence ingredient contracts only: no Map sentinel, recursive-call
// resolution, suspension-frame or native enumeration conformance is asserted.
[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "TreeSequenceRecipes")>]
type TreeSequenceRecipeCases() =
    [<Theory>]
    [<InlineData("keys")>]
    [<InlineData("values")>]
    [<InlineData("pairs")>]
    member _.``Tree producers retain typed captures and unit generator bodies``(operation: string) =
        let key, value = Types.intType, Types.boolType
        let mapType = NativeType.TMap(key, value)
        let producer, element =
            match operation with
            | "keys" -> TreePatterns.inOrderKeysSeq, key
            | "values" -> TreePatterns.inOrderValuesSeq, value
            | "pairs" -> TreePatterns.inOrderPairsSeq, NativeType.TTuple([key; value], false)
            | name -> failwithf "Unknown tree producer: %s" name
        let range: SourceRange =
            { File = "tree-sequence.clef"; Start = { Line = 3; Column = 4 }; End = { Line = 3; Column = 30 } }
        let state = SaturationState.create range ("Map." + operation) 1 (NodeId 0) None
        let recipe = saturation {
            let! input = TreePrimitives.patternBinding "input" mapType
            return! producer input key value
        }
        let result, emitted = run state recipe
        match result with Matched _ -> () | NoMatch reason -> failwith reason
        let nodes = emitted |> List.map (fun node -> node.Id, node) |> Map.ofList
        let owner = emitted |> List.filter (fun node -> match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false) |> Assert.Single
        Assert.Equal<NativeType>(Types.mkSeqType element, owner.Type)
        let generatorId, ownerCaptures =
            match owner.Kind with SemanticKind.SeqExpr(id, captures) -> id, captures | _ -> failwith "Missing sequence owner"
        let generator = nodes[generatorId]
        let formalId, bodyId =
            match generator.Kind with
            | SemanticKind.Lambda([(name, ty, formal)], body, captures, enclosing, LambdaContext.SeqGenerator) ->
                Assert.Equal(SemanticKind.PatternBinding name, nodes[formal].Kind)
                Assert.Equal<NativeType>(NativeType.TNativePtr owner.Type, ty)
                Assert.Equal<NativeType>(ty, nodes[formal].Type)
                Assert.Equal<NativeType>(NativeType.TFun(ty, Types.boolType), generator.Type)
                Assert.Equal<CaptureInfo list>(ownerCaptures, captures)
                Assert.Equal(Some "traverse", enclosing)
                formal, body
            | kind -> failwithf "Missing typed sequence generator: %A" kind
        Assert.True(NodeId.value formalId >= 0)
        Assert.Equal<NodeId list>([generatorId], owner.Children)
        Assert.Equal<NodeId list>([formalId; bodyId], generator.Children)
        Assert.Equal(Some generatorId, nodes[formalId].Parent)
        Assert.Equal(Some generatorId, nodes[bodyId].Parent)
        Assert.Equal(Some owner.Id, generator.Parent)
        let outer = emitted |> List.filter (fun node -> match node.Kind with SemanticKind.Lambda(_, _, _, _, LambdaContext.RegularClosure) -> true | _ -> false) |> Assert.Single
        let treeId =
            match outer.Kind with
            | SemanticKind.Lambda([("tree", ty, tree)], body, _, _, _) ->
                Assert.Equal<NativeType>(mapType, ty)
                Assert.Equal<NodeId list>([tree; owner.Id], outer.Children)
                Assert.Equal(owner.Id, body)
                tree
            | kind -> failwithf "Missing outer tree formal: %A" kind
        let capture = Assert.Single ownerCaptures
        Assert.Equal(Some treeId, capture.SourceNodeId)
        Assert.False(capture.IsMutable)
        Assert.Equal<NativeType>(mapType, capture.Type)
        Assert.Equal<NativeType>(Types.unitType, nodes[bodyId].Type)
        match nodes[bodyId].Kind with
        | SemanticKind.IfThenElse(_, empty, Some yielding) ->
            Assert.Equal(SemanticKind.Literal NativeLiteral.Unit, nodes[empty].Kind)
            for id in [empty; yielding] do Assert.Equal<NativeType>(Types.unitType, nodes[id].Type)
        | kind -> failwithf "Generator lost its unit empty branch: %A" kind
        let rec walk seen id = if Set.contains id seen then seen else nodes[id].Children |> List.fold walk (Set.add id seen)
        let bodyNodes = walk Set.empty bodyId |> Set.toList |> List.map (fun id -> nodes[id])
        Assert.DoesNotContain(bodyNodes, fun node -> node.Id = treeId)
        let reference = bodyNodes |> List.filter (fun node -> match node.Kind with SemanticKind.VarRef("tree", _) -> true | _ -> false) |> Assert.Single
        Assert.Equal(SemanticKind.VarRef("tree", Some treeId), reference.Kind)
        Assert.Equal<NativeType>(mapType, reference.Type)
        let yields = bodyNodes |> List.choose (fun node -> match node.Kind with SemanticKind.Yield id -> Some(node, id, element) | SemanticKind.YieldBang id -> Some(node, id, owner.Type) | _ -> None)
        Assert.Equal(3, yields.Length)
        for node, payload, expected in yields do
            Assert.Equal<NativeType>(Types.unitType, node.Type)
            Assert.Equal<NativeType>(expected, nodes[payload].Type)
            match nodes[payload].Kind with
            | SemanticKind.TupleExpr values -> Assert.Equal<NodeId list>(values, nodes[payload].Children)
            | _ -> ()
