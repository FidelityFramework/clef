namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.Nanopass.Recipe
module FoldIn = Clef.Compiler.Nanopass.FoldIn

module private FoldReferences =
    let range: SourceRange =
        { File = "fold-references.clef"; Start = { Line = 1; Column = 0 }; End = { Line = 1; Column = 12 } }

    let recipe original replacement nodes =
        { OriginalNodeId = original; ReplacementRootId = replacement
          NewNodes = nodes; ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = "Reference fixture" }

    let capture source mutableValue =
        { Name = "value"; Type = Types.boolType; IsMutable = mutableValue; SourceNodeId = source }

    let capturing kind body captures =
        match kind with
        | "lambda" -> SemanticKind.Lambda([], body, captures, Some "owner", LambdaContext.RegularClosure)
        | "lazy" -> SemanticKind.LazyExpr(body, captures)
        | "seq" -> SemanticKind.SeqExpr(body, captures)
        | _ -> failwith "Unknown capture fixture"

    let captures (node: SemanticNode) =
        match node.Kind with
        | SemanticKind.Lambda(_, _, captures, _, _)
        | SemanticKind.LazyExpr(_, captures)
        | SemanticKind.SeqExpr(_, captures) -> captures
        | kind -> failwithf "Expected captures, got %A" kind

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "FoldInReferences")>]
type FoldInReferenceCases() =
    [<Theory>]
    [<InlineData("lambda", true)>]
    [<InlineData("lazy", false)>]
    [<InlineData("seq", true)>]
    member _.``Surviving captures and resolved references follow the same replaced definition``(kind, mutableValue) =
        let builder = NodeBuilder()
        let create k = builder.Create(k, Types.boolType, FoldReferences.range)
        let original = create (SemanticKind.Binding("value", mutableValue, false, None))
        let shadow = create (SemanticKind.Binding("value", false, false, None))
        let read = create (SemanticKind.VarRef("value", Some original.Id))
        let shadowRead = create (SemanticKind.VarRef("value", Some shadow.Id))
        let unresolved = create (SemanticKind.VarRef("value", None))
        let captures = [FoldReferences.capture (Some original.Id) mutableValue
                        FoldReferences.capture (Some shadow.Id) false
                        FoldReferences.capture None false]
        let owner = create (FoldReferences.capturing kind read.Id captures)
        let graph = { builder.Build [] with Edges = kindEdges read.Id read.Kind }
        let originalNodes, originalEdges = graph.Nodes, graph.Edges
        let replacement = create (SemanticKind.Binding("replacement", mutableValue, false, None))
        let recipes = RecipeSet.fromList "Baker" [FoldReferences.recipe original.Id replacement.Id [replacement]]
        let folded = FoldIn.foldIn recipes graph
        let changed = FoldReferences.captures folded.Nodes[owner.Id]
        Assert.Equal<NodeId option list>([Some replacement.Id; Some shadow.Id; None], changed |> List.map _.SourceNodeId)
        Assert.Equal<bool list>([mutableValue; false; false], changed |> List.map _.IsMutable)
        for capture in changed do
            Assert.Equal("value", capture.Name)
            Assert.Equal("bool", formatType capture.Type)
            capture.SourceNodeId |> Option.iter (fun id -> Assert.True(folded.Nodes.ContainsKey id))
        match folded.Nodes[read.Id].Kind, folded.Nodes[shadowRead.Id].Kind, folded.Nodes[unresolved.Id].Kind with
        | SemanticKind.VarRef("value", Some target), SemanticKind.VarRef("value", Some other), SemanticKind.VarRef("value", None) ->
            Assert.Equal(replacement.Id, target)
            Assert.Equal(shadow.Id, other)
        | kinds -> failwithf "Reference identity changed unexpectedly: %A" kinds
        let reference = folded.Edges |> List.find (fun edge -> edge.Target = read.Id && edge.Class = EdgeClass.Reference)
        Assert.Equal<NodeId list>([replacement.Id], reference.Sources)
        Assert.False(folded.Nodes.ContainsKey original.Id)
        Assert.Equal(FoldReferences.range, folded.Nodes[owner.Id].Range)
        Assert.Same(originalNodes, graph.Nodes)
        Assert.Same(originalEdges, graph.Edges)
        Assert.Equal(Some original.Id, (FoldReferences.captures graph.Nodes[owner.Id]).Head.SourceNodeId)

    [<Theory>]
    [<InlineData("lambda")>]
    [<InlineData("lazy")>]
    [<InlineData("seq")>]
    member _.``A capture recipe follows a simultaneous definition replacement``(kind) =
        let builder = NodeBuilder()
        let create k = builder.Create(k, Types.boolType, FoldReferences.range)
        let original = create (SemanticKind.Binding("value", true, false, None))
        let read = create (SemanticKind.VarRef("value", Some original.Id))
        let captures = [FoldReferences.capture (Some original.Id) true]
        let owner = create (FoldReferences.capturing kind read.Id captures)
        let graph = builder.Build []
        let replacement = create (SemanticKind.Binding("replacement", true, false, None))
        let freshRead = create (SemanticKind.VarRef("value", Some original.Id))
        let freshOwner = create (FoldReferences.capturing kind freshRead.Id captures)
        let recipes = RecipeSet.fromList "Baker"
                        [FoldReferences.recipe original.Id replacement.Id [replacement]
                         FoldReferences.recipe owner.Id freshOwner.Id [freshRead; freshOwner]]
        let folded = FoldIn.foldIn recipes graph
        Assert.Equal(Some replacement.Id, (Assert.Single(FoldReferences.captures folded.Nodes[freshOwner.Id])).SourceNodeId)
        match folded.Nodes[freshRead.Id].Kind with
        | SemanticKind.VarRef("value", Some target) -> Assert.Equal(replacement.Id, target)
        | kind -> failwithf "Recipe-created reference lost its definition: %A" kind
        Assert.Equal(Some freshOwner.Id, folded.Nodes[freshRead.Id].Parent)
        Assert.False(folded.Nodes.ContainsKey original.Id)
        Assert.False(folded.Nodes.ContainsKey owner.Id)

    [<Fact>]
    member _.``Recipe incidence remaps every participant across simultaneous replacements``() =
        let builder = NodeBuilder()
        let create name = builder.Create(SemanticKind.PatternBinding name, Types.boolType, FoldReferences.range)
        let source, target, retained = create "source", create "target", create "retained"
        let graph = builder.Build []
        let replacementSource, replacementTarget = create "source occurrence", create "target occurrence"
        let edge = { Class = EdgeClass.Provenance; Role = EdgeRole.BranchOccurrence
                     Sources = [source.Id; retained.Id]; Target = target.Id; Ordinal = 3 }
        let sourceRecipe = { FoldReferences.recipe source.Id replacementSource.Id [replacementSource] with NewEdges = [edge] }
        let targetRecipe = FoldReferences.recipe target.Id replacementTarget.Id [replacementTarget]
        let folded = FoldIn.foldIn (RecipeSet.fromList "incidence" [sourceRecipe; targetRecipe]) graph
        let actual = Assert.Single folded.Edges
        Assert.Equal<NodeId list>([replacementSource.Id; retained.Id], actual.Sources)
        Assert.Equal(replacementTarget.Id, actual.Target)
        Assert.Equal(3, actual.Ordinal)
        Assert.Empty graph.Edges
        use json = System.Text.Json.JsonDocument.Parse(Clef.Compiler.Nanopass.Serialization.serializeRecipe sourceRecipe)
        let serialized = json.RootElement.GetProperty("newEdges").EnumerateArray() |> Seq.exactlyOne
        Assert.Equal(NodeId.value target.Id, serialized.GetProperty("target").GetInt32())
        Assert.Equal<int list>([NodeId.value source.Id; NodeId.value retained.Id],
            serialized.GetProperty("sources").EnumerateArray() |> Seq.map (fun value -> value.GetInt32()) |> Seq.toList)
