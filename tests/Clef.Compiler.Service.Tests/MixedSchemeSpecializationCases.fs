namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module MixedMono = Clef.Compiler.Nanopass.Monomorphization
module MixedInstances = Clef.Compiler.PSGSaturation.SemanticGraph.SchemeInstances

module private MixedSchemeFixture =
    // A phantom measure needs its checker-issued argument: the result type
    // alone cannot recover all scheme parameters or authorize substitution.
    let create dimensions =
        let builder = NodeBuilder()
        let range = { File = "mixed-scheme.clef"; Start = { Line = 1; Column = 0 }; End = { Line = 1; Column = 40 } }
        let valueParameter = freshTypeParam "'value" TypeParamKind.Type range
        let measureParameter = freshMeasureVar None |> measureCellOf
        let phantomParameter = freshMeasureVar None |> measureCellOf
        let parameters = [measureParameter; valueParameter; phantomParameter]
        let valueType = NativeType.TVar valueParameter
        let measured = DimensionalCases.measured (Dimension.ofVar (measureVarOf measureParameter))
        let signature = NativeType.TFun(valueType, NativeType.TFun(measured, measured))
        let tag = builder.Create(SemanticKind.PatternBinding "tag", valueType, range)
        let value = builder.Create(SemanticKind.PatternBinding "value", measured, range)
        let read = builder.Create(SemanticKind.VarRef("value", Some value.Id), measured, range)
        let code = builder.Create(SemanticKind.Lambda(["tag", valueType, tag.Id; "value", measured, value.Id], read.Id, [], Some "select", LambdaContext.RegularClosure), signature, range, children = [tag.Id; value.Id; read.Id])
        let scheme = NativeType.TForall(parameters, signature)
        let declaration = builder.Create(SemanticKind.Binding("select", false, false, None), scheme, range, children = [code.Id])
        let uses = dimensions |> List.map (fun dimension ->
            let arguments = [NativeType.TMeasure dimension; Types.boolType; NativeType.TMeasure DimensionalCases.second]
            let node = builder.Create(SemanticKind.VarRef("select", Some declaration.Id), instantiate parameters arguments signature, range)
            let metadata =
                arguments |> List.indexed |> List.fold (fun metadata (ordinal, argument) ->
                    Map.add (SchemeMetadata.argument ordinal) (MetadataValue.Type argument) metadata)
                    (Map.ofList [SchemeMetadata.Definition, MetadataValue.NodeId declaration.Id; SchemeMetadata.Declaration, MetadataValue.Type scheme])
            { node with Metadata = metadata })
        builder.Create(SemanticKind.ModuleDef("Mixed", declaration.Id :: (uses |> List.map _.Id)), Types.unitType, range) |> ignore
        let graph = builder.Build []
        let graph = { graph with Nodes = uses |> List.fold (fun nodes node -> Map.add node.Id node nodes) graph.Nodes }
        graph, declaration.Id, code.Id, uses

    let run graph =
        let result = MixedMono.runWithEvidence graph.Nodes
        { graph with Nodes = result.Nodes; Edges = result.Derivations }

    let clones declaration (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Metadata.TryFind SchemeMetadata.Specialization with
            | Some(MetadataValue.Specialization trace) when trace.SourceNode = declaration && trace.CloneNode = node.Id -> Some(node, trace)
            | _ -> None) |> Seq.toList

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "MixedSchemeSpecialization")>]
type MixedSchemeSpecializationCases() =
    [<Fact>]
    member _.``One checked measure specializes an existing physical group including its phantom argument``() =
        let before, declaration, _, uses = MixedSchemeFixture.create [DimensionalCases.metre]
        let graph = MixedSchemeFixture.run before
        let clone, trace = MixedSchemeFixture.clones declaration graph |> Assert.Single
        Assert.Equal(uses.Head.Type, clone.Type)
        Assert.Empty(freeMeasureVars clone.Type)
        Assert.False(clone.Metadata.ContainsKey SchemeMetadata.Declaration)
        Assert.False(graph.Nodes[uses.Head.Id].Metadata.ContainsKey SchemeMetadata.Declaration)
        Assert.Equal(3, trace.Parameters.Length)
        Assert.Equal<string list>(["m"; "bool"; "s"], trace.CodeArguments)
        Assert.False(graph.Nodes[declaration].IsReachable)

    [<Fact>]
    member _.``Distinct checked measures retain one code group and exact residual instances``() =
        let before, declaration, code, uses = MixedSchemeFixture.create [DimensionalCases.metre; DimensionalCases.second]
        let graph = MixedSchemeFixture.run before
        let clone, trace = MixedSchemeFixture.clones declaration graph |> Assert.Single
        let parameters, signature = MixedInstances.scheme clone |> Option.get
        Assert.Equal(TypeParamKind.Measure, (Assert.Single parameters).Kind)
        Assert.Equal(clone.Type, signature)
        Assert.Equal(2, trace.Requests.Length)
        let implementation = graph.Nodes[Assert.Single clone.Children]
        Assert.Equal(MixedInstances.scheme clone, MixedInstances.scheme implementation)
        Assert.Equal(MetadataValue.NodeId clone.Id, implementation.Metadata[SchemeMetadata.ImplementationDeclaration])
        let instance = MixedInstances.reader graph
        for useSite in uses do
            let actual = instance useSite.Id |> Option.get
            Assert.Equal(clone.Id, actual.Declaration)
            Assert.Equal(useSite.Type, instantiate actual.Parameters actual.Arguments actual.Signature)
            Assert.Equal(1, actual.Arguments.Length)
            Assert.False(graph.Nodes[useSite.Id].Metadata.ContainsKey(SchemeMetadata.argument 1))
        Assert.Contains(graph.Edges, fun edge -> edge.Role = EdgeRole.SchemeSpecialization && List.contains code edge.Sources)
        Assert.Equal(before.Nodes[declaration].Type, graph.Nodes[declaration].Type)

    [<Fact>]
    member _.``Same printed type name from distinct nominal owners cannot merge physical instances``() =
        let before, declaration, _, uses = MixedSchemeFixture.create [DimensionalCases.metre; DimensionalCases.metre]
        let nominal owner =
            NativeType.TApp({ Types.boolTyCon with Name = "Token"; Module = [owner]; NTUKind = None }, [])
        let left, right = nominal "Left", nominal "Right"
        Assert.Equal(formatType left, formatType right)
        Assert.NotEqual(left, right)
        let nodes = List.zip uses [left; right] |> List.fold (fun nodes (occurrence, argument) ->
            let ty = match occurrence.Type with NativeType.TFun(_, result) -> NativeType.TFun(argument, result) | _ -> failwith "Expected callable"
            Map.add occurrence.Id { occurrence with Type = ty; Metadata = occurrence.Metadata.Add(SchemeMetadata.argument 1, MetadataValue.Type argument) } nodes) before.Nodes
        let graph = MixedSchemeFixture.run { before with Nodes = nodes }
        Assert.Equal(2, MixedSchemeFixture.clones declaration graph |> List.length)
        for occurrence in uses do
            match graph.Nodes[occurrence.Id].Kind with
            | SemanticKind.VarRef(_, Some target) -> Assert.Equal(nodes[occurrence.Id].Type, graph.Nodes[target].Type)
            | _ -> failwith "Lost checked reference"

    [<Theory>]
    [<InlineData("missing")>]
    [<InlineData("extra")>]
    [<InlineData("kind")>]
    [<InlineData("owner")>]
    [<InlineData("signature")>]
    member _.``Incomplete or stale instance metadata cannot authorize measure specialization``(mutation: string) =
        let before, declaration, _, uses = MixedSchemeFixture.create [DimensionalCases.metre]
        let occurrence = uses.Head
        let metadata =
            match mutation with
            | "missing" -> occurrence.Metadata.Remove(SchemeMetadata.argument 2)
            | "extra" -> occurrence.Metadata.Add(SchemeMetadata.argument 3, MetadataValue.Type(NativeType.TMeasure DimensionalCases.metre))
            | "kind" -> occurrence.Metadata.Add(SchemeMetadata.argument 0, MetadataValue.Type Types.boolType)
            | "owner" -> occurrence.Metadata.Add(SchemeMetadata.Definition, MetadataValue.NodeId occurrence.Id)
            | "signature" -> occurrence.Metadata.Add(SchemeMetadata.argument 0, MetadataValue.Type(NativeType.TMeasure DimensionalCases.second))
            | _ -> failwith "Unknown mutation"
        let graph = MixedSchemeFixture.run { before with Nodes = before.Nodes.Add(occurrence.Id, { occurrence with Metadata = metadata }) }
        let clone, _ = MixedSchemeFixture.clones declaration graph |> Assert.Single
        let residual, _ = MixedInstances.scheme clone |> Option.get
        Assert.Equal(2, residual.Length)
        Assert.NotEmpty(freeMeasureVars clone.Type)
        Assert.True(MixedInstances.reader graph occurrence.Id |> Option.isNone)

    [<Fact>]
    member _.``Measured field projection agrees at checked occurrence clone body and public result``() =
        let result = DimensionalCases.check """
let inline project<[<Measure>] 'u, 'a> (x:'a) : float<'u> = x.Value
type Distance = { Value: float<m> }
let value = project<m,Distance> { Value = 2.0<m> }
[<EntryPoint>]
let main _ = if value = 2.0<m> then 0 else 1
"""
        DimensionalCases.noErrors result
        let expected = DimensionalCases.measured DimensionalCases.metre
        Assert.Equal(expected, DimensionalCases.bindingType "value" result)
        let clones = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(name, _, _, _) -> name.StartsWith("project__mono") | _ -> false)
        let clone = Assert.Single clones
        match applySubst clone.Type with
        | NativeType.TFun(_, actual) -> Assert.Equal(expected, actual)
        | other -> failwithf "Expected specialized projection, got %s" (formatType other)
        let liveFields = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.FieldGet _ -> true | _ -> false)
        Assert.NotEmpty liveFields
        for field in liveFields do Assert.Equal(expected, applySubst field.Type)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Adding a differently measured source request preserves one shared code body in either order``(reverse: bool) =
        let definition = "let select<[<Measure>] 'u, 'a> (tag:'a) (value:float<'u>) = value\n"
        let metre = "let length = select<m,bool> true 2.0<m>\n"
        let second = "let time = select<s,bool> false 3.0<s>\n"
        let requests = if reverse then second + metre else metre + second
        let result = DimensionalCases.check (definition + requests + "[<EntryPoint>]\nlet main _ = if length = 2.0<m> && time = 3.0<s> then 0 else 1\n")
        DimensionalCases.noErrors result
        Assert.Equal(DimensionalCases.measured DimensionalCases.metre, DimensionalCases.bindingType "length" result)
        Assert.Equal(DimensionalCases.measured DimensionalCases.second, DimensionalCases.bindingType "time" result)
        let clones = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(name, _, _, _) -> name.StartsWith("select__mono") | _ -> false)
        let clone = Assert.Single clones
        let residual, _ = MixedInstances.scheme clone |> Option.get
        Assert.Equal(TypeParamKind.Measure, (Assert.Single residual).Kind)
        let occurrences = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.VarRef(_, Some target) -> target = clone.Id | _ -> false) |> Seq.toList
        Assert.Equal(2, occurrences.Length)
        for occurrence in occurrences do Assert.True(MixedInstances.reader result.Graph occurrence.Id |> Option.isSome)

    [<Theory>]
    [<InlineData("missing")>]
    [<InlineData("wrong-kind")>]
    member _.``One malformed request prevents uniform measure specialization of its entire physical group``(mutation: string) =
        let before, declaration, _, uses = MixedSchemeFixture.create [DimensionalCases.metre; DimensionalCases.metre]
        let valid, invalid = uses[0], uses[1]
        let metadata =
            match mutation with
            | "missing" -> invalid.Metadata.Remove(SchemeMetadata.argument 2)
            | "wrong-kind" -> invalid.Metadata.Add(SchemeMetadata.argument 0, MetadataValue.Type Types.boolType)
            | _ -> failwith "Unknown mutation"
        let graph =
            MixedSchemeFixture.run
                { before with Nodes = before.Nodes.Add(invalid.Id, { invalid with Metadata = metadata }) }
        let clone, trace = MixedSchemeFixture.clones declaration graph |> Assert.Single
        let residual, signature = MixedInstances.scheme clone |> Option.get
        Assert.Equal(2, residual.Length)
        Assert.All(residual, fun parameter -> Assert.Equal(TypeParamKind.Measure, parameter.Kind))
        Assert.NotEmpty(freeMeasureVars signature)
        Assert.Equal(2, trace.Requests.Length)
        for occurrence in uses do
            match graph.Nodes[occurrence.Id].Kind with
            | SemanticKind.VarRef(_, Some target) -> Assert.Equal(clone.Id, target)
            | _ -> failwith "Lost the source occurrence's physical group"
        let instance = MixedInstances.reader graph
        let actual = instance valid.Id |> Option.get
        Assert.Equal(clone.Id, actual.Declaration)
        Assert.Equal(2, actual.Arguments.Length)
        Assert.Equal(valid.Type, instantiate actual.Parameters actual.Arguments actual.Signature)
        Assert.True(instance invalid.Id |> Option.isNone)
