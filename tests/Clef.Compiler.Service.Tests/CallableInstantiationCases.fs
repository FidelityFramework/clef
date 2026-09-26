namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.Nanopass.Recipe

module Instances = Clef.Compiler.PSGSaturation.SemanticGraph.CallableInstantiations
module InstanceEnvironments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments

module private InstanceFixture =
    // NTU dimensional architecture §§3.2, 5.3 and 7.2 retain exact units in
    // source types while sharing representation-neutral measure instances.
    // The native kinds below deliberately avoid inherited fixed-width F# names.
    let source = """module Instances
[<Measure>] type m
[<Measure>] type s
[<EntryPoint>]
let main _ =
    let scale = 2
    let mutable calls = 0
    let mapper = fun value -> calls <- (calls + 1) % 100; value * scale
    let alias = mapper
    let length = alias 3<m>
    let time = alias 4<s>
    let velocity = alias 5<m/s>
    if length = 6<m> && time = 8<s> && velocity = 10<m/s> then calls else 0
"""
    let check () =
        match parseAndCheck source "callable-instances.clef" with
        | Success result -> DimensionalCases.noErrors result; result.Graph
        | other -> failwithf "Expected checked source: %A" other

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
        |> Assert.Single

    let sites (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with SemanticKind.VarRef("alias", Some _) -> true | _ -> false)
        |> Seq.sortBy (fun node -> node.Range.Start.Line) |> Seq.toList

    let signature (graph: SemanticGraph) implementation =
        match graph.Nodes[implementation].Metadata.TryFind ClosureMetadata.SourceSignature with
        | Some(MetadataValue.Type ty) -> ty
        | _ -> failwith "Expected retained source callable signature"

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "CallableInstantiations")>]
type CallableInstantiationCases() =
    [<Fact>]
    member _.``Closure write rewrite retires replaced target reads but retains actual reads and shared cells``() =
        let graph = InstanceFixture.check ()
        let cell = InstanceFixture.binding "calls" graph
        let writes = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.EnvironmentWrite(_, slot, _) -> slot = cell.Id | _ -> false) |> Seq.toList
        Assert.NotEmpty writes
        let replacedTargets =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                match node.Kind, node.Parent with
                | SemanticKind.EnvironmentRead(_, slot), Some parent when slot = cell.Id ->
                    writes |> List.exists (fun write -> write.Id = parent && not (List.contains node.Id write.Children))
                | _ -> false)
            |> Seq.toList
        Assert.NotEmpty replacedTargets
        for target in replacedTargets do
            Assert.False(target.IsReachable, "A former Set target is no longer an evaluated EnvironmentWrite operand")
            for child in target.Children do Assert.False(graph.Nodes[child].IsReachable)
            Assert.Contains(graph.Edges, fun edge ->
                edge.Role = EdgeRole.CaptureReferenceOrigin && edge.Target = target.Id && List.contains cell.Id edge.Sources)
        Assert.Contains(graph.Nodes.Values, fun node ->
            node.IsReachable && match node.Kind with SemanticKind.EnvironmentRead(_, slot) -> slot = cell.Id | _ -> false)
        for write in writes do
            match write.Kind with
            | SemanticKind.EnvironmentWrite(environment, slot, value) ->
                Assert.Equal(cell.Id, slot)
                Assert.Equal<NodeId list>([environment; value], write.Children)
                Assert.True(graph.Nodes[environment].IsReachable)
                Assert.True(graph.Nodes[value].IsReachable)
            | _ -> failwith "Expected an environment write"

    [<Fact>]
    member _.``Rejected signature lookup cannot poison the shared declaration cache``() =
        let graph = InstanceFixture.check ()
        let mapper = InstanceFixture.binding "mapper" graph
        let implementation = InstanceEnvironments.tryImplementation graph mapper.Id |> Option.get
        let signature = InstanceFixture.signature graph implementation
        let site = InstanceFixture.sites graph |> List.head
        let wrong = NativeType.TFun(Types.boolType, Types.boolType)
        let rejectedFirst = Instances.reader graph
        Assert.True((rejectedFirst implementation wrong site.Id).IsNone)
        let afterRejected = rejectedFirst implementation signature site.Id |> Option.get
        let acceptedFirst = Instances.reader graph
        let beforeRejected = acceptedFirst implementation signature site.Id |> Option.get
        Assert.True((acceptedFirst implementation wrong site.Id).IsNone)
        Assert.Equal(beforeRejected, afterRejected)
        Assert.Equal(beforeRejected, acceptedFirst implementation signature site.Id |> Option.get)

    [<Fact>]
    member _.``Fold-in remaps scheme declaration authority with its actual callable value``() =
        let graph = InstanceFixture.check ()
        let mapper = InstanceFixture.binding "mapper" graph
        let alias = InstanceFixture.binding "alias" graph
        let implementation = InstanceEnvironments.tryImplementation graph mapper.Id |> Option.get
        let site = InstanceFixture.sites graph |> List.head
        let originals = [mapper; alias; graph.Nodes[implementation]; site]
        let replacements = originals |> List.map (fun node -> node.Id, { node with Id = NodeId.fresh() }) |> Map.ofList
        let recipes = originals |> List.map (fun node ->
            let replacement = replacements[node.Id]
            { OriginalNodeId = node.Id
              ReplacementRootId = replacement.Id; NewNodes = [replacement]
              ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = "Measured callable replacement" })
        let folded = Clef.Compiler.Nanopass.FoldIn.foldIn (Clef.Compiler.Nanopass.Recipe.RecipeSet.fromList "Baker" recipes) graph
        let code = replacements[implementation].Id
        let occurrence = replacements[site.Id].Id
        let proof = Instances.reader folded code (InstanceFixture.signature folded code) occurrence |> Option.get
        Assert.Equal(replacements[mapper.Id].Id, proof.Template.Declaration)
        Assert.Contains(replacements[alias.Id].Id, proof.ValuePath)
        Assert.Equal("int<m> -> int<m>", formatType proof.InstanceType)
        for original in originals do
            Assert.False(folded.Nodes.ContainsKey original.Id)
            Assert.DoesNotContain(original.Id, proof.Participants)
        Assert.Equal(MetadataValue.NodeId replacements[alias.Id].Id, folded.Nodes[occurrence].Metadata[SchemeMetadata.Definition])
        Assert.Equal(MetadataValue.NodeId replacements[mapper.Id].Id, folded.Nodes[code].Metadata[SchemeMetadata.ImplementationDeclaration])

    [<Fact>]
    member _.``Distinct and composed measures retain checked instances of one actual captured closure``() =
        let graph = InstanceFixture.check ()
        let mapper = InstanceFixture.binding "mapper" graph
        let alias = InstanceFixture.binding "alias" graph
        let calls = InstanceFixture.binding "calls" graph
        let implementation = InstanceEnvironments.tryImplementation graph mapper.Id |> Option.get
        let signature = InstanceFixture.signature graph implementation
        let read = Instances.reader graph
        let sites = InstanceFixture.sites graph
        Assert.Equal(3, sites.Length)
        let proofs = sites |> List.map (fun node -> read implementation signature node.Id |> Option.get)
        Assert.NotEqual<NativeType list>(proofs[0].Arguments, proofs[1].Arguments)
        Assert.Equal("int<m> -> int<m>", formatType proofs[0].InstanceType)
        Assert.Equal("int<s> -> int<s>", formatType proofs[1].InstanceType)
        Assert.NotEqual<NativeType list>(proofs[1].Arguments, proofs[2].Arguments)
        Assert.Empty(freeMeasureVars proofs[2].InstanceType)
        for proof in proofs do
            Assert.Equal(mapper.Id, proof.Template.Declaration)
            Assert.Equal(implementation, proof.Template.Implementation)
            Assert.Contains(alias.Id, proof.ValuePath)
            Assert.Contains(mapper.Id, proof.ValuePath)
            Assert.True(Instances.canTransport graph alias.Id proof.Occurrence)
        let known = InstanceEnvironments.knownCallables graph
        let owner = known[mapper.Id].EnvironmentOwner
        for node in alias :: sites do
            Assert.Equal(owner, known[node.Id].EnvironmentOwner)
            Assert.Equal(implementation, known[node.Id].Implementation)
        let captures = InstanceEnvironments.capturedInitializers graph owner |> Option.get
        Assert.Contains(captures, fun (slot, value, mutableCell) -> slot = calls.Id && value = calls.Id && mutableCell)
        Assert.Single(graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.EnvironmentCreate(actual, _) -> actual = owner | _ -> false)) |> ignore
        Assert.False(Instances.canTransport graph sites[0].Id sites[1].Id)

    [<Fact>]
    member _.``Sharing measured code does not admit mismatched source dimensions``() =
        let source = InstanceFixture.source.Replace("let time = alias 4<s>", "let time: int<s> = alias 4<m>")
        match parseAndCheck source "callable-instance-mismatch.clef" with
        | Success result | CheckFailure result ->
            Assert.Contains(result.Diagnostics, fun diagnostic ->
                Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error)
        | ParseFailure errors -> failwithf "Dimensional disagreement must be checked, not rejected by parsing: %A" errors

    [<Theory>]
    [<InlineData("missing argument")>]
    [<InlineData("extra argument")>]
    [<InlineData("wrong argument")>]
    [<InlineData("wrong argument kind")>]
    [<InlineData("missing declaration")>]
    [<InlineData("wrong declaration")>]
    [<InlineData("changed occurrence type")>]
    [<InlineData("mutable alias")>]
    [<InlineData("changed implementation owner")>]
    member _.``Changed scheme occurrence participants retract instance authority``(change: string) =
        let graph = InstanceFixture.check ()
        let mapper = InstanceFixture.binding "mapper" graph
        let alias = InstanceFixture.binding "alias" graph
        let implementation = InstanceEnvironments.tryImplementation graph mapper.Id |> Option.get
        let signature = InstanceFixture.signature graph implementation
        let site = InstanceFixture.sites graph |> List.head
        Assert.True((Instances.reader graph implementation signature site.Id).IsSome)
        let changeNode id f = { graph with Nodes = graph.Nodes.Add(id, f graph.Nodes[id]) }
        let metadata key value = changeNode site.Id (fun node -> { node with Metadata = node.Metadata.Add(key, value) })
        let changed =
            match change with
            | "missing argument" -> changeNode site.Id (fun node -> { node with Metadata = node.Metadata.Remove(SchemeMetadata.argument 0) })
            | "extra argument" -> metadata (SchemeMetadata.argument 1) (MetadataValue.Type Types.unitType)
            | "wrong argument" ->
                let other = InstanceFixture.sites graph |> List.last
                metadata (SchemeMetadata.argument 0) other.Metadata[SchemeMetadata.argument 0]
            | "wrong argument kind" -> metadata (SchemeMetadata.argument 0) (MetadataValue.Type Types.unitType)
            | "missing declaration" -> changeNode site.Id (fun node -> { node with Metadata = node.Metadata.Remove SchemeMetadata.Declaration })
            | "wrong declaration" -> metadata SchemeMetadata.Definition (MetadataValue.NodeId mapper.Id)
            | "changed occurrence type" -> changeNode site.Id (fun node -> { node with Type = NativeType.TFun(Types.boolType, Types.boolType) })
            | "mutable alias" -> changeNode alias.Id (fun node -> { node with Kind = SemanticKind.Binding("alias", true, false, None) })
            | "changed implementation owner" -> changeNode implementation (fun node -> { node with Metadata = node.Metadata.Add(SchemeMetadata.ImplementationDeclaration, MetadataValue.NodeId alias.Id) })
            | _ -> failwith "Unknown mutation"
        Assert.True((Instances.reader changed implementation signature site.Id).IsNone, change)
        Assert.True((Instances.reader graph implementation signature site.Id).IsSome, "The original immutable graph must retain its proof")

    [<Theory>]
    [<InlineData(1, 1, 1)>]
    [<InlineData(2, 3, 1)>]
    [<InlineData(2, 4, 2)>]
    member _.``Reciprocal scheme normalization preserves the coupled exponent lattice``(leftPower: int, rightPower: int, survivingPower: int) =
        // Kennedy Types at Work §§3.8–3.10: normalization is a scheme operation,
        // not plain ML variable subtraction or equality of printed dimensions.
        let left, right = freshMeasureVar None, freshMeasureVar None
        let dimension =
            Clef.Compiler.NativeTypedTree.DimensionAlgebra.Dimension.mul
                (Clef.Compiler.NativeTypedTree.DimensionAlgebra.Dimension.pow leftPower (Clef.Compiler.NativeTypedTree.DimensionAlgebra.Dimension.ofVar left))
                (Clef.Compiler.NativeTypedTree.DimensionAlgebra.Dimension.pow rightPower (Clef.Compiler.NativeTypedTree.DimensionAlgebra.Dimension.ofVar right))
        let reciprocal = Clef.Compiler.NativeTypedTree.DimensionAlgebra.Dimension.pow -1 dimension
        let original = NativeType.TFun(DimensionalCases.measured dimension, DimensionalCases.measured reciprocal)
        match generalizeType Set.empty original with
        | NativeType.TForall([parameter], body) ->
            Assert.Equal(TypeParamKind.Measure, parameter.Kind)
            for unit in [DimensionalCases.metre; DimensionalCases.second] do
                let input = Clef.Compiler.NativeTypedTree.DimensionAlgebra.Dimension.pow survivingPower unit
                let output = Clef.Compiler.NativeTypedTree.DimensionAlgebra.Dimension.pow -1 input
                let actual = instantiate [parameter] [NativeType.TMeasure unit] body |> applySubst
                Assert.Equal(NativeType.TFun(DimensionalCases.measured input, DimensionalCases.measured output), actual)
        | other -> failwithf "Expected one scheme parameter for the exponent matrix rank: %s" (formatType other)

    [<Fact>]
    member _.``Instantiation preserves a measured record constructor and its projected dimensional result``() =
        let source = """module RecordInstances
[<Measure>] type m
[<Measure>] type s
type Quantity<[<Measure>] 'u> = { Value: float<'u> }
[<EntryPoint>]
let main _ =
    let mutable calls = 0
    let project = fun (value: Quantity<'u>) -> calls <- (calls + 1) % 100; value.Value
    let alias = project
    let length = alias { Value = 3.0<m> }
    let time = alias { Value = 4.0<s> }
    if length = 3.0<m> && time = 4.0<s> then calls else 0
"""
        let graph =
            match parseAndCheck source "record-callable-instances.clef" with
            | Success result -> DimensionalCases.noErrors result; result.Graph
            | other -> failwithf "Expected a checked measured record: %A" other
        let definition = InstanceFixture.binding "project" graph
        let implementation = InstanceEnvironments.tryImplementation graph definition.Id |> Option.get
        let read = Instances.reader graph implementation (InstanceFixture.signature graph implementation)
        let sites = InstanceFixture.sites graph
        Assert.Equal(2, sites.Length)
        for site in sites do
            let proof = read site.Id |> Option.get
            match proof.InstanceType with
            | NativeType.TFun(NativeType.TApp(record, [NativeType.TMeasure input]), NativeType.TNum(_, output)) ->
                Assert.Equal("Quantity", record.Name)
                Assert.Equal(input, output)
                Assert.Empty(input.Vars)
            | ty -> failwithf "Measured aggregate shape was not retained: %s" (formatType ty)
            Assert.Equal(definition.Id, proof.Template.Declaration)
        Assert.NotEqual(sites[0].Type, sites[1].Type)
