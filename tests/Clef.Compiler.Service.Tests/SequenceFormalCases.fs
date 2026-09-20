namespace Clef.Compiler.Service.Tests

open System
open System.IO
open System.Text.Json
open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.NativeTypedTree.Infrastructure
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

// Generator parameters are resident graph participants. This does not settle
// suspension, frame layout, or the MoveNext transition from yield to bool.
module private SequenceFormals =
    let check source =
        let prelude = "module Dimensions\n[<Measure>] type m\n"
        let directory = Path.Combine(Path.GetTempPath(), "clef-sequence-formals-" + Guid.NewGuid().ToString("N"))
        let previous = PhaseConfig.getConfig ()
        Directory.CreateDirectory directory |> ignore
        try
            PhaseConfig.enableArtifacts directory [1]
            let result =
                match parseAndCheck (prelude + source) "sequence-formals.clef" with
                | Success result -> result
                | CheckFailure result -> failwithf "Expected admitted sequence source: %A" result.Diagnostics
                | ParseFailure errors -> failwithf "Expected parsed sequence source: %A" errors
            DimensionalCases.noErrors result
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Error _ -> true | _ -> false)
            use document = JsonDocument.Parse(File.ReadAllText(Path.Combine(directory, "01_psg0.json")))
            let raw = document.RootElement.GetProperty("nodes").EnumerateArray()
                      |> Seq.map (fun node -> node.GetProperty("id").GetInt32(), node.Clone()) |> Map.ofSeq
            result, raw
        finally
            PhaseConfig.setConfig previous
            Directory.Delete(directory, true)

    let rawChildren (raw: Map<int, JsonElement>) id =
        raw[NodeId.value id].GetProperty("children").EnumerateArray() |> Seq.map (fun child -> child.GetInt32()) |> Seq.toList

    let owners (result: CheckResult) =
        result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.SeqExpr _ -> true | _ -> false) |> Seq.toList

    let assertFormal (result: CheckResult) (raw: Map<int, JsonElement>) (owner: SemanticNode) =
        let nodes = result.Graph.Nodes
        match owner.Kind with
        | SemanticKind.SeqExpr (generatorId, ownerCaptures) ->
            let generator = nodes[generatorId]
            match generator.Kind with
            | SemanticKind.Lambda ([(name, parameterType, parameterId)], body, captures, _, LambdaContext.SeqGenerator) ->
                Assert.True(nodes.ContainsKey parameterId, sprintf "Generator formal %A is not resident in the graph" parameterId)
                let parameter = nodes[parameterId]
                Assert.Equal(SemanticKind.PatternBinding name, parameter.Kind)
                let expected = NativeType.TNativePtr owner.Type
                DimensionalCases.same expected parameterType
                DimensionalCases.same expected parameter.Type
                Assert.Empty(freeTypeVars parameter.Type)
                match applySubst generator.Type with
                | NativeType.TFun (domain, resultType) ->
                    DimensionalCases.same expected domain
                    DimensionalCases.same Types.boolType resultType
                | ty -> failwithf "Generator lost its callable signature: %A" ty
                Assert.Equal<NodeId list>([parameterId; body], generator.Children)
                Assert.Equal<int list>([NodeId.value parameterId; NodeId.value body], rawChildren raw generatorId)
                Assert.Equal<int list>([NodeId.value generatorId], rawChildren raw owner.Id)
                let originalParameter = raw[NodeId.value parameterId]
                Assert.Equal(sprintf "PatternBinding \"%s\"" name, originalParameter.GetProperty("kind").GetString())
                Assert.Equal(NodeId.value generatorId, originalParameter.GetProperty("parent").GetInt32())
                Assert.Equal(Some generatorId, parameter.Parent)
                Assert.Equal(Some generatorId, nodes[body].Parent)
                Assert.Equal(Some owner.Id, generator.Parent)
                Assert.Equal<NodeId list>([generatorId], owner.Children)
                let sourceAnchor = { owner.Range with End = owner.Range.Start }
                Assert.Equal<SourceRange>(sourceAnchor, parameter.Range)
                // Structural relations are the canonical kind projection; F
                // stores enrichments until the fixpoint needs materialization.
                let relations = kindEdges generatorId generator.Kind
                for role, participant in [EdgeRole.Parameter, parameterId; EdgeRole.Body, body] do
                    Assert.Contains(relations, fun edge ->
                        edge.Class = EdgeClass.Structural && edge.Role = role && edge.Ordinal = 0 &&
                        edge.Target = generatorId && edge.Sources = [participant])
                Assert.Equal<CaptureInfo list>(ownerCaptures, captures)
                for capture in captures do
                    Assert.True(capture.SourceNodeId |> Option.exists nodes.ContainsKey)
                    Assert.NotEqual(Some parameterId, capture.SourceNodeId)
                parameter, captures
            | kind -> failwithf "Expected one explicit generator parameter: %A" kind
        | kind -> failwithf "Expected a sequence owner: %A" kind

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceFormals")>]
type SequenceFormalCases() =
    [<Theory>]
    [<InlineData("let observed = seq { yield 1<m> }")>]
    [<InlineData("let observed: seq<int<m>> = seq { () }")>]
    [<InlineData("let observed = seq { yield 0.25<1/m> }")>]
    member _.``Measured and empty sequences retain real typed generator formals``(source: string) =
        let result, raw = SequenceFormals.check (source + "\n[<EntryPoint>]\nlet main _ = ignore observed; 0\n")
        let owner = SequenceFormals.owners result |> Assert.Single
        let _, captures = SequenceFormals.assertFormal result raw owner
        Assert.Empty captures

    [<Fact>]
    member _.``Nested owners have distinct formals with their own sequence domains``() =
        let result, raw = SequenceFormals.check """
let observed = seq { yield (seq { yield 1<m> }) }
[<EntryPoint>]
let main _ = ignore observed; 0
"""
        let owners = SequenceFormals.owners result
        Assert.Equal(2, owners.Length)
        let parameters = owners |> List.map (SequenceFormals.assertFormal result raw >> fst)
        Assert.Equal(2, parameters |> List.map (fun parameter -> parameter.Id) |> Set.ofList |> Set.count)
        for parameter in parameters do
            Assert.DoesNotContain(owners, fun owner -> owner.Id = parameter.Id)
        let actualDomains = parameters |> List.map (fun parameter -> applySubst parameter.Type)
        let element = DimensionalCases.measuredInt DimensionalCases.metre
        Assert.Contains(NativeType.TNativePtr (Types.mkSeqType element), actualDomains)
        Assert.Contains(NativeType.TNativePtr (Types.mkSeqType (Types.mkSeqType element)), actualDomains)

    [<Theory>]
    [<InlineData("_seq_ptr", false)>]
    [<InlineData("seed", true)>]
    member _.``Internal formals do not replace lexical capture identities``(name: string, isMutable: bool) =
        let mutableKeyword = if isMutable then "mutable " else ""
        let result, raw = SequenceFormals.check $"""
[<EntryPoint>]
let main _ =
    let {mutableKeyword}{name}: int<m> = 3<m>
    let observed = seq {{ yield {name} }}
    ignore observed
    0
"""
        let owner = SequenceFormals.owners result |> Assert.Single
        let parameter, captures = SequenceFormals.assertFormal result raw owner
        let capture = Assert.Single captures
        let source = result.Graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.Binding (actual, _, _, _) -> actual = name | _ -> false)
        Assert.Equal(name, capture.Name)
        Assert.Equal(isMutable, capture.IsMutable)
        Assert.Equal(Some source.Id, capture.SourceNodeId)
        Assert.NotEqual(source.Id, parameter.Id)
        let payloads = result.Graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with SemanticKind.Yield payload -> Some result.Graph.Nodes[payload] | _ -> None) |> Seq.toList
        let payload = Assert.Single payloads
        match payload.Kind with
        | SemanticKind.VarRef (actual, Some definition) ->
            Assert.Equal(name, actual)
            Assert.Equal(source.Id, definition)
        | kind -> failwithf "Internal formal changed the source capture read: %A" kind
