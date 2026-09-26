namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module RecursiveSchemes = Clef.Compiler.PSGSaturation.SemanticGraph.SchemeInstances

module private MixedRecursionOracle =
    let check source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        result
    let declarations names (result: CheckResult) =
        result.Graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with
            | SemanticKind.Binding(name, false, true, None) -> names |> List.exists (fun original -> name.StartsWith(original + "__rec_mono", System.StringComparison.Ordinal))
            | _ -> false) |> Seq.toList
    let assertResidual (declarations: SemanticNode list) (result: CheckResult) =
        let targets = declarations |> List.map _.Id |> Set.ofList
        for declaration in declarations do
            match RecursiveSchemes.scheme declaration with
            | Some(parameters, signature) ->
                Assert.Single(parameters) |> ignore
                Assert.All(parameters, fun parameter -> Assert.Equal(TypeParamKind.Measure, parameter.Kind))
                Assert.Equal<NativeType>(applySubst signature, applySubst declaration.Type)
                Assert.NotEmpty(freeMeasureVars signature)
            | None -> failwith "The physical specialization lost its residual source scheme"
        let instances = RecursiveSchemes.reader result.Graph
        let uses = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.VarRef(_, Some target) -> targets.Contains target | _ -> false) |> Seq.toList
        Assert.NotEmpty uses
        for use' in uses do
            match instances use'.Id with
            | Some proof ->
                Assert.Single(proof.Arguments) |> ignore
                Assert.Contains(use'.Id, proof.Participants)
                Assert.Equal<NativeType>(applySubst use'.Type, applySubst (instantiate proof.Parameters proof.Arguments proof.Signature))
            | None -> failwithf "Occurrence %A lost its exact residual measure instance" use'.Id
        uses

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "MixedRecursiveSchemes")>]
type MixedRecursiveSchemeCases() =
    [<Fact>]
    member _.``Two measures share one recursive physical body with exact source instances``() =
        let result = MixedRecursionOracle.check """
let rec carry token value count =
    if count = 0 then (token, value * 1.0)
    else carry token value (count - 1)
let first = carry true 2.0<m> 2
let second = carry false 3.0<s> 3
"""
        let declarations = MixedRecursionOracle.declarations ["carry"] result
        Assert.Single declarations |> ignore
        let uses = MixedRecursionOracle.assertResidual declarations result
        Assert.Equal(3, uses.Length)
        let original = result.Graph.Nodes.Values |> Seq.find (fun node -> match node.Kind with SemanticKind.Binding("carry", _, _, _) -> true | _ -> false)
        Assert.False original.IsReachable
        match RecursiveSchemes.scheme original with
        | Some(parameters, _) -> Assert.Contains(parameters, fun parameter -> parameter.Kind = TypeParamKind.Type)
        | _ -> failwith "Original source scheme was erased"
        Assert.True(declarations.Head.Metadata.ContainsKey SchemeMetadata.Specialization)

    [<Fact>]
    member _.``Mutually recursive peers preserve each exact shared measure boundary``() =
        let result = MixedRecursionOracle.check """
let rec left token value count =
    if count = 0 then (token, value * 1.0)
    else right token value (count - 1)
and right token value count =
    if count = 0 then (token, value * 1.0)
    else left token value (count - 1)
let first = left true 2.0<m> 2
let second = right false 3.0<s> 3
"""
        let declarations = MixedRecursionOracle.declarations ["left"; "right"] result
        Assert.Equal(2, declarations.Length)
        let uses = MixedRecursionOracle.assertResidual declarations result
        Assert.Equal(4, uses.Length)

    [<Fact>]
    member _.``Physical type specialization stays separate from measure-only use variation``() =
        let result = MixedRecursionOracle.check """
let rec carry token value count =
    if count = 0 then (token, value * 1.0)
    else carry token value (count - 1)
let boolLength = carry true 2.0<m> 2
let boolTime = carry false 3.0<s> 3
let intLength = carry 4 5.0<m> 2
let intTime = carry 6 7.0<s> 3
"""
        let declarations = MixedRecursionOracle.declarations ["carry"] result
        Assert.Equal(2, declarations.Length)
        MixedRecursionOracle.assertResidual declarations result |> ignore
