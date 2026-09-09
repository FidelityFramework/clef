namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module IntegerDischarge = Clef.Compiler.Nanopass.ObligationDischarge
module IntegerElaboration = Clef.Compiler.Nanopass.ObligationElaboration

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "IntegerObligations")>]
type IntegerObligationTests() =
    [<Fact>]
    member _.``Measured integer literals publish their analysed range obligations``() =
        let result = DimensionalCases.check """let speed (distance: int<m>) (elapsed: int<s>) = distance / elapsed
[<EntryPoint>]
let main _ =
    let distance = 12<m>
    let elapsed = 3<s>
    if speed distance elapsed > 0<m/s> then 0 else 1
"""
        DimensionalCases.noErrors result
        let obligations = IntegerDischarge.ofGraph result.Graph
        for value in [12L; 3L] do
            let site = result.Graph.Nodes.Values |> Seq.find (fun node ->
                node.IsReachable && (match node.Kind with SemanticKind.Literal(NativeLiteral.Int(actual, _)) -> actual = value | _ -> false))
            Assert.Contains(obligations, fun ob -> ob.Kind = "integer-literal-range" && ob.Source = sprintf "%s:%d:%d" site.Range.File site.Range.Start.Line site.Range.Start.Column)

    [<Fact>]
    member _.``Integer evidence preserves analysed bounds and diagnoses missing facts``() =
        let result = DimensionalCases.check "[<EntryPoint>]\nlet main _ = 12\n"
        DimensionalCases.noErrors result
        let site = result.Graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable && (match node.Kind with SemanticKind.Literal(NativeLiteral.Int(12L, _)) -> true | _ -> false))
        let evidence range =
            let graph = { result.Graph with Nodes = result.Graph.Nodes |> Map.add site.Id { site with ValueRange = range } }
            let enrichment, diagnostics = IntegerElaboration.elaborateSettled graph
            let bodies = enrichment.NewNodes |> List.choose (fun node ->
                if node.Range <> site.Range then None
                else match node.Kind with SemanticKind.Obligation ob -> Some ob.Body | _ -> None)
            bodies, diagnostics
        let bounds, errors = evidence (Some (ValueRange.Bounded(10I, 20I)))
        Assert.Empty errors
        Assert.Contains(ObligationBody.IntegerLiteralRange(12I, 10I, 20I), bounds)
        let corrupt, errors = evidence (Some (ValueRange.Bounded(0I, 5I)))
        Assert.Contains(ObligationBody.IntegerLiteralRange(12I, 0I, 5I), corrupt)
        Assert.Contains(errors, fun error -> error.Code = "CCS8012")
        for missing in [None; Some ValueRange.Unbounded; Some ValueRange.Empty] do
            let bodies, errors = evidence missing
            Assert.DoesNotContain(bodies, fun body -> match body with ObligationBody.IntegerLiteralRange _ -> true | _ -> false)
            Assert.Contains(errors, fun error -> error.Code = "CCS8011")

    [<Fact>]
    member _.``Signed and unsigned integer literal evidence is exact beyond narrow host widths``() =
        let result = DimensionalCases.check "[<EntryPoint>]\nlet main _ = -2147483649\n"
        DimensionalCases.noErrors result
        Assert.Contains(IntegerDischarge.ofGraph result.Graph, fun ob ->
            match ob.Body with ObligationBody.IntegerLiteralRange(value, lower, upper) -> value = -2147483649I && lower = value && upper = value | _ -> false)
        let site = result.Graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable && (match node.Kind with SemanticKind.Literal(NativeLiteral.Int _) -> true | _ -> false))
        // Exercise the native unsigned literal branch without introducing a
        // width-named source spelling that the language deliberately rejects.
        let value = bigint System.UInt64.MaxValue
        let unsigned = { site with Kind = SemanticKind.Literal(NativeLiteral.UInt(System.UInt64.MaxValue, NTUKind.NTUuint(NTUWidth.Fixed 64)))
                                   Type = Types.uint64Type; ValueRange = Some (ValueRange.point value) }
        let graph = { result.Graph with Nodes = result.Graph.Nodes |> Map.add site.Id unsigned }
        let enrichment, diagnostics = IntegerElaboration.elaborateSettled graph
        Assert.Empty diagnostics
        Assert.Contains(enrichment.NewNodes, fun node ->
            match node.Kind with
            | SemanticKind.Obligation { Body = ObligationBody.IntegerLiteralRange(actual, lower, upper) } -> actual = value && lower = value && upper = value
            | _ -> false)

    [<Fact>]
    member _.``No platform declaration produces no assumed string layout theorem``() =
        let result = DimensionalCases.check "let left = \"one\"\nlet right = \"two\"\n[<EntryPoint>]\nlet main _ = if left = right then 0 else 1\n"
        DimensionalCases.noErrors result
        Assert.True(result.Graph.StaticStringPool.IsNone)
        Assert.DoesNotContain(IntegerDischarge.ofGraph result.Graph, fun ob -> ob.Id = "layout_user_strings")
