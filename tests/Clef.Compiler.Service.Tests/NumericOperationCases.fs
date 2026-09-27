namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module OperationPublication = Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication

module NumericOperationFixture =
    let check body = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.authority ("module NumericOperations\n[<EntryPoint>]\nlet main _ =\n" + body)
    let admitted body =
        let result = check body
        DimensionalCases.noErrors result
        let facts = OperationPublication.project result.Graph |> function Ok facts -> facts | Error failures -> failwithf "%A" failures
        result.Graph, facts
    let operation kind (facts: NumericWitnessProjection) = facts.Operations.Values |> Seq.filter (fun operation -> operation.Kind = kind) |> Assert.Single

type NumericOperationCases() =
    [<Fact>]
    member _.``Exact sum capacity remains wider than subsequent modular result`` () =
        let graph, facts = NumericOperationFixture.admitted "    let sum = 255 + 255\n    let reduced = sum % 256\n    reduced\n"
        let addition = NumericOperationFixture.operation NumericOperationKind.Add facts
        let remainder = NumericOperationFixture.operation NumericOperationKind.Remainder facts
        Assert.Equal(Some(ValueRange.bounded 255I 510I), addition.Range)
        match addition.OperationCarrier with
        | Some(SettledSlot.Integer(bits, _)) -> Assert.True(bits >= 9)
        | _ -> failwith "An integer sum must have its source-selected operation carrier."
        Assert.Equal(Some(ValueRange.bounded 0I 255I), graph.Nodes[remainder.Site].ValueRange)
        Assert.True(remainder.ResultAdaptation.IsSome)
        Assert.Contains(remainder.Obligations, fun id ->
            match graph.Nodes[id].Kind with
            | SemanticKind.Obligation { Body = ObligationBody.IntegerDivisorNonzero(lo, hi) } -> lo = 256I && hi = 256I
            | _ -> false)

    [<Fact>]
    member _.``Repeated actual identities retain ordered positions and one canonical adaptation`` () =
        let graph, facts = NumericOperationFixture.admitted "    let result = 255 + 255\n    result\n"
        let operation = NumericOperationFixture.operation NumericOperationKind.Add facts
        let first = operation.Operands.Head.Actual
        let old = graph.Nodes[operation.Site]
        let callee = match old.Kind with SemanticKind.Application(callee,_) -> callee | _ -> failwith "Expected source application."
        let changed = { old with Kind = SemanticKind.Application(callee,[first;first]); Children = [callee;first;first] }
        let edges = graph.Edges |> List.filter (fun edge -> not(edge.Target = old.Id && edge.Class = EdgeClass.Structural))
        let graph = { graph with Nodes = graph.Nodes.Add(old.Id,changed); Edges = edges @ kindEdges changed.Id changed.Kind }
                    |> Clef.Compiler.Nanopass.OrdinaryDemand.normalize
                    |> Clef.Compiler.Nanopass.NumericSettlement.normalize
        let settled = OperationPublication.project graph |> function Ok facts -> facts | Error failures -> failwithf "%A" failures
        let repeated = settled.Operations[old.Id]
        Assert.Equal<NodeId list>([first;first], repeated.Operands |> List.map _.Actual)
        Assert.Equal(repeated.Operands[0].Adaptation,repeated.Operands[1].Adaptation)
        Assert.Single(graph.Codata.Value.Meets[old.Id] |> List.filter (fun meet -> meet.Operand = first)) |> ignore

    [<Theory>]
    [<InlineData("row")>]
    [<InlineData("proof")>]
    [<InlineData("meet")>]
    member _.``Operation publication refuses absent construction proof and adaptation`` defect =
        let graph, facts = NumericOperationFixture.admitted "    let result = 255 + 255\n    result\n"
        let operation = NumericOperationFixture.operation NumericOperationKind.Add facts
        let changed =
            match defect with
            | "row" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.NumericOperation fact when fact.Site = operation.Site -> false | _ -> true) }
            | "proof" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.NumericOperationProof fact when fact.Site = operation.Site -> false | _ -> true) }
            | _ -> let codata = graph.Codata.Value in { graph with Codata = lazy { codata with Meets = codata.Meets.Remove operation.Site } }
        match OperationPublication.project changed with Error _ -> () | Ok _ -> failwith "An incomplete source operation was admitted."

    [<Fact>]
    member _.``Shift definedness is an actual refuted obligation when count exceeds the carrier`` () =
        let result = NumericOperationFixture.check "    let shifted = 0 <<< 64\n    shifted\n"
        match OperationPublication.project result.Graph with Error _ -> () | Ok _ -> failwith "An undefined native shift was admitted."
        Assert.Contains(result.Graph.Nodes.Values, fun node ->
            match node.Kind with
            | SemanticKind.Obligation { Body = ObligationBody.IntegerShiftCount(lo, hi, bits) } -> lo = 64I && hi = 64I && bits <= 64
            | _ -> false)

    [<Fact>]
    member _.``Constant match uses ordinary equality with source carrier proof and explicit selection`` () =
        let graph, facts = NumericOperationFixture.admitted "    let input = 7\n    match input with\n    | 7 -> 1\n    | _ -> 0\n"
        Assert.Contains(facts.Operations.Values, fun operation -> operation.Kind = NumericOperationKind.Equal && not operation.Obligations.IsEmpty)
        Assert.DoesNotContain(graph.Nodes.Values, fun node -> node.IsReachable && (match node.Kind with SemanticKind.CaseElimination(_,arms) -> arms |> List.exists (fun arm -> match arm.Pattern with Pattern.Const _ -> true | _ -> false) | _ -> false))

    [<Theory>]
    [<InlineData("=", "a", "a")>]
    [<InlineData("=", "", "")>]
    [<InlineData("<>", "", "")>]
    [<InlineData("=", "", "a")>]
    [<InlineData("<>", "", "a")>]
    [<InlineData("=", "a", "")>]
    [<InlineData("<>", "a", "")>]
    [<InlineData("<>", "a", "longer")>]
    [<InlineData("=", "a\\000b", "a\\000c")>]
    member _.``String equality is a source length test and guarded byte traversal`` (operator:string,left:string,right:string) =
        let program = $"module TextEquality\nlet compareText first second =\n    let alias = first\n    alias {operator} second\n[<EntryPoint>]\nlet main _ = if compareText \"{left}\" \"{right}\" then 0 else 1\n"
        let result = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.authority program
        DimensionalCases.noErrors result
        let boundary = Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project result.Graph |> function Ok facts -> facts | Error errors -> failwithf "%A" errors
        Assert.Empty boundary.Imports
        Assert.Empty boundary.IntrinsicWrites
        let lengthOnly = left="" || right=""
        Assert.Equal((if lengthOnly then 0 else 2),boundary.ByteViews.Count)
        let constructions = Clef.Compiler.Baker.Recipes.StringComparisonRecipes.constructions result.Graph
        if lengthOnly then
            Assert.Empty constructions
            let construction = Clef.Compiler.Baker.Recipes.StringComparisonRecipes.lengthConstructions result.Graph |> Assert.Single
            Assert.True(Clef.Compiler.Baker.Recipes.StringComparisonRecipes.validLengthStructure result.Graph construction)
        else
            let construction = Assert.Single constructions
            Assert.True(Clef.Compiler.Baker.Recipes.StringComparisonRecipes.validStructure result.Graph construction)
            let decision =
                if not construction.Negated then construction.Decision else
                match result.Graph.Nodes[construction.Decision].Kind with SemanticKind.IfThenElse(same,_,_) -> same | _ -> failwith "Expected source Boolean negation."
            let unequalLengthFalse = match result.Graph.Nodes[decision].Kind with SemanticKind.IfThenElse(_,_,Some no) -> no | _ -> failwith "Missing unequal-length branch."
            let mismatchFalse =
                match result.Graph.Nodes[construction.Stop].Kind with
                | SemanticKind.Sequential (markFalse::_) ->
                    match result.Graph.Nodes[markFalse].Kind with SemanticKind.Set(_,value) -> value | _ -> failwith "Missing mismatch result store."
                | _ -> failwith "Missing mismatch branch."
            Assert.NotEqual(unequalLengthFalse,mismatchFalse)
        let memory = Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication.project result.Graph |> function Ok facts -> facts | Error errors -> failwithf "%A" errors
        Assert.Equal((if lengthOnly then 0 else 2),memory.Operations.Values |> Seq.filter (function MemoryWitnessOperation.ArrayAccess _ -> true | _ -> false) |> Seq.length)

    [<Theory>]
    [<InlineData("read-range")>]
    [<InlineData("view")>]
    [<InlineData("extent")>]
    [<InlineData("construction")>]
    [<InlineData("guard")>]
    member _.``String comparison retracts when a byte or guarded lifetime premise disappears`` defect =
        let graph,_ = NumericOperationFixture.admitted "    if \"a\" = \"a\" then 0 else 1\n"
        let removed (edge:Hyperedge) =
            match defect,edge.Role with
            | "read-range",EdgeRole.StringByteRange _ | "view",EdgeRole.StringByteView _ | "extent",EdgeRole.StringExtent _
            | "construction",EdgeRole.StringComparisonConstruction _ | "guard",EdgeRole.MemoryAccessGuard -> true
            | _ -> false
        let changed = { graph with Edges=graph.Edges |> List.filter (removed >> not) }
        if defect="read-range" || defect="view" || defect="extent" then
            match OperationPublication.project changed with Error _ -> () | Ok _ -> failwith "Numeric carrier survived removed byte evidence."
        match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare changed with
        | Error _ -> ()
        | Ok _ -> failwith "String comparison survived removed source proof correspondence."

    [<Fact>]
    member _.``Captured string comparison does not bypass an unresolved environment lifetime`` () =
        let program = "module CapturedEquality\nlet make expected = fun actual -> expected = actual\n[<EntryPoint>]\nlet main _ =\n    let same = make \"a\\000b\"\n    if same \"a\\000b\" then 0 else 1\n"
        let authority = IntrinsicWriteFixture.authority.Replace("Name = \"octet\"", "Name = \"uint8\"")
        let result = IntrinsicWriteFixture.checkSource authority program
        Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Message.Contains("Captured callable environment requires further settlement: UnknownInputRegion"))

    [<Fact>]
    member _.``Selected strings compare through their actual runtime descriptor extent`` () =
        let program = "module SelectedEquality\nlet compareSelected select =\n    let expected = if select then \"a\\000b\" else \"a\\000c\"\n    expected = \"a\\000b\"\n[<EntryPoint>]\nlet main _ = if compareSelected true then 0 else 1\n"
        let result = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.authority program
        DimensionalCases.noErrors result
        let boundary = Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project result.Graph |> function Ok facts -> facts | Error errors -> failwithf "%A" errors
        Assert.Contains(boundary.ByteViews.Values, fun view -> view.StaticOrigins.IsEmpty)
        Assert.Contains(boundary.StringExtents.Values, fun extent -> extent.StaticOrigins.IsEmpty)
        Assert.Empty boundary.Imports

    [<Theory>]
    [<InlineData("=",true)>]
    [<InlineData("<>",true)>]
    [<InlineData("=",false)>]
    [<InlineData("<>",false)>]
    member _.``One proved empty operand needs only actual descriptor length equality`` (operator:string,emptyFirst:bool) =
        let comparison = if emptyFirst then $"\"\" {operator} expected" else $"expected {operator} \"\""
        let program = $"module EmptySelectedEquality\nlet compareSelected select =\n    let expected = if select then \"\" else \"a\\000b\"\n    {comparison}\n[<EntryPoint>]\nlet main _ = if compareSelected true then 0 else 1\n"
        let result = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.authority program
        DimensionalCases.noErrors result
        let construction = Clef.Compiler.Baker.Recipes.StringComparisonRecipes.lengthConstructions result.Graph |> Assert.Single
        Assert.True(Clef.Compiler.Baker.Recipes.StringComparisonRecipes.validLengthStructure result.Graph construction)
        let boundary = Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission.project result.Graph |> function Ok facts -> facts | Error errors -> failwithf "%A" errors
        Assert.Empty boundary.ByteViews
        Assert.Contains(boundary.StringExtents.Values,fun extent -> extent.StaticOrigins.IsEmpty)
        let changed = { result.Graph with Edges=result.Graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.StringLengthComparison _ -> false | _ -> true) }
        match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare changed with
        | Error _ -> ()
        | Ok _ -> failwith "Missing zero-extent comparison proof was accepted."

type StringExtentCases() =
    [<Theory>]
    [<InlineData("property")>]
    [<InlineData("intrinsic")>]
    [<InlineData("alias")>]
    [<InlineData("curried")>]
    [<InlineData("first-class")>]
    member _.``Ordinary string extents retain the actual descriptor through source callable forms`` form =
        let declarations, invocation =
            match form with
            | "property" -> "let measure (text:string) = text.Length\n", "measure text"
            | "alias" -> "let measure (text:string) =\n    let extent = String.length\n    extent text\n", "measure text"
            | "curried" -> "let measure ignored (text:string) = String.length text\n", "let length = measure 7\n    length text"
            | "first-class" -> "let apply measure text = measure text\n", "apply String.length text"
            | _ -> "let measure (text:string) = String.length text\n", "measure text"
        let program = "module OrdinaryExtent\nlet select choose = if choose then \"a\\000b\" else \"longer\"\n"+declarations+"[<EntryPoint>]\nlet main _ =\n    let text = select true\n    "+invocation+"\n"
        let result = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.authority program
        DimensionalCases.noErrors result
        let memory = Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication.project result.Graph |> function Ok facts -> facts | Error errors -> failwithf "%A" errors
        let extents = memory.Operations.Values |> Seq.choose (function MemoryWitnessOperation.BufferExtent extent -> Some extent | _ -> None) |> Seq.toList
        Assert.NotEmpty extents
        Assert.Contains(extents,fun extent -> extent.Extent.StaticOrigins.IsEmpty)
        for extent in extents do
            Assert.Equal(extent.Source,extent.Extent.Source)
            Assert.True(extent.Participants.Contains extent.Source)
        if form = "first-class" then
            let generated = extents |> List.filter (fun extent ->
                result.Graph.Nodes[extent.Site].Metadata.TryFind ElaborationMetadata.For = Some(MetadataValue.String "String.length"))
            let extent = Assert.Single generated
            match result.Graph.Nodes[extent.Site].Kind with
            | SemanticKind.FieldGet(source, "Length") -> Assert.Equal(extent.Source, source)
            | _ -> failwith "The first-class intrinsic must use the ordinary source descriptor observation."
            let callables = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.tryCallable result.Graph |> Result.defaultWith failwith
            Assert.Contains(callables.Declarations.Values, fun declaration -> declaration.Result = extent.Site)
        if form = "curried" then
            let codata = result.Graph.Codata.Value
            let completed = Assert.Single codata.Curry.SaturatedCalls
            let callables = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.tryCallable result.Graph |> Result.defaultWith failwith
            let proof = callables.Calls[completed.Key]
            Assert.Equal<NodeId list>(completed.Value.AllArgNodes, proof.Arguments)
            Assert.Equal(2, proof.Parameters.Length)
            let partial = Assert.Single codata.Curry.PartialApplications
            Assert.Contains(partial.Key, proof.Participants)
            let curry = { codata.Curry with PartialApplications = Map.empty }
            let damaged = { result.Graph with Codata = lazy { codata with Curry = curry } }
            match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare damaged with
            | Error _ -> ()
            | Ok _ -> failwith "Completed call survived the loss of its saved-argument owner relation."
            let curry = { codata.Curry with SaturatedCalls = Map.empty }
            let damaged = { result.Graph with Codata = lazy { codata with Curry = curry } }
            match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare damaged with
            | Error _ -> ()
            | Ok _ -> failwith "Completed call survived the loss of its completion owner relation."
        let changed = { result.Graph with Edges=result.Graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.StringExtent _ -> false | _ -> true) }
        match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare changed with
        | Error _ -> ()
        | Ok _ -> failwith "String length survived missing source descriptor evidence."
