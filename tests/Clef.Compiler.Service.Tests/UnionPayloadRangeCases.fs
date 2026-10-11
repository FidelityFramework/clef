namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

module private UnionPayloadRangeFixture =
    let check source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        result.Graph

    let payload name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with
                                | SemanticKind.DUEliminate(_, _, actual, _) -> actual = name
                                | _ -> false) |> Assert.Single

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with
                                | SemanticKind.Binding(actual, _, _, _) -> actual = name
                                | _ -> false) |> Assert.Single

    /// Every error is CCS8011; the payload stays unobservable and one refusal is located at the
    /// binding that names it (the pass reports once per enclosing binding).
    let refusedAtPayload name bindingName result =
        let errors = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.CheckResult.errors result
        Assert.Equal(Some ValueRange.Unbounded, (payload name result.Graph).ValueRange)
        let named = binding bindingName result.Graph
        Assert.NotEmpty errors
        Assert.All(errors, fun diagnostic -> Assert.Equal("CCS8011", diagnostic.Code))
        Assert.Contains(errors, fun diagnostic -> diagnostic.RelatedNodes = [named.Id] && diagnostic.Range = named.Range)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "UnionPayloadRange")>]
type UnionPayloadRangeCases() =
    [<Fact>]
    member _.``Fresh range facts read the current payload instead of cached projection ranges``() =
        let graph = UnionPayloadRangeFixture.check """
type Number = IntVal of int
[<EntryPoint>]
let main _ = match IntVal 42 with IntVal x -> x
"""
        let payload = UnionPayloadRangeFixture.payload "IntVal" graph
        let literal = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Literal(NativeLiteral.Int(42L, _)) -> true | _ -> false) |> Assert.Single
        let kind = match literal.Kind with SemanticKind.Literal(NativeLiteral.Int(_, kind)) -> kind | _ -> failwith "literal"
        let changed = { literal with Kind = SemanticKind.Literal(NativeLiteral.Int(300L, kind)) }
        let current = { graph with Nodes = graph.Nodes.Add(literal.Id, changed) }
        let facts = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.sourceFacts current
        Assert.Equal(ValueRange.Bounded(300I, 300I), facts[payload.Id])
        Assert.Equal(Some(ValueRange.Bounded(42I, 42I)), graph.Nodes[payload.Id].ValueRange)

    [<Fact>]
    member _.``An integer union payload retains its value rather than its tag``() =
        let graph = UnionPayloadRangeFixture.check """
type Number = IntVal of int | FloatVal of float
let extract n = match n with IntVal x -> x | FloatVal _ -> 0
[<EntryPoint>]
let main _ = extract (IntVal 42)
"""
        Assert.Equal(Some(ValueRange.Bounded(42I, 42I)), (UnionPayloadRangeFixture.payload "IntVal" graph).ValueRange)

    [<Fact>]
    member _.``All actual callers contribute but another union case does not``() =
        let graph = UnionPayloadRangeFixture.check """
type Number = IntVal of int | Other of int
let extract n = match n with IntVal x -> x | Other _ -> 0
[<EntryPoint>]
let main _ = extract (IntVal 7) + extract (IntVal 300) + extract (Other 9000)
"""
        Assert.Equal(Some(ValueRange.Bounded(7I, 300I)), (UnionPayloadRangeFixture.payload "IntVal" graph).ValueRange)

    [<Fact>]
    member _.``A mutable union includes every assignment``() =
        let graph = UnionPayloadRangeFixture.check """
type Number = IntVal of int | Other
[<EntryPoint>]
let main _ =
    let mutable selected = IntVal 7
    selected <- IntVal 300
    match selected with IntVal x -> x | Other -> 0
"""
        Assert.Equal(Some(ValueRange.Bounded(7I, 300I)), (UnionPayloadRangeFixture.payload "IntVal" graph).ValueRange)

    [<Fact>]
    member _.``An opaque union alternative prevents narrowing beside a known constructor``() =
        let result = DimensionalCases.check """
type Number = IntVal of int | Other
let extract (flag: bool) (input: Number) =
    let selected = if flag then IntVal 7 else input
    match selected with IntVal x -> x | Other -> 0
[<EntryPoint>]
let main _ = ignore extract; 0
"""
        // `extract` is never invoked: its body is an unreachable computation and `input` a missing
        // observation, two states that stay distinct (width-inference.md:78). The opaque alternative
        // keeps the payload unobservable, and CCS8011 attaches only where a reachable integer is
        // committed (width-inference.md:80), so the inactive body refuses nothing. The active twin
        // carries the refusal.
        Assert.Equal(Some ValueRange.Unbounded, (UnionPayloadRangeFixture.payload "IntVal" result.Graph).ValueRange)
        DimensionalCases.noErrors result

    [<Fact>]
    member _.``An invoked opaque union alternative refuses the committed payload``() =
        // Active twin: `main` supplies an alternative whose payload the pass cannot observe. The
        // payload stays unobservable and CCS8011 attaches at its commitment (width-inference.md:80).
        let result = DimensionalCases.check """
type Number = IntVal of int | Other
let extract (flag: bool) (input: Number) =
    let selected = if flag then IntVal 7 else input
    match selected with IntVal x -> x | Other -> 0
[<EntryPoint>]
let main argv = extract (argv.Length > 0) (IntVal argv.Length)
"""
        UnionPayloadRangeFixture.refusedAtPayload "IntVal" "x" result

    [<Fact>]
    member _.``Tuple fields inside a union retain distinct ranges``() =
        let graph = UnionPayloadRangeFixture.check """
type Pair = Pair of int * int
let extract n = match n with Pair (first, second) -> first + second
[<EntryPoint>]
let main _ = extract (Pair (7, 300))
"""
        Assert.Equal(Some(ValueRange.Bounded(7I, 7I)), (UnionPayloadRangeFixture.binding "first" graph).ValueRange)
        Assert.Equal(Some(ValueRange.Bounded(300I, 300I)), (UnionPayloadRangeFixture.binding "second" graph).ValueRange)

    [<Fact>]
    member _.``Nested union payload projection preserves dimensional type``() =
        let graph = UnionPayloadRangeFixture.check """
type Distance = Metres of int<m>
type Wrapped = Wrapped of Distance
let extract n = match n with Wrapped (Metres x) -> x
[<EntryPoint>]
let main _ = ignore (extract (Wrapped (Metres 42<m>))); 0
"""
        let payload = UnionPayloadRangeFixture.payload "Metres" graph
        Assert.Equal(Some(ValueRange.Bounded(42I, 42I)), payload.ValueRange)
        Assert.Contains("<m>", formatType payload.Type)

    [<Fact>]
    member _.``Known function results and branch alternatives retain payload bounds``() =
        let graph = UnionPayloadRangeFixture.check """
type Number = IntVal of int | Other
let make flag = if flag then IntVal 7 else IntVal 300
let extract n = match n with IntVal x -> x | Other -> 0
[<EntryPoint>]
let main _ = extract (make true)
"""
        Assert.Equal(Some(ValueRange.Bounded(7I, 300I)), (UnionPayloadRangeFixture.payload "IntVal" graph).ValueRange)

    [<Fact>]
    member _.``Union projection composes after a tuple selection``() =
        let graph = UnionPayloadRangeFixture.check """
type Number = IntVal of int
let extract pair = let (_, value) = pair in match value with IntVal x -> x
[<EntryPoint>]
let main _ = extract (9000, IntVal 42)
"""
        Assert.Equal(Some(ValueRange.Bounded(42I, 42I)), (UnionPayloadRangeFixture.payload "IntVal" graph).ValueRange)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Opaque producer and recursive aggregate alternatives remain conservative`` recursive =
        let producer =
            if recursive then "let rec make flag = if flag then IntVal 7 else make flag\nlet extract flag = match make flag with IntVal x -> x\n"
            else "let extract (flag: bool) (make: unit -> Number) =\n    let selected = if flag then IntVal 7 else make ()\n    match selected with IntVal x -> x\n"
        let result = DimensionalCases.check ("type Number = IntVal of int\n" + producer + "[<EntryPoint>]\nlet main _ = ignore extract; 0\n")
        // Inactive body: the opaque or recursive alternative keeps the payload unobservable, and no
        // reachable integer is committed, so there is no refusal (width-inference.md:78, :80).
        Assert.Equal(Some ValueRange.Unbounded, (UnionPayloadRangeFixture.payload "IntVal" result.Graph).ValueRange)
        DimensionalCases.noErrors result

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Invoked opaque producer and recursive alternatives refuse the committed payload`` recursive =
        // Active twins of the conservative alternatives: the payload stays unobservable and the
        // refusal sits at its commitment (width-inference.md:80).
        let program =
            if recursive then
                "let rec make flag = if flag then IntVal 7 else make flag\nlet extract flag = match make flag with IntVal x -> x\n" +
                "[<EntryPoint>]\nlet main _ = extract true\n"
            else
                "let extract (flag: bool) (make: unit -> Number) =\n    let selected = if flag then IntVal 7 else make ()\n    match selected with IntVal x -> x\n" +
                "[<EntryPoint>]\nlet main argv = extract (argv.Length > 0) (fun () -> IntVal argv.Length)\n"
        UnionPayloadRangeFixture.refusedAtPayload "IntVal" "x" (DimensionalCases.check ("type Number = IntVal of int\n" + program))

module private RecordPayloadRangeFixture =
    let declarations = "type Number = IntVal of int | Other of int\ntype Holder = { Payload: Number; Marker: int }\n"
    let extract = "let extract (holder: Holder) = match holder.Payload with IntVal value -> value | Other _ -> 0\n"
    let opaqueExtract =
        "let extract (flag: bool) (input: Holder) =\n" +
        "    let holder = if flag then { Payload = IntVal 7; Marker = 0 } else input\n" +
        "    match holder.Payload with IntVal value -> value | Other _ -> 0\n"
    let direct = declarations + extract + "[<EntryPoint>]\nlet main _ = extract { Payload = IntVal 42; Marker = 0 }\n"

    let check source = UnionPayloadRangeFixture.check source
    let payload graph = UnionPayloadRangeFixture.payload "IntVal" graph
    let factsAfterDemand (before: SemanticGraph) (mutated: SemanticGraph) payloadId =
        match Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.tryRead mutated with
        | Result.Error failures ->
            Assert.NotEmpty failures
            let withdrawn, diagnostics = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.run None mutated
            // Error Handling (CCS8415): "The exclusion SHALL be withdrawn when its
            // supporting activation, use, capture or ownership facts change".
            // Withdraw stale ranges while preserving every source field and incidence.
            Assert.Equal(mutated.Nodes.Count, withdrawn.Nodes.Count)
            for KeyValue(id, node) in mutated.Nodes do
                let current = withdrawn.Nodes[id]
                Assert.True(System.Object.Equals(node.Id, current.Id), "Id changed during range withdrawal")
                Assert.True(System.Object.Equals(node.Kind, current.Kind), "Kind changed during range withdrawal")
                Assert.True(System.Object.Equals(node.Range, current.Range), "Range changed during range withdrawal")
                Assert.True(System.Object.Equals(node.Type, current.Type), "Type changed during range withdrawal")
                Assert.True(System.Object.Equals(node.SRTPResolution, current.SRTPResolution), "SRTPResolution changed during range withdrawal")
                Assert.True(System.Object.Equals(node.ArenaAffinity, current.ArenaAffinity), "ArenaAffinity changed during range withdrawal")
                Assert.True(System.Object.Equals(node.LayoutHint, current.LayoutHint), "LayoutHint changed during range withdrawal")
                Assert.True(System.Object.Equals(node.Children, current.Children), "Children changed during range withdrawal")
                Assert.True(System.Object.Equals(node.Parent, current.Parent), "Parent changed during range withdrawal")
                Assert.True(System.Object.Equals(node.Metadata, current.Metadata), "Metadata changed during range withdrawal")
                Assert.True(System.Object.Equals(node.IsReachable, current.IsReachable), "IsReachable changed during range withdrawal")
                Assert.True(System.Object.Equals(node.EmissionStrategy, current.EmissionStrategy), "EmissionStrategy changed during range withdrawal")
                Assert.True(current.ValueRange.IsNone)
            Assert.Equal<Hyperedge list>(mutated.Edges, withdrawn.Edges)
            Assert.True(mutated.DeclarationRoots = withdrawn.DeclarationRoots)
            Assert.Same(mutated.Types, withdrawn.Types)
            Assert.Same(mutated.Modules, withdrawn.Modules)
            Assert.Empty(withdrawn.FieldRanges.Value)
            Assert.Empty(withdrawn.ElementRanges.Value)
            Assert.Empty(withdrawn.Escaping.Value)
            Assert.Empty(Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.sourceFacts withdrawn)
            Assert.Equal<Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.Diagnostic list>(
                Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.diagnostics mutated failures, diagnostics)
            Assert.Empty(Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.sourceFacts mutated)
        | Result.Ok _ -> ()
        let current = Clef.Compiler.Nanopass.OrdinaryDemand.normalize mutated
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.tryRead current |> Result.isOk)
        Assert.Equal<ValueRange option>(before.Nodes[payloadId].ValueRange, mutated.Nodes[payloadId].ValueRange)
        Assert.Equal<ValueRange option>(mutated.Nodes[payloadId].ValueRange, current.Nodes[payloadId].ValueRange)
        Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.sourceFacts current

    let refused source =
        let result = DimensionalCases.check source
        let errors = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.CheckResult.errors result
        Assert.NotEmpty errors
        Assert.All(errors, fun diagnostic ->
            Assert.Equal("CCS8011", diagnostic.Code)
            Assert.NotEmpty diagnostic.RelatedNodes
            Assert.Contains(diagnostic.RelatedNodes, fun id -> result.Graph.Nodes[id].Range = diagnostic.Range))
        Assert.Equal(Some ValueRange.Unbounded, (payload result.Graph).ValueRange)
        result.Graph

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "UnionPayloadRange")>]
type RecordPayloadRangeCases() =
    [<Theory>]
    [<InlineData("direct")>]
    [<InlineData("alias")>]
    [<InlineData("copy")>]
    [<InlineData("returned")>]
    member _.``Immutable record field paths retain the actual union payload`` path =
        let prefix, body =
            match path with
            | "direct" -> "", "extract { Payload = IntVal 42; Marker = 0 }"
            | "alias" -> "", "let original = { Payload = IntVal 42; Marker = 0 } in let alias = original in extract alias"
            | "copy" -> "", "let original = { Payload = IntVal 42; Marker = 0 } in extract { original with Marker = 1 }"
            | "returned" -> "let make value = { Payload = IntVal value; Marker = 0 }\n", "extract (make 42)"
            | _ -> failwith "Unknown record field path"
        let graph =
            RecordPayloadRangeFixture.check
                (RecordPayloadRangeFixture.declarations + prefix + RecordPayloadRangeFixture.extract +
                 "[<EntryPoint>]\nlet main _ = " + body + "\n")
        Assert.Equal(Some(ValueRange.Bounded(42I, 42I)), (RecordPayloadRangeFixture.payload graph).ValueRange)

    [<Fact>]
    member _.``Only actual supplied record occurrences contribute to the payload range``() =
        let graph =
            RecordPayloadRangeFixture.check
                (RecordPayloadRangeFixture.declarations + RecordPayloadRangeFixture.extract +
                 "let marker (holder: Holder) = holder.Marker\n[<EntryPoint>]\nlet main _ =\n" +
                 "    marker { Payload = IntVal 9000; Marker = 1 } +\n" +
                 "    extract { Payload = IntVal 7; Marker = 0 } + extract { Payload = IntVal 300; Marker = 0 }\n")
        Assert.Contains(graph.Nodes.Values, fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Literal(NativeLiteral.Int(9000L, _)) -> true
            | _ -> false)
        Assert.Equal(Some(ValueRange.Bounded(7I, 300I)), (RecordPayloadRangeFixture.payload graph).ValueRange)

    [<Fact>]
    member _.``Record projection reads fresh payload values without cached scalar field ranges``() =
        let graph = RecordPayloadRangeFixture.check RecordPayloadRangeFixture.direct
        let payload = RecordPayloadRangeFixture.payload graph
        let literal =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                node.IsReachable &&
                match node.Kind with
                | SemanticKind.Literal(NativeLiteral.Int(42L, _)) -> true
                | _ -> false)
            |> Assert.Single
        let changed =
            match literal.Kind with
            | SemanticKind.Literal(NativeLiteral.Int(_, kind)) -> { literal with Kind = SemanticKind.Literal(NativeLiteral.Int(300L, kind)) }
            | _ -> failwith "Expected literal"
        let current = { graph with Nodes = graph.Nodes.Add(literal.Id, changed) }
        Assert.Equal(ValueRange.Bounded(300I, 300I), (RecordPayloadRangeFixture.factsAfterDemand graph current payload.Id)[payload.Id])
        Assert.Equal(Some(ValueRange.Bounded(42I, 42I)), graph.Nodes[payload.Id].ValueRange)

    [<Fact>]
    member _.``A different union tag under the exact record field contributes an empty range``() =
        let graph = RecordPayloadRangeFixture.check RecordPayloadRangeFixture.direct
        let payload = RecordPayloadRangeFixture.payload graph
        let construction =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                node.IsReachable &&
                match node.Kind with
                | SemanticKind.UnionCase("IntVal", _, _) | SemanticKind.DUConstruct("IntVal", _, _, _) -> true
                | _ -> false)
            |> Assert.Single
        let changed =
            match construction.Kind with
            | SemanticKind.UnionCase(_, tag, value) -> { construction with Kind = SemanticKind.UnionCase("Other", tag + 1, value) }
            | SemanticKind.DUConstruct(_, tag, value, form) -> { construction with Kind = SemanticKind.DUConstruct("Other", tag + 1, value, form) }
            | _ -> failwith "Expected union construction"
        let current = { graph with Nodes = graph.Nodes.Add(construction.Id, changed) }
        Assert.Equal(ValueRange.Empty, (RecordPayloadRangeFixture.factsAfterDemand graph current payload.Id)[payload.Id])
        Assert.Equal(Some(ValueRange.Bounded(42I, 42I)), graph.Nodes[payload.Id].ValueRange)

    [<Theory>]
    [<InlineData("missing-mutability-authority")>]
    [<InlineData("mutable-field")>]
    [<InlineData("missing-field-incidence")>]
    [<InlineData("duplicate-record-incidence")>]
    [<InlineData("contradictory-record-incidence")>]
    [<InlineData("duplicate-field-read-incidence")>]
    [<InlineData("contradictory-field-read-incidence")>]
    member _.``Incomplete immutable record authority retracts an old payload range`` defect =
        let graph = RecordPayloadRangeFixture.check RecordPayloadRangeFixture.direct
        let payload = RecordPayloadRangeFixture.payload graph
        let construction =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                node.IsReachable &&
                match node.Kind with SemanticKind.RecordExpr _ -> true | _ -> false)
            |> Assert.Single
        let declaration =
            match Clef.Compiler.NativeTypedTree.UnionFind.applySubst construction.Type with
            | NativeType.TApp(constructor, _) ->
                Clef.Compiler.PSGSaturation.SemanticGraph.RecordInstances.tryDefinition
                    (NominalTypeIdentity.ofConstructor constructor) graph
                |> Option.defaultWith (fun () -> failwith "Missing exact record declaration")
            | _ -> failwith "Expected nominal record construction"
        let fieldRead =
            graph.Nodes.Values
            |> Seq.filter (fun node ->
                node.IsReachable &&
                match node.Kind with SemanticKind.FieldGet(_, "Payload") -> true | _ -> false)
            |> Assert.Single
        let replace (node: SemanticNode) = { graph with Nodes = graph.Nodes.Add(node.Id, node) }
        let changedIncidence (node: SemanticNode) role duplicate =
            let edge =
                Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence node
                |> List.filter (fun edge -> edge.Role = role && edge.Ordinal = 0)
                |> Assert.Single
            if duplicate then { graph with Edges = edge :: edge :: graph.Edges }
            else { graph with Edges = { edge with Ordinal = edge.Ordinal + 100 } :: graph.Edges }
        let current =
            match defect with
            | "missing-mutability-authority" -> replace { declaration with Metadata = declaration.Metadata.Remove "TypeDef.MutableFields" }
            | "mutable-field" -> replace { declaration with Metadata = declaration.Metadata.Add("TypeDef.MutableFields", MetadataValue.StringList ["Payload"]) }
            | "missing-field-incidence" -> replace { construction with Children = [] }
            | "duplicate-record-incidence" -> changedIncidence construction EdgeRole.FieldValue true
            | "contradictory-record-incidence" -> changedIncidence construction EdgeRole.FieldValue false
            | "duplicate-field-read-incidence" -> changedIncidence fieldRead EdgeRole.Subject true
            | "contradictory-field-read-incidence" -> changedIncidence fieldRead EdgeRole.Subject false
            | _ -> failwith "Unknown record authority defect"
        Assert.Equal(ValueRange.Unbounded, (RecordPayloadRangeFixture.factsAfterDemand graph current payload.Id)[payload.Id])
        Assert.Equal(Some(ValueRange.Bounded(42I, 42I)), graph.Nodes[payload.Id].ValueRange)

    [<Fact>]
    member _.``Mutable record payload stores need a complete write authority``() =
        RecordPayloadRangeFixture.refused
            ("type Number = IntVal of int | Other of int\ntype Holder = { mutable Payload: Number; Marker: int }\n" +
             RecordPayloadRangeFixture.extract + "[<EntryPoint>]\nlet main _ =\n" +
             "    let holder = { Payload = IntVal 7; Marker = 0 }\n    holder.Payload <- IntVal 300\n    extract holder\n")
        |> ignore

    [<Fact>]
    member _.``An opaque record alternative remains unbounded beside an immutable construction``() =
        // Inactive body: the opaque alternative keeps the payload unobservable and nothing is
        // committed, so there is no refusal (width-inference.md:78, :80); the active twin refuses.
        let graph =
            RecordPayloadRangeFixture.check
                (RecordPayloadRangeFixture.declarations + RecordPayloadRangeFixture.opaqueExtract +
                 "[<EntryPoint>]\nlet main _ = ignore extract; 0\n")
        Assert.Equal(Some ValueRange.Unbounded, (RecordPayloadRangeFixture.payload graph).ValueRange)

    [<Fact>]
    member _.``An invoked opaque record alternative refuses the committed payload``() =
        // Active twin: the supplied alternative's payload is unobservable, so the refusal sits at
        // the payload's commitment (width-inference.md:80).
        UnionPayloadRangeFixture.refusedAtPayload "IntVal" "value"
            (DimensionalCases.check
                (RecordPayloadRangeFixture.declarations + RecordPayloadRangeFixture.opaqueExtract +
                 "[<EntryPoint>]\nlet main argv = extract (argv.Length > 0) { Payload = IntVal argv.Length; Marker = 0 }\n"))

    [<Fact>]
    member _.``A raw field address needs its own immutable borrow authority``() =
        let graph =
            RecordPayloadRangeFixture.refused
                (RecordPayloadRangeFixture.declarations + RecordPayloadRangeFixture.extract +
                 "[<EntryPoint>]\nlet main _ =\n" +
                 "    let holder = { Payload = IntVal 42; Marker = 0 }\n" +
                 "    let _ = eager (&holder.Payload)\n    extract holder\n")
        Assert.Contains(graph.Nodes.Values, fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.AddressOf(target, _) ->
                match graph.Nodes[target].Kind with
                | SemanticKind.FieldGet(_, "Payload") -> true
                | _ -> false
            | _ -> false)
