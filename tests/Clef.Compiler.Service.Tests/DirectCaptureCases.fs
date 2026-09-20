namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeService
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

module private DirectCapture =
    let check source =
        match parseAndCheck ("module DirectCapture\n" + source) "direct-capture.clef" with
        | Success result ->
            DimensionalCases.noErrors result
            Assert.DoesNotContain(result.Graph.Nodes.Values, fun node ->
                match node.Kind with SemanticKind.Error _ -> true | _ -> false)
            result
        | CheckFailure result -> failwithf "Check failed: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Parse failed: %A" errors

    let binding name (result: CheckResult) =
        result.Graph.Nodes.Values |> Seq.find (fun node ->
            node.IsReachable && match node.Kind with
                                | SemanticKind.Binding (actual, _, _, _) -> actual = name || actual.EndsWith("." + name)
                                | _ -> false)

    let lambda name result =
        let binding = binding name result
        result.Graph.Nodes[binding.Children.Head]

    let shape node =
        match node.Kind with
        | SemanticKind.Lambda (parameters, body, captures, _, _) -> parameters, body, captures
        | other -> failwithf "Expected Lambda, got %A" other

    let descendants (result: CheckResult) root =
        let rec visit seen id =
            if Set.contains id seen then seen else
            result.Graph.Nodes[id].Children |> List.fold visit (Set.add id seen)
        visit Set.empty root

    let lifted name result =
        let node = lambda name result
        let parameters, body, captures = shape node
        Assert.Empty captures
        Assert.Equal(Some (MetadataValue.String "DirectCapture"), node.Metadata.TryFind ElaborationMetadata.For)
        let expectedChildren = (parameters |> List.map (fun (_, _, id) -> id)) @ [body]
        Assert.Equal<NodeId list>(expectedChildren, node.Children)
        node, parameters, body

    let calls name (result: CheckResult) =
        let definition = (binding name result).Id
        let rec resolves id =
            match result.Graph.Nodes[id].Kind with
            | SemanticKind.VarRef (_, Some target) -> target = definition
            | SemanticKind.TypeAnnotation (inner, _) -> resolves inner
            | _ -> false
        result.Graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Application (callee, args) when node.IsReachable && resolves callee -> Some (node, args)
            | _ -> None) |> Seq.toList

    let referenceTo expected (result: CheckResult) id =
        match result.Graph.Nodes[id].Kind with
        | SemanticKind.VarRef (_, Some target) -> Assert.Equal(expected, target)
        | other -> failwithf "Expected a reference to %A, got %A" expected other

    let unchanged name result =
        let node = lambda name result
        let _, _, captures = shape node
        Assert.NotEmpty captures
        Assert.NotEqual(Some (MetadataValue.String "DirectCapture"), node.Metadata.TryFind ElaborationMetadata.For)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "DirectCaptures")>]
type DirectCaptureTests() =
    [<Fact>]
    member _.``Capture origins follow nested formal chains by identity and ignore shadow names and unrelated enrichment``() =
        let builder = Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder.NodeBuilder()
        let range: SourceRange = { File = "capture-origin.clef"; Start = { Line = 1; Column = 0 }; End = { Line = 1; Column = 20 } }
        let create kind ty = builder.Create(kind, ty, range)
        let original = create (SemanticKind.Binding("value", false, false, None)) Types.boolType
        let shadow = create (SemanticKind.Binding("value", false, false, None)) Types.boolType
        let first = create (SemanticKind.PatternBinding "value") Types.boolType
        let second = create (SemanticKind.PatternBinding "value") Types.boolType
        let ordinary = create (SemanticKind.PatternBinding "value") Types.boolType
        let body = create (SemanticKind.Literal (NativeLiteral.Bool true)) Types.boolType
        let lambda = create (SemanticKind.Lambda ([], body.Id, [], Some "owner", LambdaContext.RegularClosure)) (NativeType.TFun (Types.unitType, Types.boolType))
        let origin source formal: Hyperedge =
            { Sources = [lambda.Id; source]; Target = formal; Class = EdgeClass.Provenance; Role = EdgeRole.CaptureOrigin; Ordinal = 0 }
        let other = { origin shadow.Id second.Id with Role = EdgeRole.EnrichedWith }
        let graph = { builder.Build [] with Edges = [origin original.Id first.Id; origin first.Id second.Id; other] }
        let find = Clef.Compiler.PSGSaturation.SemanticGraph.DirectCaptures.sourceDefinition
        Assert.Equal(original.Id, find graph second.Id)
        Assert.Equal(original.Id, find graph first.Id)
        Assert.Equal(shadow.Id, find graph shadow.Id)
        Assert.Equal(ordinary.Id, find graph ordinary.Id)
        let cyclic = { graph with Edges = [origin second.Id first.Id; origin first.Id second.Id] }
        Assert.Equal(second.Id, find cyclic second.Id)
        let ambiguous = { graph with Edges = origin shadow.Id first.Id :: graph.Edges }
        Assert.Equal(second.Id, find ambiguous second.Id)
        let missing = { graph with Edges = [origin (NodeId.fresh()) second.Id] }
        Assert.Equal(second.Id, find missing second.Id)

    [<Fact>]
    member _.``Direct capture fold replaces incidence without erasing independent resident relations or mutating input``() =
        let builder = Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder.NodeBuilder()
        let range: SourceRange = { File = "capture-graph.clef"; Start = { Line = 1; Column = 0 }; End = { Line = 1; Column = 20 } }
        let create kind ty = builder.Create(kind, ty, range)
        let yes = create (SemanticKind.Literal (NativeLiteral.Bool true)) Types.boolType
        let source = builder.Create(SemanticKind.Binding("flag", false, false, None), Types.boolType, range, children = [yes.Id])
        let parameter = create (SemanticKind.PatternBinding "_") Types.unitType
        let read = create (SemanticKind.VarRef ("flag", Some source.Id)) Types.boolType
        let capture: CaptureInfo = { Name = "flag"; Type = Types.boolType; IsMutable = false; SourceNodeId = Some source.Id }
        let fnType = NativeType.TFun (Types.unitType, Types.boolType)
        let lambda = create (SemanticKind.Lambda (["_", Types.unitType, parameter.Id], read.Id, [capture], Some "owner", LambdaContext.RegularClosure)) fnType
        let binding = builder.Create(SemanticKind.Binding("work", false, false, None), fnType, range, children = [lambda.Id])
        let reference = create (SemanticKind.VarRef ("work", Some binding.Id)) fnType
        let unitValue = create (SemanticKind.Literal NativeLiteral.Unit) Types.unitType
        let application = create (SemanticKind.Application(reference.Id, [unitValue.Id])) Types.boolType
        let initial = builder.Build []
        let independent: Hyperedge =
            { Sources = [yes.Id; source.Id]; Target = lambda.Id; Class = EdgeClass.Structural; Role = EdgeRole.Parameter; Ordinal = 17 }
        let relation: Hyperedge =
            { Sources = [source.Id]; Target = read.Id; Class = EdgeClass.Reference; Role = EdgeRole.Resides; Ordinal = 0 }
        let incidence = initial.Nodes.Values |> Seq.collect (fun node -> kindEdges node.Id node.Kind) |> Seq.toList
        let graph = { initial with Edges = independent :: relation :: incidence }
        let opaqueUse = { relation with Sources = [binding.Id]; Target = yes.Id; Role = EdgeRole.Symbol }
        Assert.Empty(Clef.Compiler.PSGSaturation.SemanticGraph.DirectCaptures.plans { graph with Edges = opaqueUse :: graph.Edges })
        let beforeNodes, beforeEdges = graph.Nodes, graph.Edges
        let folded = Clef.Compiler.Nanopass.ClosureElaboration.normalize graph
        Assert.NotSame(graph, folded)
        Assert.Same(beforeNodes, graph.Nodes)
        Assert.Same(beforeEdges, graph.Edges)
        let originalParameters, _, originalCaptures = DirectCapture.shape graph.Nodes[lambda.Id]
        Assert.Single originalParameters |> ignore
        Assert.Equal(Some source.Id, (Assert.Single originalCaptures).SourceNodeId)
        let parameters, _, captures = DirectCapture.shape folded.Nodes[lambda.Id]
        Assert.Equal(2, parameters.Length)
        Assert.Empty captures
        let _, _, formal = parameters.Head
        match folded.Nodes[read.Id].Kind with
        | SemanticKind.VarRef (_, Some target) -> Assert.Equal(formal, target)
        | other -> failwithf "Expected lifted read, got %A" other
        Assert.Contains(folded.Edges, fun edge -> obj.ReferenceEquals(edge, independent))
        Assert.Contains(folded.Edges, fun edge -> obj.ReferenceEquals(edge, relation))
        Assert.DoesNotContain(folded.Edges, fun edge -> edge.Target = read.Id && edge.Role = EdgeRole.Definition && edge.Sources = [source.Id])
        Assert.Contains(folded.Edges, fun edge -> edge.Target = read.Id && edge.Role = EdgeRole.Definition && edge.Sources = [formal])
        let argumentEdges = folded.Edges |> List.filter (fun edge -> edge.Target = application.Id && edge.Role = EdgeRole.Argument)
        Assert.Equal<int list>([0; 1], argumentEdges |> List.map _.Ordinal |> List.sort)
        for edge in folded.Edges do
            Assert.True(folded.Nodes.ContainsKey edge.Target)
            for source in edge.Sources do Assert.True(folded.Nodes.ContainsKey source)

    [<Fact>]
    member _.``Direct immutable capture becomes an ordinary typed leading parameter and argument``() =
        let result = DirectCapture.check """
[<EntryPoint>]
let main _ =
    let offset = 7
    let work value = offset + value
    work 3
"""
        let original = DirectCapture.binding "offset" result
        let lambda, parameters, body = DirectCapture.lifted "work" result
        Assert.Equal(2, parameters.Length)
        let name, ty, parameter = parameters.Head
        Assert.Equal("offset", name)
        Assert.Equal(formatType original.Type, formatType ty)
        let site, args = Assert.Single (DirectCapture.calls "work" result)
        Assert.Equal(2, args.Length)
        DirectCapture.referenceTo original.Id result args.Head
        let bodyNodes = DirectCapture.descendants result body
        let reads = bodyNodes |> Seq.choose (fun id ->
            match result.Graph.Nodes[id].Kind with
            | SemanticKind.VarRef ("offset", Some target) -> Some target
            | _ -> None) |> Seq.toList
        Assert.Equal<NodeId list>([parameter], reads)
        let provenance = result.Graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Provenance && edge.Target = parameter)
        let edge = Assert.Single provenance
        Assert.Equal(EdgeRole.CaptureOrigin, edge.Role)
        Assert.Equal(Set.ofList [lambda.Id; original.Id], Set.ofList edge.Sources)
        Assert.Equal(original.Id, Clef.Compiler.PSGSaturation.SemanticGraph.DirectCaptures.sourceDefinition result.Graph parameter)
        Assert.Equal("direct-capture.clef", result.Graph.Nodes[parameter].Range.File)
        Assert.Equal(site.Range, result.Graph.Nodes[args.Head].Range)
        Assert.Equal(EmissionStrategy.SeparateFunction 0, result.Graph.Nodes[body].EmissionStrategy)
        for ordinal, (_, _, formal) in parameters |> List.indexed do
            Assert.Contains(result.Graph.Edges, fun edge -> edge.Class = EdgeClass.Structural && edge.Role = EdgeRole.Parameter
                                                           && edge.Target = lambda.Id && edge.Ordinal = ordinal && edge.Sources = [formal])
        for ordinal, argument in args |> List.indexed do
            Assert.Contains(result.Graph.Edges, fun edge -> edge.Class = EdgeClass.Structural && edge.Role = EdgeRole.Argument
                                                           && edge.Target = site.Id && edge.Ordinal = ordinal && edge.Sources = [argument])
        let sourceSignature =
            match (DirectCapture.binding "work" result).Metadata.TryFind ClosureMetadata.SourceSignature with
            | Some (MetadataValue.Type ty) -> ty
            | _ -> failwith "Missing source signature"
        Assert.Equal("int -> int", formatType sourceSignature)
        Assert.Same(result.Graph, Clef.Compiler.Nanopass.ClosureElaboration.normalize result.Graph)

    [<Fact>]
    member _.``Recursive direct calls forward the capture formal and preserve explicit operands``() =
        let result = DirectCapture.check """
[<EntryPoint>]
let main _ =
    let answer = 42
    let rec loop value = if value = 0 then answer else loop (value - 1)
    loop 3
"""
        let _, parameters, body = DirectCapture.lifted "loop" result
        let _, _, parameter = parameters.Head
        let original = DirectCapture.binding "answer" result
        let inner = DirectCapture.descendants result body
        let calls = DirectCapture.calls "loop" result
        Assert.Equal(2, calls.Length)
        for site, args in calls do
            Assert.Equal(2, args.Length)
            DirectCapture.referenceTo (if inner.Contains site.Id then parameter else original.Id) result args.Head

    [<Fact>]
    member _.``A returned function keeps its boundary and captures the lifted formal``() =
        let result = DirectCapture.check """
[<EntryPoint>]
let main _ =
    let offset = 7
    let make () = fun value -> offset + value
    make () 3
"""
        let _, parameters, body = DirectCapture.lifted "make" result
        Assert.Equal(2, parameters.Length)
        let _, _, formal = parameters.Head
        let inner = result.Graph.Nodes[body]
        let innerParameters, _, captures = DirectCapture.shape inner
        Assert.Single innerParameters |> ignore
        let capture = Assert.Single captures
        Assert.Equal(Some formal, capture.SourceNodeId)
        Assert.False capture.IsMutable
        let _, args = Assert.Single (DirectCapture.calls "make" result)
        Assert.Equal(2, args.Length)

    [<Fact>]
    member _.``Capture substitution respects shadowed bindings with the same source name``() =
        let result = DirectCapture.check """
[<EntryPoint>]
let main _ =
    let offset = 7
    let work value =
        let first = offset + value
        let offset = 100
        first + offset
    work 3
"""
        let _, parameters, body = DirectCapture.lifted "work" result
        let _, _, formal = parameters.Head
        let inside = DirectCapture.descendants result body
        let local = inside |> Seq.map (fun id -> result.Graph.Nodes[id]) |> Seq.find (fun node ->
            match node.Kind with SemanticKind.Binding ("offset", _, _, _) -> true | _ -> false)
        let targets = inside |> Seq.choose (fun id ->
            match result.Graph.Nodes[id].Kind with SemanticKind.VarRef ("offset", Some target) -> Some target | _ -> None) |> Set.ofSeq
        Assert.Equal(Set.ofList [formal; local.Id], targets)

    [<Fact>]
    member _.``Inverse dimensions survive capture formals and resident application obligations``() =
        let result = DirectCapture.check """
[<Measure>] type s
[<EntryPoint>]
let main _ =
    let rate = 2.0<1/s>
    let work (value: float<1/s>) = rate + value
    let answer = work 3.0<1/s>
    if answer = 5.0<1/s> then 0 else 1
"""
        let _, parameters, _ = DirectCapture.lifted "work" result
        let _, captureType, formal = parameters.Head
        Assert.Equal(formatType (DirectCapture.binding "rate" result).Type, formatType captureType)
        let site, args = Assert.Single (DirectCapture.calls "work" result)
        let applications =
            result.Graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.Obligation { Body = ObligationBody.ApplicationDimensions _ } -> Some node
                | _ -> None)
            |> Seq.toList
        let evidence = result.Graph.Edges |> List.filter (fun edge ->
            (applications |> List.exists (fun obligation -> edge.Target = obligation.Id))
            && List.contains site.Id edge.Sources)
        Assert.NotEmpty evidence
        Assert.True(evidence |> List.exists (fun edge -> args |> List.forall (fun id -> List.contains id edge.Sources)))
        Assert.True(result.Graph.Nodes.ContainsKey formal)

    [<Fact>]
    member _.``Annotated callees and two eager explicit arguments retain source ordering``() =
        let result = DirectCapture.check """
[<EntryPoint>]
let main _ =
    let offset = 7
    let mutable trace = 0
    let emit = fun value -> trace <- trace * 10 + value; value
    let work first second = offset + first + second
    (work: int -> int -> int) (emit 1) (emit 2)
"""
        let _, parameters, _ = DirectCapture.lifted "work" result
        Assert.Equal(3, parameters.Length)
        let _, args = Assert.Single (DirectCapture.calls "work" result)
        Assert.Equal(3, args.Length)
        let explicit = args.Tail |> List.map (fun id ->
            match result.Graph.Nodes[id].Kind with
            | SemanticKind.Application (_, [value]) ->
                match result.Graph.Nodes[value].Kind with
                | SemanticKind.Literal (NativeLiteral.Int (value, _)) -> value
                | other -> failwithf "Expected supplied literal, got %A" other
            | other -> failwithf "Expected source effectful application, got %A" other)
        Assert.Equal<int64 list>([1L; 2L], explicit)

    [<Theory>]
    [<InlineData("let alias = work\n    alias 3")>]
    [<InlineData("let stored = Some work\n    Option.get stored 3")>]
    [<InlineData("let stored = { Apply = work }\n    stored.Apply 3")>]
    [<InlineData("let invoke = fun fn -> fn 3\n    invoke work")>]
    [<InlineData("let escaping = fun value -> work value\n    escaping 3")>]
    member _.``Named value uses are not classified as direct by binding parentage``(useSite: string) =
        let result = DirectCapture.check ("""
type Holder = { Apply: int -> int }
[<EntryPoint>]
let main _ =
    let offset = 7
    let work value = offset + value
    """ + useSite + "\n")
        DirectCapture.unchanged "work" result

    [<Fact>]
    member _.``Returned named functions retain their capture frontier``() =
        let result = DirectCapture.check """
let make offset =
    let work value = offset + value
    work
[<EntryPoint>]
let main _ = make 7 3
"""
        DirectCapture.unchanged "work" result

    [<Fact>]
    member _.``Partial named applications retain the source callable boundary``() =
        let result = DirectCapture.check """
[<EntryPoint>]
let main _ =
    let offset = 7
    let work first second = offset + first + second
    let partial = work 2
    partial 3
"""
        DirectCapture.unchanged "work" result

    [<Fact>]
    member _.``A mixed mutable frontier is left wholly unconverted``() =
        let result = DirectCapture.check """
[<EntryPoint>]
let main _ =
    let offset = 7
    let mutable state = 0
    let work value = state <- state + value; offset + state
    work 3
"""
        DirectCapture.unchanged "work" result
        let _, _, captures = DirectCapture.shape (DirectCapture.lambda "work" result)
        Assert.Contains(captures, fun capture -> capture.IsMutable)
        Assert.Contains(captures, fun capture -> not capture.IsMutable)

    [<Fact>]
    member _.``A source dimension mismatch cannot become successful through direct capture saturation``() =
        let source = """module DirectCapture
[<Measure>] type s
[<Measure>] type m
[<EntryPoint>]
let main _ =
    let rate = 2.0<1/s>
    let work (value: float<1/s>) = rate + value
    let wrong = work 3.0<m>
    0
"""
        match parseAndCheck source "direct-capture-bad.clef" with
        | CheckFailure result ->
            let mismatch = result.Diagnostics |> List.find (fun diagnostic -> diagnostic.Code = "CCS8040")
            Assert.Equal("direct-capture-bad.clef", mismatch.Range.File)
            Assert.Equal(8, mismatch.Range.Start.Line)
            Assert.True(mismatch.Range.Start.Column > 0)
            Assert.Equal(NativeDiagnosticSeverity.Error, mismatch.Severity)
        | other -> failwithf "Expected a located source failure, got %A" other
