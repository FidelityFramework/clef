namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module NumericPublication = Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication
module MemoryPublication = Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication

module private IndexTransportFixture =
    // Enter through source checking, then expose one explicit Baker dispatch.
    // This isolates its numeric contract from sequence/lazy frame construction.
    let graphFor pointerBits (number: string) =
        let authority = IntrinsicWriteFixture.authority.Replace("Name = \"Pointer\"; Bits = 64", $"Name = \"Pointer\"; Bits = {pointerBits}")
        let platform = { IntrinsicWriteFixture.platform with Dimensions = IntrinsicWriteFixture.platform.Dimensions.Add("Pointer",pointerBits) }
        let parse text path =
            match Clef.Compiler.NativeService.parseStringWithDefaults text path with
            | Clef.Compiler.NativeService.ParseSuccess input -> input
            | Clef.Compiler.NativeService.ParseError errors -> failwithf "%A" errors
        let source = $"module IndexTransport\n[<EntryPoint>]\nlet main _ =\n    let selector = {number}\n    if selector = 0 then 7 else 11\n"
        let result = Clef.Compiler.NativeService.checkParsedInputsWithPlatform
                        [parse authority "write-authority.clef";parse source "index-transport.clef"] (Some platform)
        DimensionalCases.noErrors result
        let facts = NumericPublication.project result.Graph |> Result.defaultWith (sprintf "%A" >> failwith)
        let integer = System.Numerics.BigInteger.Parse number
        let operand = facts.Values.Values |> Seq.find (fun carrier -> carrier.Range = ValueRange.point integer) |> _.Site
        let site, yes, no = result.Graph.Nodes.Values |> Seq.pick (fun node ->
            match node.Kind with SemanticKind.IfThenElse(_, yes, Some no) -> Some(node,yes,no) | _ -> None)
        let changed = { site with Kind = SemanticKind.ContinuationDispatch(operand,[0,yes],no); Children = [operand;yes;no] }
        let edges = result.Graph.Edges |> List.filter (fun edge -> not(edge.Target = site.Id && edge.Class = EdgeClass.Structural))
        { result.Graph with Nodes = result.Graph.Nodes.Add(site.Id,changed); Edges = edges @ kindEdges site.Id changed.Kind }
        |> Clef.Compiler.Nanopass.OrdinaryDemand.normalize
        |> Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.run (Some platform)
        |> fst
        |> Clef.Compiler.Nanopass.NumericSettlement.normalize

    let create number =
        let graph = graphFor 64 number
        let facts = NumericPublication.project graph |> Result.defaultWith (sprintf "%A" >> failwith)
        graph, Assert.Single facts.IndexTransports.Values

module private NumericCaptureFixture =
  let check source =
    let authority = IntrinsicWriteFixture.authority.Replace("Name = \"octet\"", "Name = \"uint8\"")
    let result = IntrinsicWriteFixture.checkSource authority source
    DimensionalCases.noErrors result
    result.Graph

  let graph = lazy (check """module NumericCaptureAuthority
let invoke (callback: int -> int) = callback 3
[<EntryPoint>]
let main _ =
    let offset = 7
    let callback = fun value -> value + offset
    let answer = invoke callback
    answer
""")

  let finiteGraph = lazy (check """module NumericCapturedFiniteAuthority
[<EntryPoint>]
let main _ =
    let mutable state = 0
    let bump () = state <- state + 1
    bump ()
    let answer = state
    answer
""")

  let contextSource = """module NumericInvocationAuthority
let double input = input * 2
let triple value = value * 3
[<EntryPoint>]
let main _ =
    let first = double 3
    let second = triple 7
    first + second
"""

  let contextGraph = lazy (check contextSource)

  let binding name (graph: SemanticGraph) =
    graph.Nodes.Values
    |> Seq.filter (fun node ->
      node.IsReachable && match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
    |> Assert.Single

  let domain (graph: SemanticGraph) =
    graph.Edges
    |> List.choose (fun edge -> match edge.Role with EdgeRole.NumericDomain domain -> Some domain | _ -> None)
    |> Assert.Single

  let capture (graph: SemanticGraph) =
    graph.Edges
    |> List.filter (fun edge -> match edge.Role with EdgeRole.EnvironmentCapture _ -> true | _ -> false)
    |> Assert.Single

  let admitted graph =
    NumericPublication.project graph |> Result.defaultWith (sprintf "%A" >> failwith)

  let invocationRefusal (graph: SemanticGraph) =
    match NumericPublication.project graph with
    | Error failures -> Assert.Contains(failures, fun failure ->
        failure.Reason = "NumericPublication: Invocation-context range premises changed or the producer receipt is absent; source range settlement is required.")
    | Ok _ -> failwith "Changed invocation evidence retained its old numeric publication."

  let heldRangeRefusal (graph: SemanticGraph) =
    match NumericPublication.project graph with
    | Error failures -> Assert.Contains(failures, fun failure ->
        failure.Reason = "NumericPublication: Invocation-context range premises changed or the producer's shared facts no longer fit the held integer range.")
    | Ok _ -> failwith "Numeric renewal admitted an integer annotation that does not enclose its current source range."

type NumericPublicationCases() =
    [<Fact>]
    member _.``Numeric publication retains the range owners invocation facts and read support`` () =
        let graph = NumericCaptureFixture.contextGraph.Value
        let facts = graph.RangeContextFacts |> Option.defaultWith (fun () -> failwith "RangeAnalysis did not issue invocation facts.")
        let domain = NumericCaptureFixture.domain graph
        Assert.Equal(Some facts, domain.RangeContextFacts)
        Assert.NotEmpty facts.Invocations
        Assert.NotEmpty facts.Reads
        Assert.Equal(Clef.Compiler.Baker.Ingredients.NumericValues.rangeContextRelations graph, facts.SourceRelations)
        Assert.True(Clef.Compiler.Baker.Ingredients.NumericValues.rangeContextCurrent graph facts)
        let numeric = NumericCaptureFixture.admitted graph
        for name, expected in ["first", 6I; "second", 21I] do
            let binding = NumericCaptureFixture.binding name graph
            let call = binding.Children |> Assert.Single
            let rows = facts.Invocations |> List.filter (fun row -> row.Call = call)
            Assert.NotEmpty rows
            for row in rows do
                Assert.NotEqual(RangeContext.Shared, row.Context)
                Assert.True(facts.Values.ContainsKey(row.Context, row.Body))
                Assert.NotEmpty row.Arguments
            Assert.Equal(ValueRange.point expected, facts.Values[RangeContext.Shared, call])
            Assert.Equal(ValueRange.point expected, numeric.Values[binding.Id].Range)

    [<Theory>]
    [<InlineData("actual")>]
    [<InlineData("literal")>]
    [<InlineData("target")>]
    member _.``Numeric renewal rejects held annotations that exclude current invocation ranges`` defect =
        let graph = NumericCaptureFixture.contextGraph.Value
        NumericCaptureFixture.admitted graph |> ignore
        let first = graph.Nodes[(NumericCaptureFixture.binding "first" graph).Children |> Assert.Single]
        let second = graph.Nodes[(NumericCaptureFixture.binding "second" graph).Children |> Assert.Single]
        let changed =
            match defect with
            | "literal" ->
                match first.Kind with
                | SemanticKind.Application(_, [actual]) ->
                    let node = graph.Nodes[actual]
                    match node.Kind with
                    | SemanticKind.Literal(NativeLiteral.Int(value, kind)) ->
                        { graph with Nodes = graph.Nodes.Add(actual, { node with Kind = SemanticKind.Literal(NativeLiteral.Int(value + 1L, kind)) }) }
                    | _ -> failwith "Expected the checked integer actual."
                | _ -> failwith "Expected the unary source application."
            | _ ->
                match first.Kind, second.Kind with
                | SemanticKind.Application(callee, arguments), SemanticKind.Application(otherCallee, otherArguments) ->
                    let kind, replace =
                        if defect = "actual" then
                            let actual, other = arguments |> Assert.Single, otherArguments |> Assert.Single
                            SemanticKind.Application(callee, [other]), (fun id -> if id = actual then other else id)
                        else
                            SemanticKind.Application(otherCallee, arguments), (fun id -> if id = callee then otherCallee else id)
                    let call = { first with Kind = kind; Children = List.map replace first.Children }
                    let edges = graph.Edges |> List.filter (fun edge -> not(edge.Target = first.Id && edge.Class = EdgeClass.Structural))
                    { graph with Nodes = graph.Nodes.Add(first.Id, call); Edges = edges @ kindEdges first.Id kind }
                | _ -> failwith "Expected two source applications with distinct callees and actuals."
        NumericCaptureFixture.invocationRefusal changed
        let renewed = changed |> Clef.Compiler.Nanopass.OrdinaryDemand.normalize |> Clef.Compiler.Nanopass.NumericSettlement.normalize
        let repeated = Clef.Compiler.Nanopass.NumericSettlement.normalize renewed
        for current in [renewed; repeated] do
            Assert.True((NumericCaptureFixture.domain current).RangeContextFacts.IsSome)
            Assert.Equal(current.RangeContextFacts, (NumericCaptureFixture.domain current).RangeContextFacts)
            Assert.NotEqual(graph.RangeContextFacts, current.RangeContextFacts)
            Assert.Equal(first.ValueRange, current.Nodes[first.Id].ValueRange)
            NumericCaptureFixture.heldRangeRefusal current
        // Only the existing range owner can issue evidence for the changed
        // source. Numeric settlement then consumes that receipt unchanged.
        let restored, _ = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.run repeated.Platform repeated
        let settled = Clef.Compiler.Nanopass.NumericSettlement.normalize restored
        NumericCaptureFixture.admitted settled |> ignore
        Assert.Equal(restored.RangeContextFacts, (NumericCaptureFixture.domain settled).RangeContextFacts)

    [<Theory>]
    [<InlineData("withdrawn")>]
    [<InlineData("replaced")>]
    member _.``Numeric settlement reissues missing evidence while passive publication refuses its loss`` defect =
        let graph = NumericCaptureFixture.contextGraph.Value
        NumericCaptureFixture.admitted graph |> ignore
        let replacement =
            if defect = "withdrawn" then None
            else
                let foreign = NumericCaptureFixture.graph.Value.RangeContextFacts
                Assert.True foreign.IsSome
                Assert.NotEqual(graph.RangeContextFacts, foreign)
                foreign
        let changed = { graph with RangeContextFacts = replacement }
        NumericCaptureFixture.invocationRefusal changed
        // Settlement may request fresh facts from RangeAnalysis for this same
        // graph. Publication itself has no such recovery authority.
        let renewed = Clef.Compiler.Nanopass.NumericSettlement.normalize changed
        let repeated = Clef.Compiler.Nanopass.NumericSettlement.normalize renewed
        for current in [renewed; repeated] do
            NumericCaptureFixture.admitted current |> ignore
            Assert.True(current.RangeContextFacts.IsSome)
            Assert.Equal(current.RangeContextFacts, (NumericCaptureFixture.domain current).RangeContextFacts)
            Assert.True(Clef.Compiler.Baker.Ingredients.NumericValues.rangeContextCurrent current current.RangeContextFacts.Value)
            NumericCaptureFixture.invocationRefusal { current with RangeContextFacts = replacement }

    [<Fact>]
    member _.``Numeric publication preserves higher order occurrence precision and shared formal carriers`` () =
        let graph = NumericCaptureFixture.check """module NumericHigherOrderAuthority
let twice (callback: int -> int) (start: int) : int = callback (callback start)
let double (input: int) : int = input * 2
[<EntryPoint>]
let main _ =
    let first = twice double 3
    let second = twice double 100
    first + second
"""
        let numeric = NumericCaptureFixture.admitted graph
        let first = NumericCaptureFixture.binding "first" graph
        let second = NumericCaptureFixture.binding "second" graph
        Assert.Equal(ValueRange.point 12I, numeric.Values[first.Id].Range)
        Assert.Equal(ValueRange.point 400I, numeric.Values[second.Id].Range)
        let width id =
            match numeric.Values[id].Slot with
            | SettledSlot.Integer(bits, _) -> bits
            | slot -> failwithf "Expected a published integer carrier, got %A." slot
        Assert.True(width first.Id < width second.Id, "Distinct occurrence enclosures must retain their selected carriers.")
        for name, expected in ["start", ValueRange.Bounded(3I, 100I); "input", ValueRange.Bounded(3I, 200I)] do
            let formal = graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && match node.Kind with SemanticKind.PatternBinding actual -> actual = name | _ -> false) |> Assert.Single
            Assert.Equal(expected, numeric.Values[formal.Id].Range)
            Assert.Equal(width first.Id, width formal.Id)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Numeric renewal preserves retained graph citizens after checking another graph`` changeLiteral =
        Clef.Compiler.CheckExecution.synchronized (fun () ->
            let graph = NumericCaptureFixture.check NumericCaptureFixture.contextSource
            NumericCaptureFixture.admitted graph |> ignore
            let first = graph.Nodes[(NumericCaptureFixture.binding "first" graph).Children |> Assert.Single]
            let retained =
                if not changeLiteral then graph
                else
                    match first.Kind with
                    | SemanticKind.Application(_, [actual]) ->
                        let node = graph.Nodes[actual]
                        match node.Kind with
                        | SemanticKind.Literal(NativeLiteral.Int(value, kind)) ->
                            { graph with Nodes = graph.Nodes.Add(actual, { node with Kind = SemanticKind.Literal(NativeLiteral.Int(value + 1L, kind)) }) }
                        | _ -> failwith "Expected the retained graph's literal argument."
                    | _ -> failwith "Expected the retained graph's unary call."
            let citizens = retained.Nodes |> Map.filter (fun _ node ->
                not (Clef.Compiler.Baker.Ingredients.NumericValues.owned node))
            let smaller = NumericCaptureFixture.check """module NumericOtherCheck
[<EntryPoint>]
let main _ = 0
"""
            let maximum (graph: SemanticGraph) = graph.Nodes.Keys |> Seq.map NodeId.value |> Seq.max
            Assert.True(maximum smaller < maximum retained, "The intervening real check must reset allocation below the retained graph's citizens.")
            let renewed = Clef.Compiler.Nanopass.NumericSettlement.normalize retained
            let repeated = Clef.Compiler.Nanopass.NumericSettlement.normalize renewed
            for current in [renewed; repeated] do
                for KeyValue(id, _) in current.Nodes |> Map.filter (fun id _ -> not (retained.Nodes.ContainsKey id)) do
                    Assert.True(NodeId.value id > maximum retained, "A renewal must allocate above its input graph before retiring its old proof nodes.")
                for KeyValue(id, node) in citizens do
                    Assert.True(current.Nodes.ContainsKey id, sprintf "Renewal removed retained citizen %A." id)
                    Assert.Equal(node.Kind, current.Nodes[id].Kind)
                    Assert.Equal(Clef.Compiler.Baker.Ingredients.Boundaries.premise node,
                                 Clef.Compiler.Baker.Ingredients.Boundaries.premise current.Nodes[id])
                if changeLiteral then NumericCaptureFixture.heldRangeRefusal current
                else NumericCaptureFixture.admitted current |> ignore)

    [<Theory>]
    [<InlineData("key")>]
    [<InlineData("node")>]
    [<InlineData("child")>]
    [<InlineData("parent")>]
    [<InlineData("source")>]
    [<InlineData("target")>]
    member _.``Retained graph allocation reserves every structural identity before enrichment`` position =
        Clef.Compiler.CheckExecution.synchronized (fun () ->
            let graph = NumericCaptureFixture.contextGraph.Value
            let semantic = graph.Nodes.Values |> Seq.head
            let maximum = Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.maxNodeId graph
            let high = NodeId(maximum + 1000)
            let changed =
                match position with
                | "key" -> { graph with Nodes = graph.Nodes.Remove(semantic.Id).Add(high, semantic) }
                | "node" -> { graph with Nodes = graph.Nodes.Add(semantic.Id, { semantic with Id = high }) }
                | "child" -> { graph with Nodes = graph.Nodes.Add(semantic.Id, { semantic with Children = high :: semantic.Children }) }
                | "parent" -> { graph with Nodes = graph.Nodes.Add(semantic.Id, { semantic with Parent = Some high }) }
                | "source" | "target" ->
                    let edge = { Class = EdgeClass.Structural; Role = EdgeRole.Attached; Ordinal = 0
                                 Sources = [if position = "source" then high else semantic.Id]
                                 Target = if position = "target" then high else semantic.Id }
                    { graph with Edges = edge :: graph.Edges }
                | _ -> failwith "Unknown structural identity position."
            NodeId.reset ()
            Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment changed (fun () ->
                Assert.True(NodeId.value (NodeId.fresh ()) > NodeId.value high,
                            "Even identities named outside the node map must not be reused.")))

    [<Fact>]
    member _.``Retained graph allocation preserves active high water through a nested real check`` () =
        Clef.Compiler.CheckExecution.synchronized (fun () ->
            let graph = NumericCaptureFixture.check NumericCaptureFixture.contextSource
            Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () ->
                let minted = List.init 4 (fun _ -> NodeId.fresh ())
                let nested = NumericCaptureFixture.check "module NumericNestedCheck\n[<EntryPoint>]\nlet main _ = 0\n"
                let after = NodeId.fresh () |> NodeId.value
                Assert.True(after > (minted |> List.map NodeId.value |> List.max),
                            "A nested reset must preserve identities minted after scope entry.")
                Assert.True(after > Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.maxNodeId nested,
                            "The parent must also preserve identities minted by the nested check."))
            NodeId.reset ()
            Assert.Equal(NodeId 0, NodeId.fresh ()))

    [<Fact>]
    member _.``Boundary enrichment preserves retained graph citizens after another real check`` () =
        Clef.Compiler.CheckExecution.synchronized (fun () ->
            let graph = NumericCaptureFixture.check NumericCaptureFixture.contextSource
            let citizens = graph.Nodes |> Map.filter (fun _ node -> not (Clef.Compiler.Baker.Ingredients.Boundaries.ownedNode node))
            let maximum = Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.maxNodeId graph
            NumericCaptureFixture.check "module BoundaryOtherCheck\n[<EntryPoint>]\nlet main _ = 0\n" |> ignore
            let renewed = Clef.Compiler.Nanopass.BoundarySettlement.normalize graph
            Assert.True(renewed.Nodes |> Map.exists (fun id _ -> NodeId.value id > maximum), "The other enrichment owner must mint a fresh domain anchor.")
            for KeyValue(id, node) in citizens do
                Assert.True(renewed.Nodes.ContainsKey id)
                Assert.Equal(node.Kind, renewed.Nodes[id].Kind)
                Assert.Equal(Clef.Compiler.Baker.Ingredients.Boundaries.premise node,
                             Clef.Compiler.Baker.Ingredients.Boundaries.premise renewed.Nodes[id]))

    [<Theory>]
    [<InlineData("structural-extra")>]
    [<InlineData("reference-extra")>]
    [<InlineData("environment-removed")>]
    [<InlineData("environment-reordered")>]
    member _.``Numeric publication requires exact ordered invocation source incidence`` (defect: string) =
        let environment = defect.StartsWith "environment"
        let graph = if environment then NumericCaptureFixture.graph.Value else NumericCaptureFixture.contextGraph.Value
        NumericCaptureFixture.admitted graph |> ignore
        let changed =
            if environment then
                let formal = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.EnvironmentFormal) |> Assert.Single
                let others = graph.Edges |> List.filter (fun edge -> not(obj.ReferenceEquals(edge, formal)))
                if defect = "environment-removed" then { graph with Edges = others }
                else
                    // Even a malformed formal targeting a publication citizen
                    // remains source input: first/last matching rows affect
                    // callable admission before numeric publication can run.
                    let owned = graph.Nodes.Values |> Seq.find Clef.Compiler.Baker.Ingredients.NumericValues.owned
                    let conflict = { formal with Target = owned.Id }
                    let first = { graph with Edges = formal :: conflict :: others }
                    let second = { graph with Edges = conflict :: formal :: others }
                    Assert.NotEqual(Clef.Compiler.Baker.Ingredients.NumericValues.rangeContextRelations first,
                                    Clef.Compiler.Baker.Ingredients.NumericValues.rangeContextRelations second)
                    second
            else
                let call = graph.Nodes[(NumericCaptureFixture.binding "first" graph).Children |> Assert.Single]
                let source = kindEdges call.Id call.Kind |> List.head
                let extra = { source with Ordinal = source.Ordinal + 1
                                          Class = if defect = "reference-extra" then EdgeClass.Reference else EdgeClass.Structural }
                // A negative census must notice a new row even where the
                // source shape and every old retained row remain unchanged.
                { graph with Edges = extra :: graph.Edges }
        Assert.Same(graph.Nodes, changed.Nodes)
        NumericCaptureFixture.invocationRefusal changed
        // Renewing may legitimately derive a different enclosure. The stale
        // incidence claim here is the passive reader's exact receipt check;
        // the changed-actual controls separately require renewal containment.
        NumericCaptureFixture.admitted graph |> ignore

    [<Theory>]
    [<InlineData("removed")>]
    [<InlineData("class")>]
    [<InlineData("mutability")>]
    [<InlineData("ordinal")>]
    [<InlineData("sources")>]
    [<InlineData("target")>]
    [<InlineData("duplicate")>]
    member _.``Numeric publication requires exact closure capture incidence`` defect =
        let graph = NumericCaptureFixture.graph.Value
        let projection = NumericCaptureFixture.admitted graph
        let answer = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding("answer", _, _, _) -> true | _ -> false) |> Assert.Single
        Assert.Equal(ValueRange.point 10I, projection.Values[answer.Id].Range)
        let domain = NumericCaptureFixture.domain graph
        Assert.True domain.RequiresCaptureReview
        Assert.False domain.RequiresFiniteCellReview
        Assert.False domain.RequiresSequenceReview
        let capture = NumericCaptureFixture.capture graph
        let replacement =
            match defect with
            | "removed" -> []
            | "class" -> [{ capture with Class = EdgeClass.Reference }]
            | "mutability" -> [{ capture with Role = EdgeRole.EnvironmentCapture true }]
            | "ordinal" -> [{ capture with Ordinal = capture.Ordinal + 1 }]
            | "sources" -> [{ capture with Sources = List.rev capture.Sources }]
            | "target" -> [{ capture with Target = answer.Id }]
            | "duplicate" -> [capture; capture]
            | _ -> failwith "Unknown capture mutation."
        let changed = { graph with Edges = replacement @ (graph.Edges |> List.filter (fun edge -> not (obj.ReferenceEquals(edge, capture)))) }
        Assert.Same(graph.Nodes, changed.Nodes)
        // The passive reader sees the retained answer and must refuse its
        // changed support before any owner has recomputed or normalized it.
        match NumericPublication.project changed with
        | Error failures ->
            Assert.Contains(failures, fun failure ->
                failure.Reason = "NumericPublication: Closure capture relation premises changed; source numeric settlement is required.")
        | Ok _ -> failwith "A changed capture retained its old numeric authority."
        NumericCaptureFixture.admitted graph |> ignore

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Numeric renewal cannot forget wholly withdrawn closure capture evidence`` capturedFiniteCell =
        let graph = if capturedFiniteCell then NumericCaptureFixture.finiteGraph.Value else NumericCaptureFixture.graph.Value
        let originalDomain = NumericCaptureFixture.domain graph
        Assert.True originalDomain.RequiresCaptureReview
        Assert.Equal(capturedFiniteCell, originalDomain.RequiresFiniteCellReview)
        NumericCaptureFixture.admitted (Clef.Compiler.Nanopass.NumericSettlement.normalize graph) |> ignore
        let capture = NumericCaptureFixture.capture graph
        let changed = { graph with Edges = graph.Edges |> List.filter (fun edge -> not (obj.ReferenceEquals(edge, capture))) }
        let renewed = Clef.Compiler.Nanopass.NumericSettlement.normalize changed
        let repeated = Clef.Compiler.Nanopass.NumericSettlement.normalize renewed
        for current in [renewed; repeated] do
            let domain = NumericCaptureFixture.domain current
            Assert.True domain.RequiresCaptureReview
            Assert.Equal(capturedFiniteCell, domain.RequiresFiniteCellReview)
            Assert.Empty domain.CaptureRelations
            for KeyValue(id, node) in graph.Nodes do
                if not (Clef.Compiler.Baker.Ingredients.NumericValues.owned node) then
                    Assert.Equal(node.ValueRange, current.Nodes[id].ValueRange)
            match NumericPublication.project current with
            | Error failures ->
                let reason =
                    if capturedFiniteCell then "NumericPublication: Finite-cell and closure capture relation premises changed or current source facts no longer fit the held integer range."
                    else "NumericPublication: Closure capture relation premises changed or current source facts no longer fit the held integer range."
                Assert.Contains(failures, fun failure ->
                    failure.Reason = reason)
            | Ok _ -> failwith "Numeric renewal blessed a held range after capture withdrawal."
        let restored = { repeated with Edges = capture :: repeated.Edges }
        // Settlement requests current owner facts for the restored census;
        // unchanged annotations again enclose those restored source ranges.
        NumericCaptureFixture.admitted (Clef.Compiler.Nanopass.NumericSettlement.normalize restored) |> ignore
        NumericCaptureFixture.admitted graph |> ignore

    [<Fact>]
    member _.``Index transport refuses a held integer outside the selected pointer capacity`` () =
        let graph = IndexTransportFixture.graphFor 32 "4294967296"
        match NumericPublication.project graph with
        | Error failures -> Assert.Contains(failures,fun failure -> failure.Reason.Contains("not representable") && failure.Occurrence.IsSome)
        | Ok _ -> failwith "A 33-bit selector range was truncated into a 32-bit index."

    [<Theory>]
    [<InlineData("-7", false)>]
    [<InlineData("255", true)>]
    member _.``Dispatch index transport retains source sign and actual coverage proof`` number unsigned =
        let graph, transport = IndexTransportFixture.create number
        let numeric = NumericCaptureFixture.admitted graph
        Assert.Equal(ValueRange.Bounded(7I, 11I), numeric.Values[transport.Site].Range)
        Assert.Equal(unsigned, transport.Unsigned)
        Assert.Equal(64, transport.PointerBits)
        Assert.Contains(transport.PointerDeclaration, transport.Participants)
        let capacity = if unsigned then ValueRange.unsignedOf 64 else ValueRange.twosComplement 64
        Assert.Equal(capacity, transport.Capacity)
        match graph.Nodes[transport.Obligation].Kind with
        | SemanticKind.Obligation info ->
            Assert.Equal("numeric-index-coverage", info.Kind)
            Assert.Equal(Some info.Body, Clef.Compiler.Baker.Ingredients.NumericValues.indexBody transport)
        | _ -> failwith "The index transport lost its source proof citizen."

    [<Theory>]
    [<InlineData("sign")>]
    [<InlineData("pointer-width")>]
    [<InlineData("operand")>]
    [<InlineData("proof")>]
    [<InlineData("rewrite")>]
    member _.``Index publication refuses matching changed rows and missing proof premises`` defect =
        let graph, transport = IndexTransportFixture.create "255"
        let changed =
            match defect with
            | "sign" -> { transport with Unsigned = false }
            | "pointer-width" -> { transport with PointerBits = 32; Capacity = ValueRange.unsignedOf 32 }
            | "operand" -> { transport with Operand = transport.Site }
            | _ -> transport
        let edges = graph.Edges |> List.choose (fun edge ->
            if defect = "proof" && edge.Target = transport.Obligation && edge.Role = EdgeRole.Constrains then None
            elif defect = "rewrite" && edge.Target = transport.Obligation && edge.Role = EdgeRole.EnrichedWith then None
            else
                let role =
                    match edge.Role with
                    | EdgeRole.NumericIndexTransport fact when fact.Site = transport.Site -> EdgeRole.NumericIndexTransport changed
                    | EdgeRole.NumericDomain domain ->
                        EdgeRole.NumericDomain { domain with IndexTransports = domain.IndexTransports |> List.map (fun fact -> if fact.Site = transport.Site then changed else fact) }
                    | role -> role
                Some { edge with Role = role })
        match NumericPublication.project { graph with Edges = edges } with
        | Error failures -> Assert.NotEmpty failures
        | Ok _ -> failwith "Changed index transport retained source authority."

    [<Theory>]
    [<InlineData("field-name")>]
    [<InlineData("field-type")>]
    [<InlineData("field-order")>]
    [<InlineData("constructor-layout")>]
    [<InlineData("constructor-count")>]
    member _.``Published representations retract on changed type definitions and constructor placement`` defect =
        let result = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.authority "module RepresentationSnapshot\ntype Pair = { Value: int; Ready: bool }\n[<EntryPoint>]\nlet main _ =\n    let pair = { Value = 7; Ready = true }\n    if pair.Ready then pair.Value else 0\n"
        DimensionalCases.noErrors result
        let graph = result.Graph
        let definition, name, fields, members = graph.Nodes.Values |> Seq.pick (fun node ->
            match node.Kind with
            | SemanticKind.TypeDef(name, TypeDefKind.RecordDef fields, members) when fields |> List.map fst = ["Value"; "Ready"] -> Some(node, name, fields, members)
            | _ -> None)
        let changed =
            match defect with
            | "field-name" -> { definition with Kind = SemanticKind.TypeDef(name, TypeDefKind.RecordDef(("Renamed", snd fields[0]) :: fields.Tail), members) }
            | "field-type" -> { definition with Kind = SemanticKind.TypeDef(name, TypeDefKind.RecordDef((fst fields[0], Types.charType) :: fields.Tail), members) }
            | "field-order" -> { definition with Kind = SemanticKind.TypeDef(name, TypeDefKind.RecordDef(List.rev fields), members) }
            | _ ->
                match definition.Type with
                | NativeType.TApp(tc, args) ->
                    let tc = if defect = "constructor-layout" then { tc with Layout = TypeLayout.Inline(128, 16) } else { tc with FieldCount = tc.FieldCount + 1 }
                    { definition with Type = NativeType.TApp(tc, args) }
                | _ -> failwith "The source record definition has no nominal constructor."
        let altered = { graph with Nodes = graph.Nodes.Add(definition.Id, changed) }
        match NumericPublication.project altered with
        | Error failures -> Assert.Contains(failures, fun failure -> failure.Reason.Contains("premises changed"))
        | Ok _ -> failwith "Changed declaration retained source representation authority."
        match NumericPublication.project graph with Ok _ -> () | Error failures -> failwithf "Original graph lost its authority: %A" failures

    [<Theory>]
    [<InlineData("character")>]
    [<InlineData("float-bits")>]
    [<InlineData("decimal-bits")>]
    [<InlineData("bytes")>]
    [<InlineData("uint16")>]
    [<InlineData("field-place")>]
    [<InlineData("place-kind")>]
    [<InlineData("allocation-count")>]
    [<InlineData("allocation-kind")>]
    [<InlineData("dispatch-label")>]
    member _.``Source premise snapshots distinguish exact literals and addressable places`` defect =
        let graph, _ = IntrinsicWriteFixture.admitted ()
        let node = graph.Nodes.Values |> Seq.head
        let before, after =
            match defect with
            | "character" -> SemanticKind.Literal(NativeLiteral.Char 'a'), SemanticKind.Literal(NativeLiteral.Char 'b')
            | "float-bits" -> SemanticKind.Literal(NativeLiteral.Float(0.0, NTUKind.NTUfloat(NTUWidth.Fixed 64))), SemanticKind.Literal(NativeLiteral.Float(-0.0, NTUKind.NTUfloat(NTUWidth.Fixed 64)))
            | "decimal-bits" -> SemanticKind.Literal(NativeLiteral.Decimal 1.0M), SemanticKind.Literal(NativeLiteral.Decimal 1.00M)
            | "bytes" -> SemanticKind.Literal(NativeLiteral.ByteArray [| 0uy; 255uy |]), SemanticKind.Literal(NativeLiteral.ByteArray [| 0uy; 254uy |])
            | "uint16" -> SemanticKind.Literal(NativeLiteral.UInt16Array [| 0us; 65535us |]), SemanticKind.Literal(NativeLiteral.UInt16Array [| 0us; 65534us |])
            | "field-place" -> SemanticKind.FieldAddress(node.Id, "Value"), SemanticKind.FieldAddress(node.Id, "Other")
            | "allocation-count" -> SemanticKind.ArrayAllocate node.Id, SemanticKind.ArrayAllocate (NodeId.fresh ())
            | "allocation-kind" -> SemanticKind.ArrayAllocate node.Id, SemanticKind.Sequential [node.Id]
            | "dispatch-label" -> SemanticKind.ContinuationDispatch(node.Id,[0,node.Id],node.Id), SemanticKind.ContinuationDispatch(node.Id,[1,node.Id],node.Id)
            | _ -> SemanticKind.CellAddress node.Id, SemanticKind.Reborrow node.Id
        let snapshot kind = Clef.Compiler.Baker.Ingredients.Boundaries.premise { node with Kind = kind }
        Assert.NotEqual(snapshot before, snapshot after)

    [<Fact>]
    member _.``Source premise fallback retains exact case names and ordered references`` () =
        let graph, _ = IntrinsicWriteFixture.admitted ()
        let node = graph.Nodes.Values |> Seq.head
        let other = graph.Nodes.Keys |> Seq.find ((<>) node.Id)
        for kind, name, references in [
            SemanticKind.WhileLoop(node.Id, other), "WhileLoop", [node.Id; other]
            SemanticKind.WhileLoop(other, node.Id), "WhileLoop", [other; node.Id]
            SemanticKind.PlatformBinding "first", "PlatformBinding", []
            SemanticKind.PlatformBinding "second", "PlatformBinding", []
        ] do
            let premise = Clef.Compiler.Baker.Ingredients.Boundaries.premise { node with Kind = kind; Children = [] }
            Assert.Equal(name, premise.Shape.Form)
            Assert.True((references = premise.Shape.References))
            Assert.Empty premise.Shape.Text
            Assert.Empty premise.Shape.Numbers

    [<Fact>]
    member _.``String length uses its source held carrier and retained exact extent`` () =
        let graph, boundary = IntrinsicWriteFixture.admitted ()
        let numeric = NumericPublication.project graph |> function Ok value -> value | Error failures -> failwithf "%A" failures
        let memory = MemoryPublication.project graph |> function Ok value -> value | Error failures -> failwithf "%A" failures
        let call = Assert.Single boundary.IntrinsicWrites.Values
        let carrier = numeric.Values[call.Count]
        Assert.Contains(call.Count, numeric.ResultSites)
        match memory.Operations[call.Count] with
        | MemoryWitnessOperation.BufferExtent extent ->
            Assert.Equal(carrier, extent.Result)
            Assert.Equal(boundary.StringExtents[call.Count], extent.Extent)
            Assert.True(carrier.Obligations.Length = 1)
        | _ -> failwith "String Length was not published as its source memory extent."

    [<Fact>]
    member _.``Numeric renewal derives string ranges from source while memory rejects a changed published extent`` () =
        let graph, boundary = IntrinsicWriteFixture.admitted ()
        let numeric = NumericCaptureFixture.admitted graph
        let call = Assert.Single boundary.IntrinsicWrites.Values
        let extent = boundary.StringExtents[call.Count]
        Assert.NotEmpty extent.StaticOrigins
        let changedExtent = { extent with StaticOrigins = extent.StaticOrigins |> Map.map (fun _ length -> length + 100I) }
        let replace extent (graph: SemanticGraph) =
            let edges = graph.Edges |> List.map (fun edge ->
                match edge.Role with
                | EdgeRole.StringExtent current when current.Site = call.Count -> { edge with Role = EdgeRole.StringExtent extent }
                | _ -> edge)
            { graph with Edges = edges }
        let changed = replace changedExtent graph
        Assert.Same(graph.Nodes, changed.Nodes)
        Assert.NotEqual(Clef.Compiler.Baker.Ingredients.NumericValues.rangeContextRelations graph,
                        Clef.Compiler.Baker.Ingredients.NumericValues.rangeContextRelations changed)
        Assert.True(Clef.Compiler.Baker.Ingredients.MemoryValues.stringRelations graph <>
                    Clef.Compiler.Baker.Ingredients.MemoryValues.stringRelations changed)
        NumericCaptureFixture.invocationRefusal changed
        let memoryRefusal reason current =
            match MemoryPublication.project current with
            | Error failures -> Assert.Contains(failures, fun failure ->
                failure.Reason = reason)
            | Ok _ -> failwith "Memory publication admitted a changed string extent."
        memoryRefusal "MemoryPublication: The exact memory source, guard, meet or declaration premises changed; source settlement is required." changed
        let renewed = Clef.Compiler.Nanopass.NumericSettlement.normalize changed
        let repeated = Clef.Compiler.Nanopass.NumericSettlement.normalize renewed
        for current in [renewed; repeated] do
            Assert.True(current.RangeContextFacts.IsSome)
            Assert.Equal(current.RangeContextFacts, (NumericCaptureFixture.domain current).RangeContextFacts)
            Assert.NotEqual(graph.RangeContextFacts, current.RangeContextFacts)
            // The published extent row is not the source of logical length.
            // Fresh range issuance still reads the unchanged string literals.
            Assert.Equal(graph.RangeContextFacts.Value.Values[RangeContext.Shared, call.Count],
                         current.RangeContextFacts.Value.Values[RangeContext.Shared, call.Count])
            let carrier = (NumericCaptureFixture.admitted current).Values[call.Count]
            Assert.Equal(numeric.Values[call.Count].Range, carrier.Range)
            Assert.Equal(numeric.Values[call.Count].Slot, carrier.Slot)
            Assert.True(Clef.Compiler.Baker.Ingredients.MemoryValues.stringRelations graph <>
                        Clef.Compiler.Baker.Ingredients.MemoryValues.stringRelations current)
            // Numeric renewal retires the citizens named by the old memory
            // domain, so that dependent domain must be settled again.
            Assert.Empty(current.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.MemoryDomain _ -> true | _ -> false))
            memoryRefusal "MemoryPublication: Exactly one source MemorySettlement domain is required before witnessing." current
        repeated |> replace extent |> Clef.Compiler.Nanopass.NumericSettlement.normalize
        |> NumericCaptureFixture.admitted |> ignore

    [<Fact>]
    member _.``Numeric renewal refuses a changed source string length outside its held range`` () =
        let graph, boundary = IntrinsicWriteFixture.admitted ()
        let call = Assert.Single boundary.IntrinsicWrites.Values
        let numeric = NumericCaptureFixture.admitted graph
        let literal = graph.Nodes[IntrinsicWriteFixture.literal graph "hello"]
        let changedLiteral = { literal with Kind = SemanticKind.Literal(NativeLiteral.String("hello" + String.replicate 100 "x")) }
        let changed = { graph with Nodes = graph.Nodes.Add(literal.Id, changedLiteral) }
        NumericCaptureFixture.invocationRefusal changed
        let renewed = changed |> Clef.Compiler.Nanopass.OrdinaryDemand.normalize |> Clef.Compiler.Nanopass.NumericSettlement.normalize
        let repeated = Clef.Compiler.Nanopass.NumericSettlement.normalize renewed
        for current in [renewed; repeated] do
            let fresh = current.RangeContextFacts.Value.Values[RangeContext.Shared, call.Count]
            Assert.False(ValueRange.contains numeric.Values[call.Count].Range fresh)
            Assert.Equal(graph.Nodes[call.Count].ValueRange, current.Nodes[call.Count].ValueRange)
            NumericCaptureFixture.heldRangeRefusal current

    [<Theory>]
    [<InlineData("range")>]
    [<InlineData("carrier")>]
    [<InlineData("proof")>]
    [<InlineData("rewrite")>]
    [<InlineData("element-premise")>]
    member _.``Numeric publication refuses changed premises missing carriers and missing proof evidence`` defect =
        let graph, boundary = IntrinsicWriteFixture.admitted ()
        let call = Assert.Single boundary.IntrinsicWrites.Values
        let changed =
            match defect with
            | "range" -> { graph with Nodes = graph.Nodes.Add(call.Count, { graph.Nodes[call.Count] with ValueRange = Some(Clef.Compiler.NativeTypedTree.NativeTypes.ValueRange.point 99I) }) }
            | "carrier" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.NumericCarrier carrier when carrier.Site = call.Count -> false | _ -> true) }
            | "proof" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.NumericProof _ when edge.Target = call.Count -> false | _ -> true) }
            | "element-premise" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.StringByteStorage _ -> false | _ -> true) }
            | _ ->
                let obligations = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.NumericCarrier carrier when carrier.Site = call.Count -> Some carrier.Obligations | _ -> None) |> List.concat |> Set.ofList
                { graph with Edges = graph.Edges |> List.filter (fun edge -> not(edge.Role = EdgeRole.EnrichedWith && obligations.Contains edge.Target)) }
        match NumericPublication.project changed with Error _ -> () | Ok _ -> failwith "Numeric publication repaired changed or missing source evidence."

    [<Fact>]
    member _.``Numeric resettlement retracts prior owned proof citizens`` () =
        let graph, _ = IntrinsicWriteFixture.admitted ()
        let prior = graph.Nodes |> Map.toList |> List.choose (fun (id, node) -> if node.Metadata.ContainsKey "Baker.NumericOwned" then Some id else None) |> Set.ofList
        let settled = Clef.Compiler.Nanopass.NumericSettlement.normalize graph
        Assert.True(prior |> Set.forall (fun id -> not (settled.Nodes.ContainsKey id)))
        match NumericPublication.project settled with Ok _ -> () | Error failures -> failwithf "%A" failures

module private TransparentScalarFixture =
    let private check source =
        let result = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.authority source
        DimensionalCases.noErrors result
        result.Graph

    let alias = lazy (check "module OrdinaryExtent\nlet select choose = if choose then \"a\\000b\" else \"longer\"\nlet measure (text:string) =\n    let extent = String.length\n    extent text\n[<EntryPoint>]\nlet main _ =\n    let text = select true\n    measure text\n")

    let narrow = lazy (check "module NarrowBlocks\nlet narrow () =\n    let value = 7\n    value\n[<EntryPoint>]\nlet main _ =\n    let value = narrow ()\n    value\n")

    let body (graph: SemanticGraph) name =
        let binding = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false) |> Assert.Single
        let implementation = graph.Nodes[binding.Children |> Assert.Single]
        match implementation.Kind with
        | SemanticKind.Lambda(_, result, _, _, _) -> implementation, graph.Nodes[result]
        | _ -> failwith "Expected the source function's actual lambda."

    let terminal (graph: SemanticGraph) (block: SemanticNode) =
        match block.Kind with
        | SemanticKind.Sequential values ->
            Assert.Equal<NodeId list>(values, block.Children)
            graph.Nodes[List.last values]
        | _ -> failwith "Expected a source Sequential body."

type TransparentScalarCarrierCases() =
    [<Fact>]
    member _.``Sequential publication preserves its terminal callable ABI carrier`` () =
        let graph = TransparentScalarFixture.alias.Value
        let implementation, block = TransparentScalarFixture.body graph "measure"
        let result = TransparentScalarFixture.terminal graph block
        match result.Kind with SemanticKind.Application _ -> () | _ -> failwith "Expected the actual alias call."
        let numeric = NumericPublication.project graph |> Result.defaultWith (sprintf "%A" >> failwith)
        let expected = SettledSlot.Integer(64, Some "unsigned64")
        Assert.Equal(ValueRange.Bounded(3I, 6I), numeric.Values[result.Id].Range)
        Assert.Equal(expected, numeric.Values[result.Id].Slot)
        Assert.Equal(expected, numeric.Values[block.Id].Slot)
        Assert.Equal(numeric.Values[result.Id].Representation, numeric.Values[block.Id].Representation)
        Assert.Equal(block.Id, numeric.Values[block.Id].Site)
        Assert.Contains(result.Id, numeric.Values[block.Id].Participants)
        Assert.Contains(block.Id, numeric.ResultSites)
        Assert.DoesNotContain(implementation.Id, graph.Codata.Value.ReturnMeets.Keys)

    [<Theory>]
    [<InlineData("narrow", 8, "octet")>]
    [<InlineData("main", 8, "octet")>]
    member _.``Transparent blocks preserve source carriers and the separate entry ABI`` name bits representation =
        let graph = TransparentScalarFixture.narrow.Value
        let implementation, block = TransparentScalarFixture.body graph name
        let result = TransparentScalarFixture.terminal graph block
        let numeric = NumericPublication.project graph |> Result.defaultWith (sprintf "%A" >> failwith)
        let expected = SettledSlot.Integer(bits, Some representation)
        Assert.Equal(expected, numeric.Values[result.Id].Slot)
        Assert.Equal(expected, numeric.Values[block.Id].Slot)
        if name = "main" then
            // Startup moves the exported root to a generated wrapper; source
            // main remains an ordinary narrow function, with no return meet.
            let storage = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.tryStorage graph |> Result.defaultWith failwith
            let startup = storage.Startup |> Option.defaultWith (fun () -> failwith "Missing settled program entry.")
            Assert.Equal(implementation.Id, startup.SourceLambda)
            Assert.Equal(block.Id, startup.OriginalBody)
            Assert.NotEqual<NodeId>(implementation.Id, startup.EntryLambda)
            Assert.DoesNotContain(implementation.Id, graph.Codata.Value.DeclarationRootLambdas.Keys)
            Assert.DoesNotContain(implementation.Id, graph.Codata.Value.ReturnMeets.Keys)
            Assert.Equal(DeclRoot.EntryPoint, graph.Codata.Value.DeclarationRootLambdas[startup.EntryLambda])
            let entryBody = graph.Nodes[startup.Spine]
            let entryResult = TransparentScalarFixture.terminal graph entryBody
            Assert.Equal(startup.EntryCall, entryResult.Id)
            let entryCarrier = SettledSlot.Integer(64, Some "unsigned64")
            Assert.Equal(entryCarrier, numeric.Values[entryBody.Id].Slot)
            Assert.Equal(entryCarrier, numeric.Values[entryResult.Id].Slot)

    [<Theory>]
    [<InlineData("missing-final")>]
    [<InlineData("cycle")>]
    [<InlineData("children")>]
    [<InlineData("type")>]
    member _.``Invalid transparent scalar paths cannot regain a range selected carrier`` defect =
        let graph = TransparentScalarFixture.alias.Value
        let _, block = TransparentScalarFixture.body graph "measure"
        let result = TransparentScalarFixture.terminal graph block
        let changed =
            match defect with
            | "missing-final" -> { graph with Nodes = graph.Nodes.Remove result.Id }
            | "cycle" ->
                let values = [block.Id]
                { graph with Nodes = graph.Nodes.Add(block.Id, { block with Kind = SemanticKind.Sequential values; Children = values }) }
            | "children" -> { graph with Nodes = graph.Nodes.Add(block.Id, { block with Children = [] }) }
            | _ -> { graph with Nodes = graph.Nodes.Add(result.Id, { result with Type = Types.boolType }) }
        Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedWidth changed block.Id).IsNone)
        Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedRepresentation changed block.Id).IsNone)
        Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth changed block.Id).IsNone)
        match NumericPublication.project changed with
        | Error failures -> Assert.NotEmpty failures
        | Ok _ -> failwith "Changed block path retained its prior numeric publication."
