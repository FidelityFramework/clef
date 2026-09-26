namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
module EagerDemand = Clef.Compiler.Nanopass.EagerDemand

module private EagerGraph =
    let check source =
        match parseAndCheck ("module EagerGraph\n" + source) "eager-graph.clef" with
        | Success result | CheckFailure result -> DimensionalCases.noErrors result; result.Graph
        | ParseFailure errors -> failwithf "Eager graph source failed parsing: %A" errors

    let markers (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.EagerExpr operand when node.IsReachable -> Some (node, graph.Nodes[operand])
            | _ -> None) |> Seq.toList

    let frontiers (graph: SemanticGraph) owner kind =
        graph.Edges |> List.filter (fun edge ->
            edge.Target = owner && edge.Class = EdgeClass.Demand && edge.Role = EdgeRole.EagerDemand kind)

    let incidence (edges: Hyperedge list) =
        edges |> List.map (fun edge -> edge.Sources, edge.Target, edge.Class, edge.Role, edge.Ordinal)

    let onPlatform bits source =
        let representations =
            [ "int8", "int", 8, "-128", "127"; "uint8", "uint", 8, "0", "255"
              "int" + string bits, "int", bits, string (- (1I <<< (bits - 1))), string ((1I <<< (bits - 1)) - 1I)
              "uint" + string bits, "uint", bits, "0", string ((1I <<< bits) - 1I) ]
            |> List.map (fun (name, family, width, low, high) ->
                { Name = name; Family = family; Bits = width; Capability = "native"
                  MinMagnitude = low; MaxMagnitude = high; Boundary = "wrap" }: NumericRepresentation)
        let platform: PlatformContext =
            { PlatformId = "demand-test"; Dimensions = Map.ofList ["Pointer", bits; "Register", bits]
              Representations = representations |> List.map (fun rep -> rep.Name, rep) |> Map.ofList
              EndpointReturns = Map.empty; PlatformLibraryPath = None; PlatformDescription = Some "DemandPlatform.description"
              PlatformArchitecture = None; PlatformOS = None
              PlatformSourcePaths = Set.singleton (System.IO.Path.GetFullPath "demand-platform.clef")
              Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
              AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None }
        let declarations = representations |> List.map (fun rep ->
            sprintf "{ Name=\"%s\"; Family=\"%s\"; Bits=%d; Capability=\"native\"; MinMagnitude=\"%s\"; MaxMagnitude=\"%s\"; Boundary=\"wrap\" }"
                rep.Name rep.Family rep.Bits rep.MinMagnitude rep.MaxMagnitude) |> String.concat "; "
        let declaration = """module DemandPlatform
type WidthDeclaration = { Name: string; Bits: int }
type Representation = { Name: string; Family: string; Bits: int; Capability: string; MinMagnitude: string; MaxMagnitude: string; Boundary: string }
type TargetCore = { Widths: WidthDeclaration array; Representations: Representation array }
type MemorySpace = { Name: string; Kind: string; Capacity: int; Alignment: int; Granularity: int; Growth: string; Access: string; Base: int option }
type ProgramLifetimeSpaces = { Immutable: string; Mutable: string option }
type PlatformDescription = { Id: string; Core: TargetCore option; Spaces: MemorySpace array; ProgramLifetime: ProgramLifetimeSpaces option }
let image = { Name="image"; Kind="rodata"; Capacity=4096; Alignment=16; Granularity=16; Growth="fixed"; Access="r"; Base=None }
let core: TargetCore = { Widths = [| { Name="Pointer"; Bits=""" + string bits + " }; { Name=\"Register\"; Bits=" + string bits + " } |]; Representations = [| " + declarations + """ |] }
let description = { Id="demand-test"; Core=Some core; Spaces=[|image|]; ProgramLifetime=Some { Immutable="image"; Mutable=None } }
"""
        let parse path text =
            match parseStringWithDefaults text path with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Platform demand fixture failed parsing: %A" errors
        let result = checkParsedInputsWithPlatformAndSources
                         [parse "demand-platform.clef" declaration; parse "eager-graph.clef" ("module EagerGraph\n" + source)]
                         (Some platform) (Set.singleton (System.IO.Path.GetFullPath "eager-graph.clef"))
        DimensionalCases.noErrors result
        result.Graph

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "EagerGraph")>]
type EagerGraphCases() =
    [<Fact>]
    member _.``Explicit demand retains operand type and its value range``() =
        let graph = EagerGraph.check """
let value = eager 3
[<EntryPoint>]
let main _ = value + 1
"""
        let marker, operand = EagerGraph.markers graph |> Assert.Single
        Assert.Equal(formatType operand.Type, formatType marker.Type)
        Assert.Equal(operand.ValueRange, marker.ValueRange)
        Assert.Equal(Some (ValueRange.Bounded(3I, 3I)), marker.ValueRange)
        let expression = EagerGraph.frontiers graph marker.Id EagerFrontier.Expression |> Assert.Single
        Assert.Equal<NodeId list>([marker.Id; operand.Id], expression.Sources)

    [<Fact>]
    member _.``Eager formation of an explicit lazy value retains the deferred thunk``() =
        let graph = EagerGraph.check """
let delayed = eager (lazy 3)
[<EntryPoint>]
let main _ = Lazy.force delayed
"""
        let marker, operand = EagerGraph.markers graph |> Assert.Single
        match marker.Type, operand.Kind with
        | NativeType.TLazy _, SemanticKind.LazyExpr(thunk, _) ->
            Assert.DoesNotContain(graph.Edges, fun edge ->
                edge.Target = marker.Id && edge.Class = EdgeClass.Demand && List.contains thunk edge.Sources)
        | NativeType.TLazy _, SemanticKind.LazyValue(thunk, _) ->
            let contract = Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues.instance graph operand.Id
                           |> Option.defaultWith (fun () -> failwith "Explicit eager lost the actual lazy instance")
            Assert.Equal(thunk, contract.Thunk)
            Assert.DoesNotContain(graph.Edges, fun edge ->
                edge.Target = marker.Id && edge.Class = EdgeClass.Demand && List.contains thunk edge.Sources)
        | other -> failwithf "Eager formation changed the explicit lazy boundary: %A" other

    [<Fact>]
    member _.``Specialization remaps eager reads to each actual formal``() =
        let graph = EagerGraph.check """
let evaluate value = eager value
[<EntryPoint>]
let main _ = if evaluate true then evaluate 1 else 0
"""
        let markers = EagerGraph.markers graph
        Assert.Equal(2, markers.Length)
        Assert.Equal<string list>(["bool"; "int"], markers |> List.map (fst >> _.Type >> formatType) |> List.sort)
        let formals = markers |> List.map (fun (marker, operand) ->
            match operand.Kind, marker.Parent |> Option.map (fun id -> graph.Nodes[id].Kind) with
            | SemanticKind.VarRef(_, Some formal), Some (SemanticKind.Lambda(parameters, body, _, _, _)) ->
                Assert.Equal(marker.Id, body)
                Assert.Contains(parameters, fun (_, _, id) -> id = formal)
                Assert.Equal(formatType marker.Type, formatType graph.Nodes[formal].Type)
                formal
            | other -> failwithf "Specialized demand lost its lexical formal: %A" other)
        Assert.Equal(2, formals |> List.distinct |> List.length)

    [<Fact>]
    member _.``Local fan out retains explicit actual order without activating an enclosing deferred argument``() =
        let builder = NodeBuilder()
        let value = builder.Create(SemanticKind.Literal(NativeLiteral.Bool true), Types.boolType, dummyRange)
        let make kind ty children = builder.Create(kind, ty, dummyRange, children = children)
        let first = make (SemanticKind.EagerExpr value.Id) value.Type [value.Id]
        let last = make (SemanticKind.EagerExpr value.Id) value.Type [value.Id]
        let wrapped = make (SemanticKind.TypeAnnotation(first.Id, value.Type)) value.Type [first.Id]
        let parameters = ["first"; "middle"; "last"] |> List.map (fun name ->
            let formal = make (SemanticKind.PatternBinding name) value.Type []
            name, formal.Type, formal.Id)
        let calleeType = List.foldBack (fun (_, ty, _) result -> NativeType.TFun(ty, result)) parameters value.Type
        let callee = make (SemanticKind.Lambda(parameters, value.Id, [], None, LambdaContext.RegularClosure)) calleeType
                         ((parameters |> List.map (fun (_, _, id) -> id)) @ [value.Id])
        let inner = make (SemanticKind.Application(callee.Id, [wrapped.Id; value.Id; last.Id])) value.Type [callee.Id; wrapped.Id; value.Id; last.Id]
        let outer = make (SemanticKind.Application(callee.Id, [inner.Id])) value.Type [callee.Id; inner.Id]
        let binding = make (SemanticKind.Binding("deferred", false, false, None)) value.Type [outer.Id]
        let original = builder.Build []
        let graph = EagerDemand.normalize original
        Assert.Same(original.Nodes, graph.Nodes)
        Assert.Empty(EagerGraph.frontiers graph outer.Id EagerFrontier.Actual)
        Assert.Empty(EagerGraph.frontiers graph binding.Id EagerFrontier.Binding)
        let demands = EagerGraph.frontiers graph inner.Id EagerFrontier.Actual
        Assert.Equal<int list>([0; 2], demands |> List.map _.Ordinal)
        let authority = (parameters |> List.map (fun (_, _, id) -> id)) @ [callee.Id]
        Assert.Equal<NodeId list>([first.Id; value.Id; wrapped.Id] @ authority, demands.Head.Sources)
        Assert.Equal<NodeId list>([last.Id; value.Id] @ authority, demands.Tail.Head.Sources)
        Assert.Equal<(NodeId list * NodeId * EdgeClass * EdgeRole * int) list>(
            EagerGraph.incidence graph.Edges, EagerGraph.incidence (EagerDemand.normalize graph).Edges)

    [<Fact>]
    member _.``Replacing a marker retracts its frontier facts and preserves unrelated incidence``() =
        let builder = NodeBuilder()
        let operand = builder.Create(SemanticKind.Literal(NativeLiteral.Bool true), Types.boolType, dummyRange)
        let marker = builder.Create(SemanticKind.EagerExpr operand.Id, operand.Type, dummyRange, children = [operand.Id])
        let binding = builder.Create(SemanticKind.Binding("forced", false, false, None), marker.Type, dummyRange, children = [marker.Id])
        let original = builder.Build []
        let graph = EagerDemand.normalize original
        Assert.Single(EagerGraph.frontiers graph binding.Id EagerFrontier.Binding) |> ignore
        let changed = { graph with Nodes = graph.Nodes.Add(marker.Id, { marker with Kind = operand.Kind; Children = [] }) }
        let normalized = EagerDemand.normalize changed
        Assert.DoesNotContain(normalized.Edges, fun edge -> edge.Class = EdgeClass.Demand)
        Assert.Equal<(NodeId list * NodeId * EdgeClass * EdgeRole * int) list>(
            EagerGraph.incidence original.Edges, EagerGraph.incidence normalized.Edges)

    [<Fact>]
    member _.``Missing eager operand becomes an explicit pending premise``() =
        let builder = NodeBuilder()
        let operand = builder.Create(SemanticKind.Literal(NativeLiteral.Bool true), Types.boolType, dummyRange)
        let marker = builder.Create(SemanticKind.EagerExpr operand.Id, operand.Type, dummyRange, children = [operand.Id])
        let original = builder.Build []
        let graph = EagerDemand.normalize { original with Nodes = original.Nodes.Remove operand.Id }
        Assert.Empty(EagerGraph.frontiers graph marker.Id EagerFrontier.Expression)
        let pending = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.EagerDemandPending) |> Assert.Single
        Assert.Equal(marker.Id, pending.Target)
        Assert.All(pending.Sources, fun id -> Assert.True(graph.Nodes.ContainsKey id))

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``A removed or retired callee retracts eager actual authority``(retire: bool) =
        let builder = NodeBuilder()
        let operand = builder.Create(SemanticKind.Literal(NativeLiteral.Bool true), Types.boolType, dummyRange)
        let marker = builder.Create(SemanticKind.EagerExpr operand.Id, operand.Type, dummyRange, children = [operand.Id])
        let callee = builder.Create(SemanticKind.PatternBinding "callee", NativeType.TFun(operand.Type, operand.Type), dummyRange)
        let call = builder.Create(SemanticKind.Application(callee.Id, [marker.Id]), operand.Type, dummyRange, children = [callee.Id; marker.Id])
        let graph = builder.Build [] |> EagerDemand.normalize
        Assert.Single(EagerGraph.frontiers graph call.Id EagerFrontier.Actual) |> ignore
        let nodes =
            if retire then graph.Nodes.Add(callee.Id, { callee with IsReachable = false })
            else graph.Nodes.Remove callee.Id
        let changed = EagerDemand.normalize { graph with Nodes = nodes }
        Assert.Empty(EagerGraph.frontiers changed call.Id EagerFrontier.Actual)
        let pending = changed.Edges |> List.filter (fun edge -> edge.Target = call.Id && edge.Role = EdgeRole.EagerDemandPending) |> Assert.Single
        Assert.All(pending.Sources, fun id -> Assert.True(changed.Nodes.ContainsKey id))
        Assert.Contains(marker.Id, pending.Sources)

    [<Fact>]
    member _.``An annotated direct eager initializer belongs to its binding frontier``() =
        let graph = EagerGraph.check """
[<EntryPoint>]
let main _ =
    let chosen = (eager true : bool)
    if chosen then 0 else 1
"""
        let marker, operand = EagerGraph.markers graph |> Assert.Single
        let demand = graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.EagerDemand EagerFrontier.Binding && edge.Sources.Head = marker.Id) |> Assert.Single
        match graph.Nodes[demand.Target].Kind with
        | SemanticKind.Binding("chosen", false, _, _) -> ()
        | kind -> failwithf "Explicit initializer lost its actual binding frontier: %A" kind
        Assert.Equal<NodeId list>([marker.Id; operand.Id], List.take 2 demand.Sources)

    [<Theory>]
    [<InlineData("", "(eager true, false, eager true)")>]
    [<InlineData("", "[| eager true; false; eager true |]")>]
    [<InlineData("", "[eager true; false; eager true]")>]
    [<InlineData("type Fields = { First: bool; Middle: bool; Last: bool }", "{ Last = eager true; Middle = false; First = eager true }")>]
    member _.``Explicit aggregate components retain written order and ordinary siblings``(declaration: string, expression: string) =
        let graph = EagerGraph.check (declaration + "\n[<EntryPoint>]\nlet main _ =\n    let observed = " + expression + "\n    ignore observed\n    0\n")
        let markers = EagerGraph.markers graph
        Assert.Equal(2, markers.Length)
        let components = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.EagerDemand EagerFrontier.Component)
        Assert.Equal<int list>([0; 2], components |> List.map _.Ordinal)
        let owner = components |> List.map _.Target |> List.distinct |> Assert.Single
        let operands =
            match graph.Nodes[owner].Kind with
            | SemanticKind.TupleExpr ids | SemanticKind.ArrayExpr ids | SemanticKind.ListExpr ids -> ids
            | SemanticKind.RecordExpr(fields, _) ->
                Assert.Equal<string list>(["Last"; "Middle"; "First"], List.map fst fields)
                List.map snd fields
            | kind -> failwithf "Unexpected explicit component frontier: %A" kind
        Assert.Equal<NodeId list>([operands[0]; operands[2]], List.map (_.Sources >> List.head) components)
        match graph.Nodes[operands[1]].Kind with
        | SemanticKind.Literal(NativeLiteral.Bool false) -> ()
        | kind -> failwithf "Ordinary sibling changed identity: %A" kind

    [<Fact>]
    member _.``Explicit callable formation preserves the same implementation identity``() =
        let graph = EagerGraph.check """
let identity flag = flag
[<EntryPoint>]
let main _ =
    let chosen = eager identity
    if chosen true then 0 else 1
"""
        let marker, operand = EagerGraph.markers graph |> Assert.Single
        let implementation = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments.tryImplementation graph
        let expected = implementation operand.Id
        Assert.True expected.IsSome
        Assert.Equal(expected, implementation marker.Id)
        let origins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
        let call = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            (match node.Kind with
             | SemanticKind.Application(callee, _) -> implementation callee = expected
             | _ -> false)) |> Assert.Single
        Assert.False origins.Calls[call.Id].Unknown
        Assert.Equal(expected.Value, (Assert.Single origins.Calls[call.Id].Targets).Lambda)

    [<Fact>]
    member _.``Explicit sequence formation preserves origin without demanding its body``() =
        let graph = EagerGraph.check """
[<EntryPoint>]
let main _ =
    let work = eager (seq { yield true })
    for value in work do ignore value
    0
"""
        let marker, operand = EagerGraph.markers graph |> Assert.Single
        let origins, _ = Clef.Compiler.PSGSaturation.SemanticGraph.SequenceOrigins.settle graph graph.Codata.Value.Curry
        Assert.Equal(operand.Id, origins[marker.Id])
        match operand.Kind with
        | SemanticKind.SeqExpr(generator, _) ->
            Assert.DoesNotContain(graph.Edges, fun edge ->
                edge.Target = marker.Id && edge.Class = EdgeClass.Demand && List.contains generator edge.Sources)
        | kind -> failwithf "Sequence formation lost its original deferred owner: %A" kind

    [<Theory>]
    [<InlineData(32)>]
    [<InlineData(64)>]
    member _.``Continuation rewriting reprojects demand onto actual live occurrences``(bits: int) =
        let graph = EagerGraph.onPlatform bits """
[<EntryPoint>]
let main _ =
    let work = seq { yield eager true; yield eager false }
    for value in work do ignore value
    0
"""
        Assert.Single graph.Codata.Value.ContinuationFrames |> ignore
        let markers = EagerGraph.markers graph
        Assert.Equal(2, markers.Length)
        for marker, operand in markers do
            let demand = EagerGraph.frontiers graph marker.Id EagerFrontier.Expression |> Assert.Single
            Assert.Equal<NodeId list>([marker.Id; operand.Id], demand.Sources)
            match operand.Kind with
            | SemanticKind.FrameRead _ -> ()
            | kind -> failwithf "Expected the actual cloned frame operand, got %A" kind
        let retired = graph.Nodes.Values |> Seq.filter (fun node ->
            not node.IsReachable && match node.Kind with SemanticKind.EagerExpr _ -> true | _ -> false) |> Seq.toList
        Assert.Equal(2, retired.Length)
        for edge in graph.Edges do
            if edge.Class = EdgeClass.Demand then
                Assert.True(graph.Nodes[edge.Target].IsReachable)
                Assert.All(edge.Sources, fun id -> Assert.True(graph.Nodes[id].IsReachable))

    [<Fact>]
    member _.``Partial formation retains eager results separately from ordinary deferred actuals``() =
        let graph = EagerGraph.check """
let choose (first: bool) (second: bool) (third: bool) = if third then 1 else 0
[<EntryPoint>]
let main _ =
    let partial = choose (eager true : bool) false
    partial (eager false)
"""
        let formation, partial = graph.Codata.Value.Curry.PartialApplications |> Map.toList |> Assert.Single
        Assert.Equal(2, partial.SuppliedArgNodes.Length)
        let explicit, ordinary = partial.SuppliedArgNodes[0], partial.SuppliedArgNodes[1]
        let first = EagerGraph.frontiers graph formation EagerFrontier.Actual |> Assert.Single
        Assert.Equal(0, first.Ordinal)
        Assert.DoesNotContain(explicit, graph.Codata.Value.Curry.DeferredArgNodes)
        Assert.Contains(ordinary, graph.Codata.Value.Curry.DeferredArgNodes)
        let later = graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.EagerDemand EagerFrontier.Actual && edge.Target <> formation) |> Assert.Single
        Assert.DoesNotContain(first.Sources.Head, later.Sources)
        Assert.Equal(0, later.Ordinal)
        let complete = graph.Codata.Value.Curry.SaturatedCalls[later.Target]
        Assert.Equal<NodeId list>(partial.SuppliedArgNodes, List.take 2 complete.AllArgNodes)

    [<Theory>]
    [<InlineData("Some (eager true)")>]
    [<InlineData("Case (eager true)")>]
    member _.``An explicit direct union payload belongs to constructor activation``(expression: string) =
        let graph = EagerGraph.check ("type Choice = Case of bool\n[<EntryPoint>]\nlet main _ =\n    let selected = " + expression + "\n    ignore selected\n    0\n")
        let marker, operand = EagerGraph.markers graph |> Assert.Single
        let frontier = graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.EagerDemand EagerFrontier.Component && edge.Sources.Head = marker.Id) |> Assert.Single
        match graph.Nodes[frontier.Target].Kind with
        | SemanticKind.DUConstruct(_, _, Some payload, _) -> Assert.Equal(marker.Id, payload)
        | kind -> failwithf "Expected actual union construction: %A" kind
        Assert.Equal<NodeId list>([marker.Id; operand.Id], frontier.Sources)

    [<Fact>]
    member _.``A changed annotation cycle retracts its former direct marker relation``() =
        let builder = NodeBuilder()
        let operand = builder.Create(SemanticKind.Literal(NativeLiteral.Bool true), Types.boolType, dummyRange)
        let marker = builder.Create(SemanticKind.EagerExpr operand.Id, operand.Type, dummyRange, children = [operand.Id])
        let wrapper = builder.Create(SemanticKind.TypeAnnotation(marker.Id, marker.Type), marker.Type, dummyRange, children = [marker.Id])
        let binding = builder.Create(SemanticKind.Binding("value", false, false, None), marker.Type, dummyRange, children = [wrapper.Id])
        let original = builder.Build [] |> EagerDemand.normalize
        Assert.Single(EagerGraph.frontiers original binding.Id EagerFrontier.Binding) |> ignore
        let edited = { wrapper with Kind = SemanticKind.TypeAnnotation(wrapper.Id, wrapper.Type); Children = [wrapper.Id] }
        let changed = EagerDemand.normalize { original with Nodes = original.Nodes.Add(wrapper.Id, edited) }
        Assert.Empty(EagerGraph.frontiers changed binding.Id EagerFrontier.Binding)
        let pending = changed.Edges |> List.filter (fun edge -> edge.Target = binding.Id && edge.Role = EdgeRole.EagerDemandPending) |> Assert.Single
        Assert.Equal<NodeId list>([wrapper.Id], pending.Sources)

    [<Theory>]
    [<InlineData("annotation-declared-type")>]
    [<InlineData("annotation-result-type")>]
    [<InlineData("annotation-incidence")>]
    [<InlineData("marker-result-type")>]
    [<InlineData("marker-incidence")>]
    [<InlineData("operand-type")>]
    [<InlineData("retired-operand")>]
    [<InlineData("missing-operand")>]
    member _.``Direct eager frontier retracts changed type and structural premises`` defect =
        let builder = NodeBuilder()
        let operand = builder.Create(SemanticKind.Literal(NativeLiteral.Bool true), Types.boolType, dummyRange)
        let marker = builder.Create(SemanticKind.EagerExpr operand.Id, operand.Type, dummyRange)
        let wrapper = builder.Create(SemanticKind.TypeAnnotation(marker.Id, marker.Type), marker.Type, dummyRange)
        let binding = builder.Create(SemanticKind.Binding("value", false, false, None), marker.Type, dummyRange, children = [wrapper.Id])
        let original = builder.Build [] |> EagerDemand.normalize
        let admitted = EagerGraph.frontiers original binding.Id EagerFrontier.Binding |> Assert.Single
        Assert.Contains(wrapper.Id, admitted.Sources)
        Assert.Contains(marker.Id, admitted.Sources)
        Assert.Contains(operand.Id, admitted.Sources)
        let nodes =
            match defect with
            | "annotation-declared-type" -> original.Nodes.Add(wrapper.Id, { wrapper with Kind = SemanticKind.TypeAnnotation(marker.Id, Types.unitType) })
            | "annotation-result-type" -> original.Nodes.Add(wrapper.Id, { wrapper with Type = Types.unitType })
            | "annotation-incidence" -> original.Nodes.Add(wrapper.Id, { wrapper with Children = [operand.Id] })
            | "marker-result-type" -> original.Nodes.Add(marker.Id, { marker with Type = Types.unitType })
            | "marker-incidence" -> original.Nodes.Add(marker.Id, { marker with Children = [] })
            | "operand-type" -> original.Nodes.Add(operand.Id, { operand with Type = Types.unitType })
            | "retired-operand" -> original.Nodes.Add(operand.Id, { operand with IsReachable = false })
            | _ -> original.Nodes.Remove operand.Id
        let changed = EagerDemand.normalize { original with Nodes = nodes }
        Assert.Empty(EagerGraph.frontiers changed binding.Id EagerFrontier.Binding)
        Assert.Contains(changed.Edges, fun edge -> edge.Target = binding.Id && edge.Role = EdgeRole.EagerDemandPending)
        let repaired = EagerDemand.normalize { changed with Nodes = original.Nodes }
        // Saturation rebuilds relation objects. Repair restores their complete
        // semantic identity, rather than the old object's reference identity.
        let restored = EagerGraph.frontiers repaired binding.Id EagerFrontier.Binding |> Assert.Single
        Assert.Equal<NodeId list>(admitted.Sources, restored.Sources)
        Assert.Equal(admitted.Target, restored.Target)
        Assert.Equal(admitted.Class, restored.Class)
        Assert.Equal(admitted.Role, restored.Role)
        Assert.Equal(admitted.Ordinal, restored.Ordinal)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``A differing or opaque alternative cannot authorize later actuals at the first boundary``(opaque: bool) =
        let supplied = if opaque then "opaque" else "staged"
        let source = """
let declared (first: bool) (second: bool) = second
let staged (first: bool) = fun (second: bool) -> second
let select (opaque: bool -> bool -> bool) (flag: bool) =
    let chosen = if flag then declared else ALTERNATIVE
    chosen (eager true) (eager false)
[<EntryPoint>]
let main _ = ignore select; 0
"""
        let graph = EagerGraph.check (source.Replace("ALTERNATIVE", supplied))
        let markers = EagerGraph.markers graph
        Assert.Equal(2, markers.Length)
        let actual = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.EagerDemand EagerFrontier.Actual) |> Assert.Single
        Assert.Equal(0, actual.Ordinal)
        let pending = graph.Edges |> List.filter (fun edge -> edge.Target = actual.Target && edge.Role = EdgeRole.EagerDemandPending) |> Assert.Single
        Assert.Equal(1, pending.Ordinal)
        let boundaries = (Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph).FirstBoundaries
        let boundary = boundaries[actual.Target]
        Assert.Equal(opaque, not boundary.UnknownOrigins.IsEmpty)
        Assert.Equal((if opaque then 1 else 2), boundary.Targets.Length)
        for target in boundary.Targets do
            Assert.Contains(target.Lambda, actual.Sources)
            for _, _, formal in target.Parameters do Assert.Contains(formal, actual.Sources)
