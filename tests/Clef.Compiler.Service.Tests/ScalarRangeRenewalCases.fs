namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module private ScalarRangeFixture =
    module Establishment = Clef.Compiler.Nanopass.PremiseEstablishment
    let normalize = Establishment.normalize
    let authority = MemoryAccessFixture.stackAuthority.Replace("Name = \"octet\"", "Name = \"uint8\"")
    let source = """module ScalarRanges
[<EntryPoint>]
let main _ =
    let temporary = Array.zeroCreate<int> 1
    let alias = temporary
    let held = 65
    Array.set alias 0 held
    let output = Array.zeroCreate<int> 1
    let observed = Array.get temporary 0
    Array.set output 0 observed
    let text = String.fromBytes output
    String.length text
"""
    let check source = IntrinsicWriteFixture.checkSource authority source
    let original = lazy (check source)
    let read (graph: SemanticGraph) =
        graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.StringByteRead) |> Assert.Single
    let fact (graph: SemanticGraph) =
        let read = read graph
        graph.Edges |> List.filter (fun edge -> edge.Target = read.Target && match edge.Role with EdgeRole.StringByteRange _ -> true | _ -> false) |> Assert.Single
    let prepared () =
        let graph = original.Value.Graph
        let read = read graph
        let row = { read with Role = EdgeRole.StringByteRange(0I, 65I) }
        let retained = graph.Edges |> List.filter (fun edge ->
            not (edge.Target = read.Target && match edge.Role with EdgeRole.StringByteRange _ -> true | _ -> false))
        { graph with Edges = row :: retained }
    let allocation (graph: SemanticGraph) =
        let read = read graph
        let input = match graph.Nodes[read.Target].Kind with SemanticKind.IndexGet(input, _) -> input | other -> failwithf "%A" other
        let rec follow id =
            let node = graph.Nodes[id]
            match node.Kind with
            | SemanticKind.ArrayAllocate _ -> node
            | SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _) -> follow source
            | SemanticKind.Binding(_, false, _, _) -> follow (Assert.Single node.Children)
            | SemanticKind.Sequential values -> follow (List.last values)
            | other -> failwithf "Unexpected current array origin: %A" other
        follow input
    let changedText = "The scalar range of this array read changed after source range settlement."
    let missingText = "The scalar range of this array read lacks its complete current allocation and write premises."
    let expectFailure message (graph: SemanticGraph) =
        let site = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.StringByteRead)
                   |> List.map _.Target |> List.distinct |> Assert.Single
        let normalized, diagnostics = Establishment.normalize graph
        Assert.Contains(diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8404" && diagnostic.Severity = NativeDiagnosticSeverity.Error &&
            diagnostic.Range = graph.Nodes[site].Range && diagnostic.Message = message && List.contains site diagnostic.RelatedNodes)
        Assert.DoesNotContain(normalized.Edges, fun edge ->
            edge.Target = site && match edge.Role with EdgeRole.StringByteRange _ -> true | _ -> false)
        Assert.Equal<NodeId list>(Map.keys graph.Nodes |> Seq.toList, Map.keys normalized.Nodes |> Seq.toList)

type ScalarRangeRenewalCases() =
    [<Fact>]
    member _.``Temporary integer read retains its scalar range after complete source checking`` () =
        let result = ScalarRangeFixture.original.Value
        DimensionalCases.noErrors result
        let fact = ScalarRangeFixture.fact result.Graph
        Assert.Equal(EdgeRole.StringByteRange(0I, 65I), fact.Role)
        let allocation = ScalarRangeFixture.allocation result.Graph
        Assert.Equal<SettledSlot option>(None, Clef.Compiler.PSGSaturation.SemanticGraph.StringByteStorage.element result.Graph allocation.Id)

    [<Fact>]
    member _.``Renewed scalar evidence names current allocation and initialization writes`` () =
        let graph = ScalarRangeFixture.prepared ()
        let renewed, diagnostics = ScalarRangeFixture.normalize graph
        Assert.Empty diagnostics
        let fact = ScalarRangeFixture.fact renewed
        let read = ScalarRangeFixture.read renewed
        Assert.Equal<NodeId list>(read.Sources, fact.Sources)
        let allocation = ScalarRangeFixture.allocation graph
        Assert.Contains(allocation.Id, fact.Sources)
        let construction = graph.Edges |> List.choose (fun edge ->
            match edge.Role with EdgeRole.ArrayAllocationConstruction row when row.Site = allocation.Id -> Some row | _ -> None) |> Assert.Single
        let init = construction.Initialization |> Option.get
        let write = graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.MemoryAccessGuard && List.last edge.Sources = init.Write) |> Assert.Single
        Assert.Contains(write.Target, fact.Sources)
        Assert.Equal<NodeId list>(Map.keys graph.Nodes |> Seq.toList, Map.keys renewed.Nodes |> Seq.toList)

    [<Fact>]
    member _.``Every known alias write contributes to renewed scalar evidence`` () =
        let source = ScalarRangeFixture.source.Replace("    let output =", "    Array.set alias 0 64\n    let output =")
        let result = ScalarRangeFixture.check source
        DimensionalCases.noErrors result
        let fact = ScalarRangeFixture.fact result.Graph
        Assert.Equal(EdgeRole.StringByteRange(0I, 65I), fact.Role)
        let writes = result.Graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && node.Range.Start.Line >= 7 && node.Range.Start.Line <= 8 &&
            match node.Kind with SemanticKind.IndexSet _ -> true | _ -> false) |> Seq.toList
        Assert.Equal(2, writes.Length)
        for write in writes do Assert.Contains(write.Id, fact.Sources)

    [<Theory>]
    [<InlineData(66)>]
    [<InlineData(300)>]
    member _.``Cached scalar parents cannot mask a changed stored value`` (value: int) =
        let graph = ScalarRangeFixture.prepared ()
        let literal = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Literal(NativeLiteral.Int(65L, _)) -> true | _ -> false) |> Assert.Single
        let kind = match literal.Kind with SemanticKind.Literal(NativeLiteral.Int(_, kind)) -> kind | _ -> failwith "literal"
        let changed = { literal with Kind = SemanticKind.Literal(NativeLiteral.Int(int64 value, kind)); ValueRange = Some(ValueRange.point (bigint value)) }
        ScalarRangeFixture.expectFailure ScalarRangeFixture.changedText { graph with Nodes = graph.Nodes.Add(literal.Id, changed) }

    [<Fact>]
    member _.``A changed initialization value invalidates the resident scalar range`` () =
        let graph = ScalarRangeFixture.prepared ()
        let allocation = ScalarRangeFixture.allocation graph
        let construction = graph.Edges |> List.choose (fun edge ->
            match edge.Role with EdgeRole.ArrayAllocationConstruction row when row.Site = allocation.Id -> Some row | _ -> None) |> Assert.Single
        let original = graph.Nodes[construction.Default |> Option.get]
        let kind = match original.Kind with SemanticKind.Literal(NativeLiteral.Int(_, kind)) -> kind | _ -> failwith "default"
        let changed = { original with Kind = SemanticKind.Literal(NativeLiteral.Int(300L, kind)); ValueRange = Some(ValueRange.point 300I) }
        // zeroCreate's source default must still be zero; this mutation breaks
        // construction authority before a new scalar bound can be established.
        ScalarRangeFixture.expectFailure ScalarRangeFixture.missingText { graph with Nodes = graph.Nodes.Add(original.Id, changed) }

    [<Fact>]
    member _.``A missing initialization write cannot justify a bounded scalar read`` () =
        let graph = ScalarRangeFixture.prepared ()
        let allocation = ScalarRangeFixture.allocation graph
        let construction = graph.Edges |> List.choose (fun edge ->
            match edge.Role with EdgeRole.ArrayAllocationConstruction row when row.Site = allocation.Id -> Some row | _ -> None) |> Assert.Single
        let initialization = construction.Initialization |> Option.get
        let guard = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.MemoryAccessGuard && List.last edge.Sources = initialization.Write) |> Assert.Single
        let write = graph.Nodes[guard.Target]
        let changed = { write with Kind = SemanticKind.Literal NativeLiteral.Unit; Children = [] }
        ScalarRangeFixture.expectFailure ScalarRangeFixture.missingText { graph with Nodes = graph.Nodes.Add(write.Id, changed) }

    [<Fact>]
    member _.``Missing allocation construction is an array-premise error at the read`` () =
        let graph = ScalarRangeFixture.prepared ()
        let allocation = ScalarRangeFixture.allocation graph
        let edges = graph.Edges |> List.filter (fun edge ->
            match edge.Role with EdgeRole.ArrayAllocationConstruction row when row.Site = allocation.Id -> false | _ -> true)
        let changed = { graph with Edges = edges }
        ScalarRangeFixture.expectFailure ScalarRangeFixture.missingText changed

    [<Fact>]
    member _.``Scalar renewal is idempotent`` () =
        let first, firstDiagnostics = ScalarRangeFixture.normalize (ScalarRangeFixture.prepared ())
        let second, secondDiagnostics = ScalarRangeFixture.normalize first
        Assert.Empty firstDiagnostics
        Assert.Empty secondDiagnostics
        let rows graph = graph.Edges |> List.map (fun edge -> edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target)
        Assert.Equal<_ list>(rows first, rows second)
        Assert.Equal<NodeId list>(Map.keys first.Nodes |> Seq.toList, Map.keys second.Nodes |> Seq.toList)

    [<Fact>]
    member _.``Duplicate scalar producers cannot supply unique current premises`` () =
        let graph = ScalarRangeFixture.prepared ()
        ScalarRangeFixture.expectFailure ScalarRangeFixture.missingText
            { graph with Edges = ScalarRangeFixture.read graph :: graph.Edges }

    [<Fact>]
    member _.``A missing scalar bound remains a failure on repeated establishment`` () =
        let graph = ScalarRangeFixture.prepared ()
        let site = (ScalarRangeFixture.read graph).Target
        let edges = graph.Edges |> List.filter (fun edge ->
            not (edge.Target = site && match edge.Role with EdgeRole.StringByteRange _ -> true | _ -> false))
        let graph = { graph with Edges = edges }
        ScalarRangeFixture.expectFailure ScalarRangeFixture.missingText graph
        let again, _ = ScalarRangeFixture.normalize graph
        ScalarRangeFixture.expectFailure ScalarRangeFixture.missingText again

    [<Fact>]
    member _.``A new reachable writer invalidates unchanged historical membership`` () =
        let graph = ScalarRangeFixture.prepared ()
        let literal = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Literal(NativeLiteral.Int(65L, _)) -> true | _ -> false) |> Assert.Single
        let writer = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && node.Range.Start.Line = 7 &&
            match node.Kind with SemanticKind.IndexSet _ -> true | _ -> false) |> Assert.Single
        let fresh () = NodeId(Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId ())
        let kind = match literal.Kind with SemanticKind.Literal(NativeLiteral.Int(_, kind)) -> kind | _ -> failwith "literal"
        let addedValue = { literal with Id = fresh (); Kind = SemanticKind.Literal(NativeLiteral.Int(300L, kind)); ValueRange = Some(ValueRange.point 300I) }
        let buffer, index = match writer.Kind with SemanticKind.IndexSet(buffer, index, _) -> buffer, index | _ -> failwith "write"
        let addedWrite = { writer with Id = fresh (); Kind = SemanticKind.IndexSet(buffer, index, addedValue.Id); Children = [buffer; index; addedValue.Id] }
        let continuation = graph.Nodes.Values |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Sequential items -> List.contains writer.Id items | _ -> false) |> Assert.Single
        let items = match continuation.Kind with SemanticKind.Sequential items -> items @ [addedWrite.Id] | _ -> failwith "continuation"
        let continuation = { continuation with Kind = SemanticKind.Sequential items; Children = items }
        let nodes = graph.Nodes.Add(addedValue.Id, addedValue).Add(addedWrite.Id, addedWrite).Add(continuation.Id, continuation)
        Assert.DoesNotContain(addedWrite.Id, (ScalarRangeFixture.read graph).Sources)
        ScalarRangeFixture.expectFailure ScalarRangeFixture.changedText { graph with Nodes = nodes }

    [<Fact>]
    member _.``A separate storage range at the scalar target is checked by its own producer`` () =
        let graph = ScalarRangeFixture.prepared ()
        let marker = ScalarRangeFixture.read graph
        let foreign = { marker with Role = EdgeRole.StringByteRange(0I, 255I); Sources = [marker.Target] }
        let result, diagnostics = ScalarRangeFixture.normalize { graph with Edges = foreign :: graph.Edges }
        let current = ScalarRangeFixture.fact result
        Assert.Equal(EdgeRole.StringByteRange(0I, 65I), current.Role)
        Assert.Equal<NodeId list>((ScalarRangeFixture.read result).Sources, current.Sources)
        Assert.Contains(diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8403" && diagnostic.Range = graph.Nodes[marker.Target].Range &&
            diagnostic.Message = "A string byte read lost the storage evidence of its borrow after the final demand rows.")
