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
        |> Clef.Compiler.Nanopass.NumericSettlement.normalize

    let create number =
        let graph = graphFor 64 number
        let facts = NumericPublication.project graph |> Result.defaultWith (sprintf "%A" >> failwith)
        graph, Assert.Single facts.IndexTransports.Values

type NumericPublicationCases() =
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
