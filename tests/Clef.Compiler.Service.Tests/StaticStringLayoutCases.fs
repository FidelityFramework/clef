namespace Clef.Compiler.Service.Tests

open System.Diagnostics
open System.Text
open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module StaticLayout = Clef.Compiler.PSGSaturation.SemanticGraph.StaticStringLayout
module StaticDeclaration = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
module StaticDischarge = Clef.Compiler.Nanopass.ObligationDischarge
module StaticElaboration = Clef.Compiler.Nanopass.ObligationElaboration

module private StaticEvidence =
    let template = """type MemorySpace = { Name: string; Kind: string; Capacity: int; Alignment: int; Granularity: int; Growth: string; Access: string; Base: int option }
type PlatformDescription = { Id: string; Spaces: MemorySpace array }
let rodata = { Name = "rodata"; Kind = "rodata"; Capacity = %d; Alignment = 16; Granularity = 16; Growth = "fixed"; Access = "r"; Base = %s }
let description = { Id = "layout-test"; Spaces = [| rodata |] }
let consume (left: string) (right: string) = if left = right then 1 else 0
[<EntryPoint>]
let main _ = consume "ascii" "λ🙂" + consume "" "a\000b" + consume "ascii" ""
"""
    let source capacity baseValue = template.Replace("%d", string capacity).Replace("%s", baseValue)

    let check () =
        let result = DimensionalCases.check (source 64 "None")
        DimensionalCases.noErrors result
        result.Graph

    let layout graph =
        StaticDischarge.ofGraph graph |> List.find (fun obligation -> obligation.Id = "layout_user_strings")

    let expectSolver expected obligation =
        let start = ProcessStartInfo("cvc5")
        start.ArgumentList.Add "--lang=smt2"
        start.ArgumentList.Add "--tlimit-per=2000"
        start.RedirectStandardInput <- true
        start.RedirectStandardOutput <- true
        start.RedirectStandardError <- true
        start.UseShellExecute <- false
        use solver = new Process(StartInfo = start)
        Assert.True(solver.Start())
        let output, errors = solver.StandardOutput.ReadToEndAsync(), solver.StandardError.ReadToEndAsync()
        solver.StandardInput.Write(StaticDischarge.smtLib [obligation])
        solver.StandardInput.Close()
        if not (solver.WaitForExit 5000) then
            solver.Kill(true)
            failwith "Static storage solver timed out"
        Assert.True(solver.ExitCode = 0, errors.GetAwaiter().GetResult())
        Assert.Equal(expected, output.GetAwaiter().GetResult().Trim())

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "StaticStringLayout")>]
type StaticStringLayoutTests() =
    [<Fact>]
    member _.``BAREWire settles exact UTF8 views with sentinels padding and duplicate contributors``() =
        let graph = StaticEvidence.check ()
        let pool = graph.StaticStringPool |> Option.defaultWith (fun () -> failwith "No BAREWire pool")
        // This self-contained fixture also carries reachable declaration strings.
        // Check the exact graph-wide set instead of guessing its incidental order.
        let expectedContents = graph.Nodes.Values |> Seq.choose (fun node ->
            if not node.IsReachable then None
            else match node.Kind with SemanticKind.Literal(NativeLiteral.String content) -> Some content | _ -> None) |> Set.ofSeq
        Assert.Equal<Set<string>>(expectedContents, pool.Entries |> List.map (fun entry -> entry.Content) |> Set.ofList)
        Assert.Equal(expectedContents.Count, pool.Entries.Length)
        for content in ["ascii"; "λ🙂"; ""; "a\000b"] do Assert.Contains(content, expectedContents)
        let expectedUsed = expectedContents |> Seq.sumBy (fun content -> Encoding.UTF8.GetByteCount content + 1)
        Assert.Equal(((expectedUsed + 15) / 16) * 16, pool.Size)
        Assert.Equal(16, pool.Alignment)
        Assert.Equal(expectedUsed, pool.UsedSize)
        let bytes = List.toArray pool.Bytes
        Assert.Equal(pool.Size, bytes.Length)
        for entry in pool.Entries do
            let expected = Array.append (Encoding.UTF8.GetBytes entry.Content) [|0uy|]
            Assert.Equal<byte>(expected, bytes[entry.Offset .. entry.Offset + entry.StorageLength - 1])
            Assert.Equal(expected.Length - 1, entry.Length)
            let contributing = graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && node.Kind = SemanticKind.Literal(NativeLiteral.String entry.Content)) |> Seq.map (fun node -> node.Id) |> Set.ofSeq
            Assert.Equal<Set<NodeId>>(contributing, Set.ofList entry.NodeIds)
        Assert.True((pool.Entries |> List.find (fun entry -> entry.Content = "ascii")).NodeIds.Length >= 2)
        Assert.True(bytes[pool.UsedSize ..] |> Array.forall ((=) 0uy))
        let obligation = StaticEvidence.layout graph
        Assert.Equal("static-storage-layout", obligation.Kind)
        let query = StaticDischarge.smtLib [obligation]
        Assert.DoesNotContain("declare-const b", query)
        StaticEvidence.expectSolver "unsat" obligation

    [<Fact>]
    member _.``Concrete layout counterexamples remain satisfiable rather than assumed away``() =
        let graph = StaticEvidence.check ()
        let obligation = StaticEvidence.layout graph
        let pool = graph.StaticStringPool.Value
        let original = pool.Entries |> List.map (fun entry -> entry.Offset, entry.StorageLength, 1)
        let body slots used allocated alignment capacity spaceAlignment granularity =
            { obligation with Body = ObligationBody.StaticStorageLayout(slots, used, allocated, alignment, capacity, spaceAlignment, granularity) }
        let firstOffset, _, _ = original.Head
        let overlap = original |> List.mapi (fun i (offset, length, alignment) -> if i = 1 then firstOffset, length, alignment else offset, length, alignment)
        for broken in [
            body overlap pool.UsedSize pool.Size pool.Alignment pool.Capacity pool.SpaceAlignment pool.Granularity
            body original pool.UsedSize pool.Size pool.Alignment 17L pool.SpaceAlignment pool.Granularity
            body original pool.UsedSize pool.Size 1 pool.Capacity pool.SpaceAlignment pool.Granularity
            body original pool.UsedSize (pool.Size - 1) pool.Alignment pool.Capacity pool.SpaceAlignment pool.Granularity
            body original pool.UsedSize pool.Size pool.Alignment pool.Capacity pool.SpaceAlignment 0
        ] do StaticEvidence.expectSolver "sat" broken

    [<Fact>]
    member _.``Invalid platform storage facts block settlement without fallback``() =
        for source in [StaticEvidence.source 17 "None"; StaticEvidence.source 64 "Some 4096"] do
            let result = DimensionalCases.check source
            Assert.True(result.Graph.StaticStringPool.IsNone)
            Assert.Contains(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8206" && diagnostic.Message.Contains "static string storage")
            Assert.DoesNotContain(StaticDischarge.ofGraph result.Graph, fun obligation -> obligation.Id = "layout_user_strings")
        let valid = StaticEvidence.check ()
        let declarationNode = valid.StaticStringPool.Value.DeclarationNode
        let original = valid.Nodes[declarationNode]
        let fields, typeName = match original.Kind with SemanticKind.RecordExpr(fields, name) -> fields, name | _ -> failwith "Expected memory space"
        for missing in ["Base"; "Growth"; "Granularity"] do
            let damaged = { original with Kind = SemanticKind.RecordExpr(fields |> List.filter (fun (name, _) -> name <> missing), typeName) }
            let graph = { valid with Nodes = valid.Nodes |> Map.add damaged.Id damaged }
            Assert.NotEmpty((StaticDeclaration.read graph).Findings)
            let settled, _ = StaticLayout.settle graph
            Assert.True(settled.StaticStringPool.IsNone)

    [<Fact>]
    member _.``Entry point layout cites the declaration and every contributing literal``() =
        let graph = StaticEvidence.check ()
        let entry = graph.Nodes.Values |> Seq.find (fun node -> match node.Kind with SemanticKind.Binding("main", _, _, _) -> true | _ -> false)
        let enrichment, _ = StaticElaboration.elaborateSettled graph
        let node = enrichment.NewNodes |> List.find (fun node -> match node.Kind with SemanticKind.Obligation ob -> ob.Id = "layout_user_strings" | _ -> false)
        let sources = enrichment.NewEdges |> List.find (fun edge -> edge.Target = node.Id) |> fun edge -> edge.Sources
        Assert.Equal(entry.Range, node.Range)
        Assert.Contains(entry.Id, sources)
        let pool = graph.StaticStringPool.Value
        Assert.Contains(pool.DeclarationNode, sources)
        for id in pool.Entries |> List.collect (fun entry -> entry.NodeIds) do Assert.Contains(id, sources)
