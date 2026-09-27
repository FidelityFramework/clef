namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module MemoryPublication = Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication

module MemoryAccessFixture =
    let stackAuthority =
        IntrinsicWriteFixture.authority
            .Replace("let description =", "let stack = { Name = \"stack\"; Kind = \"stack\"; Capacity = 4096; Alignment = 16; Granularity = 16; Growth = \"down\"; Access = \"rw\"; Base = None }\nlet description =")
            .Replace("Spaces = [| rodata |]", "Spaces = [| rodata; stack |]")
    let source body = "module MemoryFixture\n[<EntryPoint>]\nlet main _ =\n" + body
    let check body = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.authority (source body)
    let admittedSource authority source =
        let result = IntrinsicWriteFixture.checkSource authority source
        DimensionalCases.noErrors result
        match MemoryPublication.project result.Graph with
        | Ok facts -> result.Graph, facts
        | Error failures -> failwithf "Memory publication failed: %A" failures
    let admitted body = admittedSource IntrinsicWriteFixture.authority (source body)
    let readonlyArray = source "    let values = [| 7; 11 |]\n    values.[1]\n"
    let mutableArray = source "    let values = [| 7; 11 |]\n    values.[0] <- 19\n    values.[1]\n"
    let cellAddress = source "    let mutable value = 7\n    let _ = eager (&value)\n    value <- 11\n    value\n"
    let elementAddress = source "    let values = [| 7; 11 |]\n    let _ = eager (&values.[1])\n    values.[0]\n"
    let fieldAddress = "module MemoryFixture\ntype Cell = { Other: int; mutable Value: int }\n[<EntryPoint>]\nlet main _ =\n    let cell = { Other = 11; Value = 7 }\n    let _ = eager (&cell.Value)\n    cell.Value\n"

type MemoryAccessCases() =
    [<Fact>]
    member _.``Array access publishes actual source bounds and the exact success continuation`` () =
        let graph, facts = MemoryAccessFixture.admitted "    let values = [| 7; 11 |]\n    values.[1]\n"
        let access = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.ArrayAccess fact -> Some fact | _ -> None) |> Assert.Single
        let guard = access.Bounds.Requirement
        Assert.Equal(access.Site, guard.Continuation)
        Assert.Equal(SemanticKind.Sequential [guard.Site;access.Site], graph.Nodes[guard.Frontier].Kind)
        Assert.Equal(SemanticKind.Require(guard.Condition,guard.Diagnostic), graph.Nodes[guard.Site].Kind)
        Assert.Contains(graph.Edges, fun edge -> edge.Role = EdgeRole.MemoryAccessGuard && edge.Target = access.Site)
        let literal = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.ArrayLiteral fact -> Some fact | _ -> None) |> Assert.Single
        Assert.Equal(2, literal.Length)
        Assert.True(literal.Initializers.IsSome)
        match literal.Residence with MemoryResidence.ImmutableProgram _ -> () | _ -> failwith "A closed readonly literal requires immutable image residence."

    [<Fact>]
    member _.``Changing the guard rejects publication without synthesizing a replacement guard`` () =
        let graph, facts = MemoryAccessFixture.admitted "    let values = [| 7; 11 |]\n    values.[1]\n"
        let access = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.ArrayAccess fact -> Some fact | _ -> None) |> Assert.Single
        let guard = graph.Nodes[access.Bounds.Upper]
        let changed = { guard with Kind = SemanticKind.Literal(NativeLiteral.Bool true); Children = [] }
        let altered = { graph with Nodes = graph.Nodes.Add(guard.Id, changed) }
        match MemoryPublication.project altered with Error _ -> () | Ok _ -> failwith "Changed executable bounds cannot retain admitted memory facts."
        match MemoryPublication.project graph with Ok _ -> () | Error failures -> failwithf "Original publication changed: %A" failures

    [<Fact>]
    member _.``Address of mutable local denotes its actual cell without a scalar copy`` () =
        let graph, facts = MemoryAccessFixture.admittedSource IntrinsicWriteFixture.authority MemoryAccessFixture.cellAddress
        let address = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.Address fact -> Some fact | _ -> None) |> Assert.Single
        match address.Place with
        | MemoryPlace.MutableCell binding ->
            Assert.Equal(SemanticKind.CellAddress binding, graph.Nodes[address.Site].Kind)
            Assert.Empty(graph.Nodes[address.Site].Children)
            Assert.True(address.Element.IsSome && address.ElementBytes.IsSome)
        | _ -> failwith "A mutable local address must preserve its binding cell."

    [<Fact>]
    member _.``Mutable array uses source proved stack residence and separately guarded read and write`` () =
        let _, facts = MemoryAccessFixture.admittedSource MemoryAccessFixture.stackAuthority MemoryAccessFixture.mutableArray
        let literal = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.ArrayLiteral fact -> Some fact | _ -> None) |> Assert.Single
        match literal.Residence with MemoryResidence.Stack _ -> () | _ -> failwith "A mutated local array cannot be shared readonly image storage."
        let accesses = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.ArrayAccess fact -> Some fact | _ -> None) |> Seq.toList
        Assert.Equal(2, accesses.Length)
        Assert.Contains(accesses, fun access -> access.Value.IsSome)
        Assert.Contains(accesses, fun access -> access.Value.IsNone)
        Assert.Equal(2, accesses |> List.map _.Bounds.Requirement.Site |> List.distinct |> List.length)

    [<Fact>]
    member _.``Array element address retains exact nonzero index and its own guard`` () =
        let graph, facts = MemoryAccessFixture.admittedSource MemoryAccessFixture.stackAuthority MemoryAccessFixture.elementAddress
        let address = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.Address fact -> Some fact | _ -> None) |> Assert.Single
        match address.Place with
        | MemoryPlace.ArrayElement(buffer,index,bounds) ->
            Assert.Equal(SemanticKind.ElementAddress(buffer,index), graph.Nodes[address.Site].Kind)
            Assert.Equal(Some(ValueRange.point 1I), graph.Nodes[index].ValueRange)
            Assert.Equal(address.Site, bounds.Requirement.Continuation)
            Assert.True(address.ElementBytes.IsSome)
        | _ -> failwith "The array address must retain the actual indexed place."

    [<Fact>]
    member _.``Mutable record field address retains complete receiver extent and exact field offset`` () =
        let _, facts = MemoryAccessFixture.admittedSource MemoryAccessFixture.stackAuthority MemoryAccessFixture.fieldAddress
        let address = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.Address fact -> Some fact | _ -> None) |> Assert.Single
        match address.Place with
        | MemoryPlace.RecordField(_,bytes,field) ->
            Assert.Equal("Value",field.Name)
            Assert.True(bytes > 0 && field.Offset.IsSome && field.Size.IsSome)
            Assert.True(field.Offset.Value > 0)
            Assert.True(field.Offset.Value + field.Size.Value <= bytes)
            Assert.Equal(field.Size,address.ElementBytes)
        | _ -> failwith "The mutable field requires its receiver's actual byte storage place."

    [<Fact>]
    member _.``Effectful ordinary array initializers cannot be converted into eager stores`` () =
        let result = MemoryAccessFixture.check "    let mutable value = 0\n    let values = [| (value <- 1; value) |]\n    values.[0]\n"
        match MemoryPublication.project result.Graph with
        | Error failures -> Assert.Contains(failures, fun failure -> failure.Reason.Contains("demand and memoization"))
        | Ok _ -> failwith "Ordinary effectful array initialization needs its owning demand contract."

    [<Fact>]
    member _.``Readonly image is rejected when the complete array family contains a store`` () =
        let result = MemoryAccessFixture.check "    let values = [| 7; 11 |]\n    values.[0] <- 19\n    values.[1]\n"
        match MemoryPublication.project result.Graph with
        | Error failures -> Assert.Contains(failures, fun failure -> failure.Reason.Contains("stack space"))
        | Ok _ -> failwith "The declared fixture has no writable array residence."

    [<Theory>]
    [<InlineData("zeroCreate")>]
    [<InlineData("sub")>]
    [<InlineData("blit")>]
    member _.``Array construction cannot invent writable residence when the platform lacks stack storage`` operation =
        let body =
            match operation with
            | "zeroCreate" -> "    let values: int array = Array.zeroCreate 2\n    let _ = eager values\n    0\n"
            | "sub" -> "    let values = [| 7; 11 |]\n    let copy = Array.sub values 0 1\n    let _ = eager copy\n    0\n"
            | _ -> "    let source = [| 7; 11 |]\n    let target = [| 0; 0 |]\n    Array.blit source 0 target 0 2\n    target.[0]\n"
        let result = MemoryAccessFixture.check body
        match MemoryPublication.project result.Graph with
        | Error failures ->
            Assert.True(failures |> List.exists (fun failure -> failure.Reason.Contains("stack space") || failure.Reason.Contains("writable stack")),
                        sprintf "Expected owning %s residence refusal. Publication: %A; source diagnostics: %A" operation failures result.Diagnostics)
        | Ok _ -> failwith "Array construction acquired storage without a writable source residence."
