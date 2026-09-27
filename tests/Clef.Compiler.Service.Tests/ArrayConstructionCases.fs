namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

module private ArrayConstructionFixture =
    let body = function
        | "zeroCreate" -> "    let values: int array = eager (Array.zeroCreate 3)\n    values.[0] + values.[2]\n"
        | "sub" -> "    let values = [| 7; 11; 13 |]\n    let copied = eager (Array.sub values 1 2)\n    values.[1] <- 19\n    copied.[0]\n"
        | _ -> "    let values = [| 7; 11; 13; 17 |]\n    Array.blit values 0 values 1 3\n    values.[3]\n"

    let admitted operation =
        MemoryAccessFixture.admittedSource MemoryAccessFixture.stackAuthority (MemoryAccessFixture.source (body operation))

    let require (graph: SemanticGraph) (requirement: RequirementWitness) =
        Assert.Equal(SemanticKind.Require(requirement.Condition,requirement.Diagnostic),graph.Nodes[requirement.Site].Kind)
        Assert.Equal(SemanticKind.Sequential[requirement.Site;requirement.Continuation],graph.Nodes[requirement.Frontier].Kind)

type ArrayConstructionCases() =
    [<Theory>]
    [<InlineData("zeroCreate")>]
    [<InlineData("sub")>]
    member _.``Proven empty construction retains zero extent without phantom copy or initialization loops`` operation =
        let body =
            if operation="zeroCreate" then "    let values: int array = eager (Array.zeroCreate 0)\n    values.Length\n"
            else "    let values = [| 7; 11 |]\n    let copied = eager (Array.sub values 1 0)\n    copied.Length\n"
        let graph, facts = MemoryAccessFixture.admittedSource MemoryAccessFixture.stackAuthority (MemoryAccessFixture.source body)
        let allocation = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.ArrayAllocation fact -> Some fact | _ -> None) |> Assert.Single
        Assert.Equal(0I,allocation.MinimumCount)
        Assert.Equal(0I,allocation.MaximumCount)
        if operation="sub" then
            let copy = Assert.Single facts.ArrayCopies.Values
            Assert.True(copy.Loop.IsNone && copy.Read.IsNone && copy.Write.IsNone)
            Assert.NotEmpty copy.Requirements
        else
            let construction = graph.Edges |> List.choose (fun edge ->
                match edge.Role with EdgeRole.ArrayAllocationConstruction construction -> Some construction | _ -> None) |> Assert.Single
            Assert.True(construction.Initialization.IsNone)

    [<Fact>]
    member _.``Unforced unused construction retains lazy default without demanding writable storage`` () =
        let _, facts = MemoryAccessFixture.admitted "    let unused: int array = Array.zeroCreate 3\n    0\n"
        Assert.DoesNotContain(facts.Operations.Values,fun operation -> match operation with MemoryWitnessOperation.ArrayAllocation _ -> true | _ -> false)
        Assert.Empty facts.ArrayCopies

    [<Fact>]
    member _.``Zero initialization is source storage followed by an explicit guarded loop`` () =
        let graph, facts = ArrayConstructionFixture.admitted "zeroCreate"
        let allocation = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.ArrayAllocation fact -> Some fact | _ -> None) |> Assert.Single
        Assert.Equal(3I,allocation.MinimumCount)
        Assert.Equal(3I,allocation.MaximumCount)
        Assert.Equal(SemanticKind.ArrayAllocate allocation.Count,graph.Nodes[allocation.Site].Kind)
        match allocation.Residence with MemoryResidence.Stack _ -> () | _ -> failwith "Local zeroCreate lacks writable source residence."
        ArrayConstructionFixture.require graph allocation.Requirement
        let construction =
            graph.Edges |> List.choose (fun edge ->
                match edge.Role with
                | EdgeRole.ArrayAllocationConstruction construction when construction.Site=allocation.Site -> Some construction
                | _ -> None) |> Assert.Single
        let zero = construction.Default |> Option.defaultWith (fun () -> failwith "Source initialization lost its default value.")
        match graph.Nodes[zero].Kind with
        | SemanticKind.Literal(NativeLiteral.Int(0L,_)) -> ()
        | other -> failwithf "Integer zeroCreate lost its native zero value: %A" other
        let initialization = construction.Initialization |> Option.defaultWith (fun () -> failwith "Nonempty zeroCreate lost its source initialization loop.")
        match graph.Nodes[initialization.Loop].Kind with SemanticKind.WhileLoop _ -> () | _ -> failwith "Initialization must remain an ordinary source loop."
        let access = facts.Operations.Values |> Seq.choose (function
            | MemoryWitnessOperation.ArrayAccess access when access.Bounds.Requirement.Frontier=initialization.Write -> Some access
            | _ -> None) |> Assert.Single
        Assert.True(access.Value.IsSome)
        ArrayConstructionFixture.require graph access.Bounds.Requirement
        Assert.Contains(graph.Edges,fun edge -> edge.Role=EdgeRole.MemoryAccessGuard && edge.Target=access.Site && List.tryLast edge.Sources=Some initialization.Write)

    [<Theory>]
    [<InlineData("sub",1)>]
    [<InlineData("blit",2)>]
    member _.``Array copies publish exact source loops guarded reads writes and fresh storage`` operation count =
        let graph, facts = ArrayConstructionFixture.admitted operation
        Assert.Equal(count,facts.ArrayCopies.Count)
        for copy in facts.ArrayCopies.Values do
            Assert.NotEqual(copy.Source,copy.Destination)
            Assert.NotEmpty copy.Requirements
            for requirement in copy.Requirements do ArrayConstructionFixture.require graph requirement
            let loop = copy.Loop |> Option.defaultWith (fun () -> failwith "Nonempty source copy lost its loop.")
            match graph.Nodes[loop].Kind with SemanticKind.WhileLoop _ -> () | _ -> failwith "Copy must remain an ordinary source loop."
            let read = copy.Read |> Option.defaultWith (fun () -> failwith "Copy lost its source read.")
            let write = copy.Write |> Option.defaultWith (fun () -> failwith "Copy lost its source write.")
            Assert.True(read.Value.IsNone && write.Value.IsSome)
            ArrayConstructionFixture.require graph read.Bounds.Requirement
            ArrayConstructionFixture.require graph write.Bounds.Requirement
            Assert.Contains(loop,copy.Participants)
            Assert.Contains(read.Site,copy.Participants)
            Assert.Contains(write.Site,copy.Participants)
        let snapshot = facts.ArrayCopies.Values |> Seq.filter (fun copy -> copy.Allocation.IsSome) |> Assert.Single
        match facts.Operations[snapshot.Allocation.Value] with
        | MemoryWitnessOperation.ArrayAllocation allocation ->
            match allocation.Residence with MemoryResidence.Stack _ -> () | _ -> failwith "Copy lacks fresh source-owned local storage."
        | _ -> failwith "Copy allocation lost its source memory contract."
        if operation="blit" then
            let constructions = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.ArrayCopyConstruction fact -> Some fact | _ -> None)
            let writeback = constructions |> List.filter (fun copy -> copy.Allocation.IsNone) |> Assert.Single
            Assert.Equal(snapshot.Site,writeback.Source.Actual)

    [<Theory>]
    [<InlineData("allocation-construction")>]
    [<InlineData("copy-construction")>]
    [<InlineData("copy-receipt")>]
    [<InlineData("allocation-proof")>]
    [<InlineData("access-guard")>]
    [<InlineData("guard")>]
    member _.``Copy publication retracts missing construction receipt or changed executable guard`` defect =
        let graph, facts = ArrayConstructionFixture.admitted "sub"
        let copy = Assert.Single facts.ArrayCopies.Values
        let graph =
            if defect="guard" then
                let requirement = copy.Requirements.Head
                let predicate = graph.Nodes[requirement.Condition]
                { graph with Nodes=graph.Nodes.Add(predicate.Id,{predicate with Kind=SemanticKind.Literal(NativeLiteral.Bool true);Children=[]}) }
            else
                let keep (edge:Hyperedge) =
                    match defect,edge.Role with
                    | "allocation-construction",EdgeRole.ArrayAllocationConstruction construction -> Some construction.Site <> copy.Allocation
                    | "copy-construction",EdgeRole.ArrayCopyConstruction construction -> construction.Site <> copy.Site
                    | "copy-receipt",EdgeRole.MemoryArrayCopy receipt -> receipt.Site <> copy.Site
                    | "allocation-proof",EdgeRole.MemoryProof proof -> Some proof.Site <> copy.Allocation
                    | "access-guard",EdgeRole.MemoryAccessGuard -> Some edge.Target <> (copy.Read |> Option.map _.Site)
                    | _ -> true
                let retained = graph.Edges |> List.filter keep
                Assert.True(retained.Length < graph.Edges.Length,"Retraction fixture did not remove its named source premise.")
                { graph with Edges=retained }
        match Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication.project graph with
        | Error failures when defect="guard" ->
            Assert.Contains(failures,fun failure ->
                failure.Reason.Contains("PSG settlement (OrdinaryDemand)") &&
                failure.Reason.Contains("do not match the current complete use proof") &&
                not (Set.isEmpty failure.Participants) && failure.Occurrence.IsSome)
        | Error failures -> Assert.Contains(failures,fun failure -> failure.Reason.Contains("premises changed") || failure.Reason.Contains("rewrite record is inconsistent"))
        | Ok _ -> failwith "A damaged source copy retained passive publication."
