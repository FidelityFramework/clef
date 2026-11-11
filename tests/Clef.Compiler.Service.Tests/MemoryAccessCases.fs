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
    [<Theory>]
    [<InlineData("for index = 3 to 2 do", "        values.[index] <- 300")>]
    [<InlineData("for index = 0 downto 1 do", "        values.[index] <- 300")>]
    [<InlineData("while false do", "        values.[99] <- 300")>]
    [<InlineData("if false then", "        values.[99] <- 300")>]
    member _.``Source dead bodies are removed before numeric and memory settlement`` (control: string, body: string) =
        let source = MemoryAccessFixture.source ("    let values = [| 37 |]\n    " + control + "\n" + body + "\n    values.[0]\n")
        let graph,_ = MemoryAccessFixture.admittedSource MemoryAccessFixture.stackAuthority source
        let numeric = Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph
        Assert.True(Result.isOk numeric,sprintf "%A" numeric)
        Assert.DoesNotContain(graph.Nodes.Values,fun node -> node.IsReachable && match node.Kind with SemanticKind.WhileLoop _ | SemanticKind.IndexSet _ -> true | _ -> false)
        let published = Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph |> Result.defaultWith (sprintf "%A" >> failwith)
        Assert.Empty(Fidelity.PSG.Integrity.check published)

    [<Fact>]
    member _.``Empty loop bounds retain their ordered writes`` () =
        let source = MemoryAccessFixture.source "    let mutable value = 0\n    for index = (value <- 11; 3) to (value <- 37; 2) do\n        value <- 99\n    value\n"
        let graph,facts = MemoryAccessFixture.admittedSource MemoryAccessFixture.stackAuthority source
        Assert.DoesNotContain(graph.Nodes.Values,fun node -> node.IsReachable && match node.Kind with SemanticKind.WhileLoop _ -> true | _ -> false)
        let cell = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.LocalScalar row when row.Writes.Length=2 -> Some row | _ -> None) |> Assert.Single
        Assert.Equal<int64 list>([11L;37L],cell.Writes |> List.map (fun (_,value) -> match graph.Nodes[value].Kind with SemanticKind.Literal(NativeLiteral.Int(value,_)) -> value | _ -> failwith "source write") |> List.sort)

    [<Theory>]
    [<InlineData("0 to 0")>]
    [<InlineData("2 downto 0")>]
    [<InlineData("1 to limit")>]
    member _.``Live and mutable-bound loops are not pruned`` (range: string) =
        let source = MemoryAccessFixture.source ("    let mutable limit = 0\n    limit <- 2\n    let mutable value = 0\n    for index = " + range + " do\n        value <- 37\n    value\n")
        let graph,_ = MemoryAccessFixture.admittedSource MemoryAccessFixture.stackAuthority source
        let loop = graph.Nodes.Values |> Seq.filter(fun node -> node.IsReachable && match node.Kind with SemanticKind.WhileLoop _ -> true | _ -> false) |> Assert.Single
        let poisoned = {graph with Nodes=graph.Nodes.Add(loop.Id,{loop with ValueRange=Some ValueRange.Empty})}
        let rewritten = Clef.Compiler.Nanopass.DeadBodies.normalize poisoned
        Assert.True(match rewritten.Nodes[loop.Id].Kind with SemanticKind.WhileLoop _ -> true | _ -> false)

    [<Theory>]
    [<InlineData("true",37)>]
    [<InlineData("false",19)>]
    member _.``Constant source branches retain the selected result`` (guard: string, expected: int) =
        let source = MemoryAccessFixture.source ("    if " + guard + " then 37 else 19\n")
        let graph,_ = MemoryAccessFixture.admittedSource MemoryAccessFixture.stackAuthority source
        let selected = graph.Nodes.Values |> Seq.filter(fun node -> node.IsReachable && match node.Kind with SemanticKind.Literal(NativeLiteral.Int(value,_)) -> value=19L || value=37L | _ -> false) |> Assert.Single
        Assert.True(match selected.Kind with SemanticKind.Literal(NativeLiteral.Int(value,_)) -> value=int64 expected | _ -> false)

    [<Fact>]
    member _.``Negation does not decide deadness before overflow settlement`` () =
        let source = MemoryAccessFixture.source "    let minimum: int = -2147483648\n    if -minimum < 0 then 37 else 2\n"
        let result = IntrinsicWriteFixture.checkSource MemoryAccessFixture.stackAuthority source
        Assert.Contains(result.Graph.Nodes.Values,fun node -> node.IsReachable && match node.Kind with SemanticKind.IfThenElse _ -> true | _ -> false)

    [<Fact>]
    member _.``Dead source bodies are still type checked`` () =
        let source = MemoryAccessFixture.source "    for index = 3 to 2 do\n        let broken: bool = 1\n        ()\n    37\n"
        let result = IntrinsicWriteFixture.checkSource MemoryAccessFixture.stackAuthority source
        Assert.Contains(result.Diagnostics,fun diagnostic -> diagnostic.Severity = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.NativeDiagnosticSeverity.Error)

    [<Fact>]
    member _.``Local scalar cells and for counters publish explicit stack accounts`` () =
        let source = MemoryAccessFixture.source "    let mutable total = 0\n    for index = 0 to 2 do\n        total <- index\n    if total = 2 then 37 else 1\n"
        let graph, facts = MemoryAccessFixture.admittedSource MemoryAccessFixture.stackAuthority source
        let locals = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.LocalScalar row -> Some row | _ -> None) |> Seq.toList
        Assert.Equal(2, locals.Length)
        let published = Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph |> Result.defaultWith (sprintf "%A" >> failwith)
        Assert.Empty(Fidelity.PSG.Integrity.check published)
        for row in locals do
            Assert.True(match row.Residence with MemoryResidence.Stack _ -> true | _ -> false)
            Assert.NotEmpty row.Reads
            Assert.NotEmpty row.Writes
            let proof = [row.Layout;row.Capacity] |> List.map (fun id -> match graph.Nodes[id].Kind with SemanticKind.Obligation info -> info.Body | _ -> failwith "Missing source proof")
            Assert.Contains(ObligationBody.CapacityFits(int64 row.Bytes,4096L),proof)
            Assert.Contains(ObligationBody.ContinuationLayout([0,row.Bytes,row.Alignment],row.Bytes,row.Alignment),proof)
            let initial = graph.Nodes[row.Initializer]
            let changed = {graph with Nodes=graph.Nodes.Add(initial.Id,{initial with Kind=SemanticKind.Literal(NativeLiteral.Bool true)})}
            Assert.True(MemoryPublication.project changed |> Result.isError)

    [<Fact>]
    member _.``Local scalar permission is absent without stack authority or for addressed cells`` () =
        let source = MemoryAccessFixture.source "    let mutable value = 7\n    value <- 11\n    if value = 11 then 37 else 1\n"
        for authority,text in [IntrinsicWriteFixture.authority,source;MemoryAccessFixture.stackAuthority,MemoryAccessFixture.cellAddress] do
            let _,facts = MemoryAccessFixture.admittedSource authority text
            Assert.DoesNotContain(facts.Operations.Values,fun row -> match row with MemoryWitnessOperation.LocalScalar _ -> true | _ -> false)

    [<Fact>]
    member _.``Snapshot stores publish the exact adapted value while retaining its guarded evaluation`` () =
        let source = "module StringSnapshots\n[<EntryPoint>]\nlet main _ =\n    let text = \"A\\000B\"\n    let first = eager (String.toBytes text)\n    let second = eager (String.toBytes text)\n    first.[0] <- 512\n    if second.[0] = 65 && first.[0] = 512 then 0 else 1\n"
        let graph, facts = MemoryAccessFixture.admittedSource MemoryAccessFixture.stackAuthority source
        let stores = facts.Operations.Values |> Seq.choose (function
            | MemoryWitnessOperation.ArrayAccess ({ Value = Some _; Adaptation = Some _ } as access) -> Some access
            | _ -> None) |> Seq.toList
        Assert.Equal(2, stores.Length)
        for access in stores do
            let value, meet = access.Value.Value, access.Adaptation.Value
            Assert.Equal(value, meet.Operand)
            Assert.Equal(access.Site, meet.Consumer)
            Assert.Contains(meet, graph.Codata.Value.Meets[access.Site])
            Assert.Equal(MeetKind.ExtendUnsigned, meet.Adapt)
            Assert.True(meet.From < meet.To)
            let evaluation = match graph.Nodes[access.Site].Kind with
                             | SemanticKind.IndexSet(_, _, evaluation) -> evaluation
                             | other -> failwithf "Store lost its source operation: %A" other
            Assert.NotEqual(evaluation, value)
            Assert.Contains(evaluation, access.Participants)
            Assert.Contains(value, access.Participants)
            match graph.Nodes[evaluation].Kind with
            | SemanticKind.Sequential [_; _; required; result] ->
                Assert.Equal(value, result)
                let read = match facts.Operations[result] with
                           | MemoryWitnessOperation.ArrayAccess read -> read
                           | other -> failwithf "Snapshot value lost its source read: %A" other
                Assert.Equal(required, read.Bounds.Requirement.Site)
                Assert.Equal(evaluation, read.Bounds.Requirement.Frontier)
            | other -> failwithf "Snapshot value lost its guarded evaluation: %A" other

    [<Fact>]
    member _.``Array access publishes actual source bounds and the exact success continuation`` () =
        let graph, facts = MemoryAccessFixture.admitted "    let values = [| 7; 11 |]\n    values.[1]\n"
        let access = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.ArrayAccess fact -> Some fact | _ -> None) |> Assert.Single
        let guard = access.Bounds.Requirement
        Assert.Equal(access.Site, guard.Continuation)
        Assert.Equal(SemanticKind.Sequential [access.Buffer;access.Index;guard.Site;access.Site], graph.Nodes[guard.Frontier].Kind)
        Assert.Equal(SemanticKind.Require(guard.Condition,guard.Diagnostic), graph.Nodes[guard.Site].Kind)
        Assert.Contains(graph.Edges, fun edge -> edge.Role = EdgeRole.MemoryAccessGuard && edge.Target = access.Site)
        let literal = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.ArrayLiteral fact -> Some fact | _ -> None) |> Assert.Single
        Assert.Equal(2, literal.Length)
        Assert.True(literal.Initializers.IsSome)
        match literal.Residence with MemoryResidence.ImmutableProgram _ -> () | _ -> failwith "A closed readonly literal requires immutable image residence."

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Array guard operand order is part of its source authority`` (omit: bool) =
        let graph, facts = MemoryAccessFixture.admitted "    let values = [| 7; 11 |]\n    values.[1]\n"
        let access = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.ArrayAccess fact -> Some fact | _ -> None) |> Assert.Single
        let guard = access.Bounds.Requirement
        let frontier = graph.Nodes[guard.Frontier]
        let ordered = if omit then [guard.Site;access.Site] else [access.Index;access.Buffer;guard.Site;access.Site]
        let altered = {graph with Nodes = graph.Nodes.Add(frontier.Id,{frontier with Kind = SemanticKind.Sequential ordered; Children = ordered})}
        Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.Requirements.tryRequirement altered guard.Site |> Option.isNone)
        Assert.True(MemoryPublication.project altered |> Result.isError)

    [<Fact>]
    member _.``Array store evaluates its complete RHS before the outer bounds guard`` () =
        let source = MemoryAccessFixture.source "    let values = [| 7; 11 |]\n    values.[0] <- values.[1]\n    values.[0]\n"
        let graph, facts = MemoryAccessFixture.admittedSource MemoryAccessFixture.stackAuthority source
        let access = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.ArrayAccess fact when fact.Value.IsSome -> Some fact | _ -> None) |> Assert.Single
        let evaluation = match graph.Nodes[access.Site].Kind with SemanticKind.IndexSet(_,_,value) -> value | _ -> failwith "Missing store"
        let guard = access.Bounds.Requirement
        let frontier = graph.Nodes[guard.Frontier]
        Assert.Equal(SemanticKind.Sequential [access.Buffer;access.Index;evaluation;guard.Site;access.Site],frontier.Kind)
        for prefix in [[access.Buffer;access.Index];[access.Buffer;evaluation;access.Index]] do
            let ordered = prefix @ [guard.Site;access.Site]
            let altered = {graph with Nodes = graph.Nodes.Add(frontier.Id,{frontier with Kind = SemanticKind.Sequential ordered;Children = ordered})}
            Assert.True(Clef.Compiler.PSGSaturation.SemanticGraph.Requirements.tryRequirement altered guard.Site |> Option.isNone)
            Assert.True(MemoryPublication.project altered |> Result.isError)

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
    member _.``Reachable nominal declaration remains source authority without an executable publication body`` () =
        let graph, facts = MemoryAccessFixture.admittedSource MemoryAccessFixture.stackAuthority MemoryAccessFixture.fieldAddress
        let declaration = graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with SemanticKind.TypeDef("Cell", TypeDefKind.RecordDef _, _) -> Some node | _ -> None) |> Assert.Single
        Assert.True declaration.IsReachable
        Assert.Equal(Some(MetadataValue.StringList ["Value"]), declaration.Metadata.TryFind "TypeDef.MutableFields")
        let address = facts.Operations.Values |> Seq.choose (function MemoryWitnessOperation.Address fact -> Some fact | _ -> None) |> Assert.Single
        let receiver, extent, field =
            match address.Place with
            | MemoryPlace.RecordField(receiver, extent, field) -> receiver, extent, field
            | _ -> failwith "The fixture must retain its actual mutable record field."
        Assert.Contains(declaration.Id, address.Participants)
        let identity = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType graph.Nodes[receiver].Type
        let emission = graph.Codata.Value.WitnessEmission |> Option.defaultWith (fun () -> failwith "The source emission account is absent.")
        let layout = emission.Numeric.Layouts[identity]
        match layout with
        | SettledLayout.Record(fields, Some bytes, Some _) ->
            Assert.Equal<string list>(["Other"; "Value"], fields |> List.map _.Name)
            Assert.Equal(extent, bytes)
            Assert.Equal(field, fields |> List.find (fun value -> value.Name = "Value"))
        | _ -> failwith "The actual nominal record must have a complete settled byte layout."
        let scope = graph.Codata.Value.WitnessLiveScope |> Option.defaultWith (fun () -> failwith "The source occurrence account is absent.")
        Assert.False(scope.Occurrences.ContainsKey declaration.Id)
        Assert.False(scope.Contexts.ContainsKey declaration.Id)
        let publication = Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph |> Result.defaultWith (sprintf "%A" >> failwith)
        let publicId = Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId
        Assert.DoesNotContain(publication.Nodes.Values, fun node -> match node.Kind with Fidelity.PSG.SemanticKind.TypeDef _ -> true | _ -> false)
        Assert.False(publication.SourceReadings.Contexts.ContainsKey(publicId declaration.Id))
        Assert.Equal(Clef.Compiler.Baker.Ingredients.PublishedFactRows.mapSettledLayout layout,
                     publication.Emission.Numeric.Layouts[Clef.Compiler.Baker.Ingredients.PublishedFactRows.mapTypeIdentity identity])
        Assert.Equal(Clef.Compiler.Baker.Ingredients.PublishedFactRows.mapMemoryWitnessOperation (MemoryWitnessOperation.Address address),
                     publication.Emission.Memory.Operations[publicId address.Site])
        let allocation =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.RecordExpr _ when node.IsReachable &&
                                                Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type = identity -> Some node
                | _ -> None)
            |> Assert.Single
        Assert.Equal(Clef.Compiler.Baker.Ingredients.PublishedFactRows.mapEscapeKind graph.Codata.Value.Escapes[allocation.Id],
                     publication.Codata.Escapes[publicId allocation.Id])
        let parent, members =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.ModuleDef(_, members) when List.contains declaration.Id members -> Some(node.Id, members)
                | _ -> None)
            |> Assert.Single
        let ordinal = members |> List.findIndex ((=) declaration.Id)
        let port = publication.SourceReadings.Ports[publicId parent, Fidelity.PSG.OccurrencePort.ModuleDeclaration]
        // Body-free module ports preserve original extent and ordinals. The
        // semantic declaration's omitted slot has no sparse position or body.
        Assert.Equal(members.Length, port.Extent)
        Assert.False(port.Positions.ContainsKey ordinal)
        Assert.NotEmpty port.Positions
        for KeyValue(position, child) in port.Positions do
            Assert.Equal(publicId members[position], child)

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
