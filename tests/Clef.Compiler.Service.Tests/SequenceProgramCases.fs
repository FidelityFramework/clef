namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module SequencePrograms = Clef.Compiler.Nanopass.SequenceProgramInstances
module SequenceProgramAuthority = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorageAuthority
module SequenceProgramCopies = Clef.Compiler.Nanopass.SequenceFamilies

module SequenceProgramFixture =
    let file = System.IO.Path.GetFullPath "sequence-program.clef"
    let context: PlatformContext =
        let integer name family bits minimum maximum: NumericRepresentation =
            { Name = name; Family = family; Bits = bits; MinMagnitude = minimum; MaxMagnitude = maximum
              Capability = "native"; Boundary = "wrap" }
        let representations = [integer "signed64" "int" 64 "-9223372036854775808" "9223372036854775807"; integer "uint8" "uint" 8 "0" "255"]
        { PlatformLoading = None; PlatformId = "sequence-program"; Dimensions = Map.ofList ["Pointer", 64; "Register", 64]
          Representations = representations |> List.map (fun value -> value.Name, value) |> Map.ofList
          EndpointReturns = Map.empty; PlatformLibraryPath = None; PlatformDescription = Some "SequenceProgram.description"
          PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.singleton file
          Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
          AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None; ProjectMemoryPolicy = None }

    let header = """module SequenceProgram
type WidthDeclaration = { Name: string; Bits: int }
type Representation = { Name: string; Capability: string; Family: string; Bits: int; MinMagnitude: string; MaxMagnitude: string; Boundary: string }
type TargetCore = { Widths: WidthDeclaration array; Representations: Representation array }
type MemorySpace = { Name: string; Kind: string; Capacity: int; Alignment: int; Granularity: int; Growth: string; Access: string; Base: int option }
type ProgramLifetimeSpaces = { Immutable: string; Mutable: string option }
type PlatformDescription = { Id: string; Core: TargetCore option; Spaces: MemorySpace array; ProgramLifetime: ProgramLifetimeSpaces option }
let image = { Name = "image"; Kind = "rodata"; Capacity = 4096; Alignment = 16; Granularity = 16; Growth = "fixed"; Access = "r"; Base = None }
let state = { Name = "state"; Kind = "data"; Capacity = 4096; Alignment = 16; Granularity = 16; Growth = "fixed"; Access = "rw"; Base = None }
let core = { Widths = [| { Name = "Pointer"; Bits = 64 }; { Name = "Register"; Bits = 64 } |]; Representations = [| { Name = "signed64"; Capability = "native"; Family = "int"; Bits = 64; MinMagnitude = "-9223372036854775808"; MaxMagnitude = "9223372036854775807"; Boundary = "wrap" }; { Name = "uint8"; Capability = "native"; Family = "uint"; Bits = 8; MinMagnitude = "0"; MaxMagnitude = "255"; Boundary = "wrap" } |] }
let description = { Id = "sequence-program"; Core = Some core; Spaces = [| image; state |]; ProgramLifetime = Some { Immutable = "image"; Mutable = Some "state" } }
[<Measure>] type m
"""
    let check body =
        let source = header + body
        let input = match parseStringWithDefaults source file with ParseSuccess input -> input | ParseError errors -> failwithf "%A" errors
        let result = checkParsedInputsWithPlatform [input] (Some context)
        Assert.Empty(result.Diagnostics |> List.filter (fun diagnostic -> Diagnostic.effectiveSeverity diagnostic = NativeDiagnosticSeverity.Error))
        result.Graph

    let direct () = check """
let first = seq { yield 1<m>; yield 2<m> }
let second = seq { yield 3<m> }
let alias = first
[<EntryPoint>]
let main _ =
    for value in first do ignore value
    for value in alias do ignore value
    for value in second do ignore value
    0
"""

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding(actual, false, _, _) -> actual = name | _ -> false)
        |> Assert.Single

    let instance graph name =
        SequencePrograms.programInstance graph (binding name graph).Id
        |> Option.defaultWith (fun () -> failwithf "Missing actual program sequence %s" name)

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceProgram")>]
type SequenceProgramCases() =
    [<Fact>]
    member _.``Complete source publication retains declared program counter carriers and dispatch transport``() =
        let graph = SequenceProgramFixture.direct ()
        let numeric =
            Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project graph
            |> Result.defaultWith (fun failures -> failwithf "%A" failures)
        let counters = graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable && match node.Kind with SemanticKind.Binding("__continuation_pc", true, _, _) -> true | _ -> false) |> Seq.toList
        Assert.Equal(2, counters.Length)
        for counter in counters do
            let sites = graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && (node.Id = counter.Id || match node.Kind with SemanticKind.VarRef(_, Some binding) -> binding = counter.Id | _ -> false))
            for node in sites do
                let carrier = numeric.Values[node.Id]
                Assert.Equal(node.ValueRange, Some carrier.Range)
                Assert.Equal(SettledSlot.Integer(64, Some "signed64"), carrier.Slot)
                Assert.True carrier.Declaration.IsSome
                Assert.Contains(carrier.Declaration.Value, carrier.Participants)
            let dispatch = graph.Nodes.Values |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.ContinuationDispatch(selector, _, _) ->
                    match graph.Nodes[selector].Kind with SemanticKind.VarRef(_, Some binding) when binding = counter.Id -> Some node.Id | _ -> None
                | _ -> None) |> Assert.Single
            let transport = numeric.IndexTransports[dispatch]
            Assert.Equal(64, transport.PointerBits)
            Assert.Contains(transport.PointerDeclaration, transport.Participants)
            Assert.Equal(numeric.Values[transport.Operand], transport.Carrier)

    [<Fact>]
    member _.``Program aliases retain one template while independent values retain distinct allocations``() =
        let graph = SequenceProgramFixture.direct ()
        let first, second, alias = SequenceProgramFixture.instance graph "first", SequenceProgramFixture.instance graph "second", SequenceProgramFixture.instance graph "alias"
        Assert.Equal(first.Allocation, alias.Allocation)
        Assert.Equal(first.Generator, alias.Generator)
        Assert.NotEqual(first.Allocation, second.Allocation)
        Assert.Equal(Some EscapeKind.StaticLifetime, graph.Codata.Value.Escapes.TryFind first.Allocation)
        Assert.Contains(first.Owner, first.Participants)
        Assert.Contains(first.Generator, first.Participants)

    [<Fact>]
    member _.``Every enumeration owns fresh storage and preserves template uninitialized current``() =
        let graph = SequenceProgramFixture.direct ()
        let codata = graph.Codata.Value
        let first = SequenceProgramFixture.instance graph "first"
        let copies = codata.SequenceTemplateCopies.Values |> Seq.filter (fun copy ->
            copy.TemplateStorage.TryFind first.Owner |> Option.exists (Set.contains first.Allocation)) |> Seq.toList
        Assert.Equal(2, copies.Length)
        Assert.NotEqual(copies[0].StorageSite, copies[1].StorageSite)
        for copy in copies do
            Assert.NotEqual(first.Allocation, copy.StorageSite)
            Assert.Equal(EscapeKind.StackScoped, copy.Residence)
            let frame = codata.ContinuationFrames[first.Owner]
            Assert.Contains(frame.Current, copy.Uninitialized[first.Owner])
        let reread, _, pending = SequenceProgramCopies.copies graph codata.SequenceFamilies codata.SequenceFlows codata.Escapes codata.ContinuationRegions codata.SequenceInitializers codata.SequenceDestinations
        Assert.Empty pending
        for copy in copies do Assert.Equal(copy, reread[copy.SourceAcquisition])

    [<Theory>]
    [<InlineData("missing-program")>]
    [<InlineData("missing-storage")>]
    [<InlineData("duplicate-storage")>]
    [<InlineData("changed-generator")>]
    [<InlineData("changed-layout-proof")>]
    [<InlineData("repeated-site")>]
    member _.``Changed owning premises retract static instance instead of reusing cached metadata`` mutation =
        let graph = SequenceProgramFixture.direct ()
        let instance = SequenceProgramFixture.instance graph "first"
        let binding = SequenceProgramFixture.binding "first" graph
        let damaged =
            match mutation with
            | "missing-program" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramValue) }
            | "missing-storage" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.SequenceProgramStorage) }
            | "duplicate-storage" ->
                let row = graph.Edges |> List.find (fun edge -> edge.Role = EdgeRole.SequenceProgramStorage && edge.Target = instance.Allocation)
                { graph with Edges = row :: graph.Edges }
            | "changed-generator" ->
                let owner = graph.Nodes[instance.Owner]
                let other = SequenceProgramFixture.instance graph "second"
                let captures = match owner.Kind with SemanticKind.SeqExpr(_, captures) -> captures | _ -> failwith "Expected constructor"
                let replacement = { owner with Kind = SemanticKind.SeqExpr(other.Generator, captures); Children = [other.Generator] }
                { graph with Nodes = graph.Nodes.Add(owner.Id, replacement) }
            | "changed-layout-proof" ->
                let proof = graph.Nodes[graph.Codata.Value.ContinuationFrames[instance.Owner].Obligations.Head]
                let info = match proof.Kind with SemanticKind.Obligation info -> info | _ -> failwith "Expected proof"
                let replacement = { proof with Kind = SemanticKind.Obligation { info with Body = ObligationBody.ContinuationLayout([], 1, 1) } }
                { graph with Nodes = graph.Nodes.Add(proof.Id, replacement) }
            | "repeated-site" ->
                let root = graph.Nodes.Values |> Seq.find (fun node -> match node.Kind with SemanticKind.Lambda(_, _, _, _, LambdaContext.RegularClosure) -> true | _ -> false)
                let repeated = { root with Id = NodeId.fresh(); Kind = SemanticKind.WhileLoop(instance.Owner, instance.Owner); Children = [instance.Owner; instance.Owner]; IsReachable = true }
                { graph with Nodes = graph.Nodes.Add(repeated.Id, repeated) }
            | _ -> failwith "Unknown mutation"
        Assert.True((SequencePrograms.programInstance damaged binding.Id).IsNone, mutation)
        Assert.True((SequencePrograms.programInstance graph binding.Id).IsSome)

    [<Theory>]
    [<InlineData("missing-owned-layout-row")>]
    [<InlineData("wrong-owned-extent")>]
    [<InlineData("wrong-owned-child-layout")>]
    [<InlineData("wrong-prefix-alignment")>]
    [<InlineData("missing-owned-child-support")>]
    [<InlineData("foreign-region-child")>]
    member _.``Owned region layout changes retract the final program instance`` mutation =
        let graph = SequenceProgramFixture.check """
let input = seq { yield true }
let outer = seq { yield! input }
[<EntryPoint>]
let main _ = ignore outer; 0
"""
        // Every refusal starts with complete source admission and both actual
        // static instances. A missing unchanged instance cannot pass a negative.
        let input = SequenceProgramFixture.instance graph "input"
        let outer = SequenceProgramFixture.instance graph "outer"
        let binding = SequenceProgramFixture.binding "outer" graph
        let frame = graph.Codata.Value.ContinuationFrames[outer.Owner]
        let region = graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.ContinuationRegion && edge.Sources = [outer.Owner; input.Owner; frame.Formal]) |> Assert.Single
        let proof = frame.Obligations |> List.map (fun id -> graph.Nodes[id]) |> List.filter (fun node ->
            match node.Kind with
            | SemanticKind.Obligation { Body = ObligationBody.ContinuationLayout(fields, extent, _) } ->
                extent = frame.Bytes && fields.Length = frame.Slots.Length + 1
            | _ -> false) |> Assert.Single
        let info, fields, extent, alignment =
            match proof.Kind with
            | SemanticKind.Obligation info ->
                match info.Body with
                | ObligationBody.ContinuationLayout(fields, extent, alignment) -> info, fields, extent, alignment
                | _ -> failwith "Expected owned-region layout body"
            | _ -> failwith "Expected owned-region layout obligation"
        let support = graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.Constrains && edge.Target = proof.Id) |> Assert.Single
        Assert.Contains(input.Owner, support.Sources)
        Assert.Contains(region.Target, support.Sources)
        let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Target, edge.Sources
        let changeProof fields extent =
            let changed = { info with Body = ObligationBody.ContinuationLayout(fields, extent, alignment) }
            let replacement = { proof with Kind = SemanticKind.Obligation changed }
            { graph with Nodes = graph.Nodes.Add(proof.Id, replacement) }
        let damaged =
            match mutation with
            | "missing-owned-layout-row" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> key edge <> key support) }
            | "wrong-owned-extent" -> changeProof fields (extent + alignment)
            | "wrong-owned-child-layout" ->
                let offset, bytes, align = List.last fields
                changeProof (List.take (fields.Length - 1) fields @ [offset, bytes + align, align]) extent
            | "wrong-prefix-alignment" ->
                let prefix = graph.Nodes[frame.Obligations.Head]
                let replacement =
                    match prefix.Kind with
                    | SemanticKind.Obligation info ->
                        match info.Body with
                        | ObligationBody.ContinuationLayout(fields, bytes, align) ->
                            Assert.True(align > 1)
                            Assert.Contains(fields, fun (_, _, fieldAlignment) -> fieldAlignment = align)
                            let changed = { info with Body = ObligationBody.ContinuationLayout(fields, bytes, align / 2) }
                            { prefix with Kind = SemanticKind.Obligation changed }
                        | _ -> failwith "Expected persistent prefix layout"
                    | _ -> failwith "Expected persistent prefix obligation"
                { graph with Nodes = graph.Nodes.Add(prefix.Id, replacement) }
            | "missing-owned-child-support" ->
                let edges = graph.Edges |> List.map (fun edge ->
                    if key edge = key support then { edge with Sources = edge.Sources |> List.filter ((<>) input.Owner) } else edge)
                { graph with Edges = edges }
            | "foreign-region-child" ->
                let edges = graph.Edges |> List.map (fun edge ->
                    if key edge = key region then { edge with Sources = [outer.Owner; outer.Owner; frame.Formal] } else edge)
                { graph with Edges = edges }
            | _ -> failwith "Unknown owned-region mutation"
        let storageRows (value: SemanticGraph) = value.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.SequenceProgramStorage && edge.Target = outer.Allocation)
        Assert.NotEmpty(storageRows graph)
        Assert.True((storageRows graph |> List.map key) = (storageRows damaged |> List.map key))
        Assert.True((SequencePrograms.programInstance damaged binding.Id).IsNone, mutation)
        Assert.True((SequencePrograms.programInstance graph binding.Id).IsSome)

    [<Fact>]
    member _.``Complete factory destinations retain distinct caller storage through aliases``() =
        let graph = SequenceProgramFixture.check """
let make (value: int<m>) = seq { yield value }
let first = make 4<m>
let second = make 5<m>
let alias = first
[<EntryPoint>]
let main _ =
    for value in first do ignore value
    for value in second do ignore value
    for value in alias do ignore value
    0
"""
        let first, second, alias = SequenceProgramFixture.instance graph "first", SequenceProgramFixture.instance graph "second", SequenceProgramFixture.instance graph "alias"
        Assert.Equal(first.Owner, second.Owner)
        Assert.NotEqual(first.Allocation, second.Allocation)
        Assert.Equal(first.Allocation, alias.Allocation)
        match graph.Nodes[first.Allocation].Kind with
        | SemanticKind.ContinuationAllocate owner -> Assert.Equal(first.Owner, owner)
        | kind -> failwithf "Factory instance lost its actual caller allocation: %A" kind
        let formal = graph.Codata.Value.SequenceDestinations[first.Owner]
        let node = graph.Nodes[formal]
        let damaged = { graph with Nodes = graph.Nodes.Add(formal, { node with Type = Types.boolType }) }
        Assert.True((SequencePrograms.programInstance damaged (SequenceProgramFixture.binding "first" graph).Id).IsNone)

module private SequenceNumericFreshnessFixture =
    let graph () =
        SequenceProgramFixture.check """
[<EntryPoint>]
let main _ =
    let bias = 2<m>
    let mutable offset = 7<m>
    let mapper = fun (value: int<m>) -> value + offset + bias
    let mapped = Seq.map mapper (seq { yield 1<m> })
    let mutable total = 0<m>
    for value in mapped do total <- total + value
    if total = 10<m> then 0 else 1
"""

    let project = Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project
    let admitted graph =
        match project graph with
        | Result.Ok _ -> ()
        | Result.Error failures -> failwithf "The original represented sequence lacks numeric authority: %A" failures

    let refused graph =
        match project graph with
        | Result.Error failures -> Assert.NotEmpty failures
        | Result.Ok _ -> failwith "Changed finite-sequence premises retained numeric authority."

    let proofIds (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Obligation { Kind = "finite-sequence-pulls" | "sequence-inner-finite-pulls" | "sequence-additive-invariant" } -> Some node.Id
            | _ -> None) |> Set.ofSeq

    let changed scenario (graph: SemanticGraph) =
        let product = graph.Edges |> List.find (fun edge ->
            match edge.Role with EdgeRole.SequencePullComposition _ -> true | _ -> false)
        let inner = product.Sources[1]
        let proofs = proofIds graph
        let row =
            match scenario with
            | "product" -> product
            | "evaluation" -> graph.Edges |> List.find (fun edge -> edge.Class = EdgeClass.Evaluation && List.tryHead edge.Sources = Some inner)
            | "constraint" -> graph.Edges |> List.find (fun edge -> edge.Role = EdgeRole.Constrains && proofs.Contains edge.Target)
            | _ -> failwithf "Unknown mutation %s" scenario
        let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
        let edges = graph.Edges |> List.map (fun edge -> if key edge = key row then { edge with Ordinal = edge.Ordinal + 1 } else edge)
        { graph with Edges = edges }

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceNumericFreshness")>]
type SequenceNumericPublicationCases() =
    [<Theory>]
    [<InlineData("product")>]
    [<InlineData("evaluation")>]
    [<InlineData("constraint")>]
    member _.``Numeric publication refuses relation only changes to represented finite sequence authority`` scenario =
        let graph = SequenceNumericFreshnessFixture.graph ()
        SequenceNumericFreshnessFixture.admitted graph
        Assert.NotEmpty graph.Codata.Value.ContinuationFrames
        let changed = SequenceNumericFreshnessFixture.changed scenario graph
        Assert.Same(graph.Nodes, changed.Nodes)
        SequenceNumericFreshnessFixture.refused changed
        SequenceNumericFreshnessFixture.admitted graph

    [<Theory>]
    [<InlineData("product")>]
    [<InlineData("evaluation")>]
    [<InlineData("constraint")>]
    member _.``Repeated numeric renewal cannot bless changed represented sequence premises`` scenario =
        let graph = SequenceNumericFreshnessFixture.graph ()
        SequenceNumericFreshnessFixture.admitted graph
        SequenceNumericFreshnessFixture.admitted (Clef.Compiler.Nanopass.NumericSettlement.normalize graph)
        let changed = SequenceNumericFreshnessFixture.changed scenario graph
        let once = Clef.Compiler.Nanopass.NumericSettlement.normalize changed
        let twice = Clef.Compiler.Nanopass.NumericSettlement.normalize once
        SequenceNumericFreshnessFixture.refused once
        SequenceNumericFreshnessFixture.refused twice
        SequenceNumericFreshnessFixture.admitted graph

    [<Fact>]
    member _.``Numeric renewal refuses changed protected continuation proof body``() =
        let graph = SequenceNumericFreshnessFixture.graph ()
        SequenceNumericFreshnessFixture.admitted graph
        let authority = graph.SequenceRangeProvenance |> Option.defaultWith (fun () -> failwith "Missing actual source-to-machine handoff")
        let id, info = authority.Obligations |> List.find (fun (_, info) -> info.Kind = "continuation-state-range")
        let proof = graph.Nodes[id]
        let changedProof = { proof with Kind = SemanticKind.Obligation { info with Body = ObligationBody.Pending ["Withdrawn continuation state premise"] } }
        let changed = { graph with Nodes = graph.Nodes.Add(id, changedProof) }
        Assert.Same(graph.Edges, changed.Edges)
        SequenceNumericFreshnessFixture.refused changed
        SequenceNumericFreshnessFixture.refused (Clef.Compiler.Nanopass.NumericSettlement.normalize changed)
        SequenceNumericFreshnessFixture.admitted graph

    [<Fact>]
    member _.``Numeric renewal remembers wholly withdrawn represented sequence proof inventory``() =
        let graph = SequenceNumericFreshnessFixture.graph ()
        SequenceNumericFreshnessFixture.admitted graph
        let proofs = SequenceNumericFreshnessFixture.proofIds graph
        Assert.Equal(3, proofs.Count)
        let edges = graph.Edges |> List.filter (fun edge ->
            not (proofs.Contains edge.Target) &&
            match edge.Role with
            | EdgeRole.SequencePullBound | EdgeRole.SequencePullComposition _ | EdgeRole.SequenceAccumulation -> false
            | _ -> true)
        let changed = { graph with Nodes = graph.Nodes |> Map.filter (fun id _ -> not (proofs.Contains id)); Edges = edges }
        for KeyValue(id, node) in changed.Nodes do Assert.Equal(graph.Nodes[id].ValueRange, node.ValueRange)
        SequenceNumericFreshnessFixture.refused changed
        let once = Clef.Compiler.Nanopass.NumericSettlement.normalize changed
        let twice = Clef.Compiler.Nanopass.NumericSettlement.normalize once
        SequenceNumericFreshnessFixture.refused once
        SequenceNumericFreshnessFixture.refused twice
        SequenceNumericFreshnessFixture.admitted graph
