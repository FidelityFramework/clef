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
        { PlatformId = "sequence-program"; Dimensions = Map.ofList ["Pointer", 64; "Register", 64]
          Representations = representations |> List.map (fun value -> value.Name, value) |> Map.ofList
          EndpointReturns = Map.empty; PlatformLibraryPath = None; PlatformDescription = Some "SequenceProgram.description"
          PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.singleton file
          Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
          AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None }

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
