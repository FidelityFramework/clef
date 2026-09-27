namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module IntrinsicBoundary = Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission

module IntrinsicWriteFixture =
    let platform : PlatformContext =
        let representation name family bits minimum maximum : NumericRepresentation =
            { Name = name; Capability = "native"; Family = family; Bits = bits
              MinMagnitude = minimum; MaxMagnitude = maximum; Boundary = "wrap" }
        let representations =
            [ representation "octet" "uint" 8 "0" "255"
              representation "signed32" "int" 32 "-2147483648" "2147483647"
              representation "unsigned32" "uint" 32 "0" "4294967295"
              representation "signed64" "int" 64 "-9223372036854775808" "9223372036854775807"
              representation "unsigned64" "uint" 64 "0" "18446744073709551615" ]
        { PlatformId = "intrinsic-write-test"; Dimensions = Map.ofList ["Pointer",64; "Register",64]
          Representations = representations |> List.map (fun value -> value.Name, value) |> Map.ofList
          EndpointReturns = Map.empty; PlatformLibraryPath = None; PlatformDescription = Some "WriteAuthority.description"
          PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.singleton (System.IO.Path.GetFullPath "write-authority.clef")
          Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None; RuntimeModel = None
          AvailableMemorySpaces = []; DefaultMemorySpace = None; ClockFrequencyMhz = None; NsPerWeightUnit = None }

    let authority =
        let representations = platform.Representations.Values |> Seq.map (fun rep ->
            sprintf "{ Name = %A; Capability = %A; Family = %A; Bits = %d; MinMagnitude = %A; MaxMagnitude = %A; Boundary = %A }"
                rep.Name rep.Capability rep.Family rep.Bits rep.MinMagnitude rep.MaxMagnitude rep.Boundary) |> String.concat "; "
        let template = """module WriteAuthority
type WidthDeclaration = { Name: string; Bits: int }
type Representation = { Name: string; Capability: string; Family: string; Bits: int; MinMagnitude: string; MaxMagnitude: string; Boundary: string }
type TargetCore = { Arch: string; Os: string; Runtime: string; Triple: string; Widths: WidthDeclaration array; Representations: Representation array }
type MemorySpace = { Name: string; Kind: string; Capacity: int; Alignment: int; Granularity: int; Growth: string; Access: string; Base: int option }
type ProgramLifetimeSpaces = { Immutable: string; Mutable: string option }
type Contract = { Floor: int; AtMost: string }
type Endpoint = { Name: string; Location: string; Address: string; Contracts: Contract array }
type BoundarySurface = { Endpoints: Endpoint array }
type PlatformDescription = { Id: string; Core: TargetCore option; Spaces: MemorySpace array; ProgramLifetime: ProgramLifetimeSpaces option; Surfaces: BoundarySurface array }
let rodata = { Name = "rodata"; Kind = "rodata"; Capacity = 4096; Alignment = 16; Granularity = 16; Growth = "fixed"; Access = "r"; Base = None }
let write = { Name = "write"; Location = "syscall-number"; Address = "1"; Contracts = [| { Floor = -4095; AtMost = "count" } |] }
let description = { Id = "intrinsic-write-test"
                    Core = Some { Arch = "x86_64"; Os = "linux"; Runtime = "freestanding"; Triple = "x86_64-unknown-linux-gnu"; Widths = [| { Name = "Pointer"; Bits = 64 }; { Name = "Register"; Bits = 64 } |]; Representations = [| %s |] }
                    Spaces = [| rodata |]; ProgramLifetime = Some { Immutable = "rodata"; Mutable = None }; Surfaces = [| { Endpoints = [| write |] } |] }
"""
        template.Replace("%s", representations)

    let body = """module WriteFixture
let write (s: string) =
    let _ = Sys.write 1 s.Bytes s.Length
    ()
let print (s: string) = write s
[<EntryPoint>]
let main _ =
    print "a"
    print "hello"
    0
"""

    let checkSource declaration source =
        let parse text path = match parseStringWithDefaults text path with ParseSuccess input -> input | ParseError errors -> failwithf "%A" errors
        checkParsedInputsWithPlatform [parse declaration "write-authority.clef"; parse source "intrinsic-write.clef"] (Some platform)
    let check () = checkSource authority body
    let admitted () =
        let result = check ()
        DimensionalCases.noErrors result
        match IntrinsicBoundary.project result.Graph with
        | Ok projection -> result.Graph, projection
        | Error errors -> failwithf "%A" errors

type IntrinsicWriteCases() =
    [<Fact>]
    member _.``Source preserves exact extent through nested formals and ordered three operand write`` () =
        let graph, projection = IntrinsicWriteFixture.admitted ()
        let call = Assert.Single projection.IntrinsicWrites.Values
        let view = projection.ByteViews[call.Buffer]
        Assert.Equal<bigint list>([1I;5I], view.StaticOrigins.Values |> Seq.sort |> Seq.toList)
        Assert.Equal(Some(ValueRange.bounded 1I 5I), graph.Nodes[call.Count].ValueRange)
        Assert.Equal(Some(ValueRange.bounded -4095I 5I), graph.Nodes[call.Site].ValueRange)
        Assert.Equal(8, view.Representation.Bits)
        Assert.NotEqual(view.Source, view.ExtentSource)
        Assert.True(call.FdAdaptation.IsSome && call.CountAdaptation.IsSome && call.ResultAdaptation.IsSome)
        let proofs = graph.Nodes.Values |> Seq.choose (fun node -> match node.Kind with SemanticKind.Obligation info when info.Kind = "intrinsic-write-proof" -> Some info | _ -> None) |> Seq.toList
        Assert.Equal(4, proofs.Length)
        Assert.Contains(proofs, fun proof -> match proof.Body with ObligationBody.StringBorrowBound origins -> origins |> List.sort = [(1I,1I,2I);(5I,5I,6I)] | _ -> false)

    [<Theory>]
    [<InlineData("wrong-count")>]
    [<InlineData("other-string")>]
    [<InlineData("two-operands")>]
    [<InlineData("no-endpoint")>]
    [<InlineData("no-program-storage")>]
    [<InlineData("mutable-use")>]
    member _.``Incomplete intrinsic contracts remain source failures`` defect =
        let declaration, source =
            match defect with
            | "wrong-count" -> IntrinsicWriteFixture.authority, IntrinsicWriteFixture.body.Replace("s.Bytes s.Length", "s.Bytes 5")
            | "other-string" -> IntrinsicWriteFixture.authority, IntrinsicWriteFixture.body.Replace("let _ = Sys.write", "let other = \"other\"\n    let _ = Sys.write").Replace("s.Bytes s.Length", "s.Bytes other.Length")
            | "two-operands" -> IntrinsicWriteFixture.authority, IntrinsicWriteFixture.body.Replace("s.Bytes s.Length", "s.Bytes")
            | "no-endpoint" -> IntrinsicWriteFixture.authority.Replace("Endpoints = [| write |]", "Endpoints = [||]"), IntrinsicWriteFixture.body
            | "mutable-use" -> IntrinsicWriteFixture.authority, IntrinsicWriteFixture.body.Replace("let _ = Sys.write", "let bytes = s.Bytes\n    Array.set bytes 0 42\n    let _ = Sys.write")
            | _ -> IntrinsicWriteFixture.authority.Replace("ProgramLifetime = Some { Immutable = \"rodata\"; Mutable = None }", "ProgramLifetime = None"), IntrinsicWriteFixture.body
        let result = IntrinsicWriteFixture.checkSource declaration source
        match IntrinsicBoundary.project result.Graph with Error _ -> () | Ok _ -> failwith "An incomplete source write contract was admitted."

    [<Theory>]
    [<InlineData("count")>]
    [<InlineData("view-row")>]
    [<InlineData("proof")>]
    [<InlineData("rewrite")>]
    [<InlineData("pool")>]
    member _.``Publication refuses changed count relation proof or storage without repair`` defect =
        let graph, projection = IntrinsicWriteFixture.admitted ()
        let call = Assert.Single projection.IntrinsicWrites.Values
        let changed =
            match defect with
            | "count" -> { graph with Nodes = graph.Nodes.Add(call.Count, { graph.Nodes[call.Count] with ValueRange = Some(ValueRange.point 5I) }) }
            | "view-row" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.StringByteView _ -> false | _ -> true) }
            | "proof" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.BoundaryProof _ when edge.Target = call.Site -> false | _ -> true) }
            | "rewrite" -> { graph with Edges = graph.Edges |> List.filter (fun edge -> not (edge.Role = EdgeRole.EnrichedWith && edge.Target = call.Buffer)) }
            | _ -> { graph with StaticStringPool = None }
        match IntrinsicBoundary.project changed with Error _ -> () | Ok _ -> failwith "Stale source evidence was repaired during publication."

    [<Fact>]
    member _.``Changed actual origins require new source range settlement before boundary resettlement`` () =
        let graph, projection = IntrinsicWriteFixture.admitted ()
        let call = Assert.Single projection.IntrinsicWrites.Values
        let origin = projection.ByteViews[call.Buffer].StaticOrigins |> Map.toList |> List.find (fun (_, length) -> length = 1I) |> fst
        let changed = { graph with Nodes = graph.Nodes.Add(origin, { graph.Nodes[origin] with Kind = SemanticKind.Literal(NativeLiteral.String "changed") }) }
        let settled = Clef.Compiler.Nanopass.BoundarySettlement.normalize changed
        match IntrinsicBoundary.project settled with
        | Error errors -> Assert.Contains(errors, fun error -> error.Reason.Contains("premises changed"))
        | Ok _ -> failwith "An old numeric/storage proof was reused after the exact actual origin changed."
