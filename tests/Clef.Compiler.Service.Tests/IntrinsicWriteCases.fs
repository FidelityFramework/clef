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

    /// `discard` returns `formal`: "0" leaves its formal unused, so ordinary
    /// demand omits the actual that contains the write of "never demanded";
    /// "value" reads the formal, so that actual is demanded.
    let demandBody formal = """module WriteFixture
let write (s: string) =
    let _ = Sys.write 1 s.Bytes s.Length
    ()
let discard (value: int) = """ + formal + """
[<EntryPoint>]
let main _ =
    if discard (write "never demanded"; 0) = 0 then write "kept"
    0
"""

    /// One literal reaches the formal of `write` through a call inside an
    /// omitted actual and through a demanded call.
    let sharedBody = """module WriteFixture
let write (s: string) =
    let _ = Sys.write 1 s.Bytes s.Length
    ()
let discard (value: int) = 0
let print (s: string) =
    if discard (write s; 0) = 0 then write s
[<EntryPoint>]
let main _ =
    print "both"
    0
"""

    /// One module-level binding reaches the formal of `write` through a call
    /// inside an omitted actual and through a demanded call.
    let bindingBody = """module WriteFixture
let write (s: string) =
    let _ = Sys.write 1 s.Bytes s.Length
    ()
let discard (value: int) = 0
let msg = "both"
[<EntryPoint>]
let main _ =
    if discard (write msg; 0) = 0 then write msg
    0
"""

    /// Two demanded calls of `write` and one inside the omitted actual of `discard`.
    let threeCallsBody = """module WriteFixture
let write (s: string) =
    let _ = Sys.write 1 s.Bytes s.Length
    ()
let discard (value: int) = 0
[<EntryPoint>]
let main _ =
    write "a"
    write "bb"
    if discard (write "c"; 0) = 0 then 0 else 1
"""

    /// One text written by two demanded calls.
    let repeatedBody = """module WriteFixture
let write (s: string) =
    let _ = Sys.write 1 s.Bytes s.Length
    ()
[<EntryPoint>]
let main _ =
    write "same"
    write "same"
    0
"""

    /// A text written only by a function that no call reaches.
    let uncalledBody = """module WriteFixture
let write (s: string) =
    let _ = Sys.write 1 s.Bytes s.Length
    ()
let uncalled () = write "orphan"
[<EntryPoint>]
let main _ =
    write "kept"
    0
"""

    /// `authority` with the writable program space that a module-level value binding requires.
    let writableAuthority =
        authority
            .Replace("let rodata =", "let data = { Name = \"data\"; Kind = \"data\"; Capacity = 4096; Alignment = 16; Granularity = 16; Growth = \"fixed\"; Access = \"rw\"; Base = None }\nlet rodata =")
            .Replace("Spaces = [| rodata |]; ProgramLifetime = Some { Immutable = \"rodata\"; Mutable = None }",
                     "Spaces = [| rodata; data |]; ProgramLifetime = Some { Immutable = \"rodata\"; Mutable = Some \"data\" }")

    let checkSource declaration source =
        let parse text path = match parseStringWithDefaults text path with ParseSuccess input -> input | ParseError errors -> failwithf "%A" errors
        checkParsedInputsWithPlatform [parse declaration "write-authority.clef"; parse source "intrinsic-write.clef"] (Some platform)
    let check () = checkSource authority body
    /// The graph of a result with no error and its boundary projection.
    let graphAndProjection result =
        DimensionalCases.noErrors result
        match IntrinsicBoundary.project result.Graph with
        | Ok projection -> result.Graph, projection
        | Error errors -> failwithf "%A" errors
    let graphAndProjectionOfSource source = graphAndProjection (checkSource authority source)
    let admitted () = graphAndProjectionOfSource body

    let literal (graph: SemanticGraph) text =
        graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && node.Kind = SemanticKind.Literal(NativeLiteral.String text))
        |> Seq.map _.Id |> Seq.exactlyOne

    /// The omission relations of ordinary demand (call site, ordinal, actual)
    /// whose actual structurally contains `id`.
    let omissionsContaining (graph: SemanticGraph) id =
        let rec ancestors found current =
            match graph.Nodes.TryFind current |> Option.bind _.Parent with
            | Some parent when not (Set.contains parent found) -> ancestors (Set.add parent found) parent
            | _ -> found
        let enclosing = ancestors (Set.singleton id) id
        graph.Edges |> List.choose (fun edge ->
            match edge.Class, edge.Role, edge.Sources with
            | EdgeClass.Demand, EdgeRole.OrdinaryUnusedActual, _ :: _ :: actual :: _ when enclosing.Contains actual -> Some(edge.Target, edge.Ordinal, actual)
            | _ -> None)

    /// Reachable source calls of the fixture's one-argument `write`.
    let writeCalls (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.Application(callee, [_]) ->
                match graph.Nodes.TryFind callee with
                | Some { Kind = SemanticKind.VarRef(name, _) } -> name = "write" || name.EndsWith ".write"
                | _ -> false
            | _ -> false) |> Seq.map _.Id |> Seq.toList

    let pooled (graph: SemanticGraph) text =
        graph.StaticStringPool |> Option.exists (fun pool -> pool.Entries |> List.exists (fun entry -> entry.Content = text))

    let writeProofs (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node -> match node.Kind with SemanticKind.Obligation info -> info.Kind = "intrinsic-write-proof" | _ -> false)
        |> Seq.length

    /// The graph of a source with no error and a settled static string pool.
    let pooledGraph source =
        let graph, _ = graphAndProjectionOfSource source
        Assert.True(graph.StaticStringPool.IsSome)
        graph

    let literalKinds = ["storage-reservation"; "terminator-sentinel"; "view-containment"]

    /// The reachable nodes of one text.
    let occurrences (graph: SemanticGraph) text =
        graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && node.Kind = SemanticKind.Literal(NativeLiteral.String text))
        |> Seq.map _.Id |> Set.ofSeq

    /// The storage, view and sentinel proofs whose hyperedge names a reachable
    /// node of the text, each with its participants.
    let literalProofs (graph: SemanticGraph) text =
        let nodes = occurrences graph text
        graph.Edges |> List.choose (fun edge ->
            match graph.Nodes.TryFind edge.Target with
            | Some { Kind = SemanticKind.Obligation info }
                when edge.Class = EdgeClass.Obligation && List.contains info.Kind literalKinds && List.exists nodes.Contains edge.Sources ->
                Some (info, Set.ofList edge.Sources)
            | _ -> None)

    let proofKinds (proofs: (ObligationInfo * Set<NodeId>) list) = proofs |> List.map (fun (info, _) -> info.Kind) |> List.sort

    let textOf (graph: SemanticGraph) id =
        match graph.Nodes[id].Kind with
        | SemanticKind.Literal(NativeLiteral.String text) -> text
        | other -> failwithf "Participant %A is not a string literal: %A" id other

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
    member _.``A literal in an omitted actual is not a borrow origin and the omission relation is a participant`` () =
        let result = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.authority (IntrinsicWriteFixture.demandBody "0")
        Assert.DoesNotContain(result.Diagnostics, fun diagnostic -> diagnostic.Code = "CCS8403")
        let graph, projection = IntrinsicWriteFixture.graphAndProjection result
        let never = IntrinsicWriteFixture.literal graph "never demanded"
        let call = Assert.Single projection.IntrinsicWrites.Values
        let view = projection.ByteViews[call.Buffer]
        Assert.False(view.StaticOrigins.ContainsKey never)
        Assert.Equal<bigint list>([4I], view.StaticOrigins.Values |> Seq.toList)
        let site, _, actual = Assert.Single(IntrinsicWriteFixture.omissionsContaining graph never)
        Assert.Contains(site, view.Participants)
        Assert.Contains(actual, view.Participants)
        Assert.False(IntrinsicWriteFixture.pooled graph "never demanded")
        Assert.True(IntrinsicWriteFixture.pooled graph "kept")
        Assert.Equal(4, IntrinsicWriteFixture.writeProofs graph)

    [<Fact>]
    member _.``A literal in a demanded actual remains a borrow origin with its pool entry`` () =
        let graph, projection = IntrinsicWriteFixture.graphAndProjectionOfSource (IntrinsicWriteFixture.demandBody "value")
        let never = IntrinsicWriteFixture.literal graph "never demanded"
        let call = Assert.Single projection.IntrinsicWrites.Values
        let view = projection.ByteViews[call.Buffer]
        Assert.Empty(IntrinsicWriteFixture.omissionsContaining graph never)
        Assert.True(view.StaticOrigins.ContainsKey never)
        Assert.True(IntrinsicWriteFixture.pooled graph "never demanded")
        Assert.Equal(4, IntrinsicWriteFixture.writeProofs graph)

    [<Fact>]
    member _.``A literal reached from an omitted actual and from a demanded call is a borrow origin`` () =
        let graph, projection = IntrinsicWriteFixture.graphAndProjectionOfSource IntrinsicWriteFixture.sharedBody
        let both = IntrinsicWriteFixture.literal graph "both"
        let call = Assert.Single projection.IntrinsicWrites.Values
        let view = projection.ByteViews[call.Buffer]
        Assert.Equal<NodeId list>([both], view.StaticOrigins.Keys |> Seq.toList)
        let site, _, actual = IntrinsicWriteFixture.writeCalls graph |> List.collect (IntrinsicWriteFixture.omissionsContaining graph) |> Assert.Single
        Assert.Contains(site, view.Participants)
        Assert.Contains(actual, view.Participants)
        Assert.True(IntrinsicWriteFixture.pooled graph "both")

    [<Fact>]
    member _.``A binding written by a demanded call and inside an omitted actual is a borrow origin with its pool entry`` () =
        let result = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.writableAuthority IntrinsicWriteFixture.bindingBody
        let graph, projection = IntrinsicWriteFixture.graphAndProjection result
        let both = IntrinsicWriteFixture.literal graph "both"
        let call = Assert.Single projection.IntrinsicWrites.Values
        let view = projection.ByteViews[call.Buffer]
        Assert.Equal<NodeId list>([both], view.StaticOrigins.Keys |> Seq.toList)
        Assert.True(IntrinsicWriteFixture.pooled graph "both")
        Assert.Equal(4, IntrinsicWriteFixture.writeProofs graph)

    [<Fact>]
    member _.``The demanded inputs and the omissions of a formal are apart and ordered by call and ordinal`` () =
        let graph, _ = IntrinsicWriteFixture.graphAndProjectionOfSource IntrinsicWriteFixture.threeCallsBody
        let formal =
            graph.Nodes.Values |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.Lambda([("s", _, formal)], _, _, _, _) when node.IsReachable -> Some formal
                | _ -> None) |> Seq.exactlyOne
        let flow = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
        let inputs = Clef.Compiler.Baker.Ingredients.FormalDemand.reader graph flow formal |> Option.get
        let ordered (keys: (NodeId * int) list) = keys |> List.pairwise |> List.forall (fun (first, next) -> first < next)
        let a, bb, c = IntrinsicWriteFixture.literal graph "a", IntrinsicWriteFixture.literal graph "bb", IntrinsicWriteFixture.literal graph "c"
        Assert.Equal<Set<NodeId>>(set [a; bb], inputs.Demanded |> List.map _.Actual |> set)
        Assert.True(ordered (inputs.Demanded |> List.map (fun input -> input.Call, input.Ordinal)))
        Assert.All(inputs.Demanded, fun input ->
            Assert.Equal(0, input.Ordinal)
            Assert.Equal(Some [input.Actual], match graph.Nodes[input.Call].Kind with SemanticKind.Application(_, actuals) -> Some actuals | _ -> None))
        let omission = Assert.Single inputs.Omissions
        Assert.Equal<(NodeId * int * NodeId) list>(IntrinsicWriteFixture.omissionsContaining graph c, [omission.Site, omission.Ordinal, omission.Actual])
        Assert.Equal<NodeId list>([c], inputs.Omitted |> List.map _.Actual)

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

    [<Fact>]
    member _.``A never demanded literal has its storage view and sentinel proofs without a pool entry or residence`` () =
        let graph = IntrinsicWriteFixture.pooledGraph (IntrinsicWriteFixture.demandBody "0")
        let never = IntrinsicWriteFixture.literal graph "never demanded"
        Assert.NotEmpty(IntrinsicWriteFixture.omissionsContaining graph never)
        let proofs = IntrinsicWriteFixture.literalProofs graph "never demanded"
        Assert.Equal<string list>(IntrinsicWriteFixture.literalKinds, IntrinsicWriteFixture.proofKinds proofs)
        let anchors = Clef.Compiler.Nanopass.ObligationDischarge.ofGraph graph |> List.map _.Id |> Set.ofList
        for info, _ in proofs do Assert.Contains(info.Id, anchors)
        Assert.DoesNotContain(graph.StaticStringPool.Value.Entries, fun entry -> entry.Content = "never demanded" || List.contains never entry.NodeIds)
        Assert.DoesNotContain(graph.Edges, fun edge -> edge.Role = EdgeRole.Resides && edge.Target = never)
        Assert.Equal<string list>(IntrinsicWriteFixture.literalKinds, IntrinsicWriteFixture.proofKinds (IntrinsicWriteFixture.literalProofs graph "kept"))
        Assert.True(IntrinsicWriteFixture.pooled graph "kept")

    [<Fact>]
    member _.``The proofs of a literal are equal under either demand while the pool follows demand`` () =
        let omitted = IntrinsicWriteFixture.pooledGraph (IntrinsicWriteFixture.demandBody "0")
        let demanded = IntrinsicWriteFixture.pooledGraph (IntrinsicWriteFixture.demandBody "value")
        let statements graph =
            IntrinsicWriteFixture.literalProofs graph "never demanded"
            |> List.map (fun (info, participants) -> info.Kind, info.Statement, participants |> Set.map (IntrinsicWriteFixture.textOf graph))
            |> List.sort
        Assert.Equal<string list>(IntrinsicWriteFixture.literalKinds, IntrinsicWriteFixture.proofKinds (IntrinsicWriteFixture.literalProofs demanded "never demanded"))
        Assert.Equal<(string * string * Set<string>) list>(statements demanded, statements omitted)
        Assert.True(IntrinsicWriteFixture.pooled demanded "never demanded")
        Assert.False(IntrinsicWriteFixture.pooled omitted "never demanded")

    [<Fact>]
    member _.``Every reachable node of a text is a participant of the proofs of that text`` () =
        let graph = IntrinsicWriteFixture.pooledGraph IntrinsicWriteFixture.repeatedBody
        let nodes = IntrinsicWriteFixture.occurrences graph "same"
        Assert.Equal(2, nodes.Count)
        let proofs = IntrinsicWriteFixture.literalProofs graph "same"
        Assert.Equal<string list>(IntrinsicWriteFixture.literalKinds, IntrinsicWriteFixture.proofKinds proofs)
        for _, participants in proofs do Assert.Equal<Set<NodeId>>(nodes, participants)

    [<Fact>]
    member _.``The pool layout states materialized storage for a demanded literal and the omissions for a literal no demanded position reads`` () =
        let graph = IntrinsicWriteFixture.pooledGraph (IntrinsicWriteFixture.demandBody "0")
        let never = IntrinsicWriteFixture.literal graph "never demanded"
        let kept = IntrinsicWriteFixture.literal graph "kept"
        let entries = graph.StaticStringPool.Value.Entries
        let reachable =
            graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && (match node.Kind with SemanticKind.Literal(NativeLiteral.String _) -> true | _ -> false))
            |> Seq.map _.Id |> Set.ofSeq
        Assert.Equal<Set<NodeId>>(reachable, graph.LiteralStorage.Keys |> Set.ofSeq)
        Assert.Equal(LiteralStorage.Materialized(entries |> List.findIndex (fun entry -> List.contains kept entry.NodeIds)), graph.LiteralStorage[kept])
        let omissions =
            IntrinsicWriteFixture.omissionsContaining graph never
            |> List.map (fun (site, ordinal, actual) -> ({ Site = site; Ordinal = ordinal; Actual = actual }: OrdinaryOmission)) |> Set.ofList
        Assert.NotEmpty omissions
        Assert.Equal<Set<OrdinaryOmission>>(omissions, Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.deferrals graph |> Map.find never)
        match graph.LiteralStorage[never] with
        | LiteralStorage.NotMaterialized stated -> Assert.Equal<Set<OrdinaryOmission>>(omissions, Set.ofList stated)
        | other -> failwithf "A literal that no demanded position reads has the storage row %A" other
        entries |> List.iteri (fun index entry ->
            for id in entry.NodeIds do Assert.Equal(LiteralStorage.Materialized index, graph.LiteralStorage[id]))

    [<Fact>]
    member _.``The pool layout states materialized storage for every literal when the same literal is demanded`` () =
        let graph = IntrinsicWriteFixture.pooledGraph (IntrinsicWriteFixture.demandBody "value")
        let entries = graph.StaticStringPool.Value.Entries
        for text in ["never demanded"; "kept"] do
            let id = IntrinsicWriteFixture.literal graph text
            Assert.Equal(LiteralStorage.Materialized(entries |> List.findIndex (fun entry -> List.contains id entry.NodeIds)), graph.LiteralStorage[id])

    [<Fact>]
    member _.``A literal only in a function that is never called has no proofs`` () =
        let graph = IntrinsicWriteFixture.pooledGraph IntrinsicWriteFixture.uncalledBody
        let orphans = graph.Nodes.Values |> Seq.filter (fun node -> node.Kind = SemanticKind.Literal(NativeLiteral.String "orphan")) |> Seq.toList
        Assert.NotEmpty orphans
        Assert.All(orphans, fun node -> Assert.False node.IsReachable)
        Assert.DoesNotContain(graph.Edges, fun edge ->
            edge.Class = EdgeClass.Obligation && orphans |> List.exists (fun node -> List.contains node.Id edge.Sources))
        Assert.DoesNotContain(Clef.Compiler.Nanopass.ObligationDischarge.ofGraph graph, fun obligation -> obligation.Statement.Contains "\"orphan\"")
        Assert.Equal<string list>(IntrinsicWriteFixture.literalKinds, IntrinsicWriteFixture.proofKinds (IntrinsicWriteFixture.literalProofs graph "kept"))
