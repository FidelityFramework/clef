namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module IntrinsicBoundary = Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission

module IntrinsicWriteFixture =
    let platform = SourcePlatformFixture.platform
    let authority = SourcePlatformFixture.authority

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

    /// `writableAuthority` whose 8-bit representation is named uint8, the authority of
    /// the factory probe of step A2.
    let factoryAuthority = writableAuthority.Replace("Name = \"octet\"", "Name = \"uint8\"")

    /// The call `(pick true) "hello"` reaches the formal of `write` and resolves to two
    /// functions of one string, `write` and `other`, whose parameters differ.
    let pickBody = """module WriteFixture
let write (s: string) =
    let _ = Sys.write 1 s.Bytes s.Length
    ()
let other (t: string) = ()
let pick (flag: bool) = if flag then write else other
[<EntryPoint>]
let main _ =
    (pick true) "hello"
    0
"""

    /// The participants of targets the participant form states. A failure fails the test.
    let ofTargets call targets =
        match Clef.Compiler.Baker.Ingredients.Participants.ofTargets call targets with
        | Ok participants -> participants
        | Error failure -> failwithf "The targets of call %A cannot be stated: %A" call failure

    /// The result of a check, or the message of an exception the check throws.
    let checkWithoutException declaration source =
        try Ok (checkSource declaration source) with error -> Error error.Message

    /// The sites of the borrow rows of `write`: its byte view and its length.
    let borrowSites (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.filter (fun node ->
            node.IsReachable &&
            match node.Kind with
            | SemanticKind.StringByteBorrow _ | SemanticKind.FieldGet(_, "Length") -> true
            | _ -> false) |> Seq.map _.Id |> Seq.toList

    /// The message of the located error of a borrow whose origins are reached through a call
    /// whose targets the participant form cannot state.
    let targetsMessage text = "Source settlement is required before witnessing: BoundaryEmission: " + text

    /// The participants of an established borrow row. A pending row fails the test.
    let established (evidence: ParticipantEvidence) =
        match evidence with
        | ParticipantEvidence.Established participants -> participants
        | ParticipantEvidence.Pending _ -> failwith "The string borrow row states its participants as pending."

    /// The string byte view rows of the graph, each with the sources of its edge.
    let viewRows (graph: SemanticGraph) =
        graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringByteView view -> Some(view, edge.Sources) | _ -> None)

    /// The reachable calls of `write` whose argument is the literal of `text`.
    let writeCallOf (graph: SemanticGraph) text =
        let argument = literal graph text
        writeCalls graph |> List.filter (fun call ->
            match graph.Nodes[call].Kind with
            | SemanticKind.Application(_, [actual]) -> actual = argument
            | _ -> false) |> Seq.exactlyOne

    /// The occurrences of one group in one role.
    let inGroup group role (participants: Participant list) =
        participants |> List.filter (fun participant -> participant.Group = group && participant.Role = role)

    let occurrence node role ordinal group : Participant = { Node = node; Role = role; Ordinal = ordinal; Group = group }

    /// The omissions the participants state for an omitted call, each as a complete tuple:
    /// the omitted call, the omission's site and ordinal, and the omitted actuals stated at
    /// that site and ordinal.
    let omissionTuples omitted (participants: Participant list) =
        inGroup omitted ParticipantRole.OmissionSite participants
        |> List.map (fun site ->
            omitted, site.Node, site.Ordinal,
            participants
            |> List.filter (fun actual -> actual.Role = ParticipantRole.OmittedActual && actual.Group = site.Node && actual.Ordinal = site.Ordinal)
            |> List.map _.Node)
        |> List.sort

module private ConditionalStringOriginFixture =
    let source guard other =
        "module ConditionalStringOrigin\nlet writeChoice (flag: bool) =\n" +
        "    let text = if " + guard + " then \"é\" else \"" + other + "\"\n" +
        "    let _ = Sys.write 1 text.Bytes text.Length\n    ()\n" +
        "[<EntryPoint>]\nlet main _ =\n    writeChoice true\n    writeChoice false\n    0\n"

    let check source = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.writableAuthority source

    let conditional (graph: SemanticGraph) =
        graph.Nodes.Values |> Seq.find (fun node ->
            Types.isStringType node.Type && match node.Kind with SemanticKind.IfThenElse _ -> true | _ -> false)

    let tuple site participants =
        participants |> List.filter (fun participant -> participant.Group = site && participant.Role = ParticipantRole.Construction)
        |> List.sortBy _.Ordinal |> List.map (fun participant -> participant.Ordinal, participant.Node)

module private LazyStringOriginFixture =
    let source cohort =
        let declaration, body =
            match cohort with
            | "capture" -> "", "    let original = \"é\"\n    let delayed = lazy original\n    write (Lazy.force delayed)\n    write (Lazy.force delayed)\n"
            | "factory" -> "let make () = lazy \"é\"\n", "    let first = make ()\n    let second = make ()\n    let alias = first\n    write (Lazy.force alias)\n    write (Lazy.force second)\n"
            | _ -> "", "    let delayed = lazy \"é\"\n    write (Lazy.force delayed)\n    write (Lazy.force delayed)\n"
        "module LazyStringOrigin\nlet write (s: string) =\n    let _ = Sys.write 1 s.Bytes s.Length\n    ()\n" +
        declaration + "[<EntryPoint>]\nlet main _ =\n" + body + "    0\n"

    let check source =
        // Lazy environment storage names the platform's octet offer uint8.
        // This fixture declares that same 8-bit, 0..255 offer explicitly.
        let platform =
            let octet = IntrinsicWriteFixture.platform.Representations["octet"]
            { IntrinsicWriteFixture.platform with
                Representations = IntrinsicWriteFixture.platform.Representations.Remove("octet").Add("uint8", { octet with Name = "uint8" }) }
        let parse text path =
            match parseStringWithDefaults text path with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "%A" errors
        checkParsedInputsWithPlatform
            [ parse (IntrinsicWriteFixture.writableAuthority.Replace("\"octet\"", "\"uint8\"")) "write-authority.clef"
              parse source "intrinsic-write.clef" ] (Some platform)

type IntrinsicWriteCases() =
    [<Theory>]
    [<InlineData("literal")>]
    [<InlineData("conditional")>]
    [<InlineData("forwarded")>]
    member _.``Ordinary string call results retain immutable borrow origins and call support`` shape =
        let declaration, expression =
            match shape with
            | "conditional" -> "let make (flag: bool) = if flag then \"é\" else \"plane\"\n", "make true"
            | "forwarded" -> "let make (text: string) = text\n", "make \"é\""
            | _ -> "let make () = \"é\"\n", "make ()"
        let source = "module StringCallResult\n" + declaration +
                     "[<EntryPoint>]\nlet main _ =\n    let text = " + expression +
                     "\n    let _ = Sys.write 1 text.Bytes text.Length\n    0\n"
        let graph, projection = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.writableAuthority source |> IntrinsicWriteFixture.graphAndProjection
        let call = Assert.Single projection.IntrinsicWrites.Values
        let view = projection.ByteViews[call.Buffer]
        let extent = projection.StringExtents[call.Count]
        let expected =
            [ IntrinsicWriteFixture.literal graph "é", 2I ] @
            (if shape = "conditional" then [IntrinsicWriteFixture.literal graph "plane", 5I] else []) |> Map.ofList
        Assert.Equal<Map<NodeId,bigint>>(expected, view.StaticOrigins)
        Assert.Equal<Map<NodeId,bigint>>(expected, extent.StaticOrigins)
        let result = graph.Nodes[view.ExtentSource]
        Assert.True(match result.Kind with SemanticKind.Application _ -> true | _ -> false)
        for evidence in [view.Participants; extent.Participants] do
            let participants = IntrinsicWriteFixture.established evidence
            Assert.Contains(participants, fun participant -> participant.Role = ParticipantRole.Callee && participant.Group = result.Id)
            Assert.Contains(participants, fun participant -> participant.Role = ParticipantRole.CalleeBody)
        let changedResult = { result with Children = List.rev result.Children }
        let changed = { graph with Nodes = graph.Nodes.Add(result.Id, changedResult) }
        let flow = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
        let assertRefused current =
            Assert.Equal(Ok None, Clef.Compiler.Baker.Recipes.StringComparisonRecipes.stringOrigin current flow result.Id result.Id)
        assertRefused changed
        Assert.True(IntrinsicBoundary.project changed |> Result.isError)
        let resolved = flow.Calls[result.Id]
        for refused in [{ resolved with Complete = false }; { resolved with Unknown = true }; { resolved with Targets = [] }] do
            let alteredFlow = { flow with Calls = flow.Calls.Add(result.Id, refused) }
            Assert.Equal(Ok None, Clef.Compiler.Baker.Recipes.StringComparisonRecipes.stringOrigin graph alteredFlow result.Id result.Id)
        let target = Assert.Single resolved.Targets
        // A revisited call-result node cannot recursively manufacture an origin.
        let cyclic = { resolved with Targets = [{ target with Body = result.Id }] }
        Assert.Equal(Ok None, Clef.Compiler.Baker.Recipes.StringComparisonRecipes.stringOrigin graph { flow with Calls = flow.Calls.Add(result.Id, cyclic) } result.Id result.Id)
        // Every possible return must establish a string origin, even when the
        // first target has complete literal evidence.
        let nonString = graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.Literal(NativeLiteral.Int _) -> true | _ -> false)
        let mixed = { resolved with Targets = [target; { target with Body = nonString.Id }] }
        Assert.Equal(Ok None, Clef.Compiler.Baker.Recipes.StringComparisonRecipes.stringOrigin graph { flow with Calls = flow.Calls.Add(result.Id, mixed) } result.Id result.Id)
        if shape <> "conditional" then
            let retained = graph.Edges |> List.filter (fun edge ->
                edge.Role <> EdgeRole.OrdinaryUnusedFormal && edge.Role <> EdgeRole.OrdinaryUnusedActual)
            let brokenDemand = { graph with Edges = retained }
            Assert.NotEqual(graph.Edges.Length, brokenDemand.Edges.Length)
            let refusal = Assert.Throws<System.InvalidOperationException>(fun () ->
                Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.read brokenDemand |> ignore)
            Assert.StartsWith("PSG settlement (OrdinaryDemand) did not settle", refusal.Message)
            if shape = "literal" then
                match Clef.Compiler.Baker.Recipes.StringComparisonRecipes.stringOrigin brokenDemand flow result.Id result.Id with
                | Ok(Some(_, origins, _)) -> Assert.Equal<Map<NodeId,bigint>>(expected, origins)
                | other -> failwithf "Independent literal origin was not derived: %A" other
            else
                let formalRefusal = Assert.Throws<System.InvalidOperationException>(fun () ->
                    Clef.Compiler.Baker.Recipes.StringComparisonRecipes.stringOrigin brokenDemand flow result.Id result.Id |> ignore)
                Assert.StartsWith("PSG settlement (OrdinaryDemand) did not settle", formalRefusal.Message)
            // A local observation grants no ledger/projection authority to the
            // invalid graph. The complete incidence census still refuses it.
            Assert.True(IntrinsicBoundary.project brokenDemand |> Result.isError)
        let binding =
            let callee = match result.Kind with SemanticKind.Application(callee, _) -> callee | _ -> failwith "Missing call"
            match graph.Nodes[callee].Kind with SemanticKind.VarRef(_, Some binding) -> binding | _ -> failwith "Missing binding"
        let declaration =
            match Clef.Compiler.Baker.Recipes.BoundaryDeclarations.bindingPath graph binding with
            | Ok(path, formals, body) ->
                { Binding = binding; Path = path; Implementation = List.last path
                  Formals = formals |> List.map (fun (_, _, formal) -> formal); Body = body }
            | Error reason -> failwith reason
        Assert.Equal(target.Lambda, declaration.Implementation)
        let markedForeign = Clef.Compiler.Baker.Recipes.BoundaryDeclarations.row declaration
        let foreignGraph = { graph with Edges = markedForeign :: graph.Edges }
        assertRefused foreignGraph
        Assert.True(IntrinsicBoundary.project foreignGraph |> Result.isError)
        let unknownBody = { graph.Nodes[target.Body] with Kind = SemanticKind.VarRef("unknown", None); Children = [] }
        let unknownGraph = { graph with Nodes = graph.Nodes.Add(target.Body, unknownBody) }
        assertRefused unknownGraph
        Assert.True(IntrinsicBoundary.project unknownGraph |> Result.isError)

    [<Theory>]
    [<InlineData("flag", "plane", 5)>]
    [<InlineData("flag", "xy", 2)>]
    [<InlineData("true", "plane", 5)>]
    [<InlineData("false", "plane", 5)>]
    member _.``Conditional string origins retain both exact UTF8 branches before and after range settlement`` (guard, other, length: int) =
        let graph, projection =
            ConditionalStringOriginFixture.source guard other |> ConditionalStringOriginFixture.check
            |> IntrinsicWriteFixture.graphAndProjection
        let conditional = ConditionalStringOriginFixture.conditional graph
        let condition, yes, no =
            match conditional.Kind with SemanticKind.IfThenElse(condition, yes, Some no) -> condition, yes, no | _ -> failwith "Missing complete conditional"
        let expectedOrigins = Map.ofList [yes, 2I; no, bigint length]
        let expectedTuple = [0, conditional.Id; 1, condition; 2, yes; 3, no]
        let call = Assert.Single projection.IntrinsicWrites.Values
        let view = projection.ByteViews[call.Buffer]
        let extent = projection.StringExtents[call.Count]
        Assert.Equal<Map<NodeId, bigint>>(expectedOrigins, view.StaticOrigins)
        Assert.Equal<Map<NodeId, bigint>>(expectedOrigins, extent.StaticOrigins)
        Assert.Equal(conditional.Id, view.ExtentSource)
        Assert.Equal(view.ExtentSource, extent.ExtentSource)
        Assert.Equal(Some(ValueRange.bounded 2I (bigint length)), graph.Nodes[call.Count].ValueRange)
        for participants in [view.Participants; extent.Participants] do
            let occurrences = IntrinsicWriteFixture.established participants
            Assert.Equal<(int * NodeId) list>(expectedTuple, ConditionalStringOriginFixture.tuple conditional.Id occurrences)
            for branch in [yes; no] do
                Assert.Contains(occurrences, fun participant -> participant.Node = branch && participant.Role = ParticipantRole.Origin && participant.Group = branch)
        let histories = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringBorrowHistory history when history.Site = view.Site || history.Site = extent.Site -> Some history | _ -> None)
        Assert.Equal(2, histories.Length)
        for history in histories do
            Assert.Equal<(int * NodeId) list>(expectedTuple, ConditionalStringOriginFixture.tuple conditional.Id history.Early.Derived)
        let bounds = [2I,2I,3I; bigint length,bigint length,bigint length + 1I] |> List.sort
        Assert.Contains(projection.IntrinsicWriteProofs[call.Site], fun proof ->
            match proof.Body with ObligationBody.StringBorrowBound actual -> List.sort actual = bounds | _ -> false)

    [<Fact>]
    member _.``Conditional string origins preserve both branches through a complete formal input`` () =
        let source = "module ConditionalFormal\nlet write (text: string) =\n    let _ = Sys.write 1 text.Bytes text.Length\n    ()\nlet choose (flag: bool) =\n    write (if flag then \"é\" else \"plane\")\n[<EntryPoint>]\nlet main _ =\n    choose true\n    choose false\n    0\n"
        let graph, projection = ConditionalStringOriginFixture.check source |> IntrinsicWriteFixture.graphAndProjection
        let conditional = ConditionalStringOriginFixture.conditional graph
        let call = Assert.Single projection.IntrinsicWrites.Values
        let view = projection.ByteViews[call.Buffer]
        let expected = Map.ofList [IntrinsicWriteFixture.literal graph "é", 2I; IntrinsicWriteFixture.literal graph "plane", 5I]
        Assert.Equal<Map<NodeId,bigint>>(expected, view.StaticOrigins)
        Assert.Equal<Map<NodeId,bigint>>(expected, projection.StringExtents[call.Count].StaticOrigins)
        Assert.Equal(Some(ValueRange.bounded 2I 5I), graph.Nodes[call.Count].ValueRange)
        Assert.Contains(IntrinsicWriteFixture.established view.Participants, fun participant -> participant.Node = conditional.Id && participant.Role = ParticipantRole.ReachingActual)

    [<Theory>]
    [<InlineData("unknown")>]
    [<InlineData("mutable")>]
    [<InlineData("absent")>]
    [<InlineData("missing-else")>]
    [<InlineData("child-order")>]
    [<InlineData("guard-type")>]
    member _.``A conditional origin refuses an incomplete branch or altered source tuple`` defect =
        let graph, _ = ConditionalStringOriginFixture.source "flag" "plane" |> ConditionalStringOriginFixture.check |> IntrinsicWriteFixture.graphAndProjection
        let conditional = ConditionalStringOriginFixture.conditional graph
        let guard, yes, no = match conditional.Kind with SemanticKind.IfThenElse(g,y,Some n) -> g,y,n | _ -> failwith "Missing complete conditional"
        let change id rewrite = { graph with Nodes = graph.Nodes.Add(id, rewrite graph.Nodes[id]) }
        let changed =
            match defect with
            | "unknown" -> change yes (fun node -> { node with Kind = SemanticKind.VarRef("unknown",None); Children = [] })
            | "mutable" -> change yes (fun node -> { node with Kind = SemanticKind.Binding("mutable-source",true,false,None); Children = [no] })
            | "absent" -> { graph with Nodes = graph.Nodes.Remove no }
            | "missing-else" -> change conditional.Id (fun node -> { node with Kind = SemanticKind.IfThenElse(guard,yes,None); Children = [guard;yes] })
            | "child-order" -> change conditional.Id (fun node -> { node with Children = [guard;no;yes] })
            | _ -> change guard (fun node -> { node with Type = Types.stringType })
        let flow = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
        Assert.Equal(Ok None, Clef.Compiler.Baker.Recipes.StringComparisonRecipes.stringOrigin changed flow conditional.Id conditional.Id)
        Assert.True(IntrinsicBoundary.project changed |> Result.isError)

    [<Fact>]
    member _.``Conditional origin authority rejects reordered complete branches and a replaced guard`` () =
        let graph, _ = ConditionalStringOriginFixture.source "flag" "plane" |> ConditionalStringOriginFixture.check |> IntrinsicWriteFixture.graphAndProjection
        let conditional = ConditionalStringOriginFixture.conditional graph
        let guard, yes, no = match conditional.Kind with SemanticKind.IfThenElse(g,y,Some n) -> g,y,n | _ -> failwith "Missing complete conditional"
        let swapped = { conditional with Kind = SemanticKind.IfThenElse(guard,no,Some yes); Children = [guard;no;yes] }
        let guardNode = { graph.Nodes[guard] with Kind = SemanticKind.Literal(NativeLiteral.Bool true); Children = [] }
        for nodes in [graph.Nodes.Add(conditional.Id,swapped); graph.Nodes.Add(guard,guardNode)] do
            Assert.True(IntrinsicBoundary.project { graph with Nodes = nodes } |> Result.isError)

    [<Fact>]
    member _.``Boundary capture observations preserve the literal payload read by kernel transport`` () =
        let graph, _ = IntrinsicWriteFixture.admitted ()
        let template = graph.Nodes.Values |> Seq.find (fun node ->
            match node.Kind with SemanticKind.Literal(NativeLiteral.Int _) -> true | _ -> false)
        let literal = { template with Kind = SemanticKind.Literal(NativeLiteral.Int(16L, NTUKind.NTUint(NTUWidth.Fixed 16))); Children = [] }
        let shape = (Clef.Compiler.Baker.Ingredients.Boundaries.premise literal).Shape
        // KernelDeclarations decodes this exact singleton payload. Capture
        // metadata belongs only to lambda/sequence/lazy shapes, even when empty.
        let transported =
            match shape with
            | { Form = ("integer" | "unsigned-integer"); Numbers = [value] } -> Some value
            | _ -> None
        Assert.Equal(Some 16I, transported)
        Assert.Equal<bigint list>([16I], shape.Numbers)

    [<Fact>]
    member _.``Boundary source premise retains ordered raw capture identity and mutability`` () =
        let graph, _ = IntrinsicWriteFixture.admitted ()
        let node = graph.Nodes.Values |> Seq.find (fun node -> match node.Kind with SemanticKind.Lambda _ -> true | _ -> false)
        let formals, body, enclosing, context =
            match node.Kind with
            | SemanticKind.Lambda(formals, body, _, enclosing, context) -> formals, body, enclosing, context
            | _ -> failwith "Missing lambda"
        let captures : CaptureInfo list =
            [ { Name = "first"; Type = node.Type; IsMutable = false; SourceNodeId = Some node.Id }
              { Name = "second"; Type = node.Type; IsMutable = false; SourceNodeId = Some body } ]
        let mutations =
            [ { captures.Head with SourceNodeId = Some body } :: captures.Tail
              { captures.Head with SourceNodeId = None } :: captures.Tail
              { captures.Head with IsMutable = true } :: captures.Tail
              List.rev captures ]
        for shape in [ (fun values -> SemanticKind.Lambda(formals, body, values, enclosing, context))
                       (fun values -> SemanticKind.SeqExpr(body, values))
                       (fun values -> SemanticKind.LazyExpr(body, values)) ] do
            let original = { node with Kind = shape captures }
            let expected = Clef.Compiler.Baker.Ingredients.Boundaries.premise original
            for changed in mutations do
                let actual = Clef.Compiler.Baker.Ingredients.Boundaries.premise { node with Kind = shape changed }
                Assert.NotEqual<BoundarySourcePremise>(expected, actual)

    [<Fact>]
    member _.``Lazy zero-length comparison retains source origin authority through extent rows`` () =
        let source = "module LazyEmptyOrigin\n[<EntryPoint>]\nlet main _ =\n    let delayed = lazy \"\"\n    if Lazy.force delayed = \"\" then 0 else 1\n"
        let graph, projection = LazyStringOriginFixture.check source |> IntrinsicWriteFixture.graphAndProjection
        Assert.Empty projection.ByteViews
        Assert.Contains(projection.StringExtents.Values, fun extent ->
            IntrinsicWriteFixture.established extent.Participants |> List.exists (fun participant -> participant.Role = ParticipantRole.LazyStringOrigin))
        let domain = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryDomain value -> Some value | _ -> None) |> Assert.Single
        Assert.True(domain.StringOriginRelations.IsSome)
        let changed = { graph with Edges = graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.LazyMemoization) }
        Assert.True(IntrinsicBoundary.project changed |> Result.isError)

    [<Theory>]
    [<InlineData("missing")>]
    [<InlineData("duplicate")>]
    [<InlineData("ordinal")>]
    [<InlineData("class")>]
    [<InlineData("source-order")>]
    [<InlineData("capture-mode")>]
    [<InlineData("extra-consumer")>]
    [<InlineData("list-order")>]
    [<InlineData("declaration-root")>]
    [<InlineData("unsupported-payload")>]
    [<InlineData("marker-missing")>]
    member _.``Boundary snapshot refuses changed lazy provenance with unchanged nodes`` defect =
        let graph, _ =
            LazyStringOriginFixture.source "capture" |> LazyStringOriginFixture.check
            |> IntrinsicWriteFixture.graphAndProjection
        let force = graph.Edges |> List.find (fun edge -> edge.Role = EdgeRole.LazyMemoization)
        let replace changed = graph.Edges |> List.map (fun edge -> if obj.ReferenceEquals(edge, force) then changed else edge)
        let edges =
            match defect with
            | "missing" -> graph.Edges |> List.filter (fun edge -> not (obj.ReferenceEquals(edge, force)))
            | "duplicate" -> force :: graph.Edges
            | "ordinal" -> replace { force with Ordinal = force.Ordinal + 1 }
            | "class" -> replace { force with Class = EdgeClass.Reference }
            | "source-order" -> replace { force with Sources = List.rev force.Sources }
            | "list-order" -> List.rev graph.Edges
            | "capture-mode" -> graph.Edges |> List.map (fun edge -> match edge.Role with EdgeRole.LazyCapture false -> { edge with Role = EdgeRole.LazyCapture true } | _ -> edge)
            | "unsupported-payload" -> { force with Class = EdgeClass.Reference; Role = EdgeRole.StringByteRange(1I, 2I) } :: graph.Edges
            | "marker-missing" -> graph.Edges |> List.map (fun edge ->
                match edge.Role with
                | EdgeRole.StringByteView view ->
                    let participants = IntrinsicWriteFixture.established view.Participants |> List.filter (fun value -> value.Role <> ParticipantRole.LazyStringOrigin)
                    Clef.Compiler.Baker.Ingredients.StringBytes.viewRow { view with Participants = ParticipantEvidence.Established participants }
                | _ -> edge)
            | _ -> { Class = EdgeClass.Reference; Role = EdgeRole.Definition; Ordinal = 0; Sources = [force.Target]; Target = force.Target } :: graph.Edges
        let changed =
            if defect = "declaration-root" then { graph with DeclarationRoots = (force.Target, DeclRoot.EntryPoint) :: graph.DeclarationRoots }
            else { graph with Edges = edges }
        Assert.Same(graph.Nodes, changed.Nodes)
        Assert.True(IntrinsicBoundary.project changed |> Result.isError)

    [<Theory>]
    [<InlineData("read-kind")>]
    [<InlineData("store-order")>]
    [<InlineData("guard")>]
    [<InlineData("unguarded-read")>]
    [<InlineData("conditional-result")>]
    member _.``Lazy string origins refuse a damaged force even when the literal is resident`` defect =
        let graph, _ = LazyStringOriginFixture.source "capture" |> LazyStringOriginFixture.check |> IntrinsicWriteFixture.graphAndProjection
        let force = (Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues.settle graph).Forces.Values |> Seq.head
        let change id rewrite = { graph with Nodes = graph.Nodes.Add(id, rewrite graph.Nodes[id]) }
        let changed =
            match defect with
            | "read-kind" -> change force.CachedRead (fun node ->
                match node.Kind with
                | SemanticKind.LazyRead(environment, slot) -> { node with Kind = SemanticKind.LazyBorrow(environment, slot) }
                | _ -> failwith "Missing cached read")
            | "store-order" -> change force.UncachedBranch (fun node ->
                match node.Kind with
                | SemanticKind.Sequential [binding; store; publication; result] ->
                    { node with Kind = SemanticKind.Sequential [binding; publication; store; result]; Children = [binding; publication; store; result] }
                | _ -> failwith "Missing uncached spine")
            | "guard" -> change force.Conditional (fun node ->
                match node.Kind with
                | SemanticKind.IfThenElse(_, yes, no) -> { node with Kind = SemanticKind.IfThenElse(force.CachedRead, yes, no) }
                | _ -> failwith "Missing force guard")
            | "conditional-result" -> change force.Conditional (fun node ->
                { node with Kind = SemanticKind.Literal(NativeLiteral.String "é"); Children = [] })
            | _ ->
                let id = NodeId.fresh()
                { graph with Nodes = graph.Nodes.Add(id, { graph.Nodes[force.CachedRead] with Id = id; Parent = None }) }
        Assert.NotEmpty((Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues.settle changed).Residuals)
        Assert.True(IntrinsicBoundary.project changed |> Result.isError)
        let failed =
            try
                let flow = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve changed
                match Clef.Compiler.Baker.Recipes.StringComparisonRecipes.stringOrigin changed flow force.Site force.Site with
                | Ok (Some _) -> false
                | _ -> true
            with :? System.InvalidOperationException -> true // Stale ordinary-demand incidence is also a source refusal.
        Assert.True(failed)

    [<Fact>]
    member _.``Lazy string boundary retains the embedded declaration root independently of root rows`` () =
        let graph, _ = LazyStringOriginFixture.source "capture" |> LazyStringOriginFixture.check |> IntrinsicWriteFixture.graphAndProjection
        let binding = graph.Nodes.Values |> Seq.find (fun node -> match node.Kind with SemanticKind.Binding(_, _, _, Some _) -> true | _ -> false)
        let changedBinding =
            match binding.Kind with
            | SemanticKind.Binding(name, mutable', recursive', _) -> { binding with Kind = SemanticKind.Binding(name, mutable', recursive', None) }
            | _ -> failwith "Missing declaration binding"
        let changed = { graph with Nodes = graph.Nodes.Add(binding.Id, changedBinding) }
        Assert.Equal<(NodeId * DeclRoot) list>(graph.DeclarationRoots, changed.DeclarationRoots)
        Assert.True(IntrinsicBoundary.project changed |> Result.isError)

    [<Theory>]
    [<InlineData("literal")>]
    [<InlineData("capture")>]
    [<InlineData("factory")>]
    member _.``Two lazy forces retain the exact immutable UTF8 origin and complete protocol participants`` cohort =
        let graph, projection =
            LazyStringOriginFixture.source cohort |> LazyStringOriginFixture.check
            |> IntrinsicWriteFixture.graphAndProjection
        let call = Assert.Single projection.IntrinsicWrites.Values
        let view = projection.ByteViews[call.Buffer]
        let extent = projection.StringExtents[call.Count]
        let origin = IntrinsicWriteFixture.literal graph "é"
        Assert.Equal<Map<NodeId, bigint>>(Map.ofList [origin, 2I], view.StaticOrigins)
        Assert.Equal(view.ExtentSource, extent.ExtentSource)
        Assert.Equal<Map<NodeId, bigint>>(view.StaticOrigins, extent.StaticOrigins)
        Assert.Equal(Some(ValueRange.bounded 2I 2I), graph.Nodes[call.Count].ValueRange)
        let forces = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LazyMemoization)
        Assert.Equal(2, forces.Length)
        let viewParticipants = IntrinsicWriteFixture.established view.Participants |> List.map _.Node |> Set.ofList
        let extentParticipants = IntrinsicWriteFixture.established extent.Participants |> List.map _.Node |> Set.ofList
        for force in forces do
            Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues.force graph force.Target).IsSome)
            for participant in force.Target :: force.Sources do
                Assert.Contains(participant, viewParticipants)
                Assert.Contains(participant, extentParticipants)
        Assert.Empty((Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues.settle graph).Residuals)
        Assert.Contains(projection.IntrinsicWriteProofs[call.Site], fun proof ->
            proof.Body = ObligationBody.StringBorrowBound [(2I, 2I, 3I)])

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
        let site, ordinal, actual = Assert.Single(IntrinsicWriteFixture.omissionsContaining graph never)
        let omitted = IntrinsicWriteFixture.writeCallOf graph "never demanded"
        let participants = IntrinsicWriteFixture.established view.Participants
        Assert.Contains(IntrinsicWriteFixture.occurrence site ParticipantRole.OmissionSite ordinal omitted, participants)
        Assert.Contains((omitted, site, ordinal, [actual]), IntrinsicWriteFixture.omissionTuples omitted participants)
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
        let omitted = IntrinsicWriteFixture.writeCalls graph |> List.filter (fun call -> not (IntrinsicWriteFixture.omissionsContaining graph call).IsEmpty) |> Assert.Single
        let site, ordinal, actual = IntrinsicWriteFixture.omissionsContaining graph omitted |> Assert.Single
        let participants = IntrinsicWriteFixture.established view.Participants
        Assert.Contains(IntrinsicWriteFixture.occurrence site ParticipantRole.OmissionSite ordinal omitted, participants)
        Assert.Contains((omitted, site, ordinal, [actual]), IntrinsicWriteFixture.omissionTuples omitted participants)
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
        let omitted = Assert.Single inputs.Omitted
        let omission = Assert.Single omitted.Omissions
        Assert.Equal<(NodeId * int * NodeId) list>(IntrinsicWriteFixture.omissionsContaining graph c, [omission.Site, (match omission.Origin with OrdinaryOmissionOrigin.CallArgument ordinal -> ordinal | _ -> failwith "Expected a call omission"), omission.Actual])
        Assert.Equal(c, omitted.Input.Actual)

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
            |> List.map (fun (site, ordinal, actual) -> ({ Site = site; Origin = OrdinaryOmissionOrigin.CallArgument ordinal; Actual = actual }: OrdinaryOmission)) |> Set.ofList
        Assert.NotEmpty omissions
        Assert.Equal<Set<OrdinaryOmission>>(omissions, Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.deferrals graph |> Map.find never)
        match graph.LiteralStorage[never] with
        | LiteralStorage.NotMaterialized (StoragePremise.Established stated) -> Assert.Equal<Set<OrdinaryOmission>>(omissions, Set.ofList stated)
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

    [<Fact>]
    member _.``The borrow participants state roles and groups and pair an omitted call with its omission`` () =
        let source = """module WriteFixture
let write (s: string) =
    let _ = Sys.write 1 s.Bytes s.Length
    ()
let discard (offset: int) (unused: int) = offset
let msg = "hello"
[<EntryPoint>]
let main _ =
    write msg
    if discard 3 (write msg; 0) = 3 then 0 else 1
"""
        let result = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.factoryAuthority source
        DimensionalCases.noErrors result
        let graph = result.Graph
        let view, sources = Assert.Single(IntrinsicWriteFixture.viewRows graph)
        let participants = IntrinsicWriteFixture.established view.Participants
        Assert.Equal<NodeId list>(participants |> List.map _.Node, sources)
        let calls = IntrinsicWriteFixture.writeCalls graph
        let omitted = calls |> List.filter (fun call -> not (IntrinsicWriteFixture.omissionsContaining graph call).IsEmpty) |> Assert.Single
        let demanded = calls |> List.filter ((<>) omitted) |> Assert.Single
        let hello = IntrinsicWriteFixture.literal graph "hello"
        Assert.Contains(IntrinsicWriteFixture.occurrence demanded ParticipantRole.ReachingCall 0 demanded, participants)
        Assert.Contains(IntrinsicWriteFixture.occurrence hello ParticipantRole.Origin 0 demanded, participants)
        Assert.Contains(IntrinsicWriteFixture.occurrence omitted ParticipantRole.OmittedCall 0 omitted, participants)
        let site, ordinal, actual = IntrinsicWriteFixture.omissionsContaining graph omitted |> Assert.Single
        Assert.Equal<Participant list>([IntrinsicWriteFixture.occurrence site ParticipantRole.OmissionSite ordinal omitted],
                                       IntrinsicWriteFixture.inGroup omitted ParticipantRole.OmissionSite participants)
        Assert.Equal<(NodeId * NodeId * int * NodeId list) list>([omitted, site, ordinal, [actual]], IntrinsicWriteFixture.omissionTuples omitted participants)
        Assert.Empty(IntrinsicWriteFixture.inGroup demanded ParticipantRole.OmissionSite participants)

    [<Fact>]
    member _.``Each demanded call of one binding is its own group with the binding and its origin`` () =
        let source = IntrinsicWriteFixture.bindingBody.Replace("then write msg\n    0\n", "then write msg\n    write msg\n    0\n")
        let result = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.writableAuthority source
        DimensionalCases.noErrors result
        let graph = result.Graph
        let view, _ = Assert.Single(IntrinsicWriteFixture.viewRows graph)
        let participants = IntrinsicWriteFixture.established view.Participants
        let both = IntrinsicWriteFixture.literal graph "both"
        let binding = graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && match node.Kind with SemanticKind.Binding("msg", _, _, _) -> true | _ -> false) |> Seq.exactlyOne
        let demanded = IntrinsicWriteFixture.writeCalls graph |> List.filter (fun call -> (IntrinsicWriteFixture.omissionsContaining graph call).IsEmpty)
        Assert.Equal(2, demanded.Length)
        for call in demanded do
            Assert.Equal<Participant list>([IntrinsicWriteFixture.occurrence call ParticipantRole.ReachingCall 0 call],
                                           IntrinsicWriteFixture.inGroup call ParticipantRole.ReachingCall participants)
            Assert.Equal<NodeId list>([both], IntrinsicWriteFixture.inGroup call ParticipantRole.Origin participants |> List.map _.Node)
            Assert.Equal(1, IntrinsicWriteFixture.inGroup call ParticipantRole.Path participants |> List.filter (fun path -> path.Node = binding.Id) |> List.length)

    [<Fact>]
    member _.``Two omitted calls under different omissions each name only their own omission`` () =
        let source = """module WriteFixture
let write (s: string) =
    let _ = Sys.write 1 s.Bytes s.Length
    ()
let discard (value: int) = 0
[<EntryPoint>]
let main _ =
    write "kept"
    if discard (write "a"; 0) = 0 then (if discard (write "b"; 0) = 0 then 0 else 1) else 2
"""
        let graph, projection = IntrinsicWriteFixture.graphAndProjectionOfSource source
        let call = Assert.Single projection.IntrinsicWrites.Values
        let view = projection.ByteViews[call.Buffer]
        let participants = IntrinsicWriteFixture.established view.Participants
        let first, second = IntrinsicWriteFixture.writeCallOf graph "a", IntrinsicWriteFixture.writeCallOf graph "b"
        for omitted in [first; second] do
            let site, ordinal, actual = IntrinsicWriteFixture.omissionsContaining graph omitted |> Assert.Single
            Assert.Equal<Participant list>([IntrinsicWriteFixture.occurrence site ParticipantRole.OmissionSite ordinal omitted],
                                           IntrinsicWriteFixture.inGroup omitted ParticipantRole.OmissionSite participants)
            Assert.Equal<(NodeId * NodeId * int * NodeId list) list>([omitted, site, ordinal, [actual]], IntrinsicWriteFixture.omissionTuples omitted participants)
        let firstSites = IntrinsicWriteFixture.omissionsContaining graph first |> List.map (fun (site, _, _) -> site)
        let secondSites = IntrinsicWriteFixture.omissionsContaining graph second |> List.map (fun (site, _, _) -> site)
        Assert.NotEqual<NodeId list>(firstSites, secondSites)

    [<Fact>]
    member _.``An omitted call under a nested omission names each omission once`` () =
        let source = """module WriteFixture
let write (s: string) =
    let _ = Sys.write 1 s.Bytes s.Length
    ()
let discard (value: int) = 0
[<EntryPoint>]
let main _ =
    write "kept"
    if discard (discard (write "nested"; 0); 0) = 0 then 0 else 1
"""
        let graph, projection = IntrinsicWriteFixture.graphAndProjectionOfSource source
        let call = Assert.Single projection.IntrinsicWrites.Values
        let view = projection.ByteViews[call.Buffer]
        let participants = IntrinsicWriteFixture.established view.Participants
        let omitted = IntrinsicWriteFixture.writeCallOf graph "nested"
        let omissions = IntrinsicWriteFixture.omissionsContaining graph omitted
        Assert.Equal(2, omissions.Length)
        let expected = omissions |> List.map (fun (site, ordinal, actual) -> omitted, site, ordinal, [actual]) |> List.sort
        Assert.Equal<(NodeId * NodeId * int * NodeId list) list>(expected, IntrinsicWriteFixture.omissionTuples omitted participants)

    [<Fact>]
    member _.``One omission that is the reason for two omitted calls occurs once in each of their groups`` () =
        let source = """module WriteFixture
let write (s: string) =
    let _ = Sys.write 1 s.Bytes s.Length
    ()
let discard (value: int) = 0
[<EntryPoint>]
let main _ =
    write "kept"
    if discard (write "a"; write "b"; 0) = 0 then 0 else 1
"""
        let graph, projection = IntrinsicWriteFixture.graphAndProjectionOfSource source
        let call = Assert.Single projection.IntrinsicWrites.Values
        let view = projection.ByteViews[call.Buffer]
        let participants = IntrinsicWriteFixture.established view.Participants
        let first, second = IntrinsicWriteFixture.writeCallOf graph "a", IntrinsicWriteFixture.writeCallOf graph "b"
        let site, ordinal, actual = IntrinsicWriteFixture.omissionsContaining graph first |> Assert.Single
        Assert.Equal<(NodeId * int * NodeId) list>([site, ordinal, actual], IntrinsicWriteFixture.omissionsContaining graph second)
        for omitted in [first; second] do
            Assert.Equal<Participant list>([IntrinsicWriteFixture.occurrence site ParticipantRole.OmissionSite ordinal omitted],
                                           IntrinsicWriteFixture.inGroup omitted ParticipantRole.OmissionSite participants)
            Assert.Equal<(NodeId * NodeId * int * NodeId list) list>([omitted, site, ordinal, [actual]], IntrinsicWriteFixture.omissionTuples omitted participants)
        Assert.Equal<Participant list>([IntrinsicWriteFixture.occurrence actual ParticipantRole.OmittedActual ordinal site],
                                       participants |> List.filter (fun participant -> participant.Role = ParticipantRole.OmittedActual && participant.Node = actual))

    [<Fact>]
    member _.``Initializer omissions preserve their nonpositional origin in participants`` () =
        let call : Clef.Compiler.Baker.Ingredients.FormalDemand.Input = { Call = NodeId 10; Ordinal = 0; Actual = NodeId 11 }
        let evidence origin =
            let inputs : Clef.Compiler.Baker.Ingredients.FormalDemand.Inputs =
                { Demanded = []; Omitted = [ { Input = call; Omissions = [ { Site = NodeId 20; Origin = origin; Actual = NodeId 21 } ] } ]; Participants = Set.empty; UsedLazyForces = Set.empty }
            Clef.Compiler.Baker.Ingredients.Participants.ofInputs (NodeId 2) inputs
        let initializer = evidence OrdinaryOmissionOrigin.BindingInitializer
        Assert.Contains(IntrinsicWriteFixture.occurrence (NodeId 20) ParticipantRole.OmissionBinding 0 (NodeId 10), initializer)
        Assert.Contains(IntrinsicWriteFixture.occurrence (NodeId 21) ParticipantRole.OmittedInitializer 0 (NodeId 20), initializer)
        Assert.DoesNotContain(initializer, fun participant -> participant.Role = ParticipantRole.OmissionSite || participant.Role = ParticipantRole.OmittedActual)
        Assert.NotEqual<Participant list>(initializer, evidence (OrdinaryOmissionOrigin.CallArgument 0))

    [<Fact>]
    member _.``Crossing the actuals of two omissions of one omitted call changes the participants`` () =
        let call : Clef.Compiler.Baker.Ingredients.FormalDemand.Input = { Call = NodeId 10; Ordinal = 0; Actual = NodeId 11 }
        let evidence (omissions: OrdinaryOmission list) =
            let inputs : Clef.Compiler.Baker.Ingredients.FormalDemand.Inputs =
                { Demanded = []; Omitted = [ { Input = call; Omissions = omissions } ]; Participants = Set.empty; UsedLazyForces = Set.empty }
            Clef.Compiler.Baker.Ingredients.Participants.ordered (NodeId 1) (Clef.Compiler.Baker.Ingredients.Participants.ofInputs (NodeId 2) inputs)
        let stated : OrdinaryOmission list = [ { Site = NodeId 20; Origin = OrdinaryOmissionOrigin.CallArgument 0; Actual = NodeId 21 }; { Site = NodeId 30; Origin = OrdinaryOmissionOrigin.CallArgument 0; Actual = NodeId 31 } ]
        let crossed : OrdinaryOmission list = [ { Site = NodeId 20; Origin = OrdinaryOmissionOrigin.CallArgument 0; Actual = NodeId 31 }; { Site = NodeId 30; Origin = OrdinaryOmissionOrigin.CallArgument 0; Actual = NodeId 21 } ]
        Assert.NotEqual<Participant list>(evidence stated, evidence crossed)
        Assert.Equal<(NodeId * NodeId * int * NodeId list) list>(
            [ NodeId 10, NodeId 20, 0, [NodeId 21]; NodeId 10, NodeId 30, 0, [NodeId 31] ], IntrinsicWriteFixture.omissionTuples (NodeId 10) (evidence stated))

    [<Fact>]
    member _.``Crossing the bodies of two targets of one call changes the participants`` () =
        let target lambda body : Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.CallTarget =
            { Lambda = NodeId lambda; Parameters = [ "p", Types.intType, NodeId 50 ]; Arguments = [ NodeId 30 ]; Body = NodeId body }
        let evidence targets =
            Clef.Compiler.Baker.Ingredients.Participants.ordered (NodeId 1) (IntrinsicWriteFixture.ofTargets (NodeId 10) targets)
        let stated = evidence [ target 20 21; target 40 41 ]
        Assert.NotEqual<Participant list>(stated, evidence [ target 20 41; target 40 21 ])
        Assert.Equal<Participant list>([ IntrinsicWriteFixture.occurrence (NodeId 21) ParticipantRole.CalleeBody 0 (NodeId 20) ],
                                       stated |> List.filter (fun participant -> participant.Group = NodeId 20))

    [<Fact>]
    member _.``One lambda resolved at two calls with different parameters states each call's parameters at its own ordinals`` () =
        let target arguments parameters : Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.CallTarget =
            { Lambda = NodeId 20; Body = NodeId 21
              Parameters = parameters |> List.map (fun parameter -> "p", Types.intType, NodeId parameter); Arguments = List.map NodeId arguments }
        let stated =
            Clef.Compiler.Baker.Ingredients.Participants.ordered (NodeId 1)
                (IntrinsicWriteFixture.ofTargets (NodeId 10) [ target [30; 31] [50; 51] ]
                 @ IntrinsicWriteFixture.ofTargets (NodeId 11) [ target [32] [51] ])
        let positions call role =
            stated |> List.filter (fun participant -> participant.Group = NodeId call && participant.Role = role) |> List.map (fun participant -> participant.Ordinal, participant.Node)
        Assert.Equal<(int * NodeId) list>([ 0, NodeId 50; 1, NodeId 51 ], positions 10 ParticipantRole.CalleeParameter)
        Assert.Equal<(int * NodeId) list>([ 0, NodeId 51 ], positions 11 ParticipantRole.CalleeParameter)
        Assert.Equal<(int * NodeId) list>([ 0, NodeId 30; 1, NodeId 31 ], positions 10 ParticipantRole.CalleeArgument)
        Assert.Equal<(int * NodeId) list>([ 0, NodeId 32 ], positions 11 ParticipantRole.CalleeArgument)
        Assert.Equal<Participant list>([ IntrinsicWriteFixture.occurrence (NodeId 21) ParticipantRole.CalleeBody 0 (NodeId 20) ],
                                       stated |> List.filter (fun participant -> participant.Group = NodeId 20))

    [<Fact>]
    member _.``A target with more arguments than parameters is an error that names the call`` () =
        let target : Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.CallTarget =
            { Lambda = NodeId 20; Parameters = [ "p", Types.intType, NodeId 50 ]; Arguments = [ NodeId 30; NodeId 31 ]; Body = NodeId 21 }
        Assert.Equal(Error (Clef.Compiler.Baker.Ingredients.Participants.TargetFailure.UnequalCounts(NodeId 10, NodeId 20, 2, 1)),
                     Clef.Compiler.Baker.Ingredients.Participants.ofTargets (NodeId 10) [ target ])

    [<Theory>]
    [<InlineData("arguments")>]
    [<InlineData("parameters")>]
    member _.``Two targets of one call with different arguments or parameters are an error that names the call`` differing =
        let target lambda argument parameter : Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.CallTarget =
            { Lambda = NodeId lambda; Parameters = [ "p", Types.intType, NodeId parameter ]; Arguments = [ NodeId argument ]; Body = NodeId (lambda + 1) }
        let targets = if differing = "arguments" then [ target 20 30 50; target 40 31 50 ] else [ target 20 30 50; target 40 30 51 ]
        Assert.Equal(Error (Clef.Compiler.Baker.Ingredients.Participants.TargetFailure.DifferentLists (NodeId 10)),
                     Clef.Compiler.Baker.Ingredients.Participants.ofTargets (NodeId 10) targets)

    [<Fact>]
    member _.``A call that resolves to two functions with different parameters is a located error at each borrow site`` () =
        let checked' = IntrinsicWriteFixture.checkWithoutException IntrinsicWriteFixture.factoryAuthority IntrinsicWriteFixture.pickBody
        Assert.True(Result.isOk checked', sprintf "The check threw an exception: %A" checked')
        let result = match checked' with Ok result -> result | Error message -> failwith message
        let graph = result.Graph
        let hello = IntrinsicWriteFixture.literal graph "hello"
        let call = graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && match node.Kind with SemanticKind.Application(_, [actual]) -> actual = hello | _ -> false) |> Seq.exactlyOne
        let text =
            IntrinsicWriteFixture.targetsMessage
                (sprintf "The string's origins are reached through the call at %s, whose targets have different argument or parameter lists; the participant form states one argument list and one parameter list for a call."
                    (Clef.Compiler.Baker.Ingredients.Obligations.fmtRange call.Range))
        let sites = IntrinsicWriteFixture.borrowSites graph
        Assert.Equal(2, sites.Length)
        for site in sites do
            Assert.Contains(result.Diagnostics, fun diagnostic ->
                diagnostic.Code = "CCS8403" && diagnostic.Range = graph.Nodes[site].Range && diagnostic.Message = text
                && List.contains site diagnostic.RelatedNodes && List.contains call.Id diagnostic.RelatedNodes)

    [<Fact>]
    member _.``A target with more arguments than parameters is a located error at each borrow site`` () =
        let checked' = IntrinsicWriteFixture.checkWithoutException IntrinsicWriteFixture.factoryAuthority IntrinsicWriteFixture.pickBody
        Assert.True(Result.isOk checked', sprintf "The check threw an exception: %A" checked')
        let graph = match checked' with Ok result -> result.Graph | Error message -> failwith message
        let hello = IntrinsicWriteFixture.literal graph "hello"
        let call = graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable && match node.Kind with SemanticKind.Application(_, [actual]) -> actual = hello | _ -> false) |> Seq.exactlyOne
        // The target of the call whose body calls `other`, without its parameter: a target
        // with one argument and no parameter.
        let flow = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
        let callsOther (target: Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.CallTarget) =
            match graph.Nodes[target.Body].Kind with
            | SemanticKind.Application(callee, _) -> graph.Nodes[callee].Kind |> function SemanticKind.VarRef("other", _) -> true | _ -> false
            | _ -> false
        let target = flow.Calls[call.Id].Targets |> List.filter callsOther |> Assert.Single
        let other = graph.Nodes[target.Lambda]
        let changed =
            match other.Kind with
            | SemanticKind.Lambda(_, body, captures, enclosing, context) ->
                { graph with Nodes = graph.Nodes.Add(other.Id, { other with Kind = SemanticKind.Lambda([], body, captures, enclosing, context) }) }
            | _ -> graph
        let settled = try Ok (Clef.Compiler.Nanopass.BoundarySettlement.normalize changed) with error -> Error error.Message
        Assert.True(Result.isOk settled, sprintf "The boundary settlement threw an exception: %A" settled)
        let settled = match settled with Ok settled -> settled | Error message -> failwith message
        let failures = match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare settled with Error failures -> failures | Ok _ -> []
        let diagnostics = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.diagnostics settled failures
        let text =
            IntrinsicWriteFixture.targetsMessage
                (sprintf "The string's origins are reached through the call at %s, whose target at %s has 1 arguments and 0 parameters; the participant form states one parameter for each argument of an exact invocation."
                    (Clef.Compiler.Baker.Ingredients.Obligations.fmtRange call.Range) (Clef.Compiler.Baker.Ingredients.Obligations.fmtRange other.Range))
        let sites = IntrinsicWriteFixture.borrowSites settled
        Assert.Equal(2, sites.Length)
        for site in sites do
            Assert.Contains(diagnostics, fun diagnostic ->
                diagnostic.Code = "CCS8403" && diagnostic.Range = settled.Nodes[site].Range && diagnostic.Message = text
                && List.contains call.Id diagnostic.RelatedNodes && List.contains other.Id diagnostic.RelatedNodes)

module PremiseEstablishmentFixture =
    module Borrows = Clef.Compiler.Baker.Recipes.StringBorrowRecipes
    module Bytes = Clef.Compiler.Baker.Ingredients.StringBytes
    module Demand = Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand
    module Layout = Clef.Compiler.PSGSaturation.SemanticGraph.StaticStringLayout
    module Diagnostics = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

    let header = "module WriteFixture\nlet write (s: string) =\n    let _ = Sys.write 1 s.Bytes s.Length\n    ()\n"
    let factoryBody = header + """let make (offset: int) (unused: int) =
    fun (value: int) -> value + offset
let msg = "hello"
let first = make 3 (write msg; 0)
[<EntryPoint>]
let main _ =
    write msg
    if first 1 = 4 then 0 else 1
"""
    let lazyBody = factoryBody.Replace("fun (value: int) -> value + offset", "lazy (offset + 1)").Replace("first 1", "Lazy.force first")
    let bothRolesBody = header + """let make (offset: int) (unused: int) =
    fun (value: int) -> value + offset
let print (s: string) = make (write s; 3) (write s; 0)
let first = print "hello"
[<EntryPoint>]
let main _ =
    if first 1 = 4 then 0 else 1
"""
    let movedStorageBody = header + """let make (unused: int) (offset: int) =
    fun (value: int) -> value + offset
[<EntryPoint>]
let main _ =
    let add = make (write "never demanded"; 0) 3
    if add 1 = 4 then write "kept"
    0
"""
    let aliasBody = """module WriteFixture
let first (s: string) =
    let b = s.Bytes
    b.[0]
let make (offset: int) (unused: int) =
    fun (value: int) -> value + offset
let saved = make 3 (first "omitted"; 0)
[<EntryPoint>]
let main _ =
    if first "a" + first "bb" + saved 1 = 0 then 0 else 1
"""
    let twoOmissionsBody = (IntrinsicWriteFixture.demandBody "0").Replace("    0\n", "    if discard (write \"also omitted\"; 0) = 0 then ()\n    0\n")
    let check source = IntrinsicWriteFixture.checkSource IntrinsicWriteFixture.factoryAuthority source
    let factory = lazy (check factoryBody)
    let lazyFactory = lazy (check lazyBody)
    let bothRoles = lazy (check bothRolesBody)
    let movedStorage = lazy (check movedStorageBody)
    let aliased = lazy (check aliasBody)
    let omitted = lazy (check (IntrinsicWriteFixture.demandBody "0"))
    let twoOmissions = lazy (check twoOmissionsBody)

    let normalize = Clef.Compiler.Nanopass.PremiseEstablishment.normalize
    let establish = Borrows.establish
    let guard = Layout.premiseGuard
    let byteRange = Clef.Compiler.Baker.Recipes.MemoryAccessRecipes.byteRange

    let pendingText = "String borrow participants remain pending after the final demand rows: the origins or extent derived there differ from those source range settlement read, or no borrow is derived at this site."
    let newText = "A string borrow derived after the final demand rows has no row written before source range settlement."
    let lostText = "A string byte read lost the storage evidence of its borrow after the final demand rows."
    let premiseText = "The omission premise of this string literal differs from the final demand rows in a site, an ordinal or an actual."
    let demandedText = "The storage of this string literal was not materialized, and after the final demand rows a demanded position reads it."
    let materializedText = "The storage of this string literal was materialized, and after the final demand rows no demanded position reads it."
    let changedTexts = ["premises changed after source numeric settlement"; "evidence changed after source range settlement"; "requires complete intrinsic write-use or local guarded comparison lifetime proofs"]
    let noErrors (diagnostics: Diagnostics.Diagnostic list) =
        diagnostics |> List.filter (fun diagnostic -> diagnostic.Severity = Diagnostics.NativeDiagnosticSeverity.Error) |> Assert.Empty
    let noBorrowChanges (diagnostics: Diagnostics.Diagnostic list) =
        Assert.DoesNotContain(diagnostics, fun (diagnostic: Diagnostics.Diagnostic) -> changedTexts |> List.exists diagnostic.Message.Contains)
    let located (graph: SemanticGraph) site text (diagnostics: Diagnostics.Diagnostic list) =
        Assert.Contains(diagnostics, fun diagnostic ->
            diagnostic.Code = "CCS8403" && diagnostic.Severity = Diagnostics.NativeDiagnosticSeverity.Error
            && diagnostic.Range = graph.Nodes[site].Range && diagnostic.Message = text && List.contains site diagnostic.RelatedNodes)
    let histories (graph: SemanticGraph) =
        graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringBorrowHistory history -> Some history | _ -> None)
    let storageHistories (graph: SemanticGraph) =
        graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.LiteralStorageHistory history -> Some history | _ -> None)
    let views graph = IntrinsicWriteFixture.viewRows graph |> List.map fst
    let view graph = views graph |> Assert.Single
    let participants graph = view graph |> _.Participants |> IntrinsicWriteFixture.established
    let changeView change (graph: SemanticGraph) =
        let edges = graph.Edges |> List.map (fun edge ->
            match edge.Role with EdgeRole.StringByteView view -> Bytes.viewRow (change view) | _ -> edge)
        { graph with Edges = edges }
    let makePending (view: BoundaryByteView) =
        { view with Participants = ParticipantEvidence.Pending { Derived = IntrinsicWriteFixture.established view.Participants } }
    let changedLength (view: BoundaryByteView) =
        { view with StaticOrigins = view.StaticOrigins |> Map.map (fun _ length -> length + 1I) }
    let freshRows (graph: SemanticGraph) =
        let rows, failures = Borrows.evidence graph
        Assert.Empty failures
        rows
    let boundaryDiagnostics graph =
        let graph = Clef.Compiler.Nanopass.BoundarySettlement.normalize graph
        let failures = match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare graph with Error failures -> failures | Ok _ -> []
        Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.diagnostics graph failures
    let omissions graph literal =
        Demand.tryDeferrals graph |> Result.defaultWith (fun failures -> failwithf "%A" failures)
        |> Map.find literal |> Set.toList
    let setPremise literal premise (graph: SemanticGraph) =
        { graph with LiteralStorage = graph.LiteralStorage.Add(literal, LiteralStorage.NotMaterialized premise) }
    let assertMove (graph: SemanticGraph) =
        let histories = histories graph
        Assert.NotEmpty histories
        for view in views graph do
            let current = IntrinsicWriteFixture.established view.Participants
            let early = histories |> List.filter (fun history -> history.Site = view.Site) |> Assert.Single
            let omitted = current |> List.filter (fun participant -> participant.Role = ParticipantRole.OmissionSite)
            Assert.NotEmpty omitted
            for occurrence in omitted do
                Assert.True(match graph.Nodes[occurrence.Node].Kind with SemanticKind.Application _ -> true | _ -> false)
                Assert.Contains(graph.Edges, fun edge -> edge.Role = EdgeRole.OrdinaryUnusedActual && edge.Target = occurrence.Node && edge.Ordinal = occurrence.Ordinal)
                let old = early.Early.Derived |> List.filter (fun participant -> participant.Role = ParticipantRole.OmissionSite && participant.Group = occurrence.Group) |> Assert.Single
                Assert.NotEqual(old.Node, occurrence.Node)
                Assert.True(match graph.Nodes[old.Node].Kind with SemanticKind.Sequential values -> List.contains occurrence.Node values | _ -> false)
            Assert.Equal<NodeId list>(current |> List.map _.Node, graph.Edges |> List.find (fun edge -> edge.Role = EdgeRole.StringByteView view) |> _.Sources)
        for edge in graph.Edges do
            match edge.Role with
            | EdgeRole.StringExtent extent -> IntrinsicWriteFixture.established extent.Participants |> ignore
            | _ -> ()

type PremiseEstablishmentCases() =
    [<Fact>]
    member _.``Early borrow rows retain nonempty pending derivations`` () =
        let graph = PremiseEstablishmentFixture.factory.Value.Graph
        let rows = (Clef.Compiler.Baker.Recipes.StringBorrowRecipes.elaborate graph).NewEdges
        let evidence = rows |> List.choose (fun edge ->
            match edge.Role with EdgeRole.StringByteView view -> Some view.Participants | EdgeRole.StringExtent extent -> Some extent.Participants | _ -> None)
        Assert.NotEmpty evidence
        for value in evidence do
            Assert.True((match value with ParticipantEvidence.Pending early -> not early.Derived.IsEmpty | _ -> false), sprintf "Early row is not pending with its derivation: %A" value)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Factory moves establish final invocation occurrences and preserve early history`` lazyFactory =
        let result = if lazyFactory then PremiseEstablishmentFixture.lazyFactory.Value else PremiseEstablishmentFixture.factory.Value
        PremiseEstablishmentFixture.noErrors result.Diagnostics
        PremiseEstablishmentFixture.assertMove result.Graph

    [<Fact>]
    member _.``One identity retains its callee body role while the omission names the moved call`` () =
        let result = PremiseEstablishmentFixture.bothRoles.Value
        PremiseEstablishmentFixture.noBorrowChanges result.Diagnostics
        PremiseEstablishmentFixture.assertMove result.Graph
        let current = PremiseEstablishmentFixture.participants result.Graph
        let early = PremiseEstablishmentFixture.histories result.Graph |> List.head
        let old = early.Early.Derived |> List.filter (fun participant -> participant.Role = ParticipantRole.OmissionSite) |> Assert.Single
        Assert.Contains(current, fun participant -> participant.Role = ParticipantRole.CalleeBody && participant.Node = old.Node)
        Assert.DoesNotContain(current, fun participant -> participant.Role = ParticipantRole.OmissionSite && participant.Node = old.Node)

    [<Fact>]
    member _.``The current borrow guard rejects a stale omission site`` () =
        let result = PremiseEstablishmentFixture.factory.Value
        PremiseEstablishmentFixture.noErrors result.Diagnostics
        let graph = result.Graph
        let early = PremiseEstablishmentFixture.histories graph |> List.head
        let old = early.Early.Derived |> List.filter (fun participant -> participant.Role = ParticipantRole.OmissionSite) |> Assert.Single
        let changed = graph |> PremiseEstablishmentFixture.changeView (fun view ->
            let participants = IntrinsicWriteFixture.established view.Participants |> List.map (fun participant ->
                if participant.Role = ParticipantRole.OmissionSite then { participant with Node = old.Node } else participant)
            { view with Participants = ParticipantEvidence.Established participants })
        let diagnostics = PremiseEstablishmentFixture.boundaryDiagnostics changed
        Assert.Contains(diagnostics, fun diagnostic -> diagnostic.Message.Contains "premises changed after source numeric settlement")
        Assert.Contains(diagnostics, fun diagnostic -> diagnostic.Message.Contains "evidence changed after source range settlement")

    [<Fact>]
    member _.``Establishment rejects a changed origin length`` () =
        let graph = PremiseEstablishmentFixture.factory.Value.Graph |> PremiseEstablishmentFixture.changeView (PremiseEstablishmentFixture.changedLength >> PremiseEstablishmentFixture.makePending)
        let site = (PremiseEstablishmentFixture.view graph).Site
        let results = PremiseEstablishmentFixture.establish graph
        Assert.Contains(results, function Error(node, _, text) -> node = site && text = PremiseEstablishmentFixture.pendingText | _ -> false)

    [<Fact>]
    member _.``A contradicted pending view has one located diagnostic and keeps its early row`` () =
        let graph, _ = IntrinsicWriteFixture.admitted ()
        let changed = graph |> PremiseEstablishmentFixture.changeView (PremiseEstablishmentFixture.changedLength >> PremiseEstablishmentFixture.makePending)
        let early = PremiseEstablishmentFixture.view changed
        let normalized, diagnostics = PremiseEstablishmentFixture.normalize changed
        Assert.Single diagnostics |> ignore
        PremiseEstablishmentFixture.located changed early.Site PremiseEstablishmentFixture.pendingText diagnostics
        Assert.Equal<BoundaryByteView>(early, PremiseEstablishmentFixture.view normalized)

    [<Fact>]
    member _.``A derived borrow without an early row is a located error`` () =
        let graph, _ = IntrinsicWriteFixture.admitted ()
        let view = PremiseEstablishmentFixture.view graph
        let changed = { graph with Edges = graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.StringByteView _ | EdgeRole.StringByteStorage _ when edge.Target = view.Site -> false | _ -> true) }
        let _, diagnostics = PremiseEstablishmentFixture.normalize changed
        PremiseEstablishmentFixture.located graph view.Site PremiseEstablishmentFixture.newText diagnostics

    [<Fact>]
    member _.``An early borrow without a final derivation remains pending and is located`` () =
        let graph, _ = IntrinsicWriteFixture.admitted ()
        let graph = graph |> PremiseEstablishmentFixture.changeView PremiseEstablishmentFixture.makePending
        let site = (PremiseEstablishmentFixture.view graph).Site
        let changed = { graph with Nodes = graph.Nodes.Add(site, { graph.Nodes[site] with IsReachable = false }) }
        let normalized, diagnostics = PremiseEstablishmentFixture.normalize changed
        PremiseEstablishmentFixture.located graph site PremiseEstablishmentFixture.pendingText diagnostics
        Assert.Equal<BoundaryByteView>(PremiseEstablishmentFixture.view changed, PremiseEstablishmentFixture.view normalized)

    [<Fact>]
    member _.``Aliased byte reads renew the entire range fact from current borrow evidence`` () =
        let graph = PremiseEstablishmentFixture.aliased.Value.Graph
        let freshView = PremiseEstablishmentFixture.freshRows graph |> List.choose (fun edge ->
            match edge.Role with EdgeRole.StringByteView view -> Some view | _ -> None) |> Assert.Single
        let finalOmission = IntrinsicWriteFixture.established freshView.Participants |> List.filter (fun participant -> participant.Role = ParticipantRole.OmissionSite) |> Assert.Single
        let residentFact = graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.StringByteRange _ -> true | _ -> false) |> Assert.Single
        Assert.Contains(finalOmission.Node, residentFact.Sources)
        let histories = PremiseEstablishmentFixture.histories graph
        Assert.NotEmpty histories
        let current = PremiseEstablishmentFixture.participants graph
        Assert.Equal(2, current |> List.filter (fun participant -> participant.Role = ParticipantRole.ReachingCall) |> List.length)
        Assert.Single(current |> List.filter (fun participant -> participant.Role = ParticipantRole.OmittedCall)) |> ignore
        let old = histories.Head.Early.Derived |> List.filter (fun participant -> participant.Role = ParticipantRole.OmissionSite) |> Assert.Single
        let early = graph |> PremiseEstablishmentFixture.changeView (fun view ->
            { view with Participants = ParticipantEvidence.Pending (histories |> List.find (fun history -> history.Site = view.Site)).Early })
        let edges = early.Edges |> List.map (fun edge ->
            match edge.Role with EdgeRole.StringByteStorage _ -> Clef.Compiler.Baker.Ingredients.StringBytes.storageRow (PremiseEstablishmentFixture.view early) | _ -> edge)
        let early = { early with Edges = edges }
        let guard = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.MemoryAccessGuard) |> Assert.Single
        let oldFact = PremiseEstablishmentFixture.byteRange early guard |> Option.get
        Assert.Contains(old.Node, oldFact.Sources)
        let early = { early with Edges = early.Edges |> List.map (fun edge -> match edge.Role with EdgeRole.StringByteRange _ when edge.Target = guard.Target -> oldFact | _ -> edge) }
        let normalized, diagnostics = PremiseEstablishmentFixture.normalize early
        Assert.Empty diagnostics
        let fact = normalized.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.StringByteRange _ -> edge.Target = guard.Target | _ -> false) |> Assert.Single
        let fields (edge: Hyperedge) = edge.Sources, edge.Target, edge.Class, edge.Role, edge.Ordinal
        Assert.Equal((Some (fields fact)), PremiseEstablishmentFixture.byteRange normalized guard |> Option.map fields)
        Assert.DoesNotContain(old.Node, fact.Sources)
        Assert.Equal<Set<NodeId>>(graph.Nodes.Keys |> Set.ofSeq, normalized.Nodes.Keys |> Set.ofSeq)

    [<Fact>]
    member _.``A byte range whose borrow storage is lost reports its read site`` () =
        let graph = PremiseEstablishmentFixture.aliased.Value.Graph
        let view = PremiseEstablishmentFixture.view graph
        let guard = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.MemoryAccessGuard) |> Assert.Single
        let changed =
            { graph with Nodes = graph.Nodes.Add(view.Site, { graph.Nodes[view.Site] with IsReachable = false })
                         Edges = graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.StringByteStorage _ | EdgeRole.StringByteView _ when edge.Target = view.Site -> false | _ -> true) }
        let _, diagnostics = PremiseEstablishmentFixture.normalize changed
        PremiseEstablishmentFixture.located graph guard.Target PremiseEstablishmentFixture.lostText diagnostics

    [<Fact>]
    member _.``Borrow history is not an input of the current evidence guard`` () =
        let result = PremiseEstablishmentFixture.factory.Value
        PremiseEstablishmentFixture.noErrors result.Diagnostics
        Assert.NotEmpty(PremiseEstablishmentFixture.histories result.Graph)
        let edges = result.Graph.Edges |> List.map (fun edge ->
            match edge.Role with
            | EdgeRole.StringBorrowHistory history ->
                let early = { history.Early with Derived = history.Early.Derived |> List.tail }
                { edge with Role = EdgeRole.StringBorrowHistory { history with Early = early }; Sources = early.Derived |> List.map _.Node }
            | _ -> edge)
        let changed = { result.Graph with Edges = edges }
        PremiseEstablishmentFixture.boundaryDiagnostics changed |> PremiseEstablishmentFixture.noBorrowChanges

    [<Fact>]
    member _.``Literal storage follows its moved omission and preserves the early site and ordinal`` () =
        let result = PremiseEstablishmentFixture.movedStorage.Value
        PremiseEstablishmentFixture.noErrors result.Diagnostics
        let graph = result.Graph
        let literal = IntrinsicWriteFixture.literal graph "never demanded"
        let expected = PremiseEstablishmentFixture.omissions graph literal |> Assert.Single
        Assert.Equal(OrdinaryOmissionOrigin.CallArgument 1, expected.Origin)
        Assert.True(match graph.Nodes[expected.Site].Kind with SemanticKind.Application _ -> true | _ -> false)
        Assert.Equal<LiteralStorage>(LiteralStorage.NotMaterialized(StoragePremise.Established [expected]), graph.LiteralStorage[literal])
        let history = PremiseEstablishmentFixture.storageHistories graph |> List.filter (fun history -> history.Literal = literal) |> Assert.Single
        let early = Assert.Single history.Early
        Assert.Equal(OrdinaryOmissionOrigin.CallArgument 0, early.Origin)
        Assert.Equal(expected.Actual, early.Actual)
        Assert.NotEqual(expected.Site, early.Site)
        Assert.True(match graph.Nodes[early.Site].Kind with SemanticKind.Sequential values -> List.contains expected.Site values | _ -> false)

    [<Fact>]
    member _.``Early omitted literal storage keeps a nonempty pending premise`` () =
        let graph = PremiseEstablishmentFixture.omitted.Value.Graph
        let literal = IntrinsicWriteFixture.literal graph "never demanded"
        let settled, diagnostics = Clef.Compiler.PSGSaturation.SemanticGraph.StaticStringLayout.settle graph
        Assert.Empty diagnostics
        Assert.Equal<LiteralStorage>(LiteralStorage.NotMaterialized(StoragePremise.Pending(PremiseEstablishmentFixture.omissions graph literal)), settled.LiteralStorage[literal])

    [<Theory>]
    [<InlineData("other omission")>]
    [<InlineData("ordinal")>]
    [<InlineData("actual")>]
    [<InlineData("absent literal")>]
    member _.``The storage guard compares the whole omission for its literal`` defect =
        let graph = (if defect = "other omission" then PremiseEstablishmentFixture.twoOmissions.Value else PremiseEstablishmentFixture.movedStorage.Value).Graph
        let literal = IntrinsicWriteFixture.literal graph "never demanded"
        let expected = PremiseEstablishmentFixture.omissions graph literal |> Assert.Single
        let unrelated = IntrinsicWriteFixture.literal graph "kept"
        let premise =
            match defect with
            | "other omission" -> PremiseEstablishmentFixture.omissions graph (IntrinsicWriteFixture.literal graph "also omitted")
            | "ordinal" -> [{ expected with Origin = OrdinaryOmissionOrigin.CallArgument 0 }]
            | "actual" -> [{ expected with Actual = unrelated }]
            | _ -> [expected]
        let target = if defect = "absent literal" then unrelated else literal
        let changed = graph |> PremiseEstablishmentFixture.setPremise target (StoragePremise.Established premise)
        let diagnostics = PremiseEstablishmentFixture.guard changed
        PremiseEstablishmentFixture.located graph target PremiseEstablishmentFixture.premiseText diagnostics

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Changed literal dispositions are diagnosed without rewriting the pool`` materialized =
        let graph = PremiseEstablishmentFixture.omitted.Value.Graph
        let omitted = IntrinsicWriteFixture.literal graph "never demanded"
        let demanded = IntrinsicWriteFixture.literal graph "kept"
        let literal, text, row =
            if materialized then omitted, PremiseEstablishmentFixture.materializedText, graph.LiteralStorage[demanded]
            else demanded, PremiseEstablishmentFixture.demandedText, LiteralStorage.NotMaterialized(StoragePremise.Pending(PremiseEstablishmentFixture.omissions graph omitted))
        let changed = { graph with LiteralStorage = graph.LiteralStorage.Add(literal, row) }
        let normalized, diagnostics = PremiseEstablishmentFixture.normalize changed
        PremiseEstablishmentFixture.located graph literal text diagnostics
        Assert.Equal<StaticStringPool option>(graph.StaticStringPool, normalized.StaticStringPool)
        Assert.Equal<LiteralStorage>(row, normalized.LiteralStorage[literal])
        if materialized then PremiseEstablishmentFixture.guard changed |> PremiseEstablishmentFixture.located graph literal text

    [<Fact>]
    member _.``Storage history does not justify an incorrect current premise`` () =
        let graph = PremiseEstablishmentFixture.omitted.Value.Graph
        let literal = IntrinsicWriteFixture.literal graph "never demanded"
        let premise = PremiseEstablishmentFixture.omissions graph literal
        let bad = premise |> List.map (fun omission -> { omission with Origin = (match omission.Origin with OrdinaryOmissionOrigin.CallArgument ordinal -> OrdinaryOmissionOrigin.CallArgument (ordinal + 1) | _ -> failwith "Expected a call omission") })
        let changed = graph |> PremiseEstablishmentFixture.setPremise literal (StoragePremise.Established bad)
        let changed = { changed with Edges = { Class = EdgeClass.Provenance; Role = EdgeRole.LiteralStorageHistory { Literal = literal; Early = premise }; Sources = literal :: (premise |> List.collect (fun omission -> [omission.Site; omission.Actual])); Target = literal; Ordinal = 0 } :: changed.Edges }
        PremiseEstablishmentFixture.guard changed |> PremiseEstablishmentFixture.located graph literal PremiseEstablishmentFixture.premiseText

    [<Fact>]
    member _.``Establishment preserves specific origin failure diagnostics`` () =
        let graph = (PremiseEstablishmentFixture.check IntrinsicWriteFixture.pickBody).Graph
        let _, diagnostics = PremiseEstablishmentFixture.normalize graph
        let _, failures = Clef.Compiler.Baker.Recipes.StringBorrowRecipes.evidence graph
        Assert.NotEmpty failures
        for site, failure in failures do
            let _, related, text = Clef.Compiler.Baker.Recipes.StringComparisonRecipes.originError graph site failure
            Assert.Contains(diagnostics, fun diagnostic ->
                diagnostic.Code = "CCS8403" && diagnostic.Range = graph.Nodes[site].Range
                && diagnostic.Message.Contains text && Set.isSubset related (Set.ofList diagnostic.RelatedNodes))
        Assert.DoesNotContain(diagnostics, fun diagnostic -> diagnostic.Message = PremiseEstablishmentFixture.pendingText || diagnostic.Message = PremiseEstablishmentFixture.newText)

    [<Fact>]
    member _.``Demand reading failures keep their own located diagnostics during establishment`` () =
        let graph = PremiseEstablishmentFixture.omitted.Value.Graph
        let changed = { graph with Edges = graph.Edges |> List.map (fun edge -> if edge.Role = EdgeRole.OrdinaryUnusedActual then { edge with Ordinal = edge.Ordinal + 1 } else edge) }
        let expected = match Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.tryDeferrals changed with Error failures -> Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.diagnostics changed failures | Ok _ -> failwith "The fixture did not contradict the resident demand rows."
        Assert.NotEmpty expected
        let _, diagnostics = PremiseEstablishmentFixture.normalize changed
        for diagnostic in expected do Assert.Contains(diagnostic, diagnostics)

    [<Fact>]
    member _.``Duplicate pending view rows do not establish two histories`` () =
        let graph, _ = IntrinsicWriteFixture.admitted ()
        let graph = graph |> PremiseEstablishmentFixture.changeView PremiseEstablishmentFixture.makePending
        let view = PremiseEstablishmentFixture.view graph
        let edges = graph.Edges |> List.filter (fun edge ->
            match edge.Role with EdgeRole.StringBorrowHistory history -> history.Site <> view.Site | _ -> true)
        let changed = { graph with Edges = Clef.Compiler.Baker.Ingredients.StringBytes.viewRow view :: edges }
        let normalized, diagnostics = PremiseEstablishmentFixture.normalize changed
        PremiseEstablishmentFixture.located graph view.Site "A string borrow has more than one row written before source range settlement." diagnostics
        for row in PremiseEstablishmentFixture.views normalized do
            Assert.True(match row.Participants with ParticipantEvidence.Pending _ -> true | _ -> false)
        let histories = PremiseEstablishmentFixture.histories normalized |> List.filter (fun history -> history.Site = view.Site)
        Assert.Empty histories

module private LazyThunkWriteIngressFixture =
    let source = String.concat "\n" [
        "module LazyThunkWriteIngress"
        "let write (s: string) ="
        "    let _ = Sys.write 1 s.Bytes s.Length"
        "    ()"
        "[<EntryPoint>]"
        "let main _ ="
        "    let left = lazy (write \"left-cold\"; false)"
        "    let right = lazy (write \"right-cold\"; true)"
        "    let alias = left"
        "    if Lazy.force alias then 1 else"
        "        if Lazy.force right then"
        "            if Lazy.force left then 1 else"
        "                if Lazy.force right then 0 else 1"
        "        else 1"
        "" ]

    let checkedGraph () =
        let graph, projection =
            source |> LazyStringOriginFixture.check |> IntrinsicWriteFixture.graphAndProjection
        let call = Assert.Single projection.IntrinsicWrites.Values
        let view = projection.ByteViews[call.Buffer]
        let extent = projection.StringExtents[call.Count]
        let expected = Map.ofList [
            IntrinsicWriteFixture.literal graph "left-cold", 9I
            IntrinsicWriteFixture.literal graph "right-cold", 10I ]
        Assert.Equal<Map<NodeId, bigint>>(expected, view.StaticOrigins)
        Assert.Equal<Map<NodeId, bigint>>(expected, extent.StaticOrigins)
        Assert.Equal(view.ExtentSource, extent.ExtentSource)
        Assert.Equal(Some(ValueRange.bounded 9I 10I), graph.Nodes[call.Count].ValueRange)
        IntrinsicWriteFixture.established view.Participants |> Assert.NotEmpty
        IntrinsicWriteFixture.established extent.Participants |> Assert.NotEmpty
        let instances = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LazyInstance)
        let forces = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.LazyMemoization)
        Assert.Equal(2, instances.Length)
        Assert.Equal(4, forces.Length)
        Assert.Equal(2, instances |> List.map _.Target |> List.distinct |> List.length)
        for instance in instances do
            Assert.Equal(7, instance.Sources.Length)
            Assert.Equal(2, forces |> List.filter (fun force -> List.tryHead force.Sources = Some instance.Target) |> List.length)
        for force in forces do
            Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.LazyValues.force graph force.Target).IsSome)
        Assert.Contains(projection.IntrinsicWriteProofs[call.Site], fun proof ->
            match proof.Body with
            | ObligationBody.StringBorrowBound rows -> List.sort rows = [9I, 9I, 10I; 10I, 10I, 11I]
            | _ -> false)
        graph

type LazyThunkWriteIngressCases() =
    [<Fact>]
    member _.``Writes inside distinct Boolean lazy thunks retain both exact immutable origins`` () =
        LazyThunkWriteIngressFixture.checkedGraph () |> ignore

    [<Theory>]
    [<InlineData("instance-missing")>]
    [<InlineData("instance-ordinal")>]
    [<InlineData("memoization-missing")>]
    [<InlineData("memoization-ordinal")>]
    [<InlineData("memoization-class")>]
    [<InlineData("memoization-source-order")>]
    [<InlineData("result-call-added")>]
    member _.``Lazy thunk write authority rejects relation changes with unchanged source nodes`` (defect: string) =
        // This baseline proves that a different admission failure cannot make
        // a relation mutation pass. No owner is resettled after the mutation.
        let graph = LazyThunkWriteIngressFixture.checkedGraph ()
        let role = if defect.StartsWith("instance-", System.StringComparison.Ordinal) then EdgeRole.LazyInstance else EdgeRole.LazyMemoization
        let selected = graph.Edges |> List.find (fun edge -> edge.Role = role)
        let mutate (edge: Hyperedge) =
            if defect.EndsWith("ordinal", System.StringComparison.Ordinal) then { edge with Ordinal = edge.Ordinal + 1 }
            elif defect.EndsWith("class", System.StringComparison.Ordinal) then { edge with Class = EdgeClass.Reference }
            else { edge with Sources = List.rev edge.Sources }
        let revised =
            graph.Edges |> List.choose (fun edge ->
                if not (obj.ReferenceEquals(edge, selected)) then Some edge
                elif defect.EndsWith("missing", System.StringComparison.Ordinal) then None
                else Some(mutate edge))
        let edges =
            if defect = "result-call-added" then { selected with Role = EdgeRole.LazyResultCall } :: graph.Edges
            else revised
        let changed = { graph with Edges = edges }
        Assert.Same(graph.Nodes, changed.Nodes)
        Assert.Same(graph.DeclarationRoots, changed.DeclarationRoots)
        match IntrinsicBoundary.project changed with
        | Result.Error failures ->
            Assert.Contains(failures, fun failure ->
                failure.Reason.Contains("string-origin relation premises changed", System.StringComparison.Ordinal))
        | Result.Ok _ -> failwith "Changed lazy ingress relations retained the old boundary authority."

module internal RuntimeSnapshotWriteFixture =
    let publish graph =
        Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish graph
        |> Result.defaultWith (sprintf "%A" >> failwith)

    let authority =
        IntrinsicWriteFixture.writableAuthority
            .Replace(
                "let rodata =",
                "let stack = { Name = \"stack\"; Kind = \"stack\"; Capacity = 4096; Alignment = 16; Granularity = 16; Growth = \"down\"; Access = \"rw\"; Base = None }\nlet rodata ="
            )
            .Replace("Spaces = [| rodata; data |]", "Spaces = [| rodata; data; stack |]")

    let source mutation count =
        "module RuntimeSnapshotWrite\n[<EntryPoint>]\nlet main _ =\n"
        + "    let input = [| 195; 169 |]\n    let text = String.fromBytes input\n"
        + mutation
        + "    let _ = Sys.write 1 text.Bytes "
        + count
        + "\n    0\n"

    let check mutation count =
        IntrinsicWriteFixture.checkSource authority (source mutation count)

    let admitted mutation =
        let graph, projection =
            check mutation "text.Length" |> IntrinsicWriteFixture.graphAndProjection

        let call = Assert.Single projection.IntrinsicWrites.Values

        let domain =
            graph.Edges
            |> List.choose (fun edge ->
                match edge.Role with
                | EdgeRole.BoundaryDomain fact -> Some fact
                | _ -> None)
            |> Assert.Single

        let snapshot = Assert.Single domain.StringBorrowSnapshots
        let copy = Assert.Single domain.StringBorrowCopies
        let allocation = Assert.Single domain.StringBorrowAllocations
        Assert.Empty(projection.ByteViews[call.Buffer].StaticOrigins)
        Assert.Empty(projection.StringExtents[call.Count].StaticOrigins)
        Assert.Equal(snapshot.Snapshot, copy.Site)
        Assert.Equal(snapshot.Extent, copy.CountCarrier)
        Assert.Equal(Some allocation.Site, copy.Allocation)
        Assert.Equal(Some(ValueRange.bounded 2I 2I), graph.Nodes[call.Count].ValueRange)
        Assert.Equal(ValueRange.bounded 2I 2I, allocation.CountCarrier.Range)

        Assert.Contains(
            projection.IntrinsicWriteProofs[call.Site],
            fun proof -> proof.Ordinal = 1 && proof.Body = ObligationBody.InputBufferBound(2L, 2L)
        )

        Assert.DoesNotContain(
            projection.IntrinsicWriteProofs[call.Site],
            fun proof ->
                match proof.Body with
                | ObligationBody.StringBorrowBound _ -> true
                | _ -> false
        )

        Assert.Empty(Fidelity.PSG.Integrity.check (publish graph))

        graph, domain, call

    let dynamicAdmittedWith constructor =
        let source = """module DynamicSnapshotWrite
let emit flag =
    let n = if flag then 2 else 3
    let input = """ + constructor + """
    let text = String.fromBytes input
    let result = Sys.write 1 text.Bytes text.Length
    result
[<EntryPoint>]
let main _ =
    let first = emit true
    let second = emit false
    if first < 0 then 1 else if second < 0 then 1 else 0
"""
        let graph, projection =
            IntrinsicWriteFixture.checkSource authority source |> IntrinsicWriteFixture.graphAndProjection
        let call = Assert.Single projection.IntrinsicWrites.Values
        let domain =
            graph.Edges |> List.choose (fun edge ->
                match edge.Role with EdgeRole.BoundaryDomain value -> Some value | _ -> None)
            |> Assert.Single
        graph,domain,call

    let dynamicAdmitted () = dynamicAdmittedWith "Array.create n 65"

    let withDomain (graph:SemanticGraph) revised =
        let edges =
            graph.Edges |> List.map (fun edge ->
                match edge.Role with EdgeRole.BoundaryDomain _ -> {edge with Role=EdgeRole.BoundaryDomain revised} | _ -> edge)
        {graph with Edges=edges}

type RuntimeSnapshotWriteCases() =
    [<Fact>]
    member _.``Runtime snapshot public reader refuses coherent singleton dynamic arm``() =
        let graph,domain,call = RuntimeSnapshotWriteFixture.admitted ""
        let revision = RuntimeSnapshotWriteFixture.publish graph
        let map=Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId
        let snapshot=Assert.Single domain.StringBorrowSnapshots
        let copy=Assert.Single domain.StringBorrowCopies
        let allocation=Assert.Single domain.StringBorrowAllocations
        let proof=revision.Emission.Boundary.IntrinsicWriteProofs[map call.Site] |> List.filter (fun value -> value.Ordinal=1) |> Assert.Single
        Assert.Equal(Fidelity.PSG.ObligationBody.InputBufferBound(2L,2L),proof.Body)
        let body=Fidelity.PSG.ObligationBody.SnapshotBorrowBound(map call.Count,map snapshot.Site,map copy.Site,map allocation.Site,2I,2I,bigint allocation.ElementBytes,allocation.MaximumCount * bigint allocation.ElementBytes)
        let old=revision.CurrentClaims[proof.Obligation]
        let changed={old with Body=body}
        let boundary=revision.Emission.Boundary
        let proofs=boundary.IntrinsicWriteProofs |> Map.map (fun _ rows ->
            rows |> List.map (fun row -> if row.Obligation=proof.Obligation then {row with Body=body} else row))
        let revised=
            {revision with
                Obligations=revision.Obligations |> List.map (fun row -> if row=old then changed else row)
                CurrentClaims=revision.CurrentClaims.Add(proof.Obligation,changed)
                Emission={revision.Emission with Boundary={boundary with IntrinsicWriteProofs=proofs}}}
        Assert.Contains(Fidelity.PSG.Integrity.check revised,fun issue ->
            issue.Part="Emission.Boundary.IntrinsicWriteProofs.SnapshotBorrowBound")

    [<Fact>]
    member _.``Dynamic zero snapshot publishes allocation and complete zero initialization``() =
        let graph,domain,call = RuntimeSnapshotWriteFixture.dynamicAdmittedWith "Array.zeroCreate n"
        let constructions = graph.Edges |> List.choose (fun edge ->
            match edge.Role with EdgeRole.ArrayAllocationConstruction value -> Some value | _ -> None)
        let source = constructions |> List.filter (fun value -> value.Default.IsSome) |> Assert.Single
        let initialization = source.Initialization |> Option.defaultWith (fun () -> failwith "Missing complete zero initialization loop.")
        match graph.Nodes[source.Default.Value].Kind with
        | SemanticKind.Literal(NativeLiteral.Int(0L,_))
        | SemanticKind.Literal(NativeLiteral.UInt(0UL,_)) -> ()
        | other -> failwithf "Expected exact source zero default, got %A" other
        let support =
            Clef.Compiler.Baker.Ingredients.ArrayInitialization.tryInitialization graph source.Site
            |> Result.defaultWith failwith
        Assert.Contains(initialization.Loop,support)
        Assert.Contains(initialization.Write,support)
        Assert.Equal(Some(ValueRange.bounded 2I 3I),graph.Nodes[call.Count].ValueRange)
        let snapshot = Assert.Single domain.StringBorrowSnapshots
        Assert.Contains(graph.Edges,fun edge -> edge.Target=snapshot.Owner && edge.Role=EdgeRole.StringAscii)
        let revision = RuntimeSnapshotWriteFixture.publish graph
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let allocations =
            revision.Emission.Memory.Operations.Values
            |> Seq.choose (function
                | Fidelity.PSG.MemoryWitnessOperation.ArrayAllocation value -> Some value
                | _ -> None)
            |> Seq.toList
        Assert.Equal(2,allocations.Length)
        let sourceSite = Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId source.Site
        let sourceAllocation = allocations |> List.filter (fun value -> value.Site=sourceSite) |> Assert.Single
        Assert.Equal(Clef.Compiler.Baker.Ingredients.PublishedFactRows.mapArrayAllocationConstruction source,sourceAllocation.Construction)
        Assert.Equal(2I,sourceAllocation.MinimumCount)
        Assert.Equal(3I,sourceAllocation.MaximumCount)
        let writes =
            revision.Emission.Memory.Operations.Values
            |> Seq.choose (function
                | Fidelity.PSG.MemoryWitnessOperation.ArrayAccess value when value.Value.IsSome -> Some value
                | _ -> None)
            |> Seq.toList
        Assert.Contains(writes,fun value ->
            value.Value=Some(Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId source.Default.Value)
            && value.Bounds.Requirement.Frontier=Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId initialization.Write
            && value.Bounds.Requirement.Continuation=value.Site)
        let borrow = domain.IntrinsicProofs |> List.filter (fun proof -> proof.Site=call.Site && proof.Ordinal=1) |> Assert.Single
        let info =
            match graph.Nodes[borrow.Obligation].Kind with
            | SemanticKind.Obligation info -> info
            | _ -> failwith "Missing actual snapshot borrow obligation."
        Assert.Equal("source-checked snapshot/copy/allocation count correspondence; SMT establishes the finite nonnegative count domain",info.Statement)
        Assert.Contains(info.Statement,Clef.Compiler.Nanopass.ObligationDischarge.ledgerJson [info])
        match System.Environment.GetEnvironmentVariable "FFI_ZERO_SNAPSHOT_OUTPUT" |> Option.ofObj with
        | Some output when not(System.String.IsNullOrWhiteSpace output) ->
            let path = System.IO.Path.GetFullPath output
            Assert.StartsWith("/home/hhh/repos/clef/artifacts/ffi-reconcile-20261013/dynamic-snapshot/zero-native-prep/",path)
            Assert.False(System.IO.File.Exists path,"A frozen zero snapshot must not be overwritten.")
            let limits:Fidelity.PSG.Binary.Limits =
                {MaxBytes=4*1024*1024;MaxCollectionLength=10000;MaxDepth=128;MaxStringBytes=1024*1024;MaxBigIntegerBytes=4096;MaxValues=1000000}
            let bytes = Fidelity.PSG.Binary.encode limits revision |> Result.defaultWith (sprintf "%A" >> failwith)
            let copy = Fidelity.PSG.Binary.decode limits bytes |> Result.defaultWith (sprintf "%A" >> failwith)
            let again = Fidelity.PSG.Binary.encode limits copy |> Result.defaultWith (sprintf "%A" >> failwith)
            Assert.True((bytes=again),"Full zero snapshot codec bytes changed.")
            System.IO.File.WriteAllBytes(path,bytes)
            System.IO.File.WriteAllText(path+".facts.txt",sprintf "SOURCE_CONSTRUCTION %A\nSOURCE_INITIALIZATION_SUPPORT %A\nPUBLISHED_ALLOCATIONS %A\nPUBLISHED_WRITES %A\nASCII_OWNER %A\nCOUNT %A\n" source support allocations writes snapshot.Owner call.Count)
        | _ -> ()

    [<Theory>]
    [<InlineData("withdrawn")>]
    [<InlineData("changed")>]
    member _.``Dynamic zero snapshot refuses a changed retained initialization account`` mutation =
        let graph,_,_ = RuntimeSnapshotWriteFixture.dynamicAdmittedWith "Array.zeroCreate n"
        let revise (domain:MemoryDomain) =
            let operations =
                domain.Operations |> List.map (fun (site,operation) ->
                    match operation with
                    | MemoryWitnessOperation.ArrayAllocation allocation when allocation.Construction.Default.IsSome ->
                        let construction=allocation.Construction
                        let initialization =
                            match mutation,construction.Initialization with
                            | "withdrawn",Some _ -> None
                            | "changed",Some value -> Some {value with Write=construction.Default.Value}
                            | _ -> failwith "Expected one nonempty source zero initialization."
                        site,MemoryWitnessOperation.ArrayAllocation {allocation with Construction={construction with Initialization=initialization}}
                    | _ -> site,operation)
            {domain with Operations=operations}
        let revised =
            graph.Edges
            |> List.choose (fun edge -> match edge.Role with EdgeRole.MemoryDomain value -> Some value | _ -> None)
            |> Assert.Single
            |> revise
        let operations=Map.ofList revised.Operations
        // Keep the two stored operation copies coherent; the original construction remains unchanged.
        let edges = graph.Edges |> List.map (fun edge ->
            match edge.Role with
            | EdgeRole.MemoryDomain _ -> {edge with Role=EdgeRole.MemoryDomain revised}
            | EdgeRole.MemoryOperation _ -> {edge with Role=EdgeRole.MemoryOperation operations[edge.Target]}
            | _ -> edge)
        match Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication.project {graph with Edges=edges} with
        | Error failures ->
            Assert.Contains(failures,fun failure -> failure.Reason.Contains "allocation witness lost its exact validated construction, count or initialization account")
        | Ok _ -> failwith "A changed retained initialization account remained current."

    [<Theory>]
    [<InlineData("default")>]
    [<InlineData("initialization")>]
    [<InlineData("write")>]
    member _.``Dynamic zero snapshot public reader refuses changed initialization evidence`` mutation =
        let graph,_,_ = RuntimeSnapshotWriteFixture.dynamicAdmittedWith "Array.zeroCreate n"
        let revision=RuntimeSnapshotWriteFixture.publish graph
        let memory=revision.Emission.Memory
        let allocation=
            memory.Operations.Values
            |> Seq.choose (function
                | Fidelity.PSG.MemoryWitnessOperation.ArrayAllocation value when value.Construction.Default.IsSome -> Some value
                | _ -> None)
            |> Assert.Single
        let construction=allocation.Construction
        let initialization=construction.Initialization |> Option.defaultWith (fun () -> failwith "Missing source zero initialization.")
        let write=
            memory.Operations.Values
            |> Seq.choose (function
                | Fidelity.PSG.MemoryWitnessOperation.ArrayAccess value when value.Bounds.Requirement.Frontier=initialization.Write -> Some value
                | _ -> None)
            |> Assert.Single
        let replace construction=
            memory.Operations.Add(allocation.Site,Fidelity.PSG.MemoryWitnessOperation.ArrayAllocation {allocation with Construction=construction})
        let operations,reason=
            match mutation with
            | "default" ->
                Assert.NotEqual(construction.Default,Some construction.Guard.Zero)
                replace {construction with Default=Some construction.Guard.Zero},
                "The initialization construction differs from its exact guarded zero write."
            | "initialization" ->
                replace {construction with Initialization=None},
                "A nonempty zero allocation has no retained initialization construction."
            | "write" ->
                memory.Operations.Remove write.Site,
                "The initialization construction differs from its exact guarded zero write."
            | _ -> failwith "Unknown public initialization mutation."
        let revised={revision with Emission={revision.Emission with Memory={memory with Operations=operations}}}
        Assert.Contains(Fidelity.PSG.Integrity.check revised,fun issue ->
            issue.Part="Emission.Memory.Operations.ArrayAllocation.Construction" && issue.Reason=reason)

    [<Fact>]
    member _.``Dynamic snapshot borrow retains one actual count for both finite extents``() =
        let graph,domain,call = RuntimeSnapshotWriteFixture.dynamicAdmitted ()
        let snapshot = Assert.Single domain.StringBorrowSnapshots
        let copy = Assert.Single domain.StringBorrowCopies
        let allocation = Assert.Single domain.StringBorrowAllocations
        Assert.Equal(Some(ValueRange.bounded 2I 3I),graph.Nodes[call.Count].ValueRange)
        Assert.Equal(ValueRange.bounded 2I 3I,copy.CountCarrier.Range)
        Assert.Equal(2I,allocation.MinimumCount)
        Assert.Equal(3I,allocation.MaximumCount)
        Assert.Equal(copy.CountOperand.Actual,copy.Count)
        Assert.Equal(copy.CountOperand.Reference,allocation.Count)
        let proof = domain.IntrinsicProofs |> List.filter (fun proof -> proof.Site=call.Site && proof.Ordinal=1) |> Assert.Single
        Assert.Equal(ObligationBody.SnapshotBorrowBound(call.Count,snapshot.Site,copy.Site,allocation.Site,2I,3I,bigint allocation.ElementBytes,allocation.MaximumCount * bigint allocation.ElementBytes),proof.Body)
        Assert.Contains(graph.Edges,fun edge -> edge.Target=snapshot.Owner && edge.Role=EdgeRole.StringAscii)
        let revision = RuntimeSnapshotWriteFixture.publish graph
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let output = System.Environment.GetEnvironmentVariable "FFI_DYNAMIC_SNAPSHOT_OUTPUT" |> Option.ofObj
        match output with
        | Some output when not (System.String.IsNullOrWhiteSpace output) ->
            let allowed = "/home/hhh/repos/clef/artifacts/ffi-reconcile-20261013/"
            let path = System.IO.Path.GetFullPath output
            Assert.StartsWith(allowed,path)
            Assert.False(System.IO.File.Exists path,"A frozen dynamic snapshot must not be overwritten.")
            let directory = System.IO.Path.GetDirectoryName path |> Option.ofObj |> Option.defaultWith (fun () -> failwith "Missing snapshot directory")
            System.IO.Directory.CreateDirectory directory |> ignore
            let limits:Fidelity.PSG.Binary.Limits =
                {MaxBytes=4*1024*1024;MaxCollectionLength=10000;MaxDepth=128;MaxStringBytes=1024*1024;MaxBigIntegerBytes=4096;MaxValues=1000000}
            let bytes = Fidelity.PSG.Binary.encode limits revision |> Result.defaultWith (sprintf "%A" >> failwith)
            let copy = Fidelity.PSG.Binary.decode limits bytes |> Result.defaultWith (sprintf "%A" >> failwith)
            let again = Fidelity.PSG.Binary.encode limits copy |> Result.defaultWith (sprintf "%A" >> failwith)
            Assert.True((bytes=again),"Full dynamic snapshot codec bytes changed.")
            System.IO.File.WriteAllBytes(path,bytes)
        | _ -> ()

    [<Fact>]
    member _.``Dynamic snapshot borrow refuses an equal range from another count occurrence``() =
        let graph,domain,call = RuntimeSnapshotWriteFixture.dynamicAdmitted ()
        let copy = Assert.Single domain.StringBorrowCopies
        Assert.NotEqual(call.Count,copy.Count)
        Assert.Equal(graph.Nodes[call.Count].ValueRange,graph.Nodes[copy.Count].ValueRange)
        let proofs = domain.IntrinsicProofs |> List.map (fun proof ->
            match proof.Body with
            | ObligationBody.SnapshotBorrowBound(_,snapshot,copySite,allocation,minimum,maximum,elementBytes,allocationCapacity) ->
                {proof with Body=ObligationBody.SnapshotBorrowBound(copy.Count,snapshot,copySite,allocation,minimum,maximum,elementBytes,allocationCapacity)}
            | _ -> proof)
        let changed = RuntimeSnapshotWriteFixture.withDomain graph {domain with IntrinsicProofs=proofs}
        match IntrinsicBoundary.project changed with
        | Error failures -> Assert.Contains(failures,fun failure -> failure.Reason.Contains "runtime snapshot borrow proof lost its exact count")
        | Ok _ -> failwith "Equal ranges substituted another count occurrence into the borrow proof."

    [<Theory>]
    [<InlineData("copy")>]
    [<InlineData("allocation")>]
    member _.``Dynamic snapshot borrow refuses withdrawn storage support`` dependency =
        let graph,domain,_ = RuntimeSnapshotWriteFixture.dynamicAdmitted ()
        let revised =
            match dependency with
            | "copy" -> {domain with StringBorrowCopies=[]}
            | "allocation" -> {domain with StringBorrowAllocations=[]}
            | _ -> failwith "Unknown dynamic snapshot support"
        match RuntimeSnapshotWriteFixture.withDomain graph revised |> IntrinsicBoundary.project with
        | Error failures -> Assert.Contains(failures,fun failure -> failure.Reason.Contains "dependency account is incomplete")
        | Ok _ -> failwith "A dynamic borrow retained withdrawn storage support."

    [<Fact>]
    member _.``Dynamic snapshot borrow public reader refuses coherent equal range count substitution``() =
        let graph,_,_ = RuntimeSnapshotWriteFixture.dynamicAdmitted ()
        let revision = RuntimeSnapshotWriteFixture.publish graph
        Assert.Empty(Fidelity.PSG.Integrity.check revision)
        let proof =
            revision.Emission.Boundary.IntrinsicWriteProofs.Values
            |> Seq.collect id
            |> Seq.filter (fun proof ->
                match proof.Body with Fidelity.PSG.ObligationBody.SnapshotBorrowBound _ -> true | _ -> false)
            |> Assert.Single
        let count,snapshot,copySite,allocation,minimum,maximum,elementBytes,allocationCapacity =
            match proof.Body with
            | Fidelity.PSG.ObligationBody.SnapshotBorrowBound(a,b,c,d,e,f,g,h) -> a,b,c,d,e,f,g,h
            | _ -> failwith "Missing published dynamic borrow claim."
        let copy = revision.Emission.Memory.ArrayCopies[copySite]
        Assert.NotEqual(count,copy.Count)
        Assert.Equal(revision.Emission.Numeric.Values[count].Range,copy.CountCarrier.Range)
        let body = Fidelity.PSG.ObligationBody.SnapshotBorrowBound(copy.Count,snapshot,copySite,allocation,minimum,maximum,elementBytes,allocationCapacity)
        let old = revision.CurrentClaims[proof.Obligation]
        let changed = {old with Body=body}
        let boundary = revision.Emission.Boundary
        // Change all stored claim copies together: only original source incidence refutes this.
        let proofs = boundary.IntrinsicWriteProofs |> Map.map (fun _ rows ->
            rows |> List.map (fun row -> if row.Obligation=proof.Obligation then {row with Body=body} else row))
        let revised =
            {revision with
                Obligations=revision.Obligations |> List.map (fun row -> if row=old then changed else row)
                CurrentClaims=revision.CurrentClaims.Add(proof.Obligation,changed)
                Emission={revision.Emission with Boundary={boundary with IntrinsicWriteProofs=proofs}}}
        Assert.Contains(Fidelity.PSG.Integrity.check revised,fun issue ->
            issue.Part="Emission.Boundary.IntrinsicWriteProofs.SnapshotBorrowBound"
            && issue.Reason="The runtime borrow claim differs from its exact count, snapshot, copy or bound-operand allocation account.")

    [<Fact>]
    member _.``Dynamic snapshot borrow invalidates an inverted actual allocation guard``() =
        let graph,domain,_ = RuntimeSnapshotWriteFixture.dynamicAdmitted ()
        let allocation = Assert.Single domain.StringBorrowAllocations
        let condition = graph.Nodes[allocation.Requirement.Condition]
        let changed =
            match condition.Kind with
            | SemanticKind.Application(callee,[left;right]) ->
                {condition with Kind=SemanticKind.Application(callee,[right;left]);Children=[callee;right;left]}
            | SemanticKind.IfThenElse(predicate,yes,Some no) ->
                {condition with Kind=SemanticKind.IfThenElse(predicate,no,Some yes);Children=[predicate;no;yes]}
            | other -> failwithf "Expected the actual allocation predicate or short-circuit guard, got %A" other
        let graph = {graph with Nodes=graph.Nodes.Add(condition.Id,changed)}
        match Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication.project graph with
        | Error failures -> Assert.Contains(failures,fun failure -> failure.Reason.Contains "exact memory source, guard, meet or declaration premises changed")
        | Ok _ -> failwith "An inverted actual allocation guard retained admitted memory authority."

    [<Fact>]
    member _.``Native write retains an immutable UTF8 snapshot with an exact local count``() =
        RuntimeSnapshotWriteFixture.admitted "" |> ignore

    [<Fact>]
    member _.``A forced ASCII snapshot survives mutation of its original input``() =
        let source =
            (RuntimeSnapshotWriteFixture.source "    input[0] <- 67\n" "text.Length")
                .Replace("[| 195; 169 |]", "[| 65; 66 |]")
                .Replace("let text = String.fromBytes input", "let text = eager (String.fromBytes input)")

        let graph, projection =
            IntrinsicWriteFixture.checkSource RuntimeSnapshotWriteFixture.authority source
            |> IntrinsicWriteFixture.graphAndProjection

        let call = Assert.Single projection.IntrinsicWrites.Values

        let domain =
            graph.Edges
            |> List.choose (fun edge ->
                match edge.Role with
                | EdgeRole.BoundaryDomain fact -> Some fact
                | _ -> None)
            |> Assert.Single

        let copy = Assert.Single domain.StringBorrowCopies
        Assert.True(copy.Allocation.IsSome)
        Assert.NotEqual(copy.Source, copy.Destination)
        Assert.Equal(Some(ValueRange.bounded 2I 2I), graph.Nodes[call.Count].ValueRange)

    [<Fact>]
    member _.``Runtime snapshot aliases retain one exact borrowed descriptor``() =
        let source =
            RuntimeSnapshotWriteFixture.source "    let alias = text\n" "alias.Length"

        let graph, projection =
            IntrinsicWriteFixture.checkSource RuntimeSnapshotWriteFixture.authority (source.Replace("text.Bytes", "alias.Bytes"))
            |> IntrinsicWriteFixture.graphAndProjection

        let call = Assert.Single projection.IntrinsicWrites.Values
        Assert.Equal(projection.ByteViews[call.Buffer].ExtentSource, projection.StringExtents[call.Count].ExtentSource)

        Assert.Contains(
            projection.IntrinsicWriteProofs[call.Site],
            fun proof -> proof.Ordinal = 1 && proof.Body = ObligationBody.InputBufferBound(2L, 2L)
        )

        let revision = RuntimeSnapshotWriteFixture.publish graph
        Assert.Empty(Fidelity.PSG.Integrity.check revision)

        let source =
            Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId projection.ByteViews[call.Buffer].ExtentSource

        Assert.Contains(
            revision.Emission.Memory.Operations.Values,
            fun operation ->
                match operation with
                | Fidelity.PSG.MemoryWitnessOperation.StringView snapshot ->
                    snapshot.Site = source
                    && snapshot.Direction = Fidelity.PSG.MemoryStringViewDirection.FromBytes
                | _ -> false
        )

    [<Fact>]
    member _.``Runtime write refuses a count without the borrowed descriptor relation``() =
        let result = RuntimeSnapshotWriteFixture.check "" "1"

        match IntrinsicBoundary.project result.Graph with
        | Error failures ->
            Assert.Contains(failures, fun failure -> failure.Reason.Contains "count must preserve the exact borrowed string")
        | Ok _ -> failwith "A runtime byte borrow acquired an unrelated count."

    [<Fact>]
    member _.``Runtime write refuses an equal count from a different snapshot``() =
        let result =
            RuntimeSnapshotWriteFixture.check "    let other = String.fromBytes [| 65; 66 |]\n" "other.Length"

        match IntrinsicBoundary.project result.Graph with
        | Error failures -> Assert.Contains(failures, fun failure -> failure.Reason.Contains "same per-invocation string extent")
        | Ok _ -> failwith "Equal numeric extents substituted for exact snapshot identity."

    [<Fact>]
    member _.``Runtime write retracts changed allocation evidence with unchanged source nodes``() =
        let graph, domain, call = RuntimeSnapshotWriteFixture.admitted ""
        let domainRow =
            graph.Edges
            |> List.filter (fun edge ->
                match edge.Role with
                | EdgeRole.BoundaryDomain _ -> true
                | _ -> false)
            |> Assert.Single
        let expectedParticipants = Map.keys domain.Premises |> Set.ofSeq
        let expectedProofReason =
            "BoundaryEmission: The runtime snapshot borrow proof lost its exact count, snapshot, copy, allocation or finite range incidence."
        let expectedMemoryReason =
            "BoundaryEmission: A local string borrow lost its exact source-published guarded read, snapshot copy or lifetime correspondence."
        let expectedOriginReason =
            "BoundaryEmission: The string-origin relation premises changed; Baker must settle the new source graph."
        let allocation = Assert.Single domain.StringBorrowAllocations

        let changedAllocation =
            { allocation with
                MaximumCount = allocation.MaximumCount + 1I
            }

        let changedDomain =
            { domain with
                StringBorrowAllocations = [ changedAllocation ]
            }

        let edges =
            graph.Edges
            |> List.map (fun edge ->
                match edge.Role with
                | EdgeRole.BoundaryDomain _ ->
                    { edge with
                        Role = EdgeRole.BoundaryDomain changedDomain
                    }
                | _ -> edge)

        let changed = { graph with Edges = edges }
        Assert.Same(graph.Nodes, changed.Nodes)

        match IntrinsicBoundary.project changed with
        | Error failures ->
            Assert.Equal(2, failures.Length)
            Assert.All(
                failures,
                fun failure ->
                    Assert.Equal(WitnessProjectionFailureKind.Settlement, failure.Kind)
                    Assert.Equal(Some domainRow.Target, failure.Occurrence)
                    Assert.Equal<Set<NodeId>>(expectedParticipants, failure.Participants)
            )
            Assert.Equal<string list>(
                [ expectedProofReason; expectedMemoryReason ],
                failures |> List.map _.Reason
            )
        | Ok _ -> failwith "Changed runtime allocation evidence retained the old write authority."

        let proofOnlyDomain =
            { domain with
                IntrinsicProofs =
                    domain.IntrinsicProofs
                    |> List.map (fun proof ->
                        if proof.Ordinal = 1 then
                            { proof with Body = ObligationBody.InputBufferBound(2L, 3L) }
                        else
                            proof)
            }
        let proofOnly = RuntimeSnapshotWriteFixture.withDomain graph proofOnlyDomain
        match IntrinsicBoundary.project proofOnly with
        | Error failures ->
            let failure = Assert.Single failures
            Assert.Equal(WitnessProjectionFailureKind.Settlement, failure.Kind)
            Assert.Equal(Some domainRow.Target, failure.Occurrence)
            Assert.Equal<Set<NodeId>>(expectedParticipants, failure.Participants)
            Assert.Equal(expectedProofReason, failure.Reason)
        | Ok _ -> failwith "Corrupted runtime snapshot proof retained write authority."

        let memoryOnly =
            { graph with
                Edges =
                    graph.Edges
                    |> List.filter (fun edge ->
                        match edge.Role with
                        | EdgeRole.MemoryOperation(MemoryWitnessOperation.ArrayAllocation fact) -> fact.Site <> allocation.Site
                        | _ -> true)
            }
        match IntrinsicBoundary.project memoryOnly with
        | Error failures ->
            let failure = Assert.Single failures
            Assert.Equal(WitnessProjectionFailureKind.Settlement, failure.Kind)
            Assert.Equal(Some domainRow.Target, failure.Occurrence)
            Assert.Equal<Set<NodeId>>(expectedParticipants, failure.Participants)
            Assert.Equal(expectedMemoryReason, failure.Reason)
        | Ok _ -> failwith "Withdrawn memory allocation operation retained write authority."

        Assert.NotEmpty graph.DeclarationRoots
        let originOnlyDomain =
            { domain with
                StringOriginRelations = Some []
                StringOriginRoots = Some []
            }
        let originOnly = RuntimeSnapshotWriteFixture.withDomain graph originOnlyDomain
        match IntrinsicBoundary.project originOnly with
        | Error failures ->
            let failure = Assert.Single failures
            Assert.Equal(WitnessProjectionFailureKind.Settlement, failure.Kind)
            Assert.Equal(Some domainRow.Target, failure.Occurrence)
            Assert.Equal<Set<NodeId>>(expectedParticipants, failure.Participants)
            Assert.Equal(expectedOriginReason, failure.Reason)
        | Ok _ -> failwith "Changed string-origin premises retained write authority."

        let originAndBorrowDomain =
            { originOnlyDomain with
                StringBorrowAllocations = [ changedAllocation ]
            }
        let originAndBorrow = RuntimeSnapshotWriteFixture.withDomain graph originAndBorrowDomain
        match IntrinsicBoundary.project originAndBorrow with
        | Error failures ->
            let failure = Assert.Single failures
            Assert.Equal(WitnessProjectionFailureKind.Settlement, failure.Kind)
            Assert.Equal(Some domainRow.Target, failure.Occurrence)
            Assert.Equal<Set<NodeId>>(expectedParticipants, failure.Participants)
            Assert.Equal(expectedOriginReason, failure.Reason)
        | Ok _ -> failwith "Simultaneous string-origin and borrow drift retained write authority."

        for drifted in [ changed; proofOnly; originOnly; originAndBorrow ] do
            let resettled = Clef.Compiler.Nanopass.BoundarySettlement.normalize drifted
            let projection =
                IntrinsicBoundary.project resettled
                |> Result.defaultWith (sprintf "%A" >> failwith)
            Assert.True(projection.IntrinsicWrites.ContainsKey call.Site)

        let resettledMemory =
            memoryOnly
            |> Clef.Compiler.Nanopass.MemorySettlement.normalize
            |> Clef.Compiler.Nanopass.BoundarySettlement.normalize
        let resettledMemoryProjection =
            IntrinsicBoundary.project resettledMemory
            |> Result.defaultWith (sprintf "%A" >> failwith)
        Assert.True(resettledMemoryProjection.IntrinsicWrites.ContainsKey call.Site)

    [<Theory>]
    [<InlineData("snapshot")>]
    [<InlineData("copy")>]
    [<InlineData("allocation")>]
    [<InlineData("all")>]
    member _.``Runtime write refuses withdrawn storage dependencies`` dependency =
        let graph, domain, _ = RuntimeSnapshotWriteFixture.admitted ""

        let revised =
            match dependency with
            | "snapshot" ->
                { domain with
                    StringBorrowSnapshots = []
                }
            | "copy" -> { domain with StringBorrowCopies = [] }
            | "allocation" ->
                { domain with
                    StringBorrowAllocations = []
                }
            | "all" ->
                { domain with
                    StringBorrowSnapshots = []
                    StringBorrowCopies = []
                    StringBorrowAllocations = []
                }
            | _ -> failwithf "Unknown snapshot dependency: %s" dependency

        let edges =
            graph.Edges
            |> List.map (fun edge ->
                match edge.Role with
                | EdgeRole.BoundaryDomain _ ->
                    { edge with
                        Role = EdgeRole.BoundaryDomain revised
                    }
                | _ -> edge)

        let changed = { graph with Edges = edges }
        Assert.Same(graph.Nodes, changed.Nodes)

        match IntrinsicBoundary.project changed with
        | Error failures -> Assert.Contains(failures, fun failure -> failure.Reason.Contains "dependency account is incomplete")
        | Ok _ -> failwith "A withdrawn snapshot dependency retained native write authority."

    [<Fact>]
    member _.``Unchanged borrow renewal preserves exact logical row membership``() =
        let graph, _, _ = RuntimeSnapshotWriteFixture.admitted ""
        let first = Clef.Compiler.Nanopass.StringBorrows.normalize graph
        let second = Clef.Compiler.Nanopass.StringBorrows.normalize first

        let keys graph =
            graph.Edges
            |> List.map (fun edge -> edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target)

        Assert.True(keys first = keys second, "Repeated source-owner renewal duplicated or changed an unchanged logical row.")

    [<Fact>]
    member _.``Withdrawn borrow evidence remains refused until its source owners renew it``() =
        let graph, _, call = RuntimeSnapshotWriteFixture.admitted ""

        let edges =
            graph.Edges
            |> List.filter (fun edge ->
                match edge.Role with
                | EdgeRole.StringByteView _ when edge.Target = call.Buffer -> false
                | _ -> true)

        let withdrawn = { graph with Edges = edges }
        Assert.True(IntrinsicBoundary.project withdrawn |> Result.isError)
        let renewed = Clef.Compiler.Nanopass.StringBorrows.normalize withdrawn

        let established, diagnostics =
            Clef.Compiler.Nanopass.PremiseEstablishment.normalize renewed

        Assert.Empty diagnostics

        Assert.True(
            Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication.project established
            |> Result.isError
        )

        Assert.True(
            Clef.Compiler.PSGSaturation.SemanticGraph.NumericPublication.project established
            |> Result.isError
        )

        let ranged, rangeDiagnostics =
            Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.run established.Platform established

        Assert.DoesNotContain(rangeDiagnostics, fun diagnostic -> diagnostic.Severity = Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics.NativeDiagnosticSeverity.Error)
        let numeric = Clef.Compiler.Nanopass.NumericSettlement.normalize ranged
        let memory = Clef.Compiler.Nanopass.MemorySettlement.normalize numeric
        let settled = Clef.Compiler.Nanopass.BoundarySettlement.normalize memory

        let projection =
            IntrinsicBoundary.project settled
            |> Result.defaultWith (sprintf "%A" >> failwith)

        Assert.True(projection.IntrinsicWrites.ContainsKey call.Site)

    [<Theory>]
    [<InlineData("snapshot", "Emission.Boundary.ByteViews.Snapshot")>]
    [<InlineData("copy", "Emission.Memory.Operations.StringView.Snapshot")>]
    [<InlineData("allocation", "Emission.Memory.ArrayCopies.Allocation")>]
    [<InlineData("unstated-allocation", "Emission.Boundary.ByteViews.SnapshotAllocation")>]
    [<InlineData("all", "Emission.Boundary.ByteViews.Snapshot")>]
    [<InlineData("borrow", "Emission.Boundary.IntrinsicWrites.Buffer")>]
    member _.``Published runtime write refuses withdrawn memory authority``(dependency, part) =
        let graph, _, call = RuntimeSnapshotWriteFixture.admitted ""
        let revision = RuntimeSnapshotWriteFixture.publish graph
        let nodeId = Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId
        let view = revision.Emission.Boundary.ByteViews[nodeId call.Buffer]
        let memory = revision.Emission.Memory

        let snapshot =
            match memory.Operations[view.ExtentSource] with
            | Fidelity.PSG.MemoryWitnessOperation.StringView value -> value
            | other -> failwithf "The admitted runtime descriptor has no StringView: %A" other

        let copy = memory.ArrayCopies[snapshot.Snapshot]
        let allocation = copy.Allocation.Value

        let revised =
            match dependency with
            | "borrow" -> memory
            | "snapshot" ->
                { memory with
                    Operations = memory.Operations.Remove snapshot.Site
                }
            | "copy" ->
                { memory with
                    ArrayCopies = memory.ArrayCopies.Remove copy.Site
                }
            | "allocation" ->
                { memory with
                    Operations = memory.Operations.Remove allocation
                }
            | "unstated-allocation" ->
                { memory with
                    ArrayCopies = memory.ArrayCopies.Add(copy.Site, { copy with Allocation = None })
                }
            | "all" ->
                { memory with
                    Operations = memory.Operations.Remove(snapshot.Site).Remove(allocation)
                    ArrayCopies = memory.ArrayCopies.Remove copy.Site
                }
            | _ -> failwithf "Unknown published snapshot dependency: %s" dependency

        let boundary =
            if dependency = "borrow" then
                { revision.Emission.Boundary with
                    ByteViews = revision.Emission.Boundary.ByteViews.Remove(nodeId call.Buffer)
                }
            else
                revision.Emission.Boundary

        let changed =
            { revision with
                Emission =
                    { revision.Emission with
                        Memory = revised
                        Boundary = boundary
                    }
            }

        let violations = Fidelity.PSG.Integrity.check changed
        Assert.Contains(violations, fun violation -> violation.Part = part)

        if dependency = "unstated-allocation" then
            Assert.Contains(violations, fun violation -> violation.Part = part && violation.Reason.Contains "a stated allocation")

    [<Fact>]
    member _.``Constructed comparison does not acquire native write admission requirements``() =
        let source =
            (RuntimeSnapshotWriteFixture.source "" "text.Length")
                .Replace("    let _ = Sys.write 1 text.Bytes text.Length\n    0", "    if text = \"é\" then 0 else 1")

        let graph, projection =
            IntrinsicWriteFixture.checkSource RuntimeSnapshotWriteFixture.authority source
            |> IntrinsicWriteFixture.graphAndProjection

        Assert.Empty projection.IntrinsicWrites
        Assert.NotEmpty projection.ByteViews
        Assert.Empty(Fidelity.PSG.Integrity.check (RuntimeSnapshotWriteFixture.publish graph))

    [<Fact>]
    member _.``Dynamic snapshot borrow obligation discharges for valid snapshot and fails when copy extent exceeds independent allocation capacity``() =
        let graph,domain,call = RuntimeSnapshotWriteFixture.dynamicAdmitted ()
        let snapshot = Assert.Single domain.StringBorrowSnapshots
        let copy = Assert.Single domain.StringBorrowCopies
        let allocation = Assert.Single domain.StringBorrowAllocations
        let borrow = domain.IntrinsicProofs |> List.filter (fun proof -> proof.Site=call.Site && proof.Ordinal=1) |> Assert.Single
        let info =
            match graph.Nodes[borrow.Obligation].Kind with
            | SemanticKind.Obligation info -> info
            | _ -> failwith "Missing actual snapshot borrow obligation."
        match Clef.Compiler.Nanopass.ObligationDischarge.discharge [info] with
        | Error reason -> failwithf "Valid snapshot borrow failed design-time discharge: %s" reason
        | Ok receipt ->
            Assert.Equal("sat", (Assert.Single receipt.Premises).Verdict)
            Assert.Equal(2, receipt.NonVacuity.Length)
            Assert.Equal<int option list>([Some 0; Some 1], receipt.NonVacuity |> List.map _.ClauseIndex)
            Assert.Equal<string option list>([Some "(<= 0 snapshot_count)"; Some "(<= snapshot_copy_extent snapshot_allocation_capacity)"], receipt.NonVacuity |> List.map _.Clause)
            for nv in receipt.NonVacuity do
                Assert.Equal("sat", nv.Verdict)
                Assert.Equal<string list>(["snapshot_allocation_capacity"; "snapshot_copy_extent"; "snapshot_count"], nv.ParticipantVariables)
            Assert.Equal("unsat", (Assert.Single receipt.Evidence).Verdict)

        // End-to-end oversized copy where the count/snapshot/copy range is [2..3] while the allocation witness's own settled capacity is independently bound to 2 bytes:
        let undersizedAllocation =
            { allocation with
                MinimumCount = 2I
                MaximumCount = 2I }
        let memoryDomain =
            graph.Edges
            |> List.choose (fun edge -> match edge.Role with EdgeRole.MemoryDomain value -> Some value | _ -> None)
            |> Assert.Single
        let revisedMemoryDomain =
            { memoryDomain with
                Operations =
                    memoryDomain.Operations
                    |> List.map (fun (site, op) ->
                        if site = allocation.Site then site, MemoryWitnessOperation.ArrayAllocation undersizedAllocation
                        else site, op) }
        let edgesWithUndersizedAllocation =
            graph.Edges
            |> List.map (fun edge ->
                match edge.Role with
                | EdgeRole.MemoryDomain _ ->
                    { edge with Role = EdgeRole.MemoryDomain revisedMemoryDomain }
                | EdgeRole.MemoryOperation(MemoryWitnessOperation.ArrayAllocation fact) when fact.Site = allocation.Site ->
                    { edge with Role = EdgeRole.MemoryOperation(MemoryWitnessOperation.ArrayAllocation undersizedAllocation) }
                | _ -> edge)
        let oversizedGraph =
            { graph with Edges = edgesWithUndersizedAllocation }
            |> Clef.Compiler.Nanopass.BoundarySettlement.normalize
            |> Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.prepare
            |> Result.defaultWith (sprintf "%A" >> failwith)
        let oversizedRevision = RuntimeSnapshotWriteFixture.publish oversizedGraph
        Assert.Empty(Fidelity.PSG.Integrity.check oversizedRevision)
        let oversizedDomain =
            oversizedGraph.Edges
            |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryDomain value -> Some value | _ -> None)
            |> Assert.Single
        let oversizedBorrow =
            oversizedDomain.IntrinsicProofs
            |> List.filter (fun proof -> proof.Site = call.Site && proof.Ordinal = 1)
            |> Assert.Single
        let oversizedInfo =
            match oversizedGraph.Nodes[oversizedBorrow.Obligation].Kind with
            | SemanticKind.Obligation ob -> ob
            | _ -> failwith "Missing oversized snapshot borrow obligation."
        Assert.Equal(
            ObligationBody.SnapshotBorrowBound(call.Count, snapshot.Site, copy.Site, allocation.Site, 2I, 3I, bigint allocation.ElementBytes, 2I),
            oversizedInfo.Body)
        match Clef.Compiler.Nanopass.ObligationDischarge.discharge [oversizedInfo] with
        | Ok _ -> failwith "Snapshot borrow whose copy extent exceeds independent allocation capacity was discharged."
        | Error reason ->
            Assert.Equal(sprintf "Obligation '%s' (%s) was not discharged: solver returned 'sat'" oversizedInfo.Id oversizedInfo.Source, reason)

    [<Fact>]
    member _.``Design-time per-clause guard and relevance check refuse tautological clause and ignored participant variables with exact reasons``() =
        let graph,domain,call = RuntimeSnapshotWriteFixture.dynamicAdmitted ()
        let snapshot = Assert.Single domain.StringBorrowSnapshots
        let copy = Assert.Single domain.StringBorrowCopies
        let allocation = Assert.Single domain.StringBorrowAllocations
        let borrow = domain.IntrinsicProofs |> List.filter (fun proof -> proof.Site=call.Site && proof.Ordinal=1) |> Assert.Single
        let info =
            match graph.Nodes[borrow.Obligation].Kind with
            | SemanticKind.Obligation info -> info
            | _ -> failwith "Missing actual snapshot borrow obligation."
        let nodeId = Clef.Compiler.Baker.Ingredients.PublishedFactRows.nodeId
        let baseProjection =
            match Fidelity.PSG.SnapshotBorrowProof.ofBounds (nodeId call.Count) (nodeId snapshot.Site) (nodeId copy.Site) (nodeId allocation.Site) 2I 3I (bigint allocation.ElementBytes) (allocation.MaximumCount * bigint allocation.ElementBytes) with
            | Ok projection -> projection
            | Error reason -> failwith reason
        let countVar = Fidelity.PSG.ResourceProof.Expr.Variable "snapshot_count"
        let copyExtentVar = Fidelity.PSG.ResourceProof.Expr.Variable "snapshot_copy_extent"
        let capacityVar = Fidelity.PSG.ResourceProof.Expr.Variable "snapshot_allocation_capacity"
        let zero = Fidelity.PSG.ResourceProof.Expr.Integer 0I

        // 1. Injected negative fixture: a tautological clause next to a real one
        let tautologicalClauseProjection =
            { baseProjection with
                Conclusion =
                    Fidelity.PSG.ResourceProof.Expr.And
                        [ Fidelity.PSG.ResourceProof.Expr.LessOrEqual(zero, countVar)
                          Fidelity.PSG.ResourceProof.Expr.LessOrEqual(countVar, countVar)
                          Fidelity.PSG.ResourceProof.Expr.LessOrEqual(copyExtentVar, capacityVar) ] }
        let expectedGuardReason =
            sprintf "obligation %s (%s) clause 1 is valid without premises: (<= snapshot_count snapshot_count)" info.Id info.Kind
        let unavailableGuard =
            Clef.Compiler.Nanopass.ObligationDischarge.unavailableWithOverride (fun ob -> if ob.Id = info.Id then Some tautologicalClauseProjection else None) [info]
            |> Assert.Single
        Assert.Equal<string list>([expectedGuardReason], unavailableGuard.MissingPremises)
        match Clef.Compiler.Nanopass.ObligationDischarge.dischargeWithProjectionOverride (fun ob -> if ob.Id = info.Id then Some tautologicalClauseProjection else None) [info] with
        | Ok _ -> failwith "Injected tautological clause next to a real one was discharged."
        | Error reason -> Assert.Equal(expectedGuardReason, reason)

        // 2. Injected negative fixture: a conclusion (or projection) that ignores its published participant variables
        let ignoredParticipantsProjection =
            { baseProjection with
                Conclusion = Fidelity.PSG.ResourceProof.Expr.LessOrEqual(zero, countVar) }
        let expectedRelevanceReason =
            sprintf "obligation %s (%s) conclusion ignores participant variables: snapshot_allocation_capacity, snapshot_copy_extent" info.Id info.Kind
        let unavailableRelevance =
            Clef.Compiler.Nanopass.ObligationDischarge.unavailableWithOverride (fun ob -> if ob.Id = info.Id then Some ignoredParticipantsProjection else None) [info]
            |> Assert.Single
        Assert.Equal<string list>([expectedRelevanceReason], unavailableRelevance.MissingPremises)
        match Clef.Compiler.Nanopass.ObligationDischarge.dischargeWithProjectionOverride (fun ob -> if ob.Id = info.Id then Some ignoredParticipantsProjection else None) [info] with
        | Ok _ -> failwith "Injected conclusion ignoring participant variables was discharged."
        | Error reason -> Assert.Equal(expectedRelevanceReason, reason)

        // 3. Positive fixture: an honest obligation that uses a helper variable in a premise passes
        let publishedBody =
            Fidelity.PSG.ObligationBody.SnapshotBorrowBound(
                nodeId call.Count,
                nodeId snapshot.Site,
                nodeId copy.Site,
                nodeId allocation.Site,
                2I,
                3I,
                bigint allocation.ElementBytes,
                allocation.MaximumCount * bigint allocation.ElementBytes)
        Assert.Equal<(string * string) list>(
            [ "count", "snapshot_count"
              "snapshot", "snapshot_copy_extent"
              "copy", "snapshot_copy_extent"
              "allocation", "snapshot_allocation_capacity"
              "minimum", "snapshot_count"
              "maximum", "snapshot_count" ],
            Fidelity.PSG.ObligationBody.participantRoles publishedBody)
        Assert.Equal<(string * string) list>(
            Fidelity.PSG.ObligationBody.participantRoles publishedBody,
            baseProjection.ParticipantRoles)
        let helperVar = Fidelity.PSG.ResourceProof.Expr.Variable "snapshot_helper"
        let helperProjection =
            { baseProjection with
                Declarations = baseProjection.Declarations @ [ "snapshot_helper", Fidelity.PSG.ResourceProof.Sort.Integer ]
                Premises =
                    Fidelity.PSG.ResourceProof.Expr.And
                        [ baseProjection.Premises
                          Fidelity.PSG.ResourceProof.Expr.Equal(helperVar, countVar)
                          Fidelity.PSG.ResourceProof.Expr.LessOrEqual(zero, helperVar) ] }
        Assert.Contains("snapshot_helper", Fidelity.PSG.ResourceProof.freeVariables helperProjection.Premises)
        Assert.DoesNotContain("snapshot_helper", Fidelity.PSG.ResourceProof.freeVariables helperProjection.Conclusion)
        match Clef.Compiler.Nanopass.ObligationDischarge.dischargeWithProjectionOverride (fun ob -> if ob.Id = info.Id then Some helperProjection else None) [info] with
        | Error reason -> failwithf "Honest obligation using a helper variable in a premise failed discharge: %s" reason
        | Ok receipt ->
            Assert.Equal(2, receipt.NonVacuity.Length)
            for nv in receipt.NonVacuity do
                Assert.Equal<string list>(
                    [ "snapshot_allocation_capacity"; "snapshot_copy_extent"; "snapshot_count" ],
                    nv.ParticipantVariables)
            Assert.Equal("unsat", (Assert.Single receipt.Evidence).Verdict)
        Assert.Equal<string list>(
            [ "snapshot_allocation_capacity"; "snapshot_copy_extent"; "snapshot_count" ],
            Fidelity.PSG.ResourceProof.participantVariables helperProjection)
        Assert.Empty(Fidelity.PSG.ResourceProof.missingParticipantVariables helperProjection)
        Assert.Empty(
            Clef.Compiler.Nanopass.ObligationDischarge.unavailableWithOverride
                (fun ob -> if ob.Id = info.Id then Some helperProjection else None)
                [info])
        let droppedFromPremisesAndConclusionProjection =
            { baseProjection with
                Premises = Fidelity.PSG.ResourceProof.Expr.LessOrEqual(zero, countVar)
                Conclusion = Fidelity.PSG.ResourceProof.Expr.LessOrEqual(zero, countVar) }
        Assert.Equal<string list>(
            [ "snapshot_allocation_capacity"; "snapshot_copy_extent" ],
            Fidelity.PSG.ResourceProof.missingParticipantVariables droppedFromPremisesAndConclusionProjection)

        // 4. Conversion correspondence and structural unit-alignment settlement
        let validConversionModel : Fidelity.PSG.ResourceConversionModel =
            { Declaration = Fidelity.PSG.NodeId 10
              Acquisition = Fidelity.PSG.NodeId 11
              Import = Fidelity.PSG.NodeId 12
              OptionType = Fidelity.PSG.TypeIdentity.Error "test_option"
              HandleType = Fidelity.PSG.TypeIdentity.Error "test_handle"
              Core = Fidelity.PSG.NodeId 13
              PointerBits = 64
              SelectedPointerBits = 64
              HandleBytes = 8
              HandleAlignment = 8
              OptionBytes = 16
              OptionAlignment = 8
              PayloadOffset = 8
              TagBits = 32
              TagBytes = 4
              CaseCount = 2
              NoneCase = 0
              SomeCase = 1
              Arms =
                  [ { NativeNonNull = false; CaseOrdinal = 0; PayloadOrigin = None }
                    { NativeNonNull = true; CaseOrdinal = 1; PayloadOrigin = Some(Fidelity.PSG.NodeId 11) } ] }
        let unitAlignedConversionModel =
            { validConversionModel with
                HandleAlignment = 1
                OptionAlignment = 1
                PayloadOffset = 4
                OptionBytes = 12 }
        let unitAlignedConversionProjection =
            match Fidelity.PSG.ResourceProof.ofConversion unitAlignedConversionModel with
            | Ok projection -> projection
            | Error reason -> failwith reason
        Assert.Empty(Fidelity.PSG.ResourceProof.missingParticipantVariables unitAlignedConversionProjection)
        match Clef.Compiler.Nanopass.ObligationDischarge.dischargeWithProjectionOverride (fun ob -> if ob.Id = info.Id then Some unitAlignedConversionProjection else None) [info] with
        | Error reason -> failwithf "Honest unit-aligned conversion model failed design-time discharge: %s" reason
        | Ok receipt ->
            Assert.Equal(7, receipt.NonVacuity.Length)
            Assert.DoesNotContain(receipt.NonVacuity, fun nv -> nv.Clause |> Option.exists (fun c -> c.Contains "(mod resource_payload_offset"))
            for nv in receipt.NonVacuity do
                Assert.Equal("sat", nv.Verdict)
            Assert.Equal("unsat", (Assert.Single receipt.Evidence).Verdict)
        let vacuousUnitAlignmentProjection =
            { unitAlignedConversionProjection with
                Conclusion =
                    Fidelity.PSG.ResourceProof.Expr.And(
                        Fidelity.PSG.ResourceProof.conjuncts unitAlignedConversionProjection.Conclusion
                        @ [ Fidelity.PSG.ResourceProof.Expr.Equal(
                                Fidelity.PSG.ResourceProof.Expr.Modulo(
                                    Fidelity.PSG.ResourceProof.Expr.Variable "resource_payload_offset",
                                    Fidelity.PSG.ResourceProof.Expr.Integer 1I),
                                Fidelity.PSG.ResourceProof.Expr.Integer 0I) ]) }
        let expectedUnitAlignmentVacuityReason =
            sprintf "obligation %s (%s) clause 7 is valid without premises: (= (mod resource_payload_offset 1) 0)" info.Id info.Kind
        match Clef.Compiler.Nanopass.ObligationDischarge.dischargeWithProjectionOverride (fun ob -> if ob.Id = info.Id then Some vacuousUnitAlignmentProjection else None) [info] with
        | Ok _ -> failwith "Unit-alignment tautological clause (= (mod resource_payload_offset 1) 0) was discharged at design time."
        | Error reason -> Assert.Equal(expectedUnitAlignmentVacuityReason, reason)

        let misalignedConversionModel =
            { validConversionModel with
                PayloadOffset = 4 }
        let misalignedConversionProjection =
            match Fidelity.PSG.ResourceProof.ofConversion misalignedConversionModel with
            | Ok projection -> projection
            | Error reason -> failwith reason
        Assert.Empty(Fidelity.PSG.ResourceProof.missingParticipantVariables misalignedConversionProjection)
        Assert.Empty(
            Clef.Compiler.Nanopass.ObligationDischarge.unavailableWithOverride
                (fun ob -> if ob.Id = info.Id then Some misalignedConversionProjection else None)
                [info])
        match Clef.Compiler.Nanopass.ObligationDischarge.dischargeWithProjectionOverride (fun ob -> if ob.Id = info.Id then Some misalignedConversionProjection else None) [info] with
        | Ok _ -> failwith "Conversion model with misaligned PayloadOffset (4 mod 8 <> 0) was discharged at design time."
        | Error reason ->
            Assert.Equal(sprintf "Obligation '%s' (%s) was not discharged: solver returned 'sat'" info.Id info.Source, reason)

        let validConversionProjection =
            match Fidelity.PSG.ResourceProof.ofConversion validConversionModel with
            | Ok projection -> projection
            | Error reason -> failwith reason
        Assert.Equal<string list>(
            [ "resource_acquisition_origin"
              "resource_case"
              "resource_none_case"
              "resource_nonnull"
              "resource_payload_offset"
              "resource_payload_origin"
              "resource_some_case" ],
            Fidelity.PSG.ResourceProof.participantVariables validConversionProjection)
        Assert.Empty(Fidelity.PSG.ResourceProof.missingParticipantVariables validConversionProjection)
        match Clef.Compiler.Nanopass.ObligationDischarge.dischargeWithProjectionOverride (fun ob -> if ob.Id = info.Id then Some validConversionProjection else None) [info] with
        | Error reason -> failwithf "Honest alignment-8 conversion model failed design-time discharge: %s" reason
        | Ok receipt ->
            Assert.Equal(8, receipt.NonVacuity.Length)
            Assert.Equal(Some "(= (mod resource_payload_offset 8) 0)", receipt.NonVacuity[7].Clause)
            for nv in receipt.NonVacuity do
                Assert.Equal("sat", nv.Verdict)
            Assert.Equal("unsat", (Assert.Single receipt.Evidence).Verdict)

        let mismatchedArmModel =
            { validConversionModel with
                Arms =
                    [ { NativeNonNull = false; CaseOrdinal = 0; PayloadOrigin = None }
                      { NativeNonNull = true; CaseOrdinal = 0; PayloadOrigin = Some(Fidelity.PSG.NodeId 11) } ] }
        let mismatchedConversionProjection =
            match Fidelity.PSG.ResourceProof.ofConversion mismatchedArmModel with
            | Ok projection -> projection
            | Error reason -> failwith reason
        Assert.Empty(
            Clef.Compiler.Nanopass.ObligationDischarge.unavailableWithOverride
                (fun ob -> if ob.Id = info.Id then Some mismatchedConversionProjection else None)
                [info])
        match Clef.Compiler.Nanopass.ObligationDischarge.dischargeWithProjectionOverride (fun ob -> if ob.Id = info.Id then Some mismatchedConversionProjection else None) [info] with
        | Ok _ -> failwith "Conversion model whose arm table disagrees with SomeCase was discharged."
        | Error reason ->
            Assert.Equal(sprintf "Obligation '%s' (%s) was not discharged: solver returned 'sat'" info.Id info.Source, reason)

        // 4b. Resource cleanup with a Release point: excludes Release sites from origin variables and discharges non-vacuously;
        // restoring the release origin variable is caught by the relevance check's own message.
        let makeCleanupModel (convModel: Fidelity.PSG.ResourceConversionModel) : Fidelity.PSG.ResourceCleanupModel =
            { Acquisition = Fidelity.PSG.NodeId 11
              Declaration = Fidelity.PSG.NodeId 10
              Release = Fidelity.PSG.NodeId 14
              Conversion = Fidelity.PSG.NodeId 15
              ConversionModel = convModel
              Entry = 0
              Points =
                  [ { Label = 0; Site = Fidelity.PSG.NodeId 19; Context = []; Port = Fidelity.PSG.EvaluationPort.Entry; Event = None }
                    { Label = 1; Site = Fidelity.PSG.NodeId 19; Context = []; Port = Fidelity.PSG.EvaluationPort.OperandEntry 0; Event = None }
                    { Label = 2; Site = Fidelity.PSG.NodeId 11; Context = [0]; Port = Fidelity.PSG.EvaluationPort.Entry; Event = None }
                    { Label = 3; Site = Fidelity.PSG.NodeId 11; Context = [0]; Port = Fidelity.PSG.EvaluationPort.Exit; Event = Some Fidelity.PSG.ResourceFlowEvent.Acquisition }
                    { Label = 4; Site = Fidelity.PSG.NodeId 19; Context = []; Port = Fidelity.PSG.EvaluationPort.OperandExit 0; Event = None }
                    { Label = 5; Site = Fidelity.PSG.NodeId 19; Context = []; Port = Fidelity.PSG.EvaluationPort.OperandEntry 1; Event = None }
                    { Label = 6; Site = Fidelity.PSG.NodeId 20; Context = [1]; Port = Fidelity.PSG.EvaluationPort.Entry; Event = None }
                    { Label = 7; Site = Fidelity.PSG.NodeId 20; Context = [1]; Port = Fidelity.PSG.EvaluationPort.Exit; Event = Some(Fidelity.PSG.ResourceFlowEvent.Release(Fidelity.PSG.NodeId 11, Fidelity.PSG.NodeId 14)) }
                    { Label = 8; Site = Fidelity.PSG.NodeId 19; Context = []; Port = Fidelity.PSG.EvaluationPort.OperandExit 1; Event = None }
                    { Label = 9; Site = Fidelity.PSG.NodeId 19; Context = []; Port = Fidelity.PSG.EvaluationPort.Exit; Event = None } ]
              Relations =
                  [ { Role = Fidelity.PSG.ResourceEvaluationRole.Root; Ordinal = 0; Sources = [Fidelity.PSG.NodeId 19]; Target = Fidelity.PSG.NodeId 19 }
                    { Role = Fidelity.PSG.ResourceEvaluationRole.Operand Fidelity.PSG.EvaluationAccess.Value; Ordinal = 0; Sources = [Fidelity.PSG.NodeId 19; Fidelity.PSG.NodeId 11]; Target = Fidelity.PSG.NodeId 19 }
                    { Role = Fidelity.PSG.ResourceEvaluationRole.Flow(Fidelity.PSG.EvaluationPort.Entry, Fidelity.PSG.EvaluationPort.OperandEntry 0, Fidelity.PSG.EvaluationTransfer.Continue); Ordinal = 0; Sources = [Fidelity.PSG.NodeId 19]; Target = Fidelity.PSG.NodeId 19 }
                    { Role = Fidelity.PSG.ResourceEvaluationRole.Flow(Fidelity.PSG.EvaluationPort.Entry, Fidelity.PSG.EvaluationPort.Exit, Fidelity.PSG.EvaluationTransfer.Continue); Ordinal = 0; Sources = [Fidelity.PSG.NodeId 11]; Target = Fidelity.PSG.NodeId 11 }
                    { Role = Fidelity.PSG.ResourceEvaluationRole.Flow(Fidelity.PSG.EvaluationPort.OperandExit 0, Fidelity.PSG.EvaluationPort.Exit, Fidelity.PSG.EvaluationTransfer.WhenCase 0); Ordinal = 1; Sources = [Fidelity.PSG.NodeId 19]; Target = Fidelity.PSG.NodeId 19 }
                    { Role = Fidelity.PSG.ResourceEvaluationRole.Flow(Fidelity.PSG.EvaluationPort.OperandExit 0, Fidelity.PSG.EvaluationPort.OperandEntry 1, Fidelity.PSG.EvaluationTransfer.WhenCase 1); Ordinal = 2; Sources = [Fidelity.PSG.NodeId 19]; Target = Fidelity.PSG.NodeId 19 }
                    { Role = Fidelity.PSG.ResourceEvaluationRole.Operand Fidelity.PSG.EvaluationAccess.Value; Ordinal = 1; Sources = [Fidelity.PSG.NodeId 19; Fidelity.PSG.NodeId 20]; Target = Fidelity.PSG.NodeId 19 }
                    { Role = Fidelity.PSG.ResourceEvaluationRole.Flow(Fidelity.PSG.EvaluationPort.Entry, Fidelity.PSG.EvaluationPort.Exit, Fidelity.PSG.EvaluationTransfer.Continue); Ordinal = 0; Sources = [Fidelity.PSG.NodeId 20]; Target = Fidelity.PSG.NodeId 20 }
                    { Role = Fidelity.PSG.ResourceEvaluationRole.Flow(Fidelity.PSG.EvaluationPort.OperandExit 1, Fidelity.PSG.EvaluationPort.Exit, Fidelity.PSG.EvaluationTransfer.Continue); Ordinal = 3; Sources = [Fidelity.PSG.NodeId 19]; Target = Fidelity.PSG.NodeId 19 } ]
              Edges =
                  [ { From = 0; To = 1; Relation = 2; Connection = Fidelity.PSG.ResourceFlowConnection.Local; Transfer = Fidelity.PSG.EvaluationTransfer.Continue }
                    { From = 1; To = 2; Relation = 1; Connection = Fidelity.PSG.ResourceFlowConnection.OperandEntry; Transfer = Fidelity.PSG.EvaluationTransfer.Continue }
                    { From = 2; To = 3; Relation = 3; Connection = Fidelity.PSG.ResourceFlowConnection.Local; Transfer = Fidelity.PSG.EvaluationTransfer.Continue }
                    { From = 3; To = 4; Relation = 1; Connection = Fidelity.PSG.ResourceFlowConnection.OperandExit; Transfer = Fidelity.PSG.EvaluationTransfer.Continue }
                    { From = 4; To = 9; Relation = 4; Connection = Fidelity.PSG.ResourceFlowConnection.Local; Transfer = Fidelity.PSG.EvaluationTransfer.WhenCase 0 }
                    { From = 4; To = 5; Relation = 5; Connection = Fidelity.PSG.ResourceFlowConnection.Local; Transfer = Fidelity.PSG.EvaluationTransfer.WhenCase 1 }
                    { From = 5; To = 6; Relation = 6; Connection = Fidelity.PSG.ResourceFlowConnection.OperandEntry; Transfer = Fidelity.PSG.EvaluationTransfer.Continue }
                    { From = 6; To = 7; Relation = 7; Connection = Fidelity.PSG.ResourceFlowConnection.Local; Transfer = Fidelity.PSG.EvaluationTransfer.Continue }
                    { From = 7; To = 8; Relation = 6; Connection = Fidelity.PSG.ResourceFlowConnection.OperandExit; Transfer = Fidelity.PSG.EvaluationTransfer.Continue }
                    { From = 8; To = 9; Relation = 8; Connection = Fidelity.PSG.ResourceFlowConnection.Local; Transfer = Fidelity.PSG.EvaluationTransfer.Continue } ]
              Cases =
                  [ { Site = Fidelity.PSG.NodeId 19
                      Subject = Fidelity.PSG.NodeId 11
                      Domain = [0; 1]
                      Arms =
                          [ { Ordinal = Some 0; Body = Fidelity.PSG.NodeId 21; BooleanResult = None }
                            { Ordinal = Some 1; Body = Fidelity.PSG.NodeId 20; BooleanResult = None } ] } ]
              LiteralGuards = []
              Exits = [9] }
        let cleanupUnitProjection =
            match Fidelity.PSG.ResourceProof.ofCleanup (makeCleanupModel unitAlignedConversionModel) with
            | Ok projection -> projection
            | Error reason -> failwith reason
        match Clef.Compiler.Nanopass.ObligationDischarge.dischargeWithProjectionOverride (fun ob -> if ob.Id = info.Id then Some cleanupUnitProjection else None) [info] with
        | Error reason -> failwithf "Honest cleanup model with a Release point failed design-time discharge: %s" reason
        | Ok receipt ->
            Assert.Equal(2, receipt.Premises.Length)
            for p in receipt.Premises do
                Assert.Equal("sat", p.Verdict)
            Assert.Equal(28, receipt.NonVacuity.Length)
            for nv in receipt.NonVacuity do
                Assert.Equal("sat", nv.Verdict)
            Assert.Equal("unsat", (Assert.Single receipt.Evidence).Verdict)
        Assert.Empty(Fidelity.PSG.ResourceProof.missingParticipantVariables cleanupUnitProjection)
        Assert.DoesNotContain("resource_origin_20", Fidelity.PSG.ResourceProof.participantVariables cleanupUnitProjection)

        let restoredReleaseOriginProjection =
            { cleanupUnitProjection with
                Declarations = cleanupUnitProjection.Declarations @ [ "resource_origin_20", Fidelity.PSG.ResourceProof.Sort.Integer ]
                ParticipantRoles = cleanupUnitProjection.ParticipantRoles @ [ "origin_20", "resource_origin_20" ]
                Conclusion =
                    Fidelity.PSG.ResourceProof.Expr.And(
                        Fidelity.PSG.ResourceProof.conjuncts cleanupUnitProjection.Conclusion
                        @ [ Fidelity.PSG.ResourceProof.Expr.Implies(
                                Fidelity.PSG.ResourceProof.Expr.Variable "resource_nonnull",
                                Fidelity.PSG.ResourceProof.Expr.Equal(
                                    Fidelity.PSG.ResourceProof.Expr.Variable "resource_origin_20",
                                    Fidelity.PSG.ResourceProof.Expr.Integer 11I)) ]) }
        let expectedReleaseOriginReason =
            sprintf "obligation %s (%s) conclusion ignores participant variables: resource_origin_20" info.Id info.Kind
        let unavailableReleaseOrigin =
            Clef.Compiler.Nanopass.ObligationDischarge.unavailableWithOverride
                (fun ob -> if ob.Id = info.Id then Some restoredReleaseOriginProjection else None)
                [info]
            |> Assert.Single
        Assert.Equal<string list>([expectedReleaseOriginReason], unavailableReleaseOrigin.MissingPremises)
        match Clef.Compiler.Nanopass.ObligationDischarge.dischargeWithProjectionOverride (fun ob -> if ob.Id = info.Id then Some restoredReleaseOriginProjection else None) [info] with
        | Ok _ -> failwith "Cleanup projection with restored unconstrained release origin variable was discharged at design time."
        | Error reason -> Assert.Equal(expectedReleaseOriginReason, reason)

        // 4b (alignment 8). The same cleanup with a Release point over the alignment-8 conversion model discharges
        // non-vacuously with the guarded payload-offset clause, refuses the restored release origin, and refuses a misaligned payload offset.
        let cleanupAlign8Projection =
            match Fidelity.PSG.ResourceProof.ofCleanup (makeCleanupModel validConversionModel) with
            | Ok projection -> projection
            | Error reason -> failwith reason
        match Clef.Compiler.Nanopass.ObligationDischarge.dischargeWithProjectionOverride (fun ob -> if ob.Id = info.Id then Some cleanupAlign8Projection else None) [info] with
        | Error reason -> failwithf "Honest alignment-8 cleanup model with a Release point failed design-time discharge: %s" reason
        | Ok receipt ->
            Assert.Equal(2, receipt.Premises.Length)
            for p in receipt.Premises do
                Assert.Equal("sat", p.Verdict)
            Assert.Equal(29, receipt.NonVacuity.Length)
            Assert.Contains(receipt.NonVacuity, fun nv -> nv.Clause = Some "(= (mod resource_payload_offset 8) 0)")
            for nv in receipt.NonVacuity do
                Assert.Equal("sat", nv.Verdict)
            Assert.Equal("unsat", (Assert.Single receipt.Evidence).Verdict)
        Assert.Empty(Fidelity.PSG.ResourceProof.missingParticipantVariables cleanupAlign8Projection)
        Assert.DoesNotContain("resource_origin_20", Fidelity.PSG.ResourceProof.participantVariables cleanupAlign8Projection)

        let restoredAlign8ReleaseOriginProjection =
            { cleanupAlign8Projection with
                Declarations = cleanupAlign8Projection.Declarations @ [ "resource_origin_20", Fidelity.PSG.ResourceProof.Sort.Integer ]
                ParticipantRoles = cleanupAlign8Projection.ParticipantRoles @ [ "origin_20", "resource_origin_20" ]
                Conclusion =
                    Fidelity.PSG.ResourceProof.Expr.And(
                        Fidelity.PSG.ResourceProof.conjuncts cleanupAlign8Projection.Conclusion
                        @ [ Fidelity.PSG.ResourceProof.Expr.Implies(
                                Fidelity.PSG.ResourceProof.Expr.Variable "resource_nonnull",
                                Fidelity.PSG.ResourceProof.Expr.Equal(
                                    Fidelity.PSG.ResourceProof.Expr.Variable "resource_origin_20",
                                    Fidelity.PSG.ResourceProof.Expr.Integer 11I)) ]) }
        let unavailableAlign8ReleaseOrigin =
            Clef.Compiler.Nanopass.ObligationDischarge.unavailableWithOverride
                (fun ob -> if ob.Id = info.Id then Some restoredAlign8ReleaseOriginProjection else None)
                [info]
            |> Assert.Single
        Assert.Equal<string list>([expectedReleaseOriginReason], unavailableAlign8ReleaseOrigin.MissingPremises)
        match Clef.Compiler.Nanopass.ObligationDischarge.dischargeWithProjectionOverride (fun ob -> if ob.Id = info.Id then Some restoredAlign8ReleaseOriginProjection else None) [info] with
        | Ok _ -> failwith "Alignment-8 cleanup projection with restored unconstrained release origin variable was discharged at design time."
        | Error reason -> Assert.Equal(expectedReleaseOriginReason, reason)

        let misalignedCleanupAlign8Projection =
            match Fidelity.PSG.ResourceProof.ofCleanup (makeCleanupModel { validConversionModel with PayloadOffset = 4 }) with
            | Ok projection -> projection
            | Error reason -> failwith reason
        match Clef.Compiler.Nanopass.ObligationDischarge.dischargeWithProjectionOverride (fun ob -> if ob.Id = info.Id then Some misalignedCleanupAlign8Projection else None) [info] with
        | Ok _ -> failwith "Alignment-8 cleanup model with misaligned PayloadOffset (4 mod 8 <> 0) was discharged at design time."
        | Error reason ->
            Assert.Equal(sprintf "Obligation '%s' (%s) was not discharged: solver returned 'sat'" info.Id info.Source, reason)

        // 5. Foreign-result totality and coverage over symbolic hypotheses: per-clause guard over all Conclusion clauses
        let makeForeignObligation id lower upper (args: (int * ValueRange) list) resultRange destination abiRange : ObligationInfo =
            let hypothesis : ForeignResultHypothesis =
                { Quote = NodeId 300
                  Declaration = NodeId 301
                  Identity = "foreign:test:hypothesis"
                  Version = "1"
                  Source = "foreign.clef:1:1"
                  Lower = lower
                  Upper = upper }
            let application : ForeignResultApplication =
                { Declaration = NodeId 301
                  Call = NodeId 302
                  Context = []
                  Hypothesis = Some hypothesis
                  Arguments =
                      args
                      |> List.map (fun (idx, enc) ->
                          { Index = idx
                            Node = NodeId (310 + idx)
                            Enclosure = enc } : ForeignResultArgument) }
            let model : ForeignResultCoverageModel =
                { Application = application
                  Role = ForeignResultProofRole.LogicalCoverage
                  ResultRange = resultRange
                  Destination = destination
                  DestinationDeclaration = Some (NodeId 303)
                  Abi = Some (NodeId 304)
                  AbiRange = abiRange
                  AbiIdentity = Some "abi:test"
                  DestinationIdentity = Some "dest:test" }
            { Id = id
              Kind = "foreign-result-coverage"
              Logic = "QF_LIA"
              Statement = "foreign result coverage obligation"
              Source = "foreign.clef:1:1"
              Refs = []
              Body = ObligationBody.ForeignResultCoverage model }

        // Codex's constant-bounds [0,1] vs ABI [0,10] case: modelled over symbolic hypotheses so totality and coverage are non-vacuous
        let codexConstObligation =
            makeForeignObligation
                "foreign_const_bounds"
                (ForeignResultBound.Constant 0I)
                (ForeignResultBound.Constant 1I)
                []
                (ValueRange.Bounded(0I, 10I))
                (ValueRange.Bounded(0I, 10I))
                (ValueRange.Bounded(0I, 10I))
        let codexProjection =
            match
                Fidelity.PSG.ForeignResultCoverage.project
                    (Fidelity.PSG.ForeignResultBound.Constant 0I)
                    (Fidelity.PSG.ForeignResultBound.Constant 1I)
                    []
                    (Fidelity.PSG.ValueRange.Bounded(0I, 10I))
                    (Fidelity.PSG.ValueRange.Bounded(0I, 10I))
                    (Fidelity.PSG.ValueRange.Bounded(0I, 10I))
            with
            | Ok projection -> projection
            | Error reason -> failwith reason
        Assert.Empty(Fidelity.PSG.ForeignResultCoverage.missingParticipantVariables codexProjection)
        Assert.Equal(7, (Fidelity.PSG.ForeignResultCoverage.anchoredNonVacuityQueries "foreign_const_bounds" codexProjection).Length)
        match Clef.Compiler.Nanopass.ObligationDischarge.discharge [codexConstObligation] with
        | Error reason -> failwithf "Honest constant-bounds foreign coverage [0,1] within ABI [0,10] failed discharge: %s" reason
        | Ok receipt ->
            Assert.Single receipt.Premises |> ignore
            Assert.Equal("sat", (Assert.Single receipt.Premises).Verdict)
            Assert.Equal(7, receipt.NonVacuity.Length)
            for nv in receipt.NonVacuity do
                Assert.Equal("psg-nonvacuity", nv.Stage)
                Assert.Equal("sat", nv.Verdict)
            Assert.Equal("unsat", (Assert.Single receipt.Evidence).Verdict)

        // Negative control 5a: literal tautology in Totality is caught by the per-clause Conclusion guard
        let vacuousTotalityProjection =
            let tautology =
                Fidelity.PSG.ForeignResultCoverage.Predicate.LessOrEqual(
                    Fidelity.PSG.ForeignResultCoverage.Term.Constant 0I,
                    Fidelity.PSG.ForeignResultCoverage.Term.Constant 1I)
            { codexProjection with
                Totality = Fidelity.PSG.ForeignResultCoverage.Predicate.And [ tautology; codexProjection.Totality ]
                Conclusion =
                    Fidelity.PSG.ForeignResultCoverage.Predicate.And
                        [ tautology; codexProjection.Totality; codexProjection.Claim ] }
        match Clef.Compiler.Nanopass.ObligationDischarge.checkForeignNonVacuity codexConstObligation vacuousTotalityProjection with
        | Ok _ -> failwith "Vacuous totality clause (<= 0 1) in ForeignResultCoverage was accepted."
        | Error reason ->
            Assert.Equal("obligation foreign_const_bounds (foreign-result-coverage) clause 0 is valid without premises: (<= 0 1)", reason)

        // Negative control 5b: published coverage facts disagree (constant bounds [0,10] exceed narrower destination [0,5])
        let narrowDestObligation =
            makeForeignObligation
                "foreign_narrow_dest"
                (ForeignResultBound.Constant 0I)
                (ForeignResultBound.Constant 10I)
                []
                (ValueRange.Bounded(0I, 10I))
                (ValueRange.Bounded(0I, 5I))
                (ValueRange.Bounded(0I, 10I))
        match Clef.Compiler.Nanopass.ObligationDischarge.discharge [narrowDestObligation] with
        | Ok _ -> failwith "Foreign result coverage exceeding destination bounds was discharged."
        | Error reason ->
            Assert.Equal("Obligation 'foreign_narrow_dest' (foreign.clef:1:1) was not discharged: solver returned 'sat'", reason)

        // Negative control 5c: universal argument-tuple totality fails on one tuple in D (lower=1, upper=arg_0 with arg_0 in [0,2])
        let partialTupleObligation =
            makeForeignObligation
                "foreign_partial_tuple"
                (ForeignResultBound.Constant 1I)
                (ForeignResultBound.Argument 0)
                [ 0, ValueRange.Bounded(0I, 2I) ]
                (ValueRange.Bounded(1I, 2I))
                (ValueRange.Bounded(1I, 2I))
                (ValueRange.Bounded(0I, 10I))
        match Clef.Compiler.Nanopass.ObligationDischarge.discharge [partialTupleObligation] with
        | Ok _ -> failwith "Foreign result coverage with partial-tuple totality failure was discharged."
        | Error reason ->
            Assert.Equal("Obligation 'foreign_partial_tuple' (foreign.clef:1:1) was not discharged: solver returned 'sat'", reason)
