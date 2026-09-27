namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module BoundarySource = Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryEmission
module BoundaryDeclarations = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
module BoundaryWitness = Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission

module private BoundaryEmissionFixture =
    let vocabulary = """module BoundaryFixture
type Signedness = Signed | Unsigned
type TypeRef = Integer of Signedness * int | Bool | Pointer of int | Void
type PassBy = Value | Reference
type CallConv = | CDecl
type Transfer = | Borrowed
type ParameterInfo = { Name: string; Type: TypeRef; PassBy: PassBy }
type FunctionDescriptor = { CName: string; Parameters: ParameterInfo array; ReturnType: TypeRef; CallingConvention: CallConv; OwnershipTransfer: Transfer }
"""

    let descriptor = """
let combineDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "combine"
    Parameters = [| { Name = "left"; Type = Integer (Signed, 32); PassBy = Value }; { Name = "right"; Type = Integer (Signed, 32); PassBy = Value } |]
    ReturnType = Integer (Signed, 32); CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
"""

    let declaration = """
[<FidelityExtern("c", "combine")>]
let combine (left: int) (right: int) : int = NativeDefault.zeroed ()
"""

    let entry = """
[<EntryPoint>]
let main _ = combine 11 7
"""

    let booleanDeclaration = """
[<FidelityExtern("c", "toggle")>]
let toggle (value: bool) : bool = NativeDefault.zeroed ()
let toggleDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "toggle"; Parameters = [| { Name = "value"; Type = Bool; PassBy = Value } |]
    ReturnType = Bool; CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
"""

    let booleanEntry = """
[<EntryPoint>]
let main _ = if toggle true then 0 else 1
"""

    let platform : PlatformContext =
        let signed: NumericRepresentation =
            { Name = "int32"; Capability = "native"; Family = "int"; Bits = 32
              MinMagnitude = "-2147483648"; MaxMagnitude = "2147483647"; Boundary = "wrap" }
        let unsigned: NumericRepresentation =
            { Name = "uint32"; Capability = "native"; Family = "uint"; Bits = 32
              MinMagnitude = "0"; MaxMagnitude = "4294967295"; Boundary = "wrap" }
        { PlatformId = "boundary-emission-test"
          Dimensions = Map.ofList ["Pointer", 64; "Register", 32]
          Representations = Map.ofList [signed.Name, signed; unsigned.Name, unsigned]
          EndpointReturns = Map.empty; PlatformLibraryPath = None; PlatformDescription = None
          PlatformArchitecture = None; PlatformOS = None; PlatformSourcePaths = Set.empty
          Predicates = Map.empty; FreestandingStartup = None; SubstrateKind = None
          RuntimeModel = Some RuntimeModel.Libc; AvailableMemorySpaces = []; DefaultMemorySpace = None
          ClockFrequencyMhz = None; NsPerWeightUnit = None }

    let authority (context: PlatformContext) =
        let widths = context.Dimensions |> Map.toList |> List.map (fun (name, bits) ->
            sprintf "{ Name = %A; Bits = %d }" name bits) |> String.concat "; "
        let representations = context.Representations.Values |> Seq.map (fun representation ->
            sprintf "{ Name = %A; Capability = %A; Family = %A; Bits = %d; MinMagnitude = %A; MaxMagnitude = %A; Boundary = %A }"
                representation.Name representation.Capability representation.Family representation.Bits
                representation.MinMagnitude representation.MaxMagnitude representation.Boundary) |> String.concat "; "
        let declarations = """module BoundaryAuthority
type WidthDeclaration = { Name: string; Bits: int }
type Representation = { Name: string; Capability: string; Family: string; Bits: int; MinMagnitude: string; MaxMagnitude: string; Boundary: string }
type TargetCore = { Runtime: string; Widths: WidthDeclaration array; Representations: Representation array }
type PlatformDescription = { Id: string; Core: TargetCore option }
"""
        declarations + sprintf "let description = { Id = %A; Core = Some { Runtime = \"libc\"; Widths = [| %s |]; Representations = [| %s |] } }\n"
                           context.PlatformId widths representations

    let check context body =
        let parse source path =
            match parseStringWithDefaults source path with
            | ParseSuccess input -> input
            | ParseError errors -> failwithf "Expected parsed boundary source: %A" errors
        let input = parse (vocabulary + body) "boundary-emission.clef"
        match context with
        | None -> checkParsedInputsWithPlatform [input] None
        | Some context ->
            let authority = parse (authority context) "boundary-authority.clef"
            let selected =
                { context with PlatformDescription = Some "BoundaryAuthority.description"
                               PlatformSourcePaths = Set.singleton (System.IO.Path.GetFullPath "boundary-authority.clef") }
            checkParsedInputsWithPlatform [authority; input] (Some selected)

    let checkedGraph body =
        let result = check (Some platform) body
        DimensionalCases.noErrors result
        result.Graph

    let scalar () = checkedGraph (declaration + descriptor + entry)

    let project graph =
        match BoundarySource.project graph with
        | Ok projection -> projection
        | Error failures -> failwithf "Source boundary publication failed: %A" failures

    let rejected (graph: SemanticGraph) =
        match BoundarySource.project graph with
        | Ok projection -> failwithf "Invalid boundary was admitted: %A" projection
        | Error failures ->
            Assert.NotEmpty failures
            Assert.Contains(failures, fun failure -> failure.Occurrence.IsSome && not failure.Participants.IsEmpty)
            failures

    let binding name (graph: SemanticGraph) =
        graph.Nodes.Values
        |> Seq.filter (fun node ->
            match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
        |> Assert.Single

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "BoundaryEmission")>]
type BoundaryEmissionCases() =
    [<Fact>]
    member _.``Scalar publication preserves descriptor identity module scope and argument order``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let call = Assert.Single projection.Calls.Values
        let binding = BoundaryEmissionFixture.binding "combine" graph
        let descriptor = Assert.Single (BoundaryDeclarations.readDescriptors graph).Functions
        let parameters, body = BoundaryDeclarations.lambdaOfBinding graph binding.Id |> Option.get
        let scope = binding.Parent |> Option.get
        let site = graph.Nodes[call.Site]
        let callee, actuals =
            match site.Kind with
            | SemanticKind.Application(callee, actuals) -> callee, actuals
            | other -> failwithf "Boundary call lost its source application: %A" other
        Assert.Equal(descriptor.Node, imported.Identity)
        Assert.Equal(binding.Id, imported.Binding)
        Assert.Equal(scope, imported.Scope)
        Assert.Equal<Set<NodeId>>(Set.singleton binding.Id, projection.DeclarationLeaves)
        for participant in List.tail imported.DeclarationPath @ (parameters |> List.map (fun (_, _, formal) -> formal)) @ [body] do
            Assert.Contains(participant, projection.DeclarationOnly)
        Assert.DoesNotContain(binding.Id, projection.DeclarationOnly)
        Assert.Empty(Set.intersect projection.DeclarationOnly (Set.ofList (call.Site :: callee :: actuals)))
        Assert.Equal("c", imported.Library)
        Assert.Equal("combine", imported.Symbol)
        Assert.Equal("CDecl", imported.CallingConvention)
        Assert.Equal<NodeId list>([imported.Identity], projection.ByScope[scope])
        Assert.Equal<(NodeId * BoundaryScalar) list>(
            parameters |> List.map (fun (_, _, formal) -> formal, BoundaryScalar.Integer(32, true)), imported.Parameters)
        Assert.Equal(Some(BoundaryScalar.Integer(32, true)), imported.Result)
        Assert.Equal(imported.Identity, call.Import)
        Assert.Equal(callee, call.Callee)
        Assert.Equal<NodeId list>(actuals, call.Arguments |> List.map _.Actual)
        Assert.Equal<NodeId list>(parameters |> List.map (fun (_, _, formal) -> formal), call.Arguments |> List.map _.Formal)
        Assert.All(call.Arguments, fun argument -> Assert.Equal(BoundaryScalar.Integer(32, true), argument.Abi))
        let omitted =
            graph.Codata.Value.OrdinaryDemand.Parameters.TryFind (List.last imported.DeclarationPath)
            |> Option.defaultValue Set.empty
        for argument in call.Arguments do
            Assert.DoesNotContain(argument.Actual, graph.Codata.Value.OrdinaryDemand.DeferredOnly)
            Assert.DoesNotContain(argument.Formal, omitted)
        Assert.Empty call.ErasedUnitArguments
        Assert.Equal(imported.Result, call.Result)
        let domainRow = graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.BoundaryDomain _ -> true | _ -> false) |> Assert.Single
        Assert.Equal<Set<NodeId>>(
            Set.add domainRow.Target (Set.union (imported.DeclarationFacts |> Map.keys |> Set.ofSeq)
                (Set.ofList (scope :: body :: (BoundaryEmissionFixture.binding "combineDescriptor" graph).Id ::
                             (parameters |> List.map (fun (_, _, formal) -> formal)) @ imported.DeclarationPath))),
            imported.Participants)
        Assert.Equal(binding.Id, List.head imported.DeclarationPath)
        match graph.Nodes[List.last imported.DeclarationPath].Kind with
        | SemanticKind.Lambda(formals, declaredBody, _, _, _) ->
            Assert.Equal<(string * NativeType * NodeId) list>(parameters, formals)
            Assert.Equal(body, declaredBody)
        | other -> failwithf "The admitted declaration path lost its source lambda: %A" other
        Assert.Equal<Set<NodeId>>(
            Set.union imported.Participants (Set.ofList (call.Site :: callee :: actuals)), call.Participants)
        let sourceMeets = graph.Codata.Value.Meets.TryFind call.Site |> Option.defaultValue []
        for argument in call.Arguments do
            Assert.Equal<Meet option>(sourceMeets |> List.tryFind (fun meet -> meet.Operand = argument.Actual), argument.Adaptation)
        Assert.Equal<Meet option>(sourceMeets |> List.tryFind (fun meet -> meet.Operand = call.Site), call.ResultAdaptation)
        for participant in [imported.Identity; binding.Id; scope] do
            Assert.Contains(participant, imported.Participants)
            Assert.Contains(participant, call.Participants)
        for participant in call.Site :: callee :: actuals @ (parameters |> List.map (fun (_, _, formal) -> formal)) do
            Assert.Contains(participant, call.Participants)
        let published =
            match BoundaryWitness.tryBoundary graph with
            | Ok published -> published
            | Error reason -> failwith reason
        Assert.Equal<BoundaryEmissionProjection>(projection, published)

    [<Fact>]
    member _.``Unit domain is erased explicitly and void result has no scalar ABI``() =
        let graph = BoundaryEmissionFixture.checkedGraph """
[<FidelityExtern("c", "tick")>]
let tick () : unit = NativeDefault.zeroed ()
let tickDescriptor: Expr<FunctionDescriptor> = <@ {
    CName = "tick"; Parameters = [||]; ReturnType = Void
    CallingConvention = CDecl; OwnershipTransfer = Borrowed } @>
[<EntryPoint>]
let main _ =
    tick ()
    0
"""
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let call = Assert.Single projection.Calls.Values
        let actuals =
            match graph.Nodes[call.Site].Kind with
            | SemanticKind.Application(_, actuals) -> actuals
            | other -> failwithf "Expected unit application, got %A" other
        Assert.Empty imported.Parameters
        Assert.Empty call.Arguments
        Assert.Equal<NodeId list>(actuals, call.ErasedUnitArguments)
        Assert.Single call.ErasedUnitArguments |> ignore
        Assert.True imported.Result.IsNone
        Assert.True call.Result.IsNone

    [<Fact>]
    member _.``Boolean descriptor retains the boolean boundary universe``() =
        let graph = BoundaryEmissionFixture.checkedGraph (BoundaryEmissionFixture.booleanDeclaration + BoundaryEmissionFixture.booleanEntry)
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let call = Assert.Single projection.Calls.Values
        Assert.Equal(BoundaryScalar.Boolean, snd (Assert.Single imported.Parameters))
        Assert.Equal(Some BoundaryScalar.Boolean, imported.Result)
        Assert.Equal(BoundaryScalar.Boolean, (Assert.Single call.Arguments).Abi)
        Assert.True (Assert.Single call.Arguments).Adaptation.IsNone

    [<Fact>]
    member _.``Foreign alias rewrite retains its exact import call and callable origin``() =
        let graph = BoundaryEmissionFixture.checkedGraph
                        (BoundaryEmissionFixture.booleanDeclaration + "\nlet alias = toggle\n" +
                         BoundaryEmissionFixture.booleanEntry.Replace("toggle true", "alias true"))
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let call = Assert.Single projection.Calls.Values
        let declaration = BoundaryEmissionFixture.binding "toggle" graph
        let alias = BoundaryEmissionFixture.binding "alias" graph
        Assert.Equal(declaration.Id, imported.Binding)
        Assert.Equal(imported.Identity, call.Import)
        Assert.Contains(call.Callee, call.Participants)
        Assert.Contains(declaration.Id, call.Participants)
        match graph.Nodes[call.Callee].Kind with
        | SemanticKind.VarRef("toggle", Some binding) -> Assert.Equal(declaration.Id, binding)
        | other -> failwithf "The rewritten foreign call lost its exact declaration reference: %A" other
        // Baker reifies the value-position alias through a capture-free
        // wrapper. The retained origin belongs to that rewrite; the boundary
        // call's current direct callee belongs to the original declaration.
        let origin = graph.Edges |> List.filter (fun edge ->
            edge.Role = EdgeRole.CallableReferenceOrigin &&
            (match edge.Sources with [source; _] -> source = alias.Id | _ -> false)) |> Assert.Single
        let implementation = List.item 1 origin.Sources
        match graph.Nodes[origin.Target].Kind with
        | SemanticKind.VarRef("alias", Some target) -> Assert.Equal(implementation, target)
        | other -> failwithf "The alias rewrite lost its exact callable reference: %A" other
        let wrapperParameters, wrapperBody = BoundaryDeclarations.lambdaOfBinding graph implementation |> Option.get
        Assert.Equal(call.Site, wrapperBody)
        let wrapperLambda = Assert.Single graph.Nodes[implementation].Children
        let omitted = graph.Codata.Value.OrdinaryDemand.Parameters.TryFind wrapperLambda |> Option.defaultValue Set.empty
        for _, _, formal in wrapperParameters do Assert.DoesNotContain(formal, omitted)

    [<Theory>]
    [<InlineData("missing")>]
    [<InlineData("duplicate")>]
    [<InlineData("symbol-mismatch")>]
    [<InlineData("pointer")>]
    member _.``Incomplete ambiguous mismatched and unsupported declarations fail at source`` defect =
        let descriptor = BoundaryEmissionFixture.descriptor
        let revised =
            match defect with
            | "missing" -> ""
            | "duplicate" -> descriptor + descriptor
            | "symbol-mismatch" -> descriptor.Replace("CName = \"combine\"", "CName = \"other\"")
            | "pointer" -> descriptor.Replace("Type = Integer (Signed, 32)", "Type = Pointer 64")
            | _ -> failwithf "Unknown boundary defect: %s" defect
        let result = BoundaryEmissionFixture.check (Some BoundaryEmissionFixture.platform)
                         (BoundaryEmissionFixture.declaration + revised + BoundaryEmissionFixture.entry)
        let binding = BoundaryEmissionFixture.binding "combine" result.Graph
        let failures = BoundaryEmissionFixture.rejected result.Graph
        Assert.Contains(failures, fun failure -> failure.Participants.Contains binding.Id)

    [<Fact>]
    member _.``Explicit libc runtime remains authoritative when startup metadata exists``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let context = { graph.Platform.Value with FreestandingStartup = Some FreestandingStartup.defaultLinux_x86_64 }
        let settled = Clef.Compiler.Nanopass.BoundarySettlement.normalize { graph with Platform = Some context }
        let projection = BoundaryEmissionFixture.project settled
        Assert.Single projection.Imports |> ignore
        Assert.Single projection.Calls |> ignore

    [<Theory>]
    [<InlineData("bare")>]
    [<InlineData("freestanding")>]
    [<InlineData("undeclared")>]
    [<InlineData("no-target")>]
    member _.``Reachable C calls require explicit libc runtime authority`` runtime =
        let graph = BoundaryEmissionFixture.scalar ()
        let selected =
            match runtime with
            | "bare" -> Some { graph.Platform.Value with RuntimeModel = Some RuntimeModel.Bare }
            | "freestanding" -> Some { graph.Platform.Value with RuntimeModel = Some RuntimeModel.Freestanding }
            | "undeclared" -> Some { graph.Platform.Value with RuntimeModel = None }
            | "no-target" -> None
            | _ -> failwithf "Unknown runtime: %s" runtime
        let changed =
            if runtime = "undeclared" then
                let core = (BoundaryDeclarations.resolve graph |> Option.get).Core.Value
                let _, fields = BoundaryDeclarations.recordOf graph core.Node |> Option.get
                let runtimeId = fields |> List.find (fst >> (=) "Runtime") |> snd
                let declared = BoundaryDeclarations.valueOf graph runtimeId |> Option.get
                { graph with Platform = selected
                             Nodes = graph.Nodes.Add(declared.Id, { declared with Kind = SemanticKind.Literal (NativeLiteral.String "") }) }
            else { graph with Platform = selected }
        BoundaryEmissionFixture.rejected changed |> ignore
        let settled = Clef.Compiler.Nanopass.BoundarySettlement.normalize changed
        let failures = BoundaryEmissionFixture.rejected settled
        if runtime = "bare" || runtime = "freestanding" then
            Assert.Contains(failures, fun failure -> failure.Reason.Contains "project consistency")

    [<Fact>]
    member _.``Target free unreachable declarations project an empty boundary without witness authority``() =
        let result = BoundaryEmissionFixture.check None
                         (BoundaryEmissionFixture.declaration + BoundaryEmissionFixture.descriptor + "\n[<EntryPoint>]\nlet main _ = 0\n")
        DimensionalCases.noErrors result
        let projection = BoundaryEmissionFixture.project result.Graph
        Assert.Empty projection.Imports
        Assert.Empty projection.ByScope
        Assert.Empty projection.Calls
        Assert.Empty projection.DeclarationLeaves
        Assert.Empty projection.DeclarationOnly
        // Target-free checking has not committed every witness domain. Its
        // empty boundary projection does not grant complete witness authority.
        Assert.True(BoundaryWitness.tryBoundary result.Graph |> Result.isError)

    [<Fact>]
    member _.``Changed actual order retracts the published call contract``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let projection = BoundaryEmissionFixture.project graph
        let call = Assert.Single projection.Calls.Values
        let site = graph.Nodes[call.Site]
        let revised =
            match site.Kind with
            | SemanticKind.Application(callee, actuals) ->
                { site with Kind = SemanticKind.Application(callee, List.rev actuals) }
            | other -> failwithf "Expected boundary application, got %A" other
        let changed = { graph with Nodes = graph.Nodes.Add(site.Id, revised) }
        Assert.True(BoundaryWitness.admit changed |> Result.isError)
        BoundaryEmissionFixture.rejected changed |> ignore

    [<Fact>]
    member _.``Boundary recipe records ordered relations actual range obligations and rewrite evidence``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let call = Assert.Single (BoundaryEmissionFixture.project graph).Calls.Values
        let declarationRows = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryDeclaration value -> Some value | _ -> None)
        Assert.Single declarationRows |> ignore
        let operands = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryOperand value -> Some (edge.Ordinal, value) | _ -> None) |> List.sortBy fst
        Assert.Equal<BoundaryOperand list>(call.Arguments, operands |> List.map snd)
        let coverages = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryCoverage value -> Some value | _ -> None)
        Assert.Equal(call.Arguments.Length + 1, coverages.Length)
        for coverage in coverages do
            Assert.Contains(graph.Edges, fun edge -> edge.Target = coverage.Obligation && edge.Role = EdgeRole.Constrains)
            Assert.Contains(graph.Edges, fun edge -> edge.Target = coverage.Obligation && edge.Role = EdgeRole.EnrichedWith)
            Assert.Contains(graph.Edges, fun edge -> edge.Target = call.Site && edge.Ordinal = coverage.Ordinal && edge.Role = EdgeRole.BoundaryProof BoundaryProofOutcome.Proven)
            match graph.Nodes[coverage.Obligation].Kind with
            | SemanticKind.Obligation info -> Assert.Equal("boundary-range-coverage", info.Kind)
            | other -> failwithf "Expected a real range obligation, got %A" other

    [<Theory>]
    [<InlineData("missing-proof")>]
    [<InlineData("refuted-proof")>]
    [<InlineData("missing-call")>]
    [<InlineData("duplicate-operand")>]
    [<InlineData("missing-rewrite")>]
    member _.``Publication validates complete source rows and cannot create or repair evidence`` defect =
        let graph = BoundaryEmissionFixture.scalar ()
        let edges =
            match defect with
            | "missing-proof" -> graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.BoundaryProof _ -> false | _ -> true)
            | "refuted-proof" -> graph.Edges |> List.map (fun edge -> match edge.Role with EdgeRole.BoundaryProof _ -> { edge with Role = EdgeRole.BoundaryProof BoundaryProofOutcome.Refuted } | _ -> edge)
            | "missing-call" -> graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.BoundaryCall _ -> false | _ -> true)
            | "duplicate-operand" ->
                (graph.Edges |> List.find (fun edge -> match edge.Role with EdgeRole.BoundaryOperand _ -> true | _ -> false)) :: graph.Edges
            | "missing-rewrite" -> graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.EnrichedWith)
            | _ -> failwith "Unknown relation defect"
        BoundaryEmissionFixture.rejected { graph with Edges = edges } |> ignore

    [<Fact>]
    member _.``Boundary normalization retracts stale order and retains repeated actual occurrences``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let call = Assert.Single (BoundaryEmissionFixture.project graph).Calls.Values
        let site = graph.Nodes[call.Site]
        let repeated = [call.Arguments.Head.Actual; call.Arguments.Head.Actual]
        let changedSite = { site with Kind = SemanticKind.Application(call.Callee, repeated); Children = call.Callee :: repeated }
        let changed = { graph with Nodes = graph.Nodes.Add(site.Id, changedSite) }
        BoundaryEmissionFixture.rejected changed |> ignore
        let settled = Clef.Compiler.Nanopass.BoundarySettlement.normalize changed
        let revised = Assert.Single (BoundaryEmissionFixture.project settled).Calls.Values
        Assert.Equal<NodeId list>(repeated, revised.Arguments |> List.map _.Actual)
        let row = settled.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.BoundaryCall _ -> true | _ -> false) |> Assert.Single
        Assert.Equal(2, row.Sources |> List.take (2 + repeated.Length) |> List.filter ((=) repeated.Head) |> List.length)
        Assert.Single(settled.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.BoundaryDomain _ -> true | _ -> false)) |> ignore

    [<Fact>]
    member _.``Refuted range coverage remains an obligation and prevents publication``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let call = Assert.Single (BoundaryEmissionFixture.project graph).Calls.Values
        let actual = graph.Nodes[call.Arguments.Head.Actual]
        let changed = { graph with Nodes = graph.Nodes.Add(actual.Id, { actual with ValueRange = Some (ValueRange.Bounded(0I, 2147483648I)) }) }
        let settled = Clef.Compiler.Nanopass.BoundarySettlement.normalize changed
        BoundaryEmissionFixture.rejected settled |> ignore
        Assert.Contains(settled.Edges, fun edge -> edge.Role = EdgeRole.BoundaryProof BoundaryProofOutcome.Refuted)
        Assert.Contains(settled.Nodes.Values, fun node ->
            match node.Kind with
            | SemanticKind.Obligation info -> info.Body = ObligationBody.IntegerRepresentationCoverage(0I, 2147483648I, -2147483648I, 2147483647I)
            | _ -> false)

    [<Fact>]
    member _.``Resolved source runtime remains authoritative without a project runtime claim``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let context = { graph.Platform.Value with RuntimeModel = None }
        let settled = Clef.Compiler.Nanopass.BoundarySettlement.normalize { graph with Platform = Some context }
        let projection = BoundaryEmissionFixture.project settled
        Assert.Single projection.Imports |> ignore
        Assert.Equal<Set<string>>(Set.singleton "c", projection.Links)

    [<Theory>]
    [<InlineData("non-tuple-payload")>]
    [<InlineData("unrepresentable-width")>]
    member _.``One typed TypeRef reader rejects malformed shape and unrepresentable width`` defect =
        let graph = BoundaryEmissionFixture.scalar ()
        let imported = Assert.Single (BoundaryEmissionFixture.project graph).Imports.Values
        let _, fields = BoundaryDeclarations.recordOf graph imported.Identity |> Option.get
        let typeId = fields |> List.find (fst >> (=) "ReturnType") |> snd
        Assert.Equal(Ok (BoundaryDeclarations.DeclaredTypeRef.Scalar (BoundaryScalar.Integer(32, true))), BoundaryDeclarations.readTypeRef graph typeId)
        let _, _, payload = BoundaryDeclarations.caseOf graph typeId |> Option.get
        let pair = BoundaryDeclarations.valueOf graph payload.Value |> Option.get
        let sign, bits = match pair.Kind with SemanticKind.TupleExpr [sign; bits] -> sign, bits | other -> failwithf "Expected TypeRef tuple: %A" other
        let revised =
            match defect with
            | "non-tuple-payload" -> { pair with Kind = SemanticKind.Application(sign, [bits]); Children = [sign; bits] }
            | "unrepresentable-width" ->
                let width = graph.Nodes[bits]
                match width.Kind with
                | SemanticKind.Literal (NativeLiteral.Int(_, kind)) -> { width with Kind = SemanticKind.Literal (NativeLiteral.Int(int64 System.Int32.MaxValue + 1L, kind)) }
                | other -> failwithf "Expected literal TypeRef width: %A" other
            | _ -> failwith "Unknown TypeRef defect"
        let changed = { graph with Nodes = graph.Nodes.Add(revised.Id, revised) }
        Assert.True(BoundaryDeclarations.readTypeRef changed typeId |> Result.isError)
        Assert.NotEmpty((BoundaryDeclarations.readDescriptors changed).Findings)

    [<Theory>]
    [<InlineData("extern")>]
    [<InlineData("descriptor")>]
    member _.``Deleting a declared module member retracts the import owner contract`` memberRole =
        let graph = BoundaryEmissionFixture.scalar ()
        let imported = Assert.Single (BoundaryEmissionFixture.project graph).Imports.Values
        let scope = graph.Nodes[imported.Scope]
        let memberId =
            match memberRole with
            | "extern" -> imported.Binding
            | "descriptor" -> (BoundaryEmissionFixture.binding "combineDescriptor" graph).Id
            | _ -> failwithf "Unknown boundary module member role: %s" memberRole
        let changedScope =
            match scope.Kind with
            | SemanticKind.ModuleDef(name, members) ->
                Assert.Contains(memberId, members)
                { scope with Kind = SemanticKind.ModuleDef(name, members |> List.filter ((<>) memberId)) }
            | other -> failwithf "Expected admitted module owner, got %A" other
        let changed = { graph with Nodes = graph.Nodes.Add(scope.Id, changedScope) }
        BoundaryEmissionFixture.rejected changed |> ignore
        Assert.True(BoundaryWitness.admit changed |> Result.isError)

    [<Fact>]
    member _.``Changed descriptor symbol retracts the published import contract``() =
        let graph = BoundaryEmissionFixture.scalar ()
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let descriptor = graph.Nodes[imported.Identity]
        let cname =
            match descriptor.Kind with
            | SemanticKind.RecordExpr(fields, _) -> fields |> List.find (fst >> (=) "CName") |> snd
            | other -> failwithf "Expected exact descriptor record identity, got %A" other
        let node = graph.Nodes[cname]
        let changed = { graph with Nodes = graph.Nodes.Add(cname, { node with Kind = SemanticKind.Literal(NativeLiteral.String "changed") }) }
        BoundaryEmissionFixture.rejected changed |> ignore
        Assert.True(BoundaryWitness.admit changed |> Result.isError)

    [<Theory>]
    [<InlineData("reference")>]
    [<InlineData("binding-value")>]
    member _.``Executable uses cannot borrow an external placeholder body`` useKind =
        let graph = BoundaryEmissionFixture.scalar ()
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let call = Assert.Single projection.Calls.Values
        let _, body = BoundaryDeclarations.lambdaOfBinding graph imported.Binding |> Option.get
        let actual = graph.Nodes[call.Arguments.Head.Actual]
        let changed, useSite =
            match useKind with
            | "reference" ->
                { graph with Nodes = graph.Nodes.Add(actual.Id, { actual with Kind = SemanticKind.VarRef("placeholder", Some body); Children = [] }) }, actual.Id
            | "binding-value" ->
                let outside =
                    { actual with Id = NodeId.fresh(); Kind = SemanticKind.Binding("outside", false, false, None)
                                  Children = [body]; Parent = Some imported.Scope; Metadata = Map.empty }
                let owner = graph.Nodes[imported.Scope]
                let owner =
                    match owner.Kind with
                    | SemanticKind.ModuleDef(name, members) -> { owner with Kind = SemanticKind.ModuleDef(name, members @ [outside.Id]) }
                    | other -> failwithf "Expected exact source module owner, got %A" other
                { graph with Nodes = graph.Nodes.Add(outside.Id, outside).Add(owner.Id, owner) }, outside.Id
            | _ -> failwithf "Unknown executable placeholder use: %s" useKind
        BoundaryEmissionFixture.rejected changed |> ignore
        let settled = Clef.Compiler.Nanopass.BoundarySettlement.normalize changed
        let failures = BoundaryEmissionFixture.rejected settled
        Assert.Contains(failures, fun failure ->
            failure.Occurrence = Some useSite && failure.Participants.Contains body &&
            failure.Reason.Contains "outside its declaration leaf")
        Assert.True(BoundaryWitness.admit changed |> Result.isError)

    [<Fact>]
    member _.``Negative scalar extension preserves the settled meet and rejects an unsigned replacement``() =
        let signed8: NumericRepresentation =
            { Name = "int8"; Capability = "native"; Family = "int"; Bits = 8
              MinMagnitude = "-128"; MaxMagnitude = "127"; Boundary = "wrap" }
        let context =
            { BoundaryEmissionFixture.platform with
                Representations = BoundaryEmissionFixture.platform.Representations.Add(signed8.Name, signed8) }
        let result = BoundaryEmissionFixture.check (Some context)
                         (BoundaryEmissionFixture.declaration + BoundaryEmissionFixture.descriptor +
                          BoundaryEmissionFixture.entry.Replace("combine 11 7", "combine (-11) 7"))
        DimensionalCases.noErrors result
        let graph = result.Graph
        let projection = BoundaryEmissionFixture.project graph
        let call = Assert.Single projection.Calls.Values
        let signed = call.Arguments |> List.choose _.Adaptation |> List.filter (fun meet -> meet.Adapt = MeetKind.ExtendSigned) |> Assert.Single
        Assert.Equal(8, signed.From)
        Assert.Equal(32, signed.To)
        Assert.Contains(signed, graph.Codata.Value.Meets[call.Site])
        let changedMeets = graph.Codata.Value.Meets[call.Site] |> List.map (fun meet ->
            if meet = signed then { meet with Adapt = MeetKind.ExtendUnsigned } else meet)
        let changed =
            { graph with Codata = lazy { graph.Codata.Value with Meets = graph.Codata.Value.Meets.Add(call.Site, changedMeets) } }
        BoundaryEmissionFixture.rejected changed |> ignore
        Assert.True(BoundaryWitness.admit changed |> Result.isError)

    [<Fact>]
    member _.``Unsigned foreign result retains the source selected unsigned representation``() =
        let graph = BoundaryEmissionFixture.checkedGraph
                        (BoundaryEmissionFixture.declaration +
                         BoundaryEmissionFixture.descriptor.Replace("ReturnType = Integer (Signed, 32)", "ReturnType = Integer (Unsigned, 32)") +
                         BoundaryEmissionFixture.entry)
        let projection = BoundaryEmissionFixture.project graph
        let imported = Assert.Single projection.Imports.Values
        let call = Assert.Single projection.Calls.Values
        Assert.Equal(Some(BoundaryScalar.Integer(32, false)), imported.Result)
        Assert.Equal(imported.Result, call.Result)
        Assert.Equal(Some(ValueRange.unsignedOf 32), graph.Nodes[call.Site].ValueRange)
        let selected = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.selectedRepresentation graph call.Site |> Option.get
        Assert.Equal("uint32", selected.Name)
        Assert.Equal("uint", selected.Family)
        Assert.Equal(32, selected.Bits)
        Assert.True call.ResultAdaptation.IsNone

    [<Fact>]
    member _.``Declared foreign return range rejects narrowing justified only by a changed call range``() =
        let unsigned8: NumericRepresentation =
            { Name = "uint8"; Capability = "native"; Family = "uint"; Bits = 8
              MinMagnitude = "0"; MaxMagnitude = "255"; Boundary = "wrap" }
        let context =
            { BoundaryEmissionFixture.platform with
                Representations = BoundaryEmissionFixture.platform.Representations.Add(unsigned8.Name, unsigned8) }
        let result = BoundaryEmissionFixture.check (Some context)
                         (BoundaryEmissionFixture.declaration + BoundaryEmissionFixture.descriptor +
                          "\n[<EntryPoint>]\nlet main _ = if combine 11 7 = 0 then 0 else 1\n")
        DimensionalCases.noErrors result
        let graph = result.Graph
        let projection = BoundaryEmissionFixture.project graph
        let call = Assert.Single projection.Calls.Values
        let site = graph.Nodes[call.Site]
        Assert.Equal(Some(BoundaryScalar.Integer(32, true)), call.Result)
        Assert.True call.ResultAdaptation.IsNone
        // This deliberately stale consumer range cannot replace the declared
        // signed 32-bit return's proof premises with an unsigned byte range.
        let narrowed = { site with ValueRange = Some(ValueRange.Bounded(0I, 255I)) }
        let truncation: Meet = { Consumer = site.Id; Operand = site.Id; From = 32; To = 8; Adapt = MeetKind.Truncate }
        let meets = (graph.Codata.Value.Meets.TryFind site.Id |> Option.defaultValue []) @ [truncation]
        let changed =
            { graph with Nodes = graph.Nodes.Add(site.Id, narrowed)
                         Codata = lazy { graph.Codata.Value with Meets = graph.Codata.Value.Meets.Add(site.Id, meets) } }
        Assert.Equal(Some 8, Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.heldWidth changed site.Id)
        BoundaryEmissionFixture.rejected changed |> ignore
        Assert.True(BoundaryWitness.admit changed |> Result.isError)
