// SPDX-License-Identifier: MIT
/// Baker owns foreign declaration identity, scalar ABI and complete joint
/// call premises. Recipes return an enrichment; the nanopass folds it.
module Clef.Compiler.Baker.Recipes.BoundaryRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph
open Clef.Compiler.Baker.Ingredients.Obligations
module Declarations = PlatformResolution
module Ingredients = Clef.Compiler.Baker.Ingredients.Boundaries
module Bytes = Clef.Compiler.Baker.Ingredients.StringBytes
module Participants = Clef.Compiler.Baker.Ingredients.Participants
module StringOrigins = Clef.Compiler.Baker.Ingredients.StringOrigins

type private CheckedBuilder() =
    member _.Bind(value, next) = Result.bind next value
    member _.Return(value) = Ok value
    member _.ReturnFrom(value) = value
let private checked' = CheckedBuilder()

let private require condition message = if condition then Ok () else Error message
let private needed message = function Some value -> Ok value | None -> Error message
let private collect values =
    List.foldBack (fun value rest ->
        match value, rest with
        | Ok value, Ok rest -> Ok (value :: rest)
        | Error reason, _ | _, Error reason -> Error reason) values (Ok [])

let private field name fields = fields |> List.tryPick (fun (key, value) -> if key = name then Some value else None)
let private metadata name (node: SemanticNode) =
    match node.Metadata.TryFind name with Some (MetadataValue.String value) -> Some value | _ -> None

/// Follow only the actual callee's source references. A cycle or an unresolved
/// edge never acquires an external identity from a coincidentally matching name.
let private target = BoundaryDeclarations.target

/// Retain the exact source descriptor structure and referenced declaration
/// values. Parent/module nodes are participants, not recursively traversed.
let private declarationFacts (graph: SemanticGraph) root =
    let shape (node: SemanticNode) =
        let fact form text numbers references =
            Ok { Form = form; Text = text; Numbers = numbers; References = references
                 Children = node.Children; Parent = node.Parent
                 SourceType = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type }
        match node.Kind with
        | SemanticKind.RecordExpr(fields, copy) -> fact "record" (List.map fst fields) [] (List.map snd fields @ Option.toList copy)
        | SemanticKind.ArrayExpr values -> fact "array" [] [] values
        | SemanticKind.TupleExpr values -> fact "tuple" [] [] values
        | SemanticKind.UnionCase(name, index, value) -> fact "case" [name] [bigint index] (Option.toList value)
        | SemanticKind.DUConstruct(name, index, value, _) -> fact "settled-case" [name] [bigint index] (Option.toList value)
        | SemanticKind.Literal(NativeLiteral.String text) -> fact "string" [text] [] []
        | SemanticKind.Literal(NativeLiteral.Int(value, kind)) -> fact "integer" [string kind] [bigint value] []
        | SemanticKind.Literal(NativeLiteral.UInt(value, kind)) -> fact "unsigned-integer" [string kind] [bigint value] []
        | SemanticKind.Literal(NativeLiteral.Bool value) -> fact "boolean" [] [if value then 1I else 0I] []
        | SemanticKind.Literal NativeLiteral.Unit -> fact "unit" [] [] []
        | SemanticKind.VarRef(name, binding) -> fact "reference" [name] [] (Option.toList binding)
        | SemanticKind.Binding(name, mutable', recursive', _) -> fact "binding" [name] [if mutable' then 1I else 0I; if recursive' then 1I else 0I] node.Children
        | SemanticKind.TypeAnnotation(inner, _) -> fact "annotation" [] [] [inner]
        | SemanticKind.Quote(inner, _) -> fact "quotation" [] [] [inner]
        | SemanticKind.Application(callee, arguments) -> fact "application" [] [] (callee :: arguments)
        | SemanticKind.Intrinsic info -> fact "intrinsic" [string info.Module; info.Operation] [] []
        | _ -> Error $"Descriptor participant {NodeId.value node.Id} has no immutable boundary declaration premise."
    let rec visit facts id =
        if Map.containsKey id facts then Ok facts else
        match graph.Nodes.TryFind id with
        | None -> Error $"Descriptor participant {NodeId.value id} is absent from the source graph."
        | Some node -> checked' {
            let! value = shape node
            let next = value.References @ value.Children
            return! List.fold (fun state child -> state |> Result.bind (fun facts -> visit facts child)) (Ok (Map.add id value facts)) next }
    visit Map.empty root

let private typeRef graph typeId =
    Declarations.readTypeRef graph typeId
    |> Result.mapError _.Message
    |> Result.bind (function
        | Declarations.DeclaredTypeRef.Scalar scalar -> Ok (Some scalar)
        | Declarations.DeclaredTypeRef.Void -> Ok None
        | _ -> Error "This TypeRef requires a source-settled adapter beyond the scalar C contract.")

let private scalarRange = function
    | BoundaryScalar.Boolean -> ValueRange.boolean
    | BoundaryScalar.Integer(bits, true) -> ValueRange.twosComplement bits
    | BoundaryScalar.Integer(bits, false) -> ValueRange.unsignedOf bits

let private scalarBits = function BoundaryScalar.Boolean -> 1 | BoundaryScalar.Integer(bits, _) -> bits

let private supportedType scalar ty =
    match scalar, Types.tryGetNTUKind ty with
    | BoundaryScalar.Boolean, Some NTUKind.NTUbool -> true
    | BoundaryScalar.Integer _, Some (NTUKind.NTUint _)
    | BoundaryScalar.Integer _, Some (NTUKind.NTUuint _) -> true
    | _ -> false

let private sourceTypes (graph: SemanticGraph) ids =
    ids |> List.map (fun id ->
        match graph.Nodes.TryFind id with
        | Some node -> Ok (id, Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type)
        | _ -> Error "A scalar boundary participant has no source type identity.")
    |> collect |> Result.map Map.ofList

let private bindingPath = BoundaryDeclarations.bindingPath

let private readImport (graph: SemanticGraph) (descriptors: Declarations.Descriptors) (binding: SemanticNode) library symbol = checked' {
    let! scope = binding.Parent |> needed "The external binding has no source module owner."
    do! require (graph.Nodes.TryFind scope |> Option.exists (fun node -> match node.Kind with SemanticKind.ModuleDef(_, members) -> List.contains binding.Id members | _ -> false))
            "The external binding is not a structural member of its declared module occurrence."
    let! declarationPath, sourceFormals, body = bindingPath graph binding.Id
    let! descriptor =
        match descriptors.Functions |> List.filter (fun descriptor -> descriptor.Body = Some body) with
        | [descriptor] -> Ok descriptor
        | [] -> Error "The external binding has no matching FunctionDescriptor."
        | _ -> Error "The external binding has duplicate FunctionDescriptor declarations."
    let! _, fields = Declarations.recordOf graph descriptor.Node |> needed "The FunctionDescriptor no longer names a source record."
    let! callingId = field "CallingConvention" fields |> needed "The FunctionDescriptor has no declared calling convention."
    let! convention = Declarations.caseOf graph callingId |> Option.map (fun (_, name, _) -> name) |> needed "The calling convention is not a declared case."
    do! require (convention = "CDecl") $"Calling convention '{convention}' is not admitted by the scalar C contract."
    do! require (descriptor.CName = symbol) "FunctionDescriptor.CName disagrees with FidelityExtern.Symbol."
    do! require (descriptor.References.IsEmpty && descriptor.PointerReferences.IsEmpty && descriptor.RecordReferences.IsEmpty)
            "Reference arguments require source-settled boundary adapters; scalar C publication cannot substitute a pointer."
    let parameters =
        descriptor.Parameters |> List.map (fun (formal, declared) -> checked' {
            let! declared = declared |> needed "A boundary parameter has no admitted integer or boolean declaration; pointer and aggregate values require a source-settled adapter."
            let! _, parameterFields = Declarations.recordOf graph declared.Node |> needed "A boundary parameter declaration is missing."
            let! passing = field "PassBy" parameterFields |> needed "A scalar boundary parameter must explicitly declare PassBy.Value."
            do! require (Declarations.caseOf graph passing |> Option.exists (fun (_, name, _) -> name = "Value"))
                    "A scalar boundary parameter must explicitly declare PassBy.Value."
            let! typeId = field "Type" parameterFields |> needed "A boundary parameter has no TypeRef."
            let! scalar = typeRef graph typeId
            let! scalar = scalar |> needed "Void is a result convention, not a boundary parameter."
            let! formalNode = graph.Nodes.TryFind formal |> needed "A boundary formal is absent from the source graph."
            do! require (supportedType scalar formalNode.Type) "A boundary formal's source kind disagrees with its declared scalar ABI."
            do! require (declared.Bits = scalarBits scalar && declared.Range = scalarRange scalar) "The descriptor's scalar range and TypeRef disagree."
            return formal, scalar }) |> collect
    let! parameters = parameters
    let retainedFormals = sourceFormals |> List.map (fun (_, _, id) -> id)
    let erasedUnitFormals =
        match sourceFormals, parameters with
        | [(_, ty, id)], [] when Types.tryGetNTUKind ty = Some NTUKind.NTUunit -> [id]
        | _ -> []
    do! require ((parameters |> List.map fst) @ erasedUnitFormals = retainedFormals)
            "The descriptor's formal order differs from its exact source function declaration."
    let! returnId = field "ReturnType" fields |> needed "The FunctionDescriptor has no ReturnType."
    let! result = typeRef graph returnId
    let! bodyNode = graph.Nodes.TryFind body |> needed "The external binding body is absent from the source graph."
    do! require (match result with Some scalar -> supportedType scalar bodyNode.Type | None -> Types.tryGetNTUKind bodyNode.Type = Some NTUKind.NTUunit)
            "The binding result's source kind disagrees with its declared boundary result."
    let descriptorBindings =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind, node.Children with
            | SemanticKind.Binding _, children when node.Parent = Some scope ->
                children |> List.tryLast |> Option.bind (Declarations.recordOf graph)
                |> Option.bind (fun (record, _) -> if record.Id = descriptor.Node then Some node.Id else None)
            | _ -> None) |> Set.ofSeq
    let! descriptorBinding =
        match Set.toList descriptorBindings with
        | [binding] -> Ok binding
        | _ -> Error "The FunctionDescriptor must retain exactly one source declaration binding."
    do! require (graph.Nodes.TryFind scope |> Option.exists (fun node -> match node.Kind with SemanticKind.ModuleDef(_, members) -> List.contains descriptorBinding members | _ -> false))
            "The FunctionDescriptor binding is not a member of its exact source module occurrence."
    let! facts = declarationFacts graph descriptorBinding
    let participants = Set.unionMany [facts |> Map.keys |> Set.ofSeq; descriptorBindings; Set.ofList (scope :: body :: retainedFormals @ declarationPath)]
    let! types = sourceTypes graph (body :: retainedFormals)
    return { Identity = descriptor.Node; Binding = binding.Id; Scope = scope; Library = library; Symbol = symbol
             CallingConvention = convention; DeclarationPath = declarationPath; Parameters = parameters; Result = result; Participants = participants; SourceTypes = types; DeclarationFacts = facts }
}

let private adaptation (graph: SemanticGraph) site operand sourceBits targetBits inputRange = checked' {
    let matches = graph.Codata.Value.Meets.TryFind site |> Option.defaultValue [] |> List.filter (fun meet -> meet.Operand = operand) |> List.distinct
    if sourceBits = targetBits then
        do! require matches.IsEmpty "An unchanged scalar boundary carries an inconsistent numeric meet."
        return None
    else
        let! meet = match matches with [meet] -> Ok meet | _ -> Error "The scalar boundary requires exactly one already-settled numeric meet."
        do! require (meet.Consumer = site && meet.From = sourceBits && meet.To = targetBits)
                "The source numeric meet disagrees with the exact boundary widths."
        do! require (match meet.Adapt with MeetKind.ExtendSigned | MeetKind.ExtendUnsigned -> sourceBits < targetBits | MeetKind.Truncate -> sourceBits > targetBits | _ -> false)
                "The numeric meet is not an integer adaptation for this scalar boundary."
        do! require (match meet.Adapt with
                     | MeetKind.ExtendUnsigned -> ValueRange.isNonNegative inputRange && ValueRange.contains (ValueRange.unsignedOf sourceBits) inputRange
                     | MeetKind.ExtendSigned -> not (ValueRange.isNonNegative inputRange) && ValueRange.contains (ValueRange.twosComplement sourceBits) inputRange
                     | MeetKind.Truncate -> true // Coverage is a separate joint proof obligation.
                     | _ -> false)
                "The numeric meet's signedness or truncation premise disagrees with the established input range."
        return Some meet
}

let private sourceWidth graph id scalar =
    match scalar with
    | BoundaryScalar.Boolean -> Ok 1
    | BoundaryScalar.Integer _ -> checked' {
        let! representation = RangeAnalysis.selectedRepresentation graph id |> needed "The scalar occurrence has no source-selected offered integer representation."
        do! require (NumericRepresentation.isOffered representation && (representation.Family = "int" || representation.Family = "uint"))
                "The scalar occurrence's selected representation is not an offered integer representation."
        do! require (RangeAnalysis.heldWidth graph id = Some representation.Bits)
                "The scalar occurrence's held width disagrees with its selected offered representation."
        return representation.Bits }

let private readCall (graph: SemanticGraph) (site: SemanticNode) callee args path (import: BoundaryImport) entry = checked' {
    let ordered =
        match entry, site.Kind with
        | None, _ -> site.Children = callee :: args
        | Some _, SemanticKind.Application(intrinsic, operands) ->
            operands = callee :: args && site.Children = intrinsic :: operands &&
            (target graph intrinsic |> Option.exists (fun (node, _) ->
                match node.Kind with SemanticKind.Intrinsic { Module = IntrinsicModule.FnPtr; Operation = "invoke" } -> true | _ -> false))
        | _ -> false
    do! require ordered "The boundary application's ordered operands disagree with its source structural children."
    let operands, erased =
        match import.Parameters, args with
        | [], [unit] when graph.Nodes.TryFind unit |> Option.exists (fun node -> Types.tryGetNTUKind node.Type = Some NTUKind.NTUunit) -> [], [unit]
        | _ -> args, []
    do! require (operands.Length = import.Parameters.Length) "The external call does not supply exactly the declared ordered scalar arguments."
    let! arguments =
        List.zip operands import.Parameters |> List.map (fun (actual, (formal, abi)) -> checked' {
            let! node = graph.Nodes.TryFind actual |> needed "An actual boundary argument is absent from the source graph."
            do! require (supportedType abi node.Type) "An actual boundary argument's source kind disagrees with the declared formal."
            do! require (import.SourceTypes.TryFind formal = Some (Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type))
                    "The actual boundary argument does not retain its formal's native kind and dimension identity."
            let! range = match abi with BoundaryScalar.Boolean -> Ok ValueRange.boolean | _ -> node.ValueRange |> needed "The actual scalar argument lacks an established source range."
            let! sourceBits = sourceWidth graph actual abi
            let! meet = adaptation graph site.Id actual sourceBits (scalarBits abi) range
            return { Actual = actual; Formal = formal; Abi = abi; Adaptation = meet } }) |> collect
    let! resultAdaptation =
        match import.Result with
        | None -> checked' {
            do! require (Types.tryGetNTUKind site.Type = Some NTUKind.NTUunit) "A void foreign call cannot publish a non-unit source result."
            return None }
        | Some abi -> checked' {
            do! require (supportedType abi site.Type) "The call result's source kind disagrees with its boundary declaration."
            let! targetBits = sourceWidth graph site.Id abi
            let input = match abi with BoundaryScalar.Integer _ -> site.ValueRange |> Option.defaultValue ValueRange.Unbounded | _ -> scalarRange abi
            return! adaptation graph site.Id site.Id (scalarBits abi) targetBits input }
    let! types = sourceTypes graph (site.Id :: args)
    return { Site = site.Id; Import = import.Identity; Callee = callee; Entry = entry; Arguments = arguments; ErasedUnitArguments = erased
             Result = import.Result; ResultAdaptation = resultAdaptation
             Participants = Set.unionMany [import.Participants; path; Set.ofList (site.Id :: callee :: args)]
             SourceTypes = types }
}

type private IntrinsicDomain = {
    Views: BoundaryByteView list
    Extents: BoundaryStringExtent list
    Declarations: (NodeId * IntrinsicWriteImport) list
    Imports: IntrinsicWriteImport list
    Calls: IntrinsicWriteCall list
    Proofs: IntrinsicWriteProof list
    Snapshots: MemoryStringViewWitness list
    Copies: MemoryArrayCopyWitness list
    Allocations: MemoryArrayAllocationWitness list
    Enrichment: Enrichment
    Errors: (NodeId * Set<NodeId> * string) list
}

let private intrinsicWrites enrichId anchor (graph: SemanticGraph) =
    let views = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringByteView view -> Some view | _ -> None)
    let extents = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringExtent extent -> Some extent | _ -> None)
    let declarations = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.IntrinsicWriteAbi import -> Some(edge.Target, import) | _ -> None)
    let sourceEvidence, sourceFailures = StringBorrowRecipes.evidence graph
    let retainedEvidence =
        (views |> List.collect (fun view -> [Bytes.viewRow view; Bytes.storageRow view])) @
        (extents |> List.map Bytes.extentRow) @ (declarations |> List.map (fun (site, import) -> Bytes.abiRow site import))
    let key (edge: Hyperedge) = edge.Role, edge.Sources, edge.Target
    let currentEvidence = (sourceEvidence |> List.map key |> List.sort) = (retainedEvidence |> List.map key |> List.sort)
    let unique message values = match values with [value] -> Ok value | _ -> Error message
    let range id = graph.Nodes.TryFind id |> Option.bind _.ValueRange |> needed "The intrinsic scalar lacks its established source range."
    let coverage input destination =
        match input, destination with
        | ValueRange.Bounded(lo, hi), ValueRange.Bounded(minimum, maximum) -> Ok(ObligationBody.IntegerRepresentationCoverage(lo, hi, minimum, maximum))
        | _ -> Error "The intrinsic coverage obligation requires finite source and destination ranges."
    let read (node: SemanticNode) callee args path = checked' {
        do! require currentEvidence "The complete byte-origin/formal/actual or intrinsic ABI premises changed after source numeric settlement."
        let! fd, buffer, count = match args with [fd; buffer; count] -> Ok(fd, buffer, count) | _ -> Error "Sys.write requires exactly fd, a bounded read-only byte view, and its explicit count."
        do! require (node.Children = callee :: args) "Sys.write's ordered operands differ from its source structural occurrence."
        let! import = declarations |> List.filter (fun (site, _) -> site = node.Id) |> List.map snd |> unique "Sys.write requires one selected source syscall endpoint, return contract, Register dimension and offered octet declaration before numeric settlement."
        let! view = views |> List.filter (fun view -> view.Site = buffer) |> unique "Sys.write requires a proved string.Bytes read-only borrow with complete source storage and lifetime premises."
        let! extent = extents |> List.filter (fun extent -> extent.Site = count) |> unique "Sys.write's count must preserve the exact borrowed string's per-invocation Length relation."
        do! require (view.ExtentSource = extent.ExtentSource && view.StaticOrigins = extent.StaticOrigins)
                "Sys.write's buffer and count do not refer to the same per-invocation string extent and complete origin domain."
        do! require (view.Representation = import.ByteRepresentation) "The byte borrow and intrinsic ABI have different source-selected byte carriers."
        do! require (graph.Nodes[buffer].Kind = SemanticKind.StringByteBorrow view.Source && graph.Nodes[count].Kind = SemanticKind.FieldGet(extent.Source, "Length"))
                "The byte borrow or extent occurrence no longer retains its settled source operation."
        let readonlyUse = graph.Nodes.Values |> Seq.forall (fun consumer ->
            if not consumer.IsReachable || consumer.Id = buffer then true else
            let uses = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence consumer |> List.filter (fun edge -> List.contains buffer edge.Sources)
            uses.IsEmpty ||
            (match consumer.Kind, target graph (match consumer.Kind with SemanticKind.Application(fn, _) -> fn | _ -> consumer.Id) with
             | SemanticKind.Application(_, [_; actual; _]), Some({ Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Sys; Operation = "write" } }, _) when actual = buffer -> true
             | _ -> false))
        do! require readonlyUse "A read-only string byte borrow escapes the admitted write operand or has a mutable/unknown use."
        let! fdRange = range fd
        let! countRange = range count
        let! borrowProof, storageParticipants, snapshots, copies, allocations =
            if not view.StaticOrigins.IsEmpty then checked' {
                let! pool = graph.StaticStringPool |> needed "A byte borrow requires the settled immutable program string pool."
                let! storage = view.StaticOrigins |> Map.toList |> List.map (fun (origin, length) -> checked' {
                    let! entry = pool.Entries |> List.filter (fun entry -> List.contains origin entry.NodeIds) |> unique "A string borrow origin has no unique program-resident immutable storage entry."
                    do! require (bigint entry.Length = length && System.Text.Encoding.UTF8.GetByteCount entry.Content = entry.Length && entry.StorageLength = entry.Length + 1)
                            "The string borrow extent differs from its exact immutable storage entry."
                    do! require (graph.Nodes.TryFind origin |> Option.exists (fun node -> node.Kind = SemanticKind.Literal(NativeLiteral.String entry.Content)))
                            "The program storage entry no longer belongs to the exact literal source bytes."
                    return length, length, bigint entry.StorageLength }) |> collect
                let expectedCount = ValueRange.bounded (view.StaticOrigins.Values |> Seq.min) (view.StaticOrigins.Values |> Seq.max)
                do! require (countRange = expectedCount) "The scalar count range no longer matches the complete exact string extent domain."
                return ObligationBody.StringBorrowBound storage, Set.singleton pool.DeclarationNode, [], [], [] }
            else checked' {
                let! memory = MemoryPublication.project graph |> Result.mapError (fun _ -> "A runtime string write requires admitted source memory, copy and UTF-8 snapshot premises.")
                let! snapshots, copies, lineage = StringViewRecipes.localLineage graph memory view.Source
                let! snapshot = snapshots |> unique "A runtime string write requires one exact immutable local snapshot terminal."
                do! require (Clef.Compiler.Baker.Ingredients.ArrayShapes.reader graph view.Source
                             |> Option.exists (fun descriptor -> descriptor.StringSources=Set.singleton snapshot.Site))
                        "A runtime string write requires a complete single-snapshot source domain."
                let! copy = copies |> unique "A runtime string write requires the snapshot's exact complete copy receipt."
                let! allocationId = copy.Allocation |> needed "A runtime string write requires the snapshot's independent allocation."
                let! allocation = memory.Operations.TryFind allocationId |> Option.bind (function MemoryWitnessOperation.ArrayAllocation value -> Some value | _ -> None)
                                  |> needed "A runtime string write lost its exact source-admitted allocation."
                let canonical id = Declarations.valueOf graph id |> Option.map _.Id
                do! require (snapshot.Snapshot = copy.Site && snapshot.Extent = copy.CountCarrier &&
                             canonical allocation.Count = canonical copy.Count && canonical copy.Count <> None)
                        "The runtime borrow's snapshot, copy and allocation must retain the same actual descriptor count."
                let! scope = MemoryAccessRecipes.nearestLambda graph node.Id |> needed "A runtime string write requires an exact lexical activation."
                do! require (MemoryAccessRecipes.nearestLambda graph snapshot.Site = Some scope &&
                             (match allocation.Residence with MemoryResidence.Stack(owner,_) -> owner=scope | _ -> false))
                        "A runtime string borrow cannot cross its snapshot allocation's lexical activation."
                do! require (snapshot.Representation=import.ByteRepresentation && allocation.Element=snapshot.Element && allocation.ElementBytes=1)
                        "The runtime string's snapshot and allocation disagree with the native byte carrier."
                let! countValue =
                    match countRange with
                    | ValueRange.Bounded(lo,hi) when lo=hi && 0I<=lo && hi<=bigint System.Int64.MaxValue -> Ok lo
                    | _ -> Error "A runtime string write requires a singleton complete descriptor count; relational dynamic extent proof remains pending."
                do! require (snapshot.Extent.Range=countRange && allocation.CountCarrier.Range=countRange &&
                             allocation.MinimumCount=countValue && allocation.MaximumCount=countValue)
                        "The runtime write count must equal its exact copied descriptor and allocation extent."
                return ObligationBody.InputBufferBound(int64 countValue,int64 countValue),
                       Set.union lineage allocation.Participants, snapshots, copies, [allocation] }
        let! platform = Declarations.resolve graph |> needed "Sys.write lost its selected source platform description."
        let! result = platform.Returns |> List.filter (fun bound -> bound.Node = import.ReturnContract && bound.Endpoint = "write" && bound.AtMost = "count") |> unique "Sys.write lost its exact declared signed return bound."
        let! upper = match countRange with ValueRange.Bounded(_, hi) -> Ok hi | _ -> Error "The write count is not bounded."
        let returnRange = ValueRange.bounded result.Floor upper
        let! actualResult = range node.Id
        do! require (actualResult = returnRange) "Sys.write's result range differs from its source endpoint return contract."
        let! fdWidth = sourceWidth graph fd import.Fd
        let! countWidth = sourceWidth graph count import.Count
        let! resultWidth = sourceWidth graph node.Id import.Result
        let! fdMeet = adaptation graph node.Id fd fdWidth (scalarBits import.Fd) fdRange
        let! countMeet = adaptation graph node.Id count countWidth (scalarBits import.Count) countRange
        let! resultMeet = adaptation graph node.Id node.Id (scalarBits import.Result) resultWidth returnRange
        let! resultRepresentation = RangeAnalysis.selectedRepresentation graph node.Id |> Option.bind Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources.declaredRange |> needed "The write result has no offered representation range."
        let! fdProof = coverage fdRange (scalarRange import.Fd)
        let! countProof = coverage countRange (scalarRange import.Count)
        let! resultProof = coverage returnRange resultRepresentation
        let! viewParticipants = Participants.established view.Participants
        let! extentParticipants = Participants.established extent.Participants
        let participants =
            Set.unionMany [path; import.Participants; Set.ofList (Participants.nodes viewParticipants); Set.ofList (Participants.nodes extentParticipants)
                           storageParticipants; Set.ofList [anchor; node.Id; callee; fd; buffer; count]]
        let call = { Site = node.Id; Import = import.Identity; Callee = callee; Fd = fd; Buffer = buffer; Count = count
                     FdAdaptation = fdMeet; CountAdaptation = countMeet; ResultAdaptation = resultMeet; Participants = participants }
        return import, call, [0, fdProof; 1, borrowProof; 2, countProof; -1, resultProof], snapshots, copies, allocations }
    let evidenceErrors =
        if currentEvidence then [] else
        // The related nodes of each row: its established participants, or its site while they are pending.
        let related site evidence =
            match Participants.established evidence with
            | Ok established -> Set.ofList (Participants.nodes established)
            | Error _ -> Set.singleton site
        let participants = Set.unionMany ((views |> List.map (fun view -> related view.Site view.Participants)) @ (extents |> List.map (fun extent -> related extent.Site extent.Participants)))
        [anchor,participants,"The complete string view, descriptor extent, actual/formal or intrinsic ABI evidence changed after source range settlement."]
    // Each borrow site whose origins are reached through a call whose targets the
    // participant form cannot state, at the site, naming the call.
    let originErrors = sourceFailures |> List.map (fun (site, failure) -> StringComparisonRecipes.originError graph site failure)
    let initial = { Views = views; Extents = extents; Declarations = declarations; Imports = []; Calls = []; Proofs = []
                    Snapshots=[]; Copies=[]; Allocations=[]; Enrichment = Enrichment.empty; Errors = originErrors @ evidenceErrors }
    graph.Nodes |> Map.fold (fun state _ node ->
        match node.Kind with
        | SemanticKind.Application(callee, args) when node.IsReachable ->
            match target graph callee with
            | Some({ Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Sys; Operation = "write" } }, path) ->
                match read node callee args path with
                | Error reason -> { state with Errors = (node.Id, Set.union path (Set.ofList(node.Id :: args)), reason) :: state.Errors }
                | Ok(import, call, bodies, snapshots, copies, allocations) ->
                    let proofs, enrichment, errors = bodies |> List.fold (fun (proofs, enrichment, errors) (ordinal, body) ->
                        let info =
                            { Id = $"intrinsic_write_{NodeId.value node.Id}_{ordinal}"; Kind = "intrinsic-write-proof"; Logic = "QF_LIA"
                              Statement = "the exact ordered intrinsic write has covered scalars and a count-contained immutable borrow"
                              Source = fmtRange node.Range; Refs = []; Body = body }
                        let obligation = obligationNode node enrichId info |> Ingredients.markOwned
                        let proof = { Site = node.Id; Obligation = obligation.Id; Ordinal = ordinal; Body = body; Participants = call.Participants }
                        let errors = if Bytes.proofOutcome body = BoundaryProofOutcome.Proven then errors else (node.Id, call.Participants, "The intrinsic write obligation was refuted.") :: errors
                        proof :: proofs, Enrichment.combine enrichment { NewNodes = [obligation]; Annotated = []; NewEdges = Bytes.proofRows proof }, errors) (state.Proofs, state.Enrichment, state.Errors)
                    { state with Imports = import :: state.Imports; Calls = call :: state.Calls; Proofs = proofs
                                 Snapshots=snapshots@state.Snapshots; Copies=copies@state.Copies; Allocations=allocations@state.Allocations
                                 Enrichment = enrichment; Errors = errors }
            | _ -> state
        | _ -> state) initial

/// Late stage: all source ranges and ordinary numeric meets are already fixed.
/// The complete source domain records negative membership dependencies too.
let private elaborateCore (graph: SemanticGraph) : Enrichment =
    let enrichId = Elaboration.freshId ()
    let anchor = Ingredients.anchor enrichId graph
    let intrinsic = intrinsicWrites enrichId anchor.Id graph
    let lengthComparisons = StringComparisonRecipes.lengthConstructions graph
    let lengthErrors = graph.Nodes.Values |> Seq.choose (fun node ->
        if node.Metadata.TryFind "Baker.StringLengthComparison" <> Some(MetadataValue.Bool true) then None else
        let lost = node.Id,Set.singleton node.Id,"The descriptor-only string comparison lost its exact zero-extent origin, actual/formal membership, or ordered source construction proof."
        match lengthComparisons |> List.filter (fun fact -> fact.Site=node.Id) with
        | [fact] ->
            match StringComparisonRecipes.validLengthStructure graph fact with
            | Ok true -> None
            | Ok false -> Some lost
            | Error failure -> Some(StringComparisonRecipes.originError graph node.Id failure)
        | _ -> Some lost) |> Seq.toList
    let localViews, localReads, localSnapshots, localCopies, localErrors =
        let memory = Clef.Compiler.PSGSaturation.SemanticGraph.MemoryPublication.project graph |> Result.toOption
        StringComparisonRecipes.constructions graph |> List.fold (fun (views,reads,snapshots,copies,errors) construction ->
            let participants = Set.ofList(construction.Site::construction.Left::construction.Right::construction.Members)
            let result = checked' {
                do! require (StringComparisonRecipes.validStructure graph construction) "The source string comparison lost its ordered length test, traversal, early exit or local result correspondence."
                let! memory = memory |> needed "A local string comparison borrow requires admitted memory access and bounds proofs."
                let! accesses = [construction.LeftView,construction.LeftRead; construction.RightView,construction.RightRead]
                                |> List.map (fun (view,frontier) -> checked' {
                    let! access =
                        match graph.Nodes.TryFind frontier with
                        | Some { Kind=SemanticKind.Sequential [_;continuation] } ->
                            memory.Operations.TryFind continuation |> Option.bind (function MemoryWitnessOperation.ArrayAccess fact -> Some fact | _ -> None)
                        | _ -> None
                        |> needed "The string comparison read lacks its exact guarded access continuation."
                    do! require (access.Buffer=view && access.Index=construction.Current && access.Value.IsNone && access.Bounds.Requirement.Frontier=frontier)
                            "The string comparison borrow is not read by its exact source guard and index occurrence."
                    let allowed = Set.ofList [access.Site;access.Bounds.Length]
                    let uses =
                        let source = graph.Nodes.Values |> Seq.collect Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence |> Seq.toList
                        source @ (graph.Edges |> List.filter (fun edge -> edge.Class=EdgeClass.Structural || edge.Class=EdgeClass.Reference))
                        |> List.filter (fun edge -> List.contains view edge.Sources && graph.Nodes.TryFind edge.Target |> Option.exists _.IsReachable)
                    do! require (not uses.IsEmpty && uses |> List.forall (fun edge -> allowed.Contains edge.Target))
                            "A local string comparison byte view escapes its exact read-only guarded uses."
                    let! byteView = intrinsic.Views |> List.filter (fun fact -> fact.Site=view) |> function [fact] -> Ok fact | _ -> Error "The local comparison lacks its single exact byte view."
                    let! viewParticipants = Participants.established byteView.Participants
                    do! require (byteView.ExtentSource=byteView.Source && (Set.ofList (Participants.nodes viewParticipants)).IsSupersetOf participants)
                            "The local comparison view lost its complete actual and construction lifetime premises."
                    let! snapshots,copies,_ = StringViewRecipes.localLineage graph memory byteView.Source
                    return access,snapshots,copies }) |> collect
                return accesses }
            match result with
            | Ok accesses ->
                let localReads=accesses |> List.map(fun (read,_,_) -> read)
                let localSnapshots=accesses |> List.collect(fun (_,facts,_) -> facts)
                let localCopies=accesses |> List.collect(fun (_,_,facts) -> facts)
                Set.add construction.LeftView (Set.add construction.RightView views),localReads@reads,localSnapshots@snapshots,localCopies@copies,errors
            | Error reason -> views,reads,snapshots,copies,(construction.Site,participants,reason)::errors) (Set.empty,[],[],[],[])
    let intrinsic =
        let errors = graph.Nodes |> Map.fold (fun errors _ node ->
            match node.Kind with
            | SemanticKind.StringByteBorrow _ when node.IsReachable && not (localViews.Contains node.Id) && not (intrinsic.Calls |> List.exists (fun call -> call.Buffer = node.Id)) ->
                (node.Id, Set.singleton node.Id, "A string.Bytes borrow requires complete intrinsic write-use or local guarded comparison lifetime proofs.") :: errors
            | _ -> errors) intrinsic.Errors
        { intrinsic with Errors = lengthErrors @ localErrors @ errors }
    let descriptors = Declarations.readDescriptors graph
    let runtime = Declarations.read graph
    let runtimeContract = checked' {
        do! require runtime.Findings.IsEmpty "The selected source platform runtime has unresolved declaration or project consistency findings."
        let! platform = runtime.Platform |> needed "A reachable C import requires a resolved source PlatformDescription."
        let! core = platform.Core |> needed "A reachable C import requires a declared TargetCore.Runtime."
        do! require (Declarations.runtimeModel core = Some RuntimeModel.Libc) "A reachable C import requires source TargetCore.Runtime libc; startup or project defaults do not establish library availability."
        return () }
    let initialErrors = intrinsic.Errors @ (descriptors.Findings |> List.map (fun finding -> finding.Node, Set.singleton finding.Node, finding.Message))
    let imported binding =
        checked' {
            let! library =
                metadata "FidelityExtern.Library" binding
                |> needed "FidelityExtern.Library is missing."

            let! symbol =
                metadata "FidelityExtern.Symbol" binding
                |> needed "FidelityExtern.Symbol is missing."

            do! require (not (System.String.IsNullOrWhiteSpace symbol)) "FidelityExtern.Symbol must name an external declaration."
            do! runtimeContract
            do! require (library = "c") "This C library requires a source-settled link/load contract beyond the admitted libc boundary."
            let! import = readImport graph descriptors binding library symbol

            return
                { import with
                    Participants = Set.add anchor.Id import.Participants
                }
        }

    let loading =
        checked' {
            let! loading =
                Declarations.readLoading graph
                |> Result.mapError (fun findings -> findings |> List.map _.Message |> String.concat "; ")

            let! selected =
                loading
                |> needed
                    "FnPtr.ofExtern requires an explicitly selected source process-link loading contract; TargetCore.Runtime supplies no code lifetime."

            let! platform =
                runtime.Platform
                |> needed "The loading contract has no selected source platform."

            let! core =
                platform.Core
                |> needed "The loading contract has no selected source target core."

            let! facts =
                [ selected.Binding; platform.Node; core.Node ]
                |> List.fold (fun state root ->
                    state |> Result.bind (fun facts ->
                        declarationFacts graph root
                        |> Result.map (fun next -> Map.fold (fun facts id fact -> Map.add id fact facts) facts next))) (Ok Map.empty)

            return
                {
                    Identity = selected.Node
                    Binding = selected.Binding
                    Selector = selected.Selector
                    Contract = selected.Contract
                    Platform = platform.Node
                    Core = core.Node
                    DeclarationFacts = facts
                    Participants =
                        Set.unionMany
                            [
                                selected.Participants
                                facts |> Map.keys |> Set.ofSeq
                                Set.ofList [ anchor.Id; platform.Node; core.Node ]
                            ]
                }
                : BoundaryLoading
        }

    let purposes = Reachability.declarationPurposes graph

    let entryAt (source: BoundaryDeclarations.EntrySource) =
        checked' {
            let! formation =
                graph.Nodes.TryFind source.Formation
                |> needed "The imported entry formation is absent."

            let! declaration =
                graph.Nodes.TryFind source.Declaration
                |> needed "The imported entry's original external declaration is absent."

            let! import = imported declaration
            let! loading = loading

            let entryPurposes =
                purposes.TryFind source.Formation |> Option.defaultValue Set.empty

            do!
                require
                    (entryPurposes
                     |> Set.exists (fun (_, purpose) -> purpose = DeclRoot.LibraryExport)
                     |> not)
                    "An imported native entry reachable from an exported library interface requires a host loading contract (L3); the process-link contract grants no exported-library authority."

            do!
                require
                    (entryPurposes |> Set.exists (fun (_, purpose) -> purpose = DeclRoot.EntryPoint))
                    "The process-link contract admits imported entries only within a hosted executable entry-point image."

            let payload =
                match Clef.Compiler.NativeTypedTree.UnionFind.applySubst formation.Type with
                | NativeType.TApp(constructor, [ signature ]) when constructor.NTUKind = Some NTUKind.NTUfnptr ->
                    Some(Clef.Compiler.NativeTypedTree.TypeIdentities.ofType signature)
                | _ -> None

            do!
                require
                    (payload = Some(Clef.Compiler.NativeTypedTree.TypeIdentities.ofType declaration.Type))
                    "The imported entry's complete source signature differs from its original extern declaration."

            let participants =
                Set.unionMany
                    [
                        source.Transport
                        import.Participants
                        loading.Participants
                        Set.ofList [ source.Formation; source.Operand; source.Declaration ]
                    ]

            return
                import,
                loading,
                {
                    Formation = source.Formation
                    Operand = source.Operand
                    Import = import.Identity
                    Declaration = source.Declaration
                    Loading = loading.Identity
                    SourceType = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType formation.Type
                    Transport = source.Transport
                    Participants = participants
                }
        }

    let retainEntry (entry: BoundaryEntry) (entries: Map<NodeId, BoundaryEntry>) =
        let entry =
            match entries |> Map.tryFind entry.Formation with
            | None -> entry
            | Some previous ->
                { entry with
                    Transport = Set.union previous.Transport entry.Transport
                    Participants = Set.union previous.Participants entry.Participants
                }

        Map.add entry.Formation entry entries

    let imports, calls, entries, errors =
        graph.Nodes
        |> Map.fold
            (fun (imports, calls, entries, errors) _ node ->
                match node.Kind with
                | SemanticKind.Application(callee, args) when node.IsReachable ->
                    match target graph callee with
                    | Some(binding, path) when BoundaryDeclarations.isExternal binding ->
                        let participants = Set.union path (Set.ofList (node.Id :: args))

                        let result =
                            checked' {
                                let! import = imported binding
                                let! call = readCall graph node callee args path import None
                                return import, call
                            }

                        match result with
                        | Ok(import, call) -> Map.add import.Identity import imports, Map.add node.Id call calls, entries, errors
                        | Error reason -> imports, calls, entries, (node.Id, participants, reason) :: errors
                    | Some({
                               Kind = SemanticKind.Intrinsic {
                                                                 Module = IntrinsicModule.FnPtr
                                                                 Operation = "ofExtern"
                                                             }
                           },
                           _) ->
                        match
                            BoundaryDeclarations.entryFormation graph node.Id
                            |> needed
                                "FnPtr.ofExtern requires the actual declared extern binding, not a symbol, ordinary function or captured closure."
                            |> Result.bind entryAt
                        with
                        | Ok(import, _, entry) -> Map.add import.Identity import imports, calls, retainEntry entry entries, errors
                        | Error reason -> imports, calls, entries, (node.Id, Set.ofList (node.Id :: args), reason) :: errors
                    | Some({
                               Kind = SemanticKind.Intrinsic {
                                                                 Module = IntrinsicModule.FnPtr
                                                                 Operation = "invoke"
                                                             }
                           },
                           path) ->
                        match args with
                        | pointer :: actuals ->
                            match BoundaryDeclarations.entryFormation graph pointer with
                            | None -> imports, calls, entries, errors
                            | Some source ->
                                let result =
                                    checked' {
                                        let! import, loading, entry = entryAt source

                                        let! call =
                                            readCall
                                                graph
                                                node
                                                pointer
                                                actuals
                                                (Set.unionMany [ path; source.Transport; loading.Participants ])
                                                import
                                                (Some source.Formation)

                                        return import, entry, call
                                    }

                                match result with
                                | Ok(import, entry, call) ->
                                    Map.add import.Identity import imports, Map.add node.Id call calls, retainEntry entry entries, errors
                                | Error reason ->
                                    imports,
                                    calls,
                                    entries,
                                    (node.Id, Set.union source.Transport (Set.ofList (node.Id :: args)), reason)
                                    :: errors
                        | _ -> imports, calls, entries, errors
                    | Some({ Kind = SemanticKind.Intrinsic info }, path) when info.Module = IntrinsicModule.Sys ->
                        if info.Operation = "write" then
                            imports, calls, entries, errors
                        else
                            imports,
                            calls,
                            entries,
                            (node.Id,
                             Set.union path (Set.ofList (node.Id :: args)),
                             $"Intrinsic/system boundary Sys.{info.Operation} requires CCS/Baker intrinsic boundary settlement (Layer 1); its source-owned operand and ABI contract is unsettled, and runtime or startup defaults cannot supply it.")
                            :: errors
                    | _ -> imports, calls, entries, errors
                | _ -> imports, calls, entries, errors)
            (Map.empty, Map.empty, Map.empty, initialErrors)

    let errors =
        imports.Values |> Seq.groupBy _.Symbol |> Seq.fold (fun errors (_, declarations) ->
            match Seq.toList declarations with
            | first :: rest -> rest |> List.fold (fun errors other ->
                let reason =
                    if first.Library <> other.Library || first.CallingConvention <> other.CallingConvention ||
                       List.map snd first.Parameters <> List.map snd other.Parameters || first.Result <> other.Result then
                        "The same imported symbol has inconsistent library or scalar ABI declarations."
                    else "The same imported symbol has multiple source declaration identities; source reconciliation is required."
                (other.Identity, Set.union first.Participants other.Participants, reason) :: errors) errors
            | [] -> errors) errors
    let leaves = imports.Values |> Seq.map _.Binding |> Set.ofSeq
    let rec declarationNodes pending found errors =
        match pending with
        | [] -> found, errors
        | id :: rest when Set.contains id found -> declarationNodes rest found errors
        | id :: rest ->
            match graph.Nodes.TryFind id with
            | Some node -> declarationNodes (node.Children @ rest) (Set.add id found) errors
            | None -> declarationNodes rest found ((id, Set.add id leaves, "A structural participant of an external declaration leaf is absent.") :: errors)
    let declarationInventory, errors = declarationNodes (Set.toList leaves) Set.empty errors
    let declarationOnly = Set.difference declarationInventory leaves
    let errors = graph.Nodes |> Map.fold (fun errors _ node ->
        if not node.IsReachable || declarationInventory.Contains node.Id then errors else
        Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence node |> List.fold (fun errors edge ->
            if edge.Class <> EdgeClass.Structural && edge.Class <> EdgeClass.Reference then errors else
            edge.Sources |> List.fold (fun errors source ->
                if declarationOnly.Contains source then
                    (node.Id, Set.ofList [node.Id; source], "An external declaration placeholder participant has an executable use outside its declaration leaf.") :: errors
                else errors) errors) errors) errors
    let proofs, errors = calls |> Map.fold (fun (enrichment, errors) _ call ->
        let argumentRanges = call.Arguments |> List.mapi (fun ordinal operand ->
            let input = match operand.Abi with BoundaryScalar.Boolean -> ValueRange.boolean | _ -> graph.Nodes[operand.Actual].ValueRange |> Option.defaultValue ValueRange.Unbounded
            ordinal, operand.Actual, input, scalarRange operand.Abi)
        // Integer result narrowing belongs to Numeric's conditional foreign
        // account. The C carrier is an ABI premise, not a behavioral enclosure.
        let resultRange = call.Result |> Option.toList |> List.filter (function BoundaryScalar.Integer _ -> false | _ -> true) |> List.map (fun abi ->
            let destination =
                match abi with
                | BoundaryScalar.Boolean -> ValueRange.boolean
                | _ -> RangeAnalysis.selectedRepresentation graph call.Site
                       |> Option.bind Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources.declaredRange
                       |> Option.defaultValue ValueRange.Unbounded
            -1, call.Site, scalarRange abi, destination)
        argumentRanges @ resultRange |> List.fold (fun (enrichment, errors) (ordinal, operand, input, destination) ->
            match Ingredients.coverage enrichId graph call ordinal operand input destination with
            | Error reason -> enrichment, (call.Site, call.Participants, reason) :: errors
            | Ok (proof, _, outcome) ->
                let errors = if outcome = BoundaryProofOutcome.Proven then errors else
                                (call.Site, call.Participants, "The boundary range obligation is refuted: source range is not covered by its declared destination.") :: errors
                Enrichment.combine enrichment proof, errors) (enrichment, errors)) (Enrichment.empty, errors)
    let observedOrigins =
        (intrinsic.Views |> List.exists (fun view -> StringOrigins.used view.Participants)) ||
        (intrinsic.Extents |> List.exists (fun extent -> StringOrigins.used extent.Participants))
    let originRelations, errors =
        if not observedOrigins then None, errors else
        match StringOrigins.relations graph with
        | Ok relations -> Some relations, errors
        | Error reason -> None, (anchor.Id, Map.keys graph.Nodes |> Set.ofSeq, reason) :: errors
    let domain =
        { Premises = Ingredients.premises graph; Platform = Ingredients.platformPremise graph.Platform; Meets = graph.Codata.Value.Meets
          Declarations = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryDeclaration declaration -> Some declaration | _ -> None)
          ResultHypotheses = descriptors.ResultRanges |> List.map _.Hypothesis
          Imports = Map.keys imports |> Seq.toList; Calls = Map.keys calls |> Seq.toList
          Loading = if entries.IsEmpty then None else loading |> Result.toOption
          Entries = Map.keys entries |> Seq.toList
          ByteViews = intrinsic.Views; StringExtents = intrinsic.Extents; IntrinsicDeclarations = intrinsic.Declarations
          StringOriginRelations = originRelations
          StringOriginRoots = if observedOrigins then Some graph.DeclarationRoots else None
          StringComparisons = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringComparisonConstruction negated -> Some(edge.Target,negated,edge.Sources) | _ -> None)
          StringLengthComparisons = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.StringLengthComparison negated -> Some(edge.Target,negated,edge.Sources) | _ -> None)
          StringComparisonReads = localReads
          StringBorrowSnapshots = List.distinct (localSnapshots@intrinsic.Snapshots)
          StringBorrowCopies = List.distinct (localCopies@intrinsic.Copies)
          StringBorrowAllocations =
            let memory = MemoryPublication.project graph |> Result.toOption
            let local = localCopies |> List.choose (fun copy -> copy.Allocation |> Option.bind (fun id ->
                memory |> Option.bind (fun memory -> memory.Operations.TryFind id) |> Option.bind (function MemoryWitnessOperation.ArrayAllocation fact -> Some fact | _ -> None)))
            List.distinct (local@intrinsic.Allocations)
          IntrinsicImports = List.distinct intrinsic.Imports; IntrinsicCalls = intrinsic.Calls; IntrinsicProofs = intrinsic.Proofs
          StringStorage = Bytes.storagePremise graph
          DeclarationLeaves = leaves; DeclarationOnly = declarationOnly
          Links = imports.Values |> Seq.map _.Library |> Set.ofSeq; Failures = List.rev errors }
    let sources = Map.keys domain.Premises |> Seq.toList
    let rows =
        [Ingredients.row (EdgeRole.BoundaryDomain domain) 0 sources anchor.Id
         { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = sources; Target = anchor.Id }]
        @ (imports.Values |> Seq.map Ingredients.importRow |> Seq.toList)
        @ (entries.Values |> Seq.map (fun entry -> Ingredients.row (EdgeRole.BoundaryEntry entry) 0 (Set.toList entry.Participants) entry.Formation) |> Seq.toList)
        @ (calls.Values |> Seq.collect (fun call -> Ingredients.callRow call :: Ingredients.operandRows call) |> Seq.toList)
        @ (domain.IntrinsicImports |> List.map Bytes.importRow)
        @ (domain.IntrinsicCalls |> List.collect Bytes.callRows)
    Enrichment.combine (Enrichment.combine { NewNodes = [anchor]; Annotated = []; NewEdges = rows } proofs) intrinsic.Enrichment

let elaborate graph =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> elaborateCore graph)
