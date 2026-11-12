// SPDX-License-Identifier: MIT
/// Baker-owned, conservative segmentation of already settled witness inputs.
module Clef.Compiler.PSGSaturation.SemanticGraph.WitnessSegmentation

open System
open System.Collections
open System.Collections.Concurrent
open System.Globalization
open System.Reflection
open System.Security.Cryptography
open System.Text
open Microsoft.FSharp.Reflection
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let private flags = BindingFlags.Public ||| BindingFlags.NonPublic
let private names = ConcurrentDictionary<Type, string>()
let private typeName (t: Type) = names.GetOrAdd(t, fun t -> t.FullName |> Option.ofObj |> Option.defaultWith (fun () -> invalidOp "Unnamed source input type"))
let private properties = ConcurrentDictionary<Type * string, PropertyInfo>()
let private property name (value: obj) =
    let field = properties.GetOrAdd((value.GetType(), name), fun (key: Type * string) ->
        let ty, name = key
        ty.GetProperty(name) |> Option.ofObj |> Option.defaultWith (fun () -> invalidOp ("Missing structural field " + name)))
    field.GetValue value
let private generics = ConcurrentDictionary<Type, string>()
let private generic (t: Type) = generics.GetOrAdd(t, fun t -> if t.IsGenericType then typeName (t.GetGenericTypeDefinition()) else "")
let private isMap t = (generic t).StartsWith "Microsoft.FSharp.Collections.FSharpMap"
let private isSet t = (generic t).StartsWith "Microsoft.FSharp.Collections.FSharpSet"
let private isList t = (generic t).StartsWith "Microsoft.FSharp.Collections.FSharpList"
// Only CLR Type metadata/readers are cached. Source values, checker cells,
// TypeIdentity conversions and identity maps are always freshly evaluated.
let private tuples = ConcurrentDictionary<Type, bool>()
let private records = ConcurrentDictionary<Type, bool>()
let private unions = ConcurrentDictionary<Type, bool>()
let private isTuple ty = tuples.GetOrAdd(ty, fun ty -> FSharpType.IsTuple ty)
let private isRecord ty = records.GetOrAdd(ty, fun ty -> FSharpType.IsRecord(ty, flags))
let private isUnion ty = unions.GetOrAdd(ty, fun ty -> FSharpType.IsUnion(ty, flags))
let private tupleReaders = ConcurrentDictionary<Type, obj -> objnull array>()
let private recordReaders = ConcurrentDictionary<Type, obj -> objnull array>()
let private recordFields = ConcurrentDictionary<Type, PropertyInfo array>()
let private unionReaders = ConcurrentDictionary<Type, (obj -> int) * Map<int, UnionCaseInfo * (obj -> objnull array)>>()
let private tupleValues (value: obj) = tupleReaders.GetOrAdd(value.GetType(), Func<Type, obj -> objnull array>(fun ty -> FSharpValue.PreComputeTupleReader ty)) value
let private recordValues (value: obj) = recordReaders.GetOrAdd(value.GetType(), Func<Type, obj -> objnull array>(fun ty -> FSharpValue.PreComputeRecordReader(ty, flags))) value
let private fields (ty: Type) = recordFields.GetOrAdd(ty, fun (ty: Type) -> FSharpType.GetRecordFields(ty, flags))
let private unionValues ty (value: obj) =
    let tag, cases = unionReaders.GetOrAdd(ty, fun ty ->
        FSharpValue.PreComputeUnionTagReader(ty, flags),
        FSharpType.GetUnionCases(ty, flags)
        |> Array.map (fun case -> case.Tag, (case, FSharpValue.PreComputeUnionReader(case, flags)))
        |> Map.ofArray)
    let case, reader = cases[tag value]
    case, reader value

let internal hash (text: string) = Encoding.UTF8.GetBytes text |> SHA256.HashData |> Convert.ToHexString

/// Canonicalize declaration/site incarnation stamps ("decl_<epochGuid>_<birth>_<hexPath>[/0/1]")
/// so fresh workspace epochs or incarnation numbers do not perturb canonical digests,
/// while preserving the exact length-prefixed source-unit + lexical declaration path.
let internal canonicalizeIncarnationStamp (text: string) =
    if not (text.StartsWith("decl_", StringComparison.Ordinal)) then text
    else
        let firstSep = text.IndexOf('_', 5)
        if firstSep <= 5 then text
        else
            let secondSep = text.IndexOf('_', firstSep + 1)
            if secondSep <= firstSep + 1 then text
            else "decl_canonical_" + text.Substring(secondSep + 1)

let private canonicalizeMetadataString (text: string) =
    if text.StartsWith("claim_", StringComparison.Ordinal) then
        let hex = text.Substring 6
        if hex.Length % 2 = 0 && (hex |> Seq.forall Uri.IsHexDigit) then
            let source = Encoding.UTF8.GetString(Convert.FromHexString hex)
            if source.StartsWith("decl_", StringComparison.Ordinal) then
                "claim_" + Convert.ToHexString(Encoding.UTF8.GetBytes(canonicalizeIncarnationStamp source))
            else text
        else text
    else canonicalizeIncarnationStamp text

let private isVolatileMetadataKey (key: string) =
    key = ElaborationMetadata.Id ||
    key = "ExpansionId" ||
    key = "SourceBinding.NameRange" ||
    key = "SourceBinding.FullRange"

/// Strip volatile per-check elaboration IDs and source-range trivia from node metadata.
let internal normalizeMetadataValue (value: MetadataValue) : MetadataValue =
    match value with
    | MetadataValue.SourceRange _ -> MetadataValue.SourceRange dummyRange
    | MetadataValue.String text -> MetadataValue.String(canonicalizeMetadataString text)
    | MetadataValue.StringList texts -> MetadataValue.StringList(List.map canonicalizeMetadataString texts)
    | other -> other

let internal normalizeMetadata (metadata: Map<string, MetadataValue>) : Map<string, MetadataValue> =
    metadata
    |> Map.toSeq
    |> Seq.choose (fun (key, value) ->
        if isVolatileMetadataKey key then None
        else Some(key, normalizeMetadataValue value))
    |> Map.ofSeq

let internal normalizePremiseMetadata
    (metadata: Map<string, string list * bigint list * NodeId list * TypeIdentity option>)
    : Map<string, string list * bigint list * NodeId list * TypeIdentity option> =
    metadata
    |> Map.toSeq
    |> Seq.choose (fun (key, (strings, ints, nodes, ty)) ->
        if isVolatileMetadataKey key then None
        else Some(key, (List.map canonicalizeIncarnationStamp strings, ints, nodes, ty)))
    |> Map.ofSeq

/// Program-site ObligationInfo.Source ends with ":line:col" (Obligations.fmtRange),
/// whereas platform-declaration obligations carry "<platform id>:<decl name>".
/// Strip trailing numeric line/column coordinates so line shifts do not churn proof digests.
let internal normalizeObligationSource (source: string) : string =
    if String.IsNullOrEmpty source then "site:"
    else
        let lastColon = source.LastIndexOf ':'
        if lastColon <= 0 then "decl:" + source
        else
            let secondLastColon = source.LastIndexOf(':', lastColon - 1)
            let isDigits (s: string) = s.Length > 0 && s |> Seq.forall Char.IsDigit
            if secondLastColon >= 0 &&
               isDigits (source.Substring(secondLastColon + 1, lastColon - secondLastColon - 1)) &&
               isDigits (source.Substring(lastColon + 1)) then
                "site:" + source.Substring(0, secondLastColon)
            else
                "decl:" + source

let internal normalizeObligationInfo (info: ObligationInfo) =
    (info.Kind, info.Logic, normalizeObligationSource info.Source, info.Refs, info.Body)

/// Length-delimited, culture-independent structural encoding. Types are frozen
/// here, while Baker still owns checker substitutions. SourceRange offsets,
/// volatile Elaboration.Id entries, and raw obligation anchors/line numbers are
/// normalized so source trivia and fresh check counters never cause churn.
/// Unknown identities or host objects refuse a separate region; they never disappear.
let private encoderWithMissing (identities: Map<NodeId, string>) missing =
    let rec encode (value: objnull) : string =
        let atom (text: string) = string text.Length + ":" + text
        match value with
        | null -> "null;"
        | :? NodeId as id ->
            match identities.TryFind id with
            | Some identity -> "node" + atom identity
            | None -> missing id
        | :? SourceRange -> "range;"
        | :? NativeType as ty -> encode (box (Clef.Compiler.NativeTypedTree.TypeIdentities.ofType ty))
        | :? ObligationInfo as info ->
            let kind, logic, source, refs, body = normalizeObligationInfo info
            atom "ObligationInfo" + "{" + encode (box (kind, logic, source, refs, body)) + "}"
        | :? BoundarySourcePremise as premise ->
            let normalized =
                (premise.Shape,
                 premise.EmbeddedTypes,
                 premise.ConstructorFacts,
                 premise.Reachable,
                 premise.Range,
                 premise.ExternLibrary,
                 premise.ExternSymbol,
                 premise.HasExtern,
                 normalizePremiseMetadata premise.Metadata)
            atom "BoundarySourcePremise" + "{" + encode (box normalized) + "}"
        | :? Map<string, MetadataValue> as metadata ->
            let normalized = normalizeMetadata metadata
            let ty = metadata.GetType()
            let tagged body = atom (typeName ty) + "{" + body + "}"
            normalized
            |> Map.toSeq
            |> Seq.map (fun (k, v) -> encode (box k) + encode (box v))
            |> Seq.sort
            |> String.concat ""
            |> tagged
        | :? string as text -> "string" + atom text
        | _ ->
            let value = value |> Option.ofObj |> Option.get
            let ty = value.GetType()
            let tagged body = atom (typeName ty) + "{" + body + "}"
            if isMap ty then
                (value :?> IEnumerable) |> Seq.cast<obj>
                |> Seq.map (fun item ->
                    encode (property "Key" item) + encode (property "Value" item))
                |> Seq.sort |> String.concat "" |> tagged
            elif isSet ty then
                (value :?> IEnumerable) |> Seq.cast<objnull> |> Seq.map encode |> Seq.sort |> String.concat "" |> tagged
            elif isList ty then
                // Incidence/proof inventories can contain tens of thousands of
                // rows. Enumerate the spine; reflecting each Cons recurses once
                // per row and exhausts the host stack on real programs.
                (value :?> IEnumerable) |> Seq.cast<objnull> |> Seq.map encode |> String.concat "" |> tagged
            elif isTuple ty then tupleValues value |> Array.map (fun field -> encode field) |> String.concat "" |> tagged
            elif isRecord ty then
                recordValues value |> Array.map (fun field -> encode field) |> String.concat "" |> tagged
            elif isUnion ty then
                let case, fields = unionValues ty value
                atom case.Name + (fields |> Array.map encode |> String.concat "") |> tagged
            elif ty.IsArray then
                (value :?> IEnumerable) |> Seq.cast<objnull> |> Seq.map encode |> String.concat "" |> tagged
            elif ty.IsEnum || ty.IsPrimitive || ty = typeof<decimal> || ty = typeof<System.Numerics.BigInteger> then
                match value with
                | :? IFormattable as number -> number.ToString(null, CultureInfo.InvariantCulture) |> atom |> tagged
                | _ -> string value |> atom |> tagged
            else invalidOp ("Unadmitted witness input type: " + ty.FullName)
    encode

let internal encoder (identities: Map<NodeId, string>) =
    encoderWithMissing identities (fun id -> invalidOp (sprintf "Region has source dependency %A outside its admitted interface." id))

let private tryEncoder (identities: Map<NodeId, string>) (value: objnull) =
    let mutable admitted = true
    let encode = encoderWithMissing identities (fun _ -> admitted <- false; "")
    let result = encode value
    if admitted then Some result else None

let internal nodeLabel (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.ModuleDef(name, _) -> "module:" + name
    | SemanticKind.Binding(name, _, _, _) -> "binding:" + name
    | SemanticKind.TypeDef(name, _, _) -> "type:" + name
    | SemanticKind.MemberDef(name, _, _) -> "member:" + name
    | SemanticKind.Obligation _ -> "claim"
    | _ -> "node"

let internal canonicalRelationIdentities
    (nodeAddresses: Map<NodeId, string>)
    (contracts: Map<NodeId, CallableContract>)
    (aggregateSlots: Map<NodeId, CallableAggregateSlot>)
    : Map<NodeId, string> =
    let rec collectRefs (value: objnull) : Set<NodeId> =
        match value with
        | null -> Set.empty
        | :? NodeId as id -> Set.singleton id
        | :? NativeType | :? SourceRange | :? string -> Set.empty
        | :? IEnumerable as items -> items |> Seq.cast<objnull> |> Seq.map collectRefs |> Set.unionMany
        | _ ->
            let v = value |> Option.ofObj |> Option.get
            let ty = v.GetType()
            if isTuple ty then tupleValues v |> Seq.map collectRefs |> Set.unionMany
            elif isRecord ty then recordValues v |> Seq.map collectRefs |> Set.unionMany
            elif isUnion ty then unionValues ty v |> snd |> Seq.map collectRefs |> Set.unionMany
            else Set.empty
    let withContracts =
        contracts
        |> Map.toList
        |> List.map (fun (key, row) ->
            if key <> row.Identity || nodeAddresses.ContainsKey key then
                invalidOp "A callable relation identity is misfiled or collides with another source identity."
            let implName =
                row.Participants
                |> List.filter (fun p -> p.Role = ParticipantRole.CallableImplementation && p.Group = row.Identity && p.Ordinal = 0)
                |> List.tryHead
                |> Option.bind (fun p -> Map.tryFind p.Node nodeAddresses)
                |> Option.defaultWith (fun () ->
                    row.Participants
                    |> List.choose (fun p -> Map.tryFind p.Node nodeAddresses)
                    |> List.sort
                    |> String.concat "|")
            let participantAddresses = row.Participants |> List.choose (fun p -> nodeAddresses.TryFind p.Node |> Option.map (fun addr -> addr, p.Role, p.Ordinal)) |> List.sort
            let keyShape = encoder nodeAddresses (box (implName, row.Kind, row.Convention, row.ParameterTypes, row.ResultType, participantAddresses))
            key, "callable-contract:" + implName + ":" + string row.Kind + ":" + string row.Convention, keyShape)
        |> List.groupBy (fun (_, label, _) -> label)
        |> List.collect (fun (baseLabel, group) ->
            group
            |> List.sortBy (fun (_, _, shape) -> shape)
            |> List.mapi (fun ordinal (key, _, _) ->
                key, if ordinal = 0 then baseLabel else baseLabel + "#" + string ordinal))
        |> List.fold (fun acc (k, v) -> Map.add k v acc) nodeAddresses
    let baseEncode = encoder withContracts
    aggregateSlots
    |> Map.toList
    |> List.map (fun (key, row) ->
        if key <> row.Identity || Map.containsKey key withContracts then
            invalidOp "A callable relation identity is misfiled or collides with another source identity."
        let refs =
            collectRefs (box row)
            |> Set.remove key
            |> Seq.choose withContracts.TryFind
            |> Seq.sort
            |> String.concat "|"
        let pathKey = baseEncode (box row.Path)
        key, "callable-aggregate-slot:" + refs + ":" + pathKey, baseEncode (box (row.AggregateType, row.SourceType)))
    |> List.groupBy (fun (_, label, _) -> label)
    |> List.collect (fun (baseLabel, group) ->
        group
        |> List.sortBy (fun (_, _, shape) -> shape)
        |> List.mapi (fun ordinal (key, _, _) ->
            key, if ordinal = 0 then baseLabel else baseLabel + "#" + string ordinal))
    |> List.fold (fun acc (k, v) -> Map.add k v acc) withContracts

/// Compute range-free, NodeId-independent, Elaboration.Id-independent canonical
/// structural addresses across the graph, disambiguating retired/detached/obligation
/// collisions deterministically without consulting SourceRange.
let internal canonicalAddresses (graph: SemanticGraph) : Result<Map<NodeId, string>, (NodeId option * string) list> =
    let cycleErrors = ResizeArray<NodeId option * string>()
    let baseAddresses = Collections.Generic.Dictionary<NodeId, string>()
    let visiting = Collections.Generic.HashSet<NodeId>()
    let platformRead = PlatformResolution.read graph
    match platformRead.Platform with
    | Some platform when platformRead.Findings.IsEmpty ->
        match platform.Core with
        | Some core ->
            let named =
                (core.Node, "numeric-core:" + platform.Id) ::
                (core.Widths |> List.map (fun row -> row.Node, "numeric-width:" + platform.Id + ":" + row.Name)) @
                (core.Representations |> List.map (fun row -> row.Node, "numeric-representation:" + platform.Id + ":" + row.Representation.Name))
            if (named |> List.map fst |> Set.ofList |> Set.count) <> named.Length ||
               (named |> List.map snd |> Set.ofList |> Set.count) <> named.Length then
                invalidOp "Platform has ambiguous numeric declaration identities."
            for id, address in named do
                baseAddresses.Add(id, address)
        | None -> ()
    | _ -> ()
    let nonObligations =
        graph.Nodes
        |> Map.toList
        |> List.filter (fun (_, node) -> match node.Kind with SemanticKind.Obligation _ -> false | _ -> true)
    let rec rawAddress (id: NodeId) : string =
        match baseAddresses.TryGetValue id with
        | true, existing -> existing
        | _ when not (visiting.Add id) ->
            cycleErrors.Add(Some id, "The lexical parent relation contains a cycle.")
            "cycle"
        | _ ->
            let node = graph.Nodes[id]
            let computed =
                match node.Parent |> Option.bind graph.Nodes.TryFind with
                | Some parent ->
                    let prefix = rawAddress parent.Id
                    match node.Kind, parent.Kind with
                    | (SemanticKind.Binding _ | SemanticKind.ModuleDef _ | SemanticKind.TypeDef _ | SemanticKind.MemberDef _), SemanticKind.ModuleDef _ ->
                        prefix + "/" + nodeLabel node
                    | (SemanticKind.Binding _ | SemanticKind.ModuleDef _ | SemanticKind.TypeDef _ | SemanticKind.MemberDef _), _ ->
                        match parent.Children |> List.tryFindIndex ((=) id) with
                        | Some index -> prefix + "/" + nodeLabel node + "@" + string index
                        | None -> prefix + "/" + nodeLabel node
                    | _ ->
                        match parent.Children |> List.tryFindIndex ((=) id) with
                        | Some index -> prefix + "/" + string index
                        | None -> prefix + "/" + nodeLabel node
                | None ->
                    match node.Kind with
                    | SemanticKind.ModuleDef _ | SemanticKind.Binding _ | SemanticKind.TypeDef _ | SemanticKind.MemberDef _ ->
                        nodeLabel node
                    | _ ->
                        "detached:" + nodeLabel node
            visiting.Remove id |> ignore
            baseAddresses[id] <- computed
            computed
    for id, _ in nonObligations do
        rawAddress id |> ignore
    if cycleErrors.Count > 0 then
        Result.Error(List.ofSeq cycleErrors)
    else
        // Disambiguate any non-obligation nodes sharing a raw address (e.g. retired
        // unreachable fold-in nodes or detached comparison prefixes) without SourceRange.
        let shapeTag (node: SemanticNode) =
            let frozenTy = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type
            let kindTag =
                match node.Kind with
                | SemanticKind.Intrinsic info -> sprintf "intrinsic:%A:%s" info.Module info.Operation
                | SemanticKind.Literal lit -> sprintf "literal:%A" lit
                | SemanticKind.VarRef(name, _) -> "varref:" + name
                | SemanticKind.Application(_, args) -> sprintf "app:%d" args.Length
                | SemanticKind.PatternBinding name -> "pat:" + name
                | SemanticKind.Binding(name, m, r, d) -> sprintf "binding:%s:%b:%b:%A" name m r d
                | other ->
                    match box other with
                    | null -> invalidOp "Null semantic kind"
                    | value ->
                        let case, _ = unionValues typeof<SemanticKind> value
                        "kind:" + case.Name
            let childRaw =
                node.Children
                |> List.map (fun cid ->
                    match baseAddresses.TryGetValue cid with
                    | true, addr -> addr
                    | _ -> invalidOp (sprintf "Child %A has no canonical address." cid))
                |> String.concat ","
            sprintf "%b|%s|%A|%s" node.IsReachable kindTag frozenTy childRaw
        let settledParentAddress (addresses: Collections.Generic.Dictionary<NodeId, string>) id =
            match addresses.TryGetValue id with
            | true, address -> Some address
            | _ -> None
        let attached =
            nonObligations
            |> List.filter (fun (id, _) -> not (baseAddresses[id].StartsWith("detached:", StringComparison.Ordinal)))
            |> List.groupBy (fun (id, _) -> baseAddresses[id])
            |> List.collect (fun (addr, group) ->
                group |> List.sortBy (fun (id, node) ->
                    (if node.IsReachable then 0 else 1), shapeTag node,
                    (node.Parent |> Option.bind (settledParentAddress baseAddresses)),
                    (node.Parent |> Option.bind graph.Nodes.TryFind |> Option.bind (fun parent -> parent.Children |> List.tryFindIndex ((=) id))))
                |> List.mapi (fun ordinal (id, _) -> id, addr + (if ordinal = 0 then "" else "#" + string ordinal)))
            |> Map.ofList
        let membership id =
            graph.Codata.Value.CallableContracts.Values
            |> Seq.collect (fun contract ->
                let owner =
                    contract.Participants
                    |> List.filter (fun p -> p.Role = ParticipantRole.CallableImplementation)
                    |> List.choose (fun p -> attached.TryFind p.Node)
                    |> List.sort |> String.concat "|"
                contract.Participants
                |> Seq.filter (fun p -> p.Node = id)
                |> Seq.map (fun p -> sprintf "%s:%A:%A:%A:%d" owner contract.Kind contract.Convention p.Role p.Ordinal))
            |> Seq.sort |> String.concat "|"
        let settledNonObligations =
            nonObligations
            |> List.filter (fun (id, _) -> not (attached.ContainsKey id))
            |> List.groupBy (fun (id, node) -> baseAddresses[id], hash (shapeTag node + "|" + membership id))
            |> List.collect (fun ((addr, digest), group) ->
                group |> List.mapi (fun ordinal (id, _) ->
                    id, addr + ":" + digest.Substring(0, 16) + (if ordinal = 0 then "" else "#" + string ordinal)))
            |> List.fold (fun acc (id, addr) -> Map.add id addr acc) attached
        let known = canonicalRelationIdentities settledNonObligations graph.Codata.Value.CallableContracts graph.Codata.Value.CallableAggregateSlots
        let incidentByTarget = graph.Edges |> List.groupBy _.Target |> Map.ofList
        let obligations =
            graph.Nodes |> Map.toList |> List.choose (fun (id, node) ->
                match node.Kind with SemanticKind.Obligation info -> Some(id, info) | _ -> None)
        let rec references (value: objnull) : Set<NodeId> =
            match value with
            | null -> Set.empty
            | :? NodeId as id -> Set.singleton id
            | :? NativeType | :? SourceRange | :? string -> Set.empty
            | :? IEnumerable as items -> items |> Seq.cast<objnull> |> Seq.map references |> Set.unionMany
            | _ ->
                let v = value |> Option.ofObj |> Option.get
                let ty = v.GetType()
                if isTuple ty then tupleValues v |> Seq.map references |> Set.unionMany
                elif isRecord ty then recordValues v |> Seq.map references |> Set.unionMany
                elif isUnion ty then unionValues ty v |> snd |> Seq.map references |> Set.unionMany
                else Set.empty
        let incident id = incidentByTarget |> Map.tryFind id |> Option.defaultValue []
        let dependencies id info =
            Set.union (references (box info)) (incident id |> Seq.collect _.Sources |> Set.ofSeq)
        let obligationKey addresses id info =
            let encode = encoder addresses
            let edges =
                incident id
                |> List.map (fun edge -> encode (box (edge.Class, edge.Ordinal, edge.Sources)))
                |> List.sort |> String.concat ";"
            hash (edges + "|" + encode (box info))
        let anchor (addresses: Map<NodeId, string>) id =
            let node = graph.Nodes[id]
            let parent = node.Parent |> Option.bind addresses.TryFind |> Option.defaultValue ""
            let index = node.Parent |> Option.bind graph.Nodes.TryFind |> Option.bind (fun p -> p.Children |> List.tryFindIndex ((=) id))
            parent, index
        let assign (addresses: Map<NodeId, string>) (entries: (NodeId * string) list) =
            entries
            |> List.groupBy snd
            |> List.fold (fun state (digest, group) ->
                group |> List.sortBy (fun (id, _) -> anchor addresses id)
                |> List.mapi (fun ordinal (id, _) ->
                    id, "claim:" + digest.Substring(0, 24) + (if ordinal = 0 then "" else "#" + string ordinal))
                |> List.fold (fun acc (id, value) -> Map.add id value acc) state) addresses
        let rec resolve (addresses: Map<NodeId, string>) pending =
            let ready, rest = pending |> List.partition (fun (id, info) -> dependencies id info |> Set.forall addresses.ContainsKey)
            if not ready.IsEmpty then
                let entries = ready |> List.map (fun (id, info) -> id, obligationKey addresses id info)
                resolve (assign addresses entries) rest
            elif rest.IsEmpty then Result.Ok addresses
            else
                let unresolved = rest |> List.map fst |> Set.ofList
                let missing = rest |> List.collect (fun (id, info) -> dependencies id info |> Set.toList) |> Set.ofList |> Set.filter (fun id -> not (addresses.ContainsKey id || unresolved.Contains id))
                if not missing.IsEmpty then
                    Result.Error [ None, "Obligation references an unindexed identity." ]
                else
                    let shape =
                        rest |> List.map (fun (id, info) ->
                            let placeholders = unresolved |> Set.fold (fun acc target -> Map.add target "scc-obl" acc) addresses
                            id, "scc-obl:" + obligationKey placeholders id info) |> Map.ofList
                    let mutable refined = Map.fold (fun acc id value -> Map.add id value acc) addresses shape
                    for _ in 1 .. 2 do
                        let next = rest |> List.map (fun (id, info) -> id, "scc-obl:" + obligationKey refined id info)
                        refined <- List.fold (fun acc (id, value) -> Map.add id value acc) addresses next
                    rest |> List.map (fun (id, info) -> id, obligationKey refined id info) |> assign addresses |> Result.Ok
        resolve known obligations

/// Scope only domain indices. The selected row's complete value (including
/// every participant and negative/absence observation) is encoded without
/// pruning. A newly added domain field therefore enters the key automatically.
let private scoped (members: Set<NodeId>) (types: Set<TypeIdentity>) encode (value: objnull) =
    let rec walk (value: objnull) =
        if isNull value then encode value else
        let value = value |> Option.ofObj |> Option.get
        let ty = value.GetType()
        if isMap ty && ty.GetGenericArguments()[0] = typeof<NodeId> then
            (value :?> IEnumerable) |> Seq.cast<obj>
            |> Seq.choose (fun row ->
                let key = property "Key" row :?> NodeId
                if members.Contains key then Some (encode (box key) + encode (property "Value" row)) else None)
            |> Seq.sort |> String.concat "|"
        elif isMap ty && ty.GetGenericArguments()[0] = typeof<TypeIdentity> then
            // A scalar region reads representations of its own occurrence
            // types. Unrelated declarations may contain fresh checker binder
            // identities on every check; they are not this region's interface.
            // Retain every selected row intact, just as for node-indexed facts.
            (value :?> IEnumerable) |> Seq.cast<obj>
            |> Seq.choose (fun row ->
                let key = property "Key" row |> Option.ofObj |> Option.defaultWith (fun () -> invalidOp "Null source type identity")
                let key = key :?> TypeIdentity
                if types.Contains key then Some (encode (box key) + encode (property "Value" row)) else None)
            |> Seq.sort |> String.concat "|"
        elif isSet ty && ty.GetGenericArguments()[0] = typeof<NodeId> then
            (value :?> IEnumerable) |> Seq.cast<NodeId> |> Seq.filter members.Contains
            |> Seq.map (box >> encode) |> Seq.sort |> String.concat "|"
        elif isRecord ty then
            fields ty
            |> Array.map (fun field -> field.Name + "=" + walk (field.GetValue value))
            |> String.concat ";"
        else encode value
    walk value

/// The independent cohort has no calls, storage, effects, aggregate
/// transports, nested declarations or external reads. Extending this grammar
/// requires extending its complete source interface, not a witness heuristic.
/// A settled comparison is an intrinsic operation, not a foreign invocation.
let private supported root (members: Set<NodeId>) (comparisons: Set<NodeId>) (callees: Set<NodeId>) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Lambda(_, _, [], _, LambdaContext.RegularClosure) -> node.Id = root
    | SemanticKind.PatternBinding _ -> true
    | SemanticKind.Literal (NativeLiteral.String _ | NativeLiteral.ByteArray _ | NativeLiteral.UInt16Array _) -> false
    | SemanticKind.Literal _ -> true
    | SemanticKind.VarRef(_, Some definition) -> members.Contains definition
    | SemanticKind.Binding(_, false, false, None) -> true
    | SemanticKind.Sequential _ | SemanticKind.IfThenElse _ | SemanticKind.TypeAnnotation _ -> true
    | SemanticKind.Application _ -> comparisons.Contains node.Id
    | SemanticKind.Intrinsic _ -> callees.Contains node.Id
    | _ -> false

let private comparison (graph: SemanticGraph) (members: Set<NodeId>) (operation: NumericOperationWitness) =
    match graph.Nodes.TryFind operation.Site, graph.Nodes.TryFind operation.Callee with
    | Some { Kind = SemanticKind.Application(callee, actuals) },
      Some { Kind = SemanticKind.Intrinsic info; Children = [] }
        when members.Contains operation.Callee && callee = operation.Callee &&
             actuals = (operation.Operands |> List.map _.Actual) && List.forall members.Contains actuals &&
             info.Module = IntrinsicModule.Operators &&
             Clef.Compiler.Baker.Ingredients.NumericOperations.comparison operation.Kind &&
             Clef.Compiler.Baker.Ingredients.NumericOperations.classify info.Operation = Some operation.Kind &&
             operation.Form = NumericOperationForm.Real &&
             Clef.Compiler.Baker.Ingredients.NumericOperations.requiredBodies operation = Some [] -> true
    | _ -> false

/// Proof citizens are re-discharged in the current whole graph. Their identities
/// stay in Supports; the complete held value and format authority remain here.
let private operationInput (operation: NumericOperationWitness) =
    let carrier (value: ScalarCarrier) = { value with Obligations = []; Participants = Set.empty }
    { operation with
        Operands = operation.Operands |> List.map (fun operand -> { operand with Carrier = operand.Carrier |> Option.map carrier })
        Result = carrier operation.Result
        Obligations = []; Participants = Set.empty }

/// A closed typed interface for numeric declarations, including the complete
/// offered set whose uniqueness the source recipe inspected. This does not
/// serialize an arbitrary external graph or infer identity from physical width.
let private tryNumericInterface (graph: SemanticGraph) (operations: NumericOperationWitness list) =
    let read = PlatformResolution.read graph
    match read.Platform |> Option.filter (fun _ -> read.Findings.IsEmpty) with
    | None -> None
    | Some platform ->
      match platform.Core with
      | None -> None
      | Some core ->
          let named =
              (core.Node, "numeric-core:" + platform.Id) ::
              (core.Widths |> List.map (fun row -> row.Node, "numeric-width:" + platform.Id + ":" + row.Name)) @
              (core.Representations |> List.map (fun row -> row.Node, "numeric-representation:" + platform.Id + ":" + row.Representation.Name))
          if (named |> List.map fst |> Set.ofList |> Set.count) <> named.Length then
              invalidOp "Comparison region has duplicate source declaration nodes."
          if (named |> List.map snd |> Set.ofList |> Set.count) <> named.Length then None
          elif operations |> List.forall (fun operation -> core.Representations |> List.exists (fun row ->
              operation.Declaration = Some row.Node && operation.Representation = Some row.Representation)) then
              Some (Map.ofList named, platform.Id, core)
          else None

let private childOrder (graph: SemanticGraph) root =
    let rec visit seen id =
        if Set.contains id seen then None else
        match graph.Nodes.TryFind id with
        | None -> None
        | Some node ->
            node.Children |> List.fold (fun state child ->
                state |> Option.bind (fun (seen, order) ->
                    visit seen child |> Option.map (fun (next, descendants) -> next, order @ descendants)))
                (Some (Set.add id seen, [id]))
    visit Set.empty root |> Option.map snd

/// Flattening an intrinsic application retains its intermediate partial
/// application in the rewrite record. It is not a second live owner of the
/// actual. Admit only the exact detached, unreachable prefix of this settled
/// comparison; its nodes remain Common and in the current proof supports.
let private retiredComparisonPrefix (graph: SemanticGraph) (operations: NumericOperationWitness list) id (parent: SemanticNode) =
    if parent.IsReachable || parent.Parent.IsSome then false else
    match parent.Kind with
    | SemanticKind.Application(callee, actuals) when parent.Children = callee :: actuals && List.contains id actuals ->
        operations |> List.exists (fun operation ->
            let settled = operation.Operands |> List.map _.Actual
            actuals.Length < settled.Length && actuals = List.take actuals.Length settled &&
            match graph.Nodes.TryFind callee, graph.Nodes.TryFind operation.Callee with
            | Some { Kind = SemanticKind.Intrinsic old }, Some { Kind = SemanticKind.Intrinsic current } -> old = current
            | _ -> false)
    | _ -> false

let private nodeInput (node: SemanticNode) =
    // Range and diagnostic metadata do not enter scalar emission. All fields
    // published to scalar witnesses do; obligation anchors are separately
    // retained in the complete incident proof relations below.
    box (node.Id, node.Kind, node.Type, node.SRTPResolution, node.ArenaAffinity, node.LayoutHint,
         node.Children, node.Parent, normalizeMetadata node.Metadata,
         node.IsReachable, node.EmissionStrategy, node.ValueRange)

let internal platformLayoutCensus (platformOpt: PlatformContext option) : ProofSupportCensus list =
    match platformOpt with
    | None -> []
    | Some platform ->
        let dimEntries =
            platform.Dimensions
            |> Map.toSeq
            |> Seq.map (fun (k, v) -> sprintf "dim:%s=%d" k v)
        let repEntries =
            platform.Representations
            |> Map.toSeq
            |> Seq.map (fun (k, r) ->
                sprintf "rep:%s:%s:%s:%d:%s:%s:%s" k r.Capability r.Family r.Bits r.MinMagnitude r.MaxMagnitude r.Boundary)
        let baseEntries =
            [ yield "id:" + (if String.IsNullOrWhiteSpace platform.PlatformId then "default" else platform.PlatformId)
              yield sprintf "substrate:%A" platform.SubstrateKind
              yield sprintf "runtime:%A" platform.RuntimeModel ]
        let entries =
            Seq.concat [ Seq.ofList baseEntries; dimEntries; repEntries ]
            |> Set.ofSeq
        let idSuffix = if String.IsNullOrWhiteSpace platform.PlatformId then "default" else platform.PlatformId
        [ { Identity = "platform-layout:" + idSuffix
            Kind = ProofSupportCensusKind.PlatformLayout
            Entries = entries } ]

let internal platformSpaceCensus (graph: SemanticGraph) : ProofSupportCensus list =
    let read = PlatformResolution.read graph
    match read.Platform with
    | Some platform when read.Findings.IsEmpty && not platform.Spaces.IsEmpty ->
        let entries =
            platform.Spaces
            |> List.map (fun space -> sprintf "space:%s:%d:%d:%d:%A" space.Name space.Capacity space.Alignment space.Granularity space.Kind)
            |> Set.ofList
        [ { Identity = "platform-space:" + platform.Id
            Kind = ProofSupportCensusKind.PlatformSpace
            Entries = entries } ]
    | _ -> []

let project (graph: SemanticGraph) (emission: WitnessEmissionProjection) (liveScope: WitnessLiveScopePlan) : WitnessSegmentation =
    let codata = { graph.Codata.Value with WitnessEmission = None; WitnessSegmentation = None; WitnessLiveScope = None; WitnessPreparedRows = None; WitnessLiveRows = None; WitnessPublishedRows = None; ProofDispatch = None; SSAAssignment = None }
    // Relation identities are not executable citizens. Admit only the two
    // authored relation tables, with exact filing and source/codata agreement;
    // every other unknown NodeId remains an error in the structural encoder.
    if emission.Callable.Contracts <> codata.CallableContracts ||
       emission.Callable.AggregateSlots <> codata.CallableAggregateSlots then
        invalidOp "Callable relation tables disagree with their current source codata."
    let graphAddresses =
        match canonicalAddresses graph with
        | Result.Ok addresses -> addresses
        | Result.Error errors ->
            invalidOp ("Graph has cyclic parent containment during witness segmentation: " + (errors |> List.map snd |> String.concat "; "))
    let canonicalAllIdentities =
        graphAddresses
    let encodeProof = encoder canonicalAllIdentities
    let resolveProofAddress (id: NodeId) =
        match canonicalAllIdentities.TryFind id with
        | Some addr when not (String.IsNullOrWhiteSpace addr) -> addr
        | _ -> invalidOp (sprintf "Proof reference %A has no canonical address." id)
    // Evidence supports remain current graph citizens and are discharged anew
    // for every revision. The realization key compares the settled interface those
    // proofs justify, while CanonicalProofSupportDigest records complete proof premises.
    let witnessInputs =
        { emission with
            Callable = { emission.Callable with Supports = Map.empty }
            Numeric = { emission.Numeric with
                            Values = emission.Numeric.Values |> Map.map (fun _ carrier ->
                                { carrier with Declaration = None; Obligations = []; Participants = Set.empty })
                            Operations = emission.Numeric.Operations |> Map.map (fun _ operation -> operationInput operation) }
            Storage = { emission.Storage with Startup = None; ProgramStorage = ProgramStorageInventory.empty
                                              LiteralPoolAnchors = [] } }
    let localCodata = { codata with ProgramStorage = ProgramStorageInventory.empty }
    let candidate (declaration: CallableEmissionDeclaration) =
        match declaration.Name, graph.Nodes.TryFind declaration.Lookup with
        | CallableSymbolName.ModuleBinding(moduleName, name), Some binding
            when binding.Children = [declaration.Implementation] && declaration.Lookup <> declaration.Implementation ->
            let root = declaration.Implementation
            match childOrder graph root with
            | None -> None
            | Some ordered ->
                let members = Set.ofList ordered
                let own = members.Add binding.Id
                let contracts =
                    emission.Callable.Contracts |> Map.filter (fun _ (contract: CallableContract) ->
                        match contract.Participants |> List.filter (fun participant -> participant.Role = ParticipantRole.CallableImplementation) with
                        | [implementation] when implementation.Group = contract.Identity && implementation.Ordinal = 0 ->
                            own.Contains implementation.Node
                        | _ -> false)
                let comparisons = emission.Numeric.Operations.Values |> Seq.filter (fun operation -> members.Contains operation.Site) |> Seq.filter (comparison graph members) |> Seq.toList
                let comparisonSites = comparisons |> List.map _.Site |> Set.ofList
                let comparisonCallees = comparisons |> List.map _.Callee |> Set.ofList
                let eligible =
                    binding.IsReachable && declaration.Captures.IsEmpty &&
                    (contracts.Values |> Seq.forall (fun contract -> contract.Kind <> CallableKind.NativeEntry)) &&
                    not (codata.DeclarationRootLambdas.ContainsKey root) &&
                    not (codata.Closures.ContainsKey root || emission.Callable.TakesEnvironment.Contains root) &&
                    (Set.intersect own emission.Boundary.DeclarationLeaves |> Set.isEmpty) &&
                    (Set.intersect own emission.Boundary.DeclarationOnly |> Set.isEmpty) &&
                    (emission.Storage.Startup |> Option.forall (fun startup -> startup.EntryLambda <> root)) &&
                    (ordered |> List.forall (fun id -> supported root members comparisonSites comparisonCallees graph.Nodes[id])) &&
                    (ordered |> List.forall (fun id ->
                        id = root || comparisonCallees.Contains id ||
                        match emission.Numeric.OccurrenceRepresentations.TryFind id with
                        | Some (Ok (ValueRepresentation.Scalar (SettledSlot.Integer _ | SettledSlot.Bool | SettledSlot.Char | SettledSlot.Real _ | SettledSlot.Unit))) -> true
                        | _ -> false)) &&
                    (ordered |> List.forall (fun id ->
                        graph.Nodes.Values |> Seq.forall (fun parent ->
                            not (List.contains id parent.Children) || own.Contains parent.Id || retiredComparisonPrefix graph comparisons id parent)))
                if not eligible then None else
                let parent = binding.Parent |> Option.bind graph.Nodes.TryFind
                match parent with
                | Some parent when (match parent.Kind with SemanticKind.ModuleDef _ -> true | _ -> false) ->
                    let identities =
                        ordered |> List.mapi (fun index id -> id, "member:" + string index) |> Map.ofList
                        |> Map.add binding.Id "binding" |> Map.add parent.Id ("module:" + moduleName)
                    // Joint premises stay intact in the current whole proof
                    // envelope. Preserve their complete incidence as supports,
                    // without treating a caller's identity as a function body.
                    let relations = graph.Edges |> List.filter (fun edge ->
                        members.Contains edge.Target || edge.Sources |> List.exists members.Contains)
                    let supports =
                        relations |> List.fold (fun support edge -> Set.union support (Set.ofList (edge.Target :: edge.Sources))) (own.Add parent.Id)
                    let supports =
                        emission.Callable.Supports |> Map.fold (fun support id participants ->
                            if own.Contains id then Set.union support participants else support) supports
                    let supports =
                        emission.Numeric.Values |> Map.fold (fun support id carrier ->
                            if own.Contains id then
                                Set.union support carrier.Participants
                                |> Set.union (Set.ofList (carrier.Obligations @ Option.toList carrier.Declaration))
                            else support) supports
                    let supports =
                        comparisons |> List.fold (fun support operation ->
                            Set.union support operation.Participants
                            |> Set.union (Set.ofList (operation.Obligations @ Option.toList operation.Declaration))
                            |> Set.union operation.Result.Participants
                            |> Set.union (Set.ofList operation.Result.Obligations)
                            |> fun support -> operation.Operands |> List.fold (fun support operand ->
                                match operand.Carrier with
                                | Some carrier -> Set.union support carrier.Participants |> Set.union (Set.ofList (carrier.Obligations @ Option.toList carrier.Declaration))
                                | None -> support) support) supports
                    let numeric =
                        if comparisons.IsEmpty then Some (Map.empty, "", None)
                        else tryNumericInterface graph comparisons |> Option.map (fun (ids, platformId, core) -> ids, platformId, Some core)
                    match numeric with
                    | None -> None
                    | Some (interfaces, corePlatformId, core) ->
                        if interfaces.Keys |> Seq.exists identities.ContainsKey then
                            invalidOp "Numeric declaration is not external to its scalar region."
                        let identities = Map.fold (fun identities id name -> Map.add id name identities) identities interfaces
                        let contractNames = contracts |> Map.map (fun _ contract ->
                            let implementation = contract.Participants |> List.find (fun participant -> participant.Role = ParticipantRole.CallableImplementation)
                            "callable-contract:" + identities[implementation.Node])
                        if (contractNames.Values |> Set.ofSeq |> Set.count) <> contractNames.Count then
                            invalidOp "A scalar interface has ambiguous receiving contract identities."
                        let identities = Map.fold (fun names id name ->
                            if Map.containsKey id names then invalidOp "A callable contract collides with its scalar interface."
                            Map.add id name names) identities contractNames
                        // Only the realization/interface digests separate proof
                        // support from the settled receiving interface. Full
                        // signature/physical maps and local roles stay encoded;
                        // complete public rows and current proof discharge are
                        // unchanged, and CanonicalProofSupportDigest encodes the
                        // complete proof premises and closed-world censuses.
                        let contractInterface = contracts |> Map.map (fun _ contract ->
                            { contract with
                                SourcePremises = Map.empty
                                Participants = contract.Participants |> List.filter (fun participant -> participant.Role <> ParticipantRole.Source) })
                        let contractSupports = contracts.Values |> Seq.collect (fun contract ->
                            contract.Participants |> Seq.map (fun (participant: Participant) -> participant.Node) |> Seq.filter graph.Nodes.ContainsKey) |> Set.ofSeq
                        let supports = Set.union supports contractSupports
                        // Numeric selection reads the source declaration family,
                        // including absence/uniqueness. Fresh whole-graph proof
                        // remains mandatory; retain its complete current support.
                        let supports =
                            if comparisons.IsEmpty then supports else
                            Set.union supports (graph.Nodes.Keys |> Set.ofSeq)
                        let mutable admitted = true
                        let encode value =
                            match tryEncoder identities value with
                            | Some encoded -> encoded
                            | None -> admitted <- false; ""
                        let ownTypes = own |> Set.map (fun id -> Clef.Compiler.NativeTypedTree.TypeIdentities.ofType graph.Nodes[id].Type)
                        let ownFacts = Set.union own (contractNames.Keys |> Set.ofSeq)
                        let scope value = scoped ownFacts ownTypes encode value
                        // List-shaped boundary rows are selected by their owner.
                        let ownedHypotheses =
                            witnessInputs.Boundary.ResultHypotheses |> List.filter (fun row -> own.Contains row.Declaration)
                        let ownedUses =
                            witnessInputs.Numeric.ForeignResultUses |> List.filter (fun row -> members.Contains row.Application.Call)
                        // Link requirements belong to the declarations that import them.
                        let ownedLinks =
                            witnessInputs.Boundary.Imports.Values
                            |> Seq.filter (fun import -> own.Contains import.Binding)
                            |> Seq.map _.Library |> Set.ofSeq
                        let witnessInputs =
                            { witnessInputs with
                                Callable = { witnessInputs.Callable with Contracts = contractInterface }
                                Boundary = { witnessInputs.Boundary with ResultHypotheses = ownedHypotheses; Links = ownedLinks }
                                Numeric = { witnessInputs.Numeric with ForeignResultUses = ownedUses } }
                        let localCodata = { localCodata with CallableContracts = contractInterface }
                        let regionIdentity = "callable:" + moduleName + ":" + name
                        // 1. CallableInterfaceDigest: signature TypeIdentity, parameter/return ValueRepresentation,
                        // PassBy/ByrefKind, escape/arena summary, and settled CallableContract interface boundary.
                        let rootNode = graph.Nodes[root]
                        let lambdaParameters =
                            match rootNode.Kind with
                            | SemanticKind.Lambda(parameters, _, captures, _, context) ->
                                let paramSummary =
                                    parameters |> List.map (fun (paramName, paramType, paramId) ->
                                        let pNode = graph.Nodes[paramId]
                                        let pRep = emission.Numeric.OccurrenceRepresentations |> Map.tryFind paramId
                                        let pEscape = codata.Escapes |> Map.tryFind paramId
                                        paramName, paramType, pNode.ArenaAffinity, pNode.LayoutHint, pRep, pEscape)
                                box (paramSummary, captures, context)
                            | _ -> box rootNode.Kind
                        let interfaceMembers =
                            match rootNode.Kind with
                            | SemanticKind.Lambda(parameters, _, _, _, _) ->
                                Set.ofList (binding.Id :: root :: (parameters |> List.map (fun (_, _, pid) -> pid)))
                            | _ -> Set.ofList [ binding.Id; root ]
                        let interfaceFacts = Set.union interfaceMembers (contractNames.Keys |> Set.ofSeq)
                        let interfaceTypes =
                            interfaceMembers
                            |> Set.map (fun id -> Clef.Compiler.NativeTypedTree.TypeIdentities.ofType graph.Nodes[id].Type)
                        let scopeInterface value = scoped interfaceFacts interfaceTypes encode value
                        let platformInterface =
                            graph.Platform |> Option.map (fun p ->
                                p.PlatformId, p.SubstrateKind, p.RuntimeModel, p.Dimensions)
                        let callableInterfacePreimage =
                            [ "callable-interface-v1"
                              regionIdentity
                              moduleName
                              name
                              encode (box (binding.Kind, binding.Type, binding.SRTPResolution, binding.ArenaAffinity, binding.LayoutHint, binding.IsReachable, binding.EmissionStrategy, normalizeMetadata binding.Metadata))
                              encode (box (rootNode.Type, rootNode.SRTPResolution, rootNode.ArenaAffinity, rootNode.LayoutHint, rootNode.EmissionStrategy, normalizeMetadata rootNode.Metadata))
                              encode lambdaParameters
                              encode (box (emission.Numeric.OccurrenceRepresentations |> Map.tryFind root))
                              scopeInterface (box contractInterface)
                              scopeInterface (box witnessInputs.Callable.Carriers)
                              scopeInterface (box witnessInputs.Callable.ValueShapes)
                              scopeInterface (box witnessInputs.Callable.TakesEnvironment)
                              scopeInterface (box localCodata.Escapes)
                              encode (box ownedLinks)
                              encode (box ownedHypotheses)
                              encode (box platformInterface) ]
                            |> String.concat "\n"
                        let callableInterfaceDigest =
                            CallableInterfaceDigest(CallableInterfaceDigest.DomainPrefix + hash callableInterfacePreimage)
                        // 2. SemanticRealizationDigest: range-invariant region body + own/referenced CallableInterfaceDigest
                        // + scoped TypeIdentity representations (SourceRange and /// doc trivia excluded).
                        let realizationInputs =
                            [ "semantic-realization-v1"
                              (if comparisons.IsEmpty then "scalar-v1" else "scalar-comparison-v1")
                              moduleName
                              name
                              callableInterfaceDigest.Value
                              ordered |> List.map (fun id -> encode (nodeInput graph.Nodes[id])) |> String.concat "|"
                              encode (box binding.Kind)
                              scope (box witnessInputs)
                              scope (box localCodata)
                              encode (box graph.Platform)
                              ordered |> List.collect (fun id -> kindEdges id graph.Nodes[id].Kind) |> box |> encode ]
                            @ (core |> Option.map (fun value -> [encode (box value)]) |> Option.defaultValue [])
                        let semanticRealizationDigest =
                            SemanticRealizationDigest(SemanticRealizationDigest.DomainPrefix + hash (String.concat "\n" realizationInputs))
                        // 3. CanonicalProofSupportDigest + ProofSupportCoverage: complete obligation premises,
                        // participant roles/ordinals, and closed-world platform/numeric/absence censuses with
                        // volatile Elaboration.Id, raw NodeIds, and SourceRange stripped.
                        let contractParticipants =
                            contracts.Values
                            |> Seq.collect (fun contract ->
                                contract.Participants |> Seq.map (fun p ->
                                    ({ Address = resolveProofAddress p.Node; Role = p.Role;
                                        Ordinal = p.Ordinal; Group = resolveProofAddress p.Group } : ProofSupportParticipant)))
                        let scopedProofRelations =
                            let admittedSupportNodes =
                                Set.union own (interfaces.Keys |> Set.ofSeq)
                            relations
                            |> List.filter (fun edge ->
                                edge.Class = EdgeClass.Obligation ||
                                (match graph.Nodes.TryFind edge.Target with Some { Kind = SemanticKind.Obligation _ } -> true | _ -> false) ||
                                (edge.Target :: edge.Sources |> List.forall admittedSupportNodes.Contains))
                        let relationParticipants =
                            scopedProofRelations
                            |> Seq.collect (fun edge ->
                                let groupAddr = resolveProofAddress edge.Target
                                edge.Sources |> List.mapi (fun idx src ->
                                    ({ Address = resolveProofAddress src; Role = ParticipantRole.Source;
                                       Ordinal = edge.Ordinal * 1024 + idx; Group = groupAddr } : ProofSupportParticipant)))
                        let participants =
                            Seq.append contractParticipants relationParticipants
                            |> Seq.distinct
                            |> Seq.sortBy (fun (p: ProofSupportParticipant) -> p.Group, p.Ordinal, p.Role, p.Address)
                            |> Seq.toList
                        let branchAbsenceCensus =
                            { Identity = "callable-branch-absence:whole-revision"
                              Kind = ProofSupportCensusKind.BoundaryAbsence
                              Entries = Set.singleton (sprintf "observations:%d" emission.Callable.Branches.Observations.Count) }
                        let numericCensuses =
                            match core with
                            | None -> []
                            | Some resolvedCore ->
                                let widthEntries =
                                    resolvedCore.Widths
                                    |> List.map (fun w -> sprintf "width:%s:%d" w.Name w.Bits)
                                let repEntries =
                                    resolvedCore.Representations
                                    |> List.map (fun r ->
                                        let rep = r.Representation
                                        sprintf "rep:%s:%s:%s:%d:%s:%s:%s" rep.Name rep.Capability rep.Family rep.Bits rep.MinMagnitude rep.MaxMagnitude rep.Boundary)
                                let interfaceEntries = interfaces.Values |> Seq.map (fun label -> "decl:" + label) |> Seq.toList
                                [ { Identity = "numeric-interface:" + corePlatformId
                                    Kind = ProofSupportCensusKind.NumericInterface
                                    Entries = Set.ofList (("core:" + corePlatformId) :: widthEntries @ repEntries @ interfaceEntries) } ]
                        let censuses =
                            [ if not (ownedHypotheses.IsEmpty && ownedUses.IsEmpty && ownedLinks.IsEmpty) then yield branchAbsenceCensus
                              yield! platformLayoutCensus graph.Platform
                              yield! platformSpaceCensus graph
                              yield! numericCensuses ]
                            |> List.sortBy (fun c -> c.Kind, c.Identity)
                        let ownedObligationIds =
                            let fromCarriers =
                                emission.Numeric.Values
                                |> Map.toSeq
                                |> Seq.collect (fun (id, carrier) -> if own.Contains id then carrier.Obligations else [])
                            let fromComparisons =
                                comparisons
                                |> Seq.collect (fun op ->
                                    op.Obligations @ op.Result.Obligations @
                                    (op.Operands |> List.collect (fun o -> o.Carrier |> Option.map _.Obligations |> Option.defaultValue [])))
                            let fromRelations =
                                relations
                                |> Seq.choose (fun edge ->
                                    match graph.Nodes.TryFind edge.Target with
                                    | Some { Kind = SemanticKind.Obligation _ } -> Some edge.Target
                                    | _ -> None)
                            Seq.concat [ fromCarriers; fromComparisons; fromRelations ] |> Set.ofSeq
                        let encodedObligations =
                            ownedObligationIds
                            |> Seq.choose (fun oblId ->
                                match graph.Nodes.TryFind oblId with
                                | Some { Kind = SemanticKind.Obligation info } ->
                                    Some(resolveProofAddress oblId + ":" + encodeProof (box info))
                                | _ -> None)
                            |> Seq.sort
                            |> String.concat "|"
                        let encodedContracts =
                            contracts.Values
                            |> Seq.map (fun c -> resolveProofAddress c.Identity + ":" + encodeProof (box c))
                            |> Seq.sort
                            |> String.concat "|"
                        let encodedCarriers =
                            emission.Numeric.Values
                            |> Map.toSeq
                            |> Seq.choose (fun (id, carrier) ->
                                if own.Contains id then Some(resolveProofAddress id + ":" + encodeProof (box carrier))
                                else None)
                            |> Seq.sort
                            |> String.concat "|"
                        let encodedComparisons =
                            comparisons
                            |> Seq.map (fun op -> resolveProofAddress op.Site + ":" + encodeProof (box op))
                            |> Seq.sort
                            |> String.concat "|"
                        let encodedRelations =
                            scopedProofRelations
                            |> Seq.map (fun edge ->
                                encodeProof (box (edge.Class, edge.Ordinal, edge.Target, edge.Sources)))
                            |> Seq.sort
                            |> String.concat "|"
                        let proofSupportPreimage =
                            [ "proof-support-v1"
                              regionIdentity
                              moduleName
                              name
                              encodeProof (box participants)
                              encodeProof (box censuses)
                              encodedObligations
                              encodedContracts
                              encodedCarriers
                              encodedComparisons
                              encodedRelations ]
                            |> String.concat "\n"
                        let canonicalProofSupportDigest =
                            CanonicalProofSupportDigest(CanonicalProofSupportDigest.DomainPrefix + hash proofSupportPreimage)
                        let proofSupportCoverage =
                            if comparisons.IsEmpty then
                                ProofSupportCoverage.Local(participants, censuses)
                            else
                                ProofSupportCoverage.Global(participants, censuses)
                        match liveScope.Occurrences.TryFind root with
                        | Some { Contexts = [path] } when admitted ->
                            Some { Identity = regionIdentity
                                   Flavor = WitnessRegionKind.ScalarCallable
                                   Root = Some root; Anchor = Some(path |> List.tryLast |> Option.map _.Parent |> Option.defaultValue root); Path = path
                                   Members = members; Supports = supports; OwnerSupport = liveScope.Support
                                   CallableInterfaceDigest = callableInterfaceDigest
                                   SemanticRealizationDigest = semanticRealizationDigest
                                   CanonicalProofSupportDigest = canonicalProofSupportDigest
                                   ProofSupportCoverage = proofSupportCoverage
                                   Dependencies = Set.empty }
                        | _ -> None
                | _ -> None
        | _ -> None
    // Whole-revision origin authority includes negative/absence membership.
    // No scalar subregion may drop that shared dependency or reuse it locally.
    let candidates =
        if not emission.Callable.Branches.Observations.IsEmpty then []
        else emission.Callable.Declarations.Values |> Seq.choose candidate |> Seq.toList
    // Ambiguous names are never an identity transport authority.
    let regions = candidates |> List.groupBy _.Identity |> List.choose (fun (_, group) -> if group.Length = 1 then Some group.Head else None)
    let owned = regions |> List.fold (fun all region -> Set.union all region.Members) Set.empty
    let all = graph.Nodes |> Map.toSeq |> Seq.map fst |> Set.ofSeq
    let complete = encodeProof
    let current label value =
        try complete value
        with :? InvalidOperationException as error -> invalidOp ("Common witness input " + label + ": " + error.Message)
    let executableNodes =
        graph.Nodes.Values
        |> Seq.filter (fun node -> match node.Kind with SemanticKind.Obligation _ -> false | _ -> true)
        |> Seq.map (fun node ->
            resolveProofAddress node.Id + ":" +
            current (sprintf "Nodes[%A]" node.Id) (nodeInput node) +
            current (sprintf "Metadata[%A]" node.Id) (box (normalizeMetadata node.Metadata)))
        |> Seq.sort
        |> String.concat "|"
    let obligationNodes =
        graph.Nodes.Values
        |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Obligation info ->
                Some(resolveProofAddress node.Id + ":" + current (sprintf "Obligation[%A]" node.Id) (box info))
            | _ -> None)
        |> Seq.sort
        |> String.concat "|"
    let contractInterfacesAll =
        emission.Callable.Contracts |> Map.map (fun _ contract ->
            { contract with
                SourcePremises = Map.empty
                Participants = contract.Participants |> List.filter (fun p -> p.Role <> ParticipantRole.Source) })
    let commonInterfaceDigest =
        [ "callable-interface-common-v1"
          current "Declarations" (box emission.Callable.Declarations)
          current "ContractInterfaces" (box contractInterfacesAll)
          current "Carriers" (box emission.Callable.Carriers)
          current "ValueShapes" (box emission.Callable.ValueShapes)
          current "BoundaryImports" (box emission.Boundary.Imports)
          current "BoundaryLinks" (box emission.Boundary.Links)
          current "DeclarationRoots" (box graph.DeclarationRoots)
          current "PlatformInterface" (box (graph.Platform |> Option.map (fun p -> p.PlatformId, p.SubstrateKind, p.RuntimeModel, p.Dimensions)))
          regions |> List.map (fun r -> r.Identity + ":" + r.CallableInterfaceDigest.Value) |> List.sort |> String.concat "|" ]
        |> String.concat "\n"
        |> hash
        |> fun h -> CallableInterfaceDigest(CallableInterfaceDigest.DomainPrefix + h)
    let commonRealizationDigest =
        [ "semantic-realization-common-v1"
          commonInterfaceDigest.Value
          executableNodes
          current "WitnessInputs" (box { witnessInputs with Callable = { witnessInputs.Callable with Contracts = contractInterfacesAll } })
          current "LocalCodata" (box { localCodata with CallableContracts = contractInterfacesAll })
          current "Platform" (box graph.Platform)
          current "StaticStringPool" (box graph.StaticStringPool)
          current "LiteralStorage" (box graph.LiteralStorage) ]
        |> String.concat "\n"
        |> hash
        |> fun h -> SemanticRealizationDigest(SemanticRealizationDigest.DomainPrefix + h)
    let encodedAllEdges =
        graph.Edges
        |> Seq.map (fun edge -> current "Edge" (box edge))
        |> Seq.sort
        |> String.concat "|"
    let commonProofDigest =
        [ "proof-support-common-v1"
          obligationNodes
          encodedAllEdges
          current "CallableContracts" (box emission.Callable.Contracts)
          current "CallableSupports" (box emission.Callable.Supports)
          current "CallableBranches" (box emission.Callable.Branches)
          current "NumericValues" (box emission.Numeric.Values)
          current "NumericOperations" (box emission.Numeric.Operations)
          current "MemoryOperations" (box emission.Memory.Operations)
          current "Spatial" (box emission.Spatial)
          current "Boundary" (box emission.Boundary)
          current "ProgramStorage" (box codata.ProgramStorage)
          current "Platform" (box graph.Platform)
          current "PlatformCensuses" (box (platformLayoutCensus graph.Platform @ platformSpaceCensus graph)) ]
        |> String.concat "\n"
        |> hash
        |> fun h -> CanonicalProofSupportDigest(CanonicalProofSupportDigest.DomainPrefix + h)
    let commonSupportSet =
        let ownerLabel =
            if String.IsNullOrWhiteSpace liveScope.Support.Identity then "owner:common"
            else "owner:" + liveScope.Support.Identity
        let rootLabels =
            graph.DeclarationRoots
            |> List.map (fun (id, flavor) -> sprintf "root:%A:%s" flavor (resolveProofAddress id))
        let depLabels =
            regions |> List.map (fun r -> "callee-region:" + r.Identity)
        Set.ofList (ownerLabel :: rootLabels @ depLabels)
    // Common remains freshly witnessed. Its revision key cannot authorize old
    // source-bound operations; backend reuse must also compare typed contents.
    let common =
        { Identity = "common"; Flavor = WitnessRegionKind.Common; Root = None; Anchor = None; Path = []
          Members = Set.difference (liveScope.Occurrences.Keys |> Set.ofSeq) owned; Supports = all; OwnerSupport = liveScope.Support
          CallableInterfaceDigest = commonInterfaceDigest
          SemanticRealizationDigest = commonRealizationDigest
          CanonicalProofSupportDigest = commonProofDigest
          ProofSupportCoverage = ProofSupportCoverage.Unclassified("common-whole-revision-envelope", commonSupportSet)
          Dependencies = regions |> List.map _.Identity |> Set.ofList }
    { Version = 1; Regions = regions @ [common] }
