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

/// Length-delimited, culture-independent structural encoding. Types are frozen
/// here, while Baker still owns checker substitutions. Unknown identities or
/// host objects refuse a separate region; they never disappear from the key.
let private encoder (identities: Map<NodeId, string>) =
    let rec encode (value: objnull) : string =
        let atom (text: string) = string text.Length + ":" + text
        match value with
        | null -> "null;"
        | :? NodeId as id ->
            match identities.TryFind id with
            | Some identity -> "node" + atom identity
            | None -> invalidOp (sprintf "Region has source dependency %A outside its admitted interface." id)
        | :? NativeType as ty -> encode (box (Clef.Compiler.NativeTypedTree.TypeIdentities.ofType ty))
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

let private hash text = Encoding.UTF8.GetBytes(text: string) |> SHA256.HashData |> Convert.ToHexString

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
let private numericInterface (graph: SemanticGraph) (operations: NumericOperationWitness list) =
    let read = PlatformResolution.read graph
    let platform = read.Platform |> Option.filter (fun _ -> read.Findings.IsEmpty)
                   |> Option.defaultWith (fun () -> invalidOp "Comparison region lacks its current source platform.")
    let core = platform.Core |> Option.defaultWith (fun () -> invalidOp "Comparison region lacks its source core.")
    let named =
        (core.Node, "numeric-core:" + platform.Id) ::
        (core.Widths |> List.map (fun row -> row.Node, "numeric-width:" + platform.Id + ":" + row.Name)) @
        (core.Representations |> List.map (fun row -> row.Node, "numeric-representation:" + platform.Id + ":" + row.Representation.Name))
    if (named |> List.map fst |> Set.ofList |> Set.count) <> named.Length ||
       (named |> List.map snd |> Set.ofList |> Set.count) <> named.Length then
        invalidOp "Comparison region has ambiguous source declaration identities."
    for operation in operations do
        if not (core.Representations |> List.exists (fun row ->
            operation.Declaration = Some row.Node && operation.Representation = Some row.Representation)) then
            invalidOp "Comparison region lost its exact source representation declaration."
    Map.ofList named, core

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
    box (node.Id, node.Kind, node.Type, node.Children, node.Parent,
         node.IsReachable, node.EmissionStrategy, node.ValueRange)

let project (graph: SemanticGraph) (emission: WitnessEmissionProjection) (liveScope: WitnessLiveScopePlan) : WitnessSegmentation =
    let codata = { graph.Codata.Value with WitnessEmission = None; WitnessSegmentation = None; WitnessLiveScope = None; WitnessPreparedRows = None; WitnessLiveRows = None; WitnessPublishedRows = None; ProofDispatch = None }
    // Relation identities are not executable citizens. Admit only the two
    // authored relation tables, with exact filing and source/codata agreement;
    // every other unknown NodeId remains an error in the structural encoder.
    if emission.Callable.Contracts <> codata.CallableContracts ||
       emission.Callable.AggregateSlots <> codata.CallableAggregateSlots then
        invalidOp "Callable relation tables disagree with their current source codata."
    let relationIdentities =
        let add label (key: NodeId) (identity: NodeId) (names: Map<NodeId, string>) =
            if key <> identity || graph.Nodes.ContainsKey key || Map.containsKey key names then
                invalidOp "A callable relation identity is misfiled or collides with another source identity."
            Map.add key (label + string (NodeId.value key)) names
        let contracts = emission.Callable.Contracts |> Map.fold (fun names key (row: CallableContract) ->
            add "callable-contract:" key row.Identity names) Map.empty
        emission.Callable.AggregateSlots |> Map.fold (fun names key (row: CallableAggregateSlot) ->
            add "callable-aggregate-slot:" key row.Identity names) contracts
    // Evidence supports remain current graph citizens and are discharged anew
    // for every revision. The witness key compares the settled interface those
    // proofs justify, rather than carrying a previous revision's proof receipt.
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
                let comparisons = emission.Numeric.Operations.Values |> Seq.filter (fun operation -> members.Contains operation.Site) |> Seq.filter (comparison graph members) |> Seq.toList
                let comparisonSites = comparisons |> List.map _.Site |> Set.ofList
                let comparisonCallees = comparisons |> List.map _.Callee |> Set.ofList
                let eligible =
                    binding.IsReachable && declaration.Captures.IsEmpty &&
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
                    try
                        let interfaces, core =
                            if comparisons.IsEmpty then Map.empty, None else
                            let identities, core = numericInterface graph comparisons
                            identities, Some core
                        if interfaces.Keys |> Seq.exists identities.ContainsKey then
                            invalidOp "Numeric declaration is not external to its scalar region."
                        let identities = Map.fold (fun identities id name -> Map.add id name identities) identities interfaces
                        let contracts =
                            emission.Callable.Contracts |> Map.filter (fun _ (contract: CallableContract) ->
                                (match contract.Participants |> List.filter (fun participant -> participant.Role = ParticipantRole.CallableImplementation) with
                                | [implementation] when implementation.Group = contract.Identity && implementation.Ordinal = 0 ->
                                    own.Contains implementation.Node
                                | _ -> false))
                        // A native receiving convention has no independent
                        // scalar emission interface yet. Keep the candidate in
                        // Common instead of silently omitting that contract,
                        // including when an ordinary contract also names it.
                        if contracts.Values |> Seq.exists (fun contract -> contract.Kind = CallableKind.NativeEntry) then
                            invalidOp "Native receiving contracts are not admitted to independent scalar regions."
                        let contractNames = contracts |> Map.map (fun _ contract ->
                            let implementation = contract.Participants |> List.find (fun participant -> participant.Role = ParticipantRole.CallableImplementation)
                            "callable-contract:" + identities[implementation.Node])
                        if (contractNames.Values |> Set.ofSeq |> Set.count) <> contractNames.Count then
                            invalidOp "A scalar interface has ambiguous receiving contract identities."
                        let identities = Map.fold (fun names id name ->
                            if Map.containsKey id names then invalidOp "A callable contract collides with its scalar interface."
                            Map.add id name names) identities contractNames
                        // As with scalar carriers and operationInput above,
                        // only the reusable code fingerprint separates proof
                        // support from the settled receiving interface. Full
                        // signature/physical maps and local roles stay encoded;
                        // complete public rows and current proof discharge are
                        // unchanged. External non-proof roles still refuse the
                        // candidate through the ordinary identity encoder.
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
                        let encode = encoder identities
                        let ownTypes = own |> Set.map (fun id -> Clef.Compiler.NativeTypedTree.TypeIdentities.ofType graph.Nodes[id].Type)
                        let ownFacts = Set.union own (contractNames.Keys |> Set.ofSeq)
                        let scope value = scoped ownFacts ownTypes encode value
                        // List-shaped boundary rows are selected by their owner, as the
                        // NodeId-keyed domains are selected by membership: a result
                        // hypothesis belongs to its declaration and a foreign result use to
                        // its application call. A row this candidate does not own is not
                        // its interface and is excluded; a row it owns is retained whole, so
                        // any participant outside the admitted identities still refuses the
                        // candidate through the ordinary identity encoder. Without this
                        // selection every declared hypothesis in the program, including a
                        // platform library's, refused every scalar region.
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
                        let inputs =
                            [ (if comparisons.IsEmpty then "scalar-v1" else "scalar-comparison-v1"); moduleName; name
                              ordered |> List.map (fun id -> encode (nodeInput graph.Nodes[id])) |> String.concat "|"
                              encode (box binding.Kind)
                              scope (box witnessInputs); scope (box localCodata)
                              encode (box graph.Platform)
                              ordered |> List.collect (fun id -> kindEdges id graph.Nodes[id].Kind) |> box |> encode ]
                            @ (core |> Option.map (fun value -> [encode (box value)]) |> Option.defaultValue [])
                        match liveScope.Occurrences.TryFind root with
                        | Some { Contexts = [path] } ->
                            Some { Identity = "callable:" + moduleName + ":" + name
                                   Flavor = WitnessRegionKind.ScalarCallable
                                   Root = Some root; Anchor = Some(path |> List.tryLast |> Option.map _.Parent |> Option.defaultValue root); Path = path
                                   Members = members; Supports = supports; OwnerSupport = liveScope.Support
                                   Fingerprint = hash (String.concat "\n" inputs); Dependencies = Set.empty }
                        | _ -> None
                    with :? InvalidOperationException -> None
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
    let complete =
        all |> Set.toSeq |> Seq.map (fun (NodeId id as node) -> node, string id) |> Map.ofSeq
        |> fun identities -> Map.fold (fun names id name -> Map.add id name names) identities relationIdentities
        |> encoder
    let current label value =
        try complete value
        with :? InvalidOperationException as error -> invalidOp ("Common witness input " + label + ": " + error.Message)
    let commonFingerprint =
        [ graph.Nodes.Values |> Seq.map (fun node -> current (sprintf "Nodes[%A]" node.Id) (nodeInput node) + current (sprintf "Metadata[%A]" node.Id) (box node.Metadata)) |> String.concat "|"
          current "WitnessEmission" (box emission); current "Codata" (box codata); current "Platform" (box graph.Platform)
          current "Edges" (box graph.Edges); current "StaticStringPool" (box graph.StaticStringPool); current "LiteralStorage" (box graph.LiteralStorage) ]
        |> String.concat "\n" |> hash
    // Common remains freshly witnessed. Its revision key cannot authorize old
    // source-bound operations; backend reuse must also compare typed contents.
    let common =
        { Identity = "common"; Flavor = WitnessRegionKind.Common; Root = None; Anchor = None; Path = []
          Members = Set.difference (liveScope.Occurrences.Keys |> Set.ofSeq) owned; Supports = all; OwnerSupport = liveScope.Support
          Fingerprint = commonFingerprint
          Dependencies = regions |> List.map _.Identity |> Set.ofList }
    { Version = 1; Regions = regions @ [common] }
