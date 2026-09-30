// SPDX-License-Identifier: MIT
/// Baker-owned, conservative segmentation of already settled witness inputs.
module Clef.Compiler.PSGSaturation.SemanticGraph.WitnessSegmentation

open System
open System.Collections
open System.Globalization
open System.Reflection
open System.Security.Cryptography
open System.Text
open Microsoft.FSharp.Reflection
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let private flags = BindingFlags.Public ||| BindingFlags.NonPublic
let private typeName (t: Type) = t.FullName |> Option.ofObj |> Option.defaultWith (fun () -> invalidOp "Unnamed source input type")
let private property name (value: obj) =
    let field = value.GetType().GetProperty(name) |> Option.ofObj |> Option.defaultWith (fun () -> invalidOp ("Missing structural field " + name))
    field.GetValue value
let private generic (t: Type) = if t.IsGenericType then typeName (t.GetGenericTypeDefinition()) else ""
let private isMap t = (generic t).StartsWith "Microsoft.FSharp.Collections.FSharpMap"
let private isSet t = (generic t).StartsWith "Microsoft.FSharp.Collections.FSharpSet"
let private isList t = (generic t).StartsWith "Microsoft.FSharp.Collections.FSharpList"

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
            | None -> invalidOp "Region has a source dependency outside its admitted interface."
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
            elif FSharpType.IsTuple ty then FSharpValue.GetTupleFields value |> Array.map (fun field -> encode field) |> String.concat "" |> tagged
            elif FSharpType.IsRecord(ty, flags) then
                FSharpValue.GetRecordFields(value, flags) |> Array.map (fun field -> encode field) |> String.concat "" |> tagged
            elif FSharpType.IsUnion(ty, flags) then
                let case, fields = FSharpValue.GetUnionFields(value, ty, flags)
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
        elif FSharpType.IsRecord(ty, flags) then
            FSharpType.GetRecordFields(ty, flags)
            |> Array.map (fun field -> field.Name + "=" + walk (field.GetValue value))
            |> String.concat ";"
        else encode value
    walk value

let private hash text = Encoding.UTF8.GetBytes(text: string) |> SHA256.HashData |> Convert.ToHexString

/// The first independent cohort has no calls, storage, effects, aggregate
/// transports, nested declarations or external reads. Extending this grammar
/// requires extending its complete source interface, not a witness heuristic.
let private supported root (members: Set<NodeId>) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Lambda(_, _, [], _, LambdaContext.RegularClosure) -> node.Id = root
    | SemanticKind.PatternBinding _ -> true
    | SemanticKind.Literal (NativeLiteral.String _ | NativeLiteral.ByteArray _ | NativeLiteral.UInt16Array _) -> false
    | SemanticKind.Literal _ -> true
    | SemanticKind.VarRef(_, Some definition) -> members.Contains definition
    | SemanticKind.Binding(_, false, false, None) -> true
    | SemanticKind.Sequential _ | SemanticKind.IfThenElse _ | SemanticKind.TypeAnnotation _ -> true
    | _ -> false

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

let private nodeInput (node: SemanticNode) =
    // Range and diagnostic metadata do not enter scalar emission. All fields
    // published to scalar witnesses do; obligation anchors are separately
    // retained in the complete incident proof relations below.
    box (node.Id, node.Kind, node.Type, node.Children, node.Parent,
         node.IsReachable, node.EmissionStrategy, node.ValueRange)

let project (graph: SemanticGraph) (emission: WitnessEmissionProjection) : WitnessSegmentation =
    let codata = { graph.Codata.Value with WitnessEmission = None; WitnessSegmentation = None }
    // Evidence supports remain current graph citizens and are discharged anew
    // for every revision. The witness key compares the settled interface those
    // proofs justify, rather than carrying a previous revision's proof receipt.
    let witnessInputs =
        { emission with
            Callable = { emission.Callable with Supports = Map.empty }
            Numeric = { emission.Numeric with
                            Values = emission.Numeric.Values |> Map.map (fun _ carrier ->
                                { carrier with Declaration = None; Obligations = []; Participants = Set.empty }) }
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
                let eligible =
                    binding.IsReachable && declaration.Captures.IsEmpty &&
                    not (codata.DeclarationRootLambdas.ContainsKey root) &&
                    not (codata.Closures.ContainsKey root || emission.Callable.TakesEnvironment.Contains root) &&
                    (Set.intersect own emission.Boundary.DeclarationLeaves |> Set.isEmpty) &&
                    (Set.intersect own emission.Boundary.DeclarationOnly |> Set.isEmpty) &&
                    (emission.Storage.Startup |> Option.forall (fun startup -> startup.EntryLambda <> root)) &&
                    (ordered |> List.forall (fun id -> supported root members graph.Nodes[id])) &&
                    (ordered |> List.forall (fun id ->
                        id = root ||
                        match emission.Numeric.OccurrenceRepresentations.TryFind id with
                        | Some (Ok (ValueRepresentation.Scalar (SettledSlot.Integer _ | SettledSlot.Bool | SettledSlot.Char | SettledSlot.Real _ | SettledSlot.Unit))) -> true
                        | _ -> false)) &&
                    (ordered |> List.forall (fun id ->
                        graph.Nodes.Values |> Seq.forall (fun parent ->
                            not (List.contains id parent.Children) || own.Contains parent.Id)))
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
                    try
                        let encode = encoder identities
                        let ownTypes = own |> Set.map (fun id -> Clef.Compiler.NativeTypedTree.TypeIdentities.ofType graph.Nodes[id].Type)
                        let scope value = scoped own ownTypes encode value
                        let inputs =
                            [ "scalar-v1"; moduleName; name
                              ordered |> List.map (fun id -> encode (nodeInput graph.Nodes[id])) |> String.concat "|"
                              encode (box binding.Kind)
                              scope (box witnessInputs); scope (box localCodata)
                              encode (box graph.Platform)
                              ordered |> List.collect (fun id -> kindEdges id graph.Nodes[id].Kind) |> box |> encode ]
                        Some { Identity = "callable:" + moduleName + ":" + name
                               Flavor = WitnessRegionKind.ScalarCallable
                               Root = Some root; Anchor = Some binding.Id; Path = [binding.Id, [], []]
                               Members = members; Supports = supports
                               Fingerprint = hash (String.concat "\n" inputs); Dependencies = Set.empty }
                    with :? InvalidOperationException -> None
                | _ -> None
        | _ -> None
    let candidates = emission.Callable.Declarations.Values |> Seq.choose candidate |> Seq.toList
    // Ambiguous names are never an identity transport authority.
    let regions = candidates |> List.groupBy _.Identity |> List.choose (fun (_, group) -> if group.Length = 1 then Some group.Head else None)
    let owned = regions |> List.fold (fun all region -> Set.union all region.Members) Set.empty
    let all = graph.Nodes |> Map.toSeq |> Seq.map fst |> Set.ofSeq
    let complete = encoder (all |> Set.toSeq |> Seq.map (fun (NodeId id as node) -> node, string id) |> Map.ofSeq)
    let commonFingerprint =
        [ graph.Nodes.Values |> Seq.map (fun node -> complete (nodeInput node) + complete (box node.Metadata)) |> String.concat "|"
          complete (box emission); complete (box codata); complete (box graph.Platform)
          complete (box graph.Edges); complete (box graph.StaticStringPool); complete (box graph.LiteralStorage) ]
        |> String.concat "\n" |> hash
    // Common remains freshly witnessed. Its revision key cannot authorize old
    // source-bound operations; backend reuse must also compare typed contents.
    let common =
        { Identity = "common"; Flavor = WitnessRegionKind.Common; Root = None; Anchor = None; Path = []
          Members = Set.difference all owned; Supports = all
          Fingerprint = commonFingerprint
          Dependencies = regions |> List.map _.Identity |> Set.ofList }
    { Version = 1; Regions = regions @ [common] }
