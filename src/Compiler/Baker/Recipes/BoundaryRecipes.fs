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
let private declarationFact (node: SemanticNode) =
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
    | SemanticKind.PatternBinding name -> fact "pattern-binding" [name] [] []
    | SemanticKind.Lambda(parameters, _, [], _, _) ->
        fact "declaration-lambda" (parameters |> List.map(fun (name,_,_) -> name)) [] node.Children
    | SemanticKind.TypeAnnotation(inner, _) -> fact "annotation" [] [] [inner]
    | SemanticKind.Quote(inner, _) -> fact "quotation" [] [] [inner]
    | SemanticKind.Application(callee, arguments) -> fact "application" [] [] (callee :: arguments)
    | SemanticKind.Intrinsic info -> fact "intrinsic" [string info.Module; info.Operation] [] []
    | _ -> Error $"Descriptor participant {NodeId.value node.Id} has no immutable boundary declaration premise."

let private declarationFacts (graph: SemanticGraph) root =
    let rec visit facts id =
        if Map.containsKey id facts then Ok facts else
        match graph.Nodes.TryFind id with
        | None -> Error $"Descriptor participant {NodeId.value id} is absent from the source graph."
        | Some node -> checked' {
            let! value = declarationFact node
            let next = value.References @ value.Children
            return! List.fold (fun state child -> state |> Result.bind (fun facts -> visit facts child)) (Ok (Map.add id value facts)) next }
    visit Map.empty root

/// Complete account observation stays with the source declaration/fact owners.
let private absenceAccounts (graph:SemanticGraph) (descriptors:Declarations.Descriptors) (imports:Map<NodeId,BoundaryImport>) (invocations:Map<NodeId,BoundaryCallbackInvocation>) =
    descriptors.CallbackAbsences |> List.fold(fun state source ->
        state |> Result.bind(fun rows ->
            match imports.TryFind source.Invocation.AbiDescriptor, invocations.TryFind source.Invocation.Quote with
            | Some imported, Some invocation when imported.Binding=source.Invocation.Declaration.Binding && invocation.Import=imported.Identity && invocation.Formal=source.Invocation.Formal && invocation.Extent=BoundaryCallbackExtent.DuringCall ->
                declarationFacts graph source.DescriptorBinding |> Result.map(fun facts ->
                    let account:BoundaryCallbackAbsence =
                        {Quote=source.Quote;DescriptorBinding=source.DescriptorBinding;Record=source.Node;Import=imported.Identity
                         Parameter=source.Contract.Parameter;Formal=source.Invocation.Formal;Invocation=invocation.Identity
                         Contract=source.Contract;SourcePath=source.SourcePath;Inputs=source.Inputs;DeclarationFacts=facts}
                    Map.add source.Quote account rows)
            | _ -> Ok rows)) (Ok Map.empty)

let private bufferAbsenceAccounts (graph: SemanticGraph) (descriptors: Declarations.Descriptors) (imports: Map<NodeId, BoundaryImport>) =
    descriptors.BufferAbsences |> List.fold (fun state source ->
        state |> Result.bind (fun rows ->
            match imports.TryFind source.AbiDescriptor with
            | Some imported when imported.Binding = source.Declaration.Binding ->
                declarationFacts graph source.DescriptorBinding |> Result.map (fun facts ->
                    let account: BoundaryBufferAbsence =
                        { Quote = source.Quote; DescriptorBinding = source.DescriptorBinding; Record = source.Node; Import = imported.Identity
                          Parameter = source.Contract.Parameter; Formal = source.Formal; BufferDeclaration = source.BufferDeclaration
                          Contract = source.Contract; SourcePath = source.SourcePath; Inputs = source.Inputs; DeclarationFacts = facts }
                    Map.add source.Quote account rows)
            | _ -> Ok rows)) (Ok Map.empty)

let private computeProgramOrders (graph: SemanticGraph) =
    let orders = System.Collections.Generic.Dictionary<NodeId, int>()
    let visiting = System.Collections.Generic.HashSet<NodeId>()
    let mutable counter = 0
    let rec walk id =
        if not (orders.ContainsKey id) && not (visiting.Contains id) then
            visiting.Add id |> ignore
            match graph.Nodes.TryFind id with
            | Some node ->
                node.Children |> List.iter walk
                counter <- counter + 1
                orders[id] <- counter
            | None -> ()
            visiting.Remove id |> ignore
    let reachableNodes =
        graph.Nodes |> Map.toList |> List.sortBy (fst >> NodeId.value) |> List.filter (fun (_, node) -> node.IsReachable)
    reachableNodes
    |> List.filter (fun (_, node) ->
        not (node.Parent |> Option.exists (fun p -> graph.Nodes.TryFind p |> Option.exists _.IsReachable)))
    |> List.iter (fun (id, _) -> walk id)
    reachableNodes |> List.iter (fun (id, _) -> walk id)
    orders |> Seq.map (fun kv -> kv.Key, kv.Value) |> Map.ofSeq

let rec private canonicalExprOrigin (graph: SemanticGraph) (seen: Set<NodeId>) (id: NodeId) =
    if Set.contains id seen then id else
    let seen = Set.add id seen
    match graph.Nodes.TryFind id with
    | Some { Kind = SemanticKind.TypeAnnotation(inner, _) }
    | Some { Kind = SemanticKind.EagerExpr inner }
    | Some { Kind = SemanticKind.VarRef(_, Some inner) } -> canonicalExprOrigin graph seen inner
    | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> canonicalExprOrigin graph seen value
    | Some { Kind = SemanticKind.Sequential items } when not items.IsEmpty -> canonicalExprOrigin graph seen (List.last items)
    | Some { Kind = SemanticKind.StringByteBorrow source } -> canonicalExprOrigin graph seen source
    | Some { Kind = SemanticKind.Application(callee, args) } when not args.IsEmpty ->
        match graph.Nodes.TryFind callee with
        | Some { Kind = SemanticKind.Intrinsic info }
            when info.Module = IntrinsicModule.Array &&
                 (info.FullName = "ReadOnlyView.ofArray" || info.FullName = "ReadOnlyView.ofString" || info.FullName = "ReadOnlyView.slice") ->
            canonicalExprOrigin graph seen args.Head
        | _ -> id
    | _ -> id

let rec private immutableExprOrigin (graph: SemanticGraph) (seen: Set<NodeId>) (id: NodeId) =
    if Set.contains id seen then id else
    let seen = Set.add id seen
    match graph.Nodes.TryFind id with
    | Some { Kind = SemanticKind.TypeAnnotation(inner, _) }
    | Some { Kind = SemanticKind.EagerExpr inner } -> immutableExprOrigin graph seen inner
    | Some { Kind = SemanticKind.VarRef(_, Some inner) } ->
        match graph.Nodes.TryFind inner with
        | Some { Kind = SemanticKind.Binding(_, false, _, _) }
        | Some { Kind = SemanticKind.PatternBinding _ } -> immutableExprOrigin graph seen inner
        | _ -> id
    | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> immutableExprOrigin graph seen value
    | Some { Kind = SemanticKind.PatternBinding _ } ->
        let sourceDef = DirectCaptures.sourceDefinition graph id
        if sourceDef <> id then immutableExprOrigin graph seen sourceDef else id
    | Some { Kind = SemanticKind.EnvironmentRead(_, declaration) } ->
        match graph.Nodes.TryFind declaration with
        | Some { Kind = SemanticKind.Binding(_, false, _, _) }
        | Some { Kind = SemanticKind.PatternBinding _ } -> immutableExprOrigin graph seen declaration
        | _ -> id
    | Some { Kind = SemanticKind.Sequential items } when not items.IsEmpty -> immutableExprOrigin graph seen (List.last items)
    | Some { Kind = SemanticKind.StringByteBorrow source } -> immutableExprOrigin graph seen source
    | Some { Kind = SemanticKind.Application(callee, args) } when not args.IsEmpty ->
        match graph.Nodes.TryFind callee with
        | Some { Kind = SemanticKind.Intrinsic info }
            when info.Module = IntrinsicModule.Array &&
                 (info.FullName = "ReadOnlyView.ofArray" || info.FullName = "ReadOnlyView.ofString" || info.FullName = "ReadOnlyView.slice") ->
            immutableExprOrigin graph seen args.Head
        | _ -> id
    | _ -> id

let private buildAliasEnv (graph: SemanticGraph) =
    let setsByTarget = System.Collections.Generic.Dictionary<NodeId, NodeId list>()
    let patternScrutinees = System.Collections.Generic.Dictionary<NodeId, NodeId list>()
    let addToDict (dict: System.Collections.Generic.Dictionary<NodeId, NodeId list>) key value =
        match dict.TryGetValue key with
        | true, existing -> dict[key] <- value :: existing
        | false, _ -> dict[key] <- [value]
    let rec targetRoots seen id =
        if Set.contains id seen then [] else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.VarRef(_, Some t) } -> t :: targetRoots seen t
        | Some { Kind = SemanticKind.CellAddress b } -> b :: targetRoots seen b
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) }
        | Some { Kind = SemanticKind.EagerExpr inner }
        | Some { Kind = SemanticKind.Deref inner }
        | Some { Kind = SemanticKind.Reborrow inner } -> targetRoots seen inner
        | _ -> [id]
    for node in graph.Nodes.Values do
        if node.IsReachable then
            match node.Kind with
            | SemanticKind.Set(target, rhs)
            | SemanticKind.FieldSet(target, _, rhs) ->
                for t in targetRoots Set.empty target do
                    addToDict setsByTarget t rhs
            | SemanticKind.Match(scrutinee, cases) ->
                for c in cases do
                    for pb in c.PatternBindings do
                        addToDict patternScrutinees pb scrutinee
            | SemanticKind.CaseElimination(scrutinee, arms) ->
                for arm in arms do
                    for b in arm.Bindings do
                        addToDict patternScrutinees b scrutinee
            | _ -> ()
    setsByTarget, patternScrutinees

let private isTupleAccessorIntrinsic (graph: SemanticGraph) (callee: NodeId) =
    match target graph callee with
    | Some({ Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Operators; Operation = ("fst" | "snd") } }, _) -> true
    | _ -> false

let private isNonInvokingIntrinsic (graph: SemanticGraph) (callee: NodeId) =
    match target graph callee with
    | Some({ Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Operators; Operation = ("fst" | "snd" | "ignore" | "id") } }, _)
    | Some({ Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.FnPtr; Operation = "ofExtern" } }, _) -> true
    | _ -> false

let private isCallableContainer = function
    | SemanticKind.Lambda _ | SemanticKind.LazyExpr _ | SemanticKind.SeqExpr _ -> true
    | _ -> false

let private enclosingCallable (graph: SemanticGraph) (id: NodeId) : NodeId option =
    let rec walk seen cur =
        match graph.Nodes.TryFind cur |> Option.bind _.Parent with
        | Some p when not (Set.contains p seen) ->
            match graph.Nodes.TryFind p with
            | Some pn when isCallableContainer pn.Kind -> Some p
            | _ -> walk (Set.add p seen) p
        | _ -> None
    walk Set.empty id

let private possibleOrigins
    (graph: SemanticGraph)
    (setsByTarget: System.Collections.Generic.Dictionary<NodeId, NodeId list>)
    (patternScrutinees: System.Collections.Generic.Dictionary<NodeId, NodeId list>)
    (startId: NodeId) : Set<NodeId> =
    let visited = System.Collections.Generic.HashSet<NodeId>()
    let queue = System.Collections.Generic.Queue<NodeId>()
    let enqueue id =
        if visited.Add id then queue.Enqueue id
    enqueue startId
    while queue.Count > 0 do
        let cur = queue.Dequeue ()
        match graph.Nodes.TryFind cur with
        | Some node ->
            match node.Kind with
            | SemanticKind.TypeAnnotation(inner, _)
            | SemanticKind.EagerExpr inner
            | SemanticKind.StringByteBorrow inner
            | SemanticKind.Reborrow inner
            | SemanticKind.Deref inner
            | SemanticKind.AddressOf(inner, _)
            | SemanticKind.TupleGet(inner, _)
            | SemanticKind.FieldGet(inner, _)
            | SemanticKind.DUEliminate(inner, _, _, _)
            | SemanticKind.UnionCase(_, _, Some inner)
            | SemanticKind.DUConstruct(_, _, Some inner, _) ->
                enqueue inner
            | SemanticKind.VarRef(_, Some inner) ->
                enqueue inner
            | SemanticKind.EnvironmentRead(_, declaration) ->
                enqueue declaration
            | SemanticKind.ClosureValue(implementation, _) ->
                enqueue implementation
            | SemanticKind.Binding _ ->
                for child in node.Children do enqueue child
                match setsByTarget.TryGetValue cur with
                | true, rhss -> for rhs in rhss do enqueue rhs
                | false, _ -> ()
            | SemanticKind.PatternBinding _ ->
                for child in node.Children do enqueue child
                let sourceDef = DirectCaptures.sourceDefinition graph cur
                if sourceDef <> cur then enqueue sourceDef
                match patternScrutinees.TryGetValue cur with
                | true, srcs -> for src in srcs do enqueue src
                | false, _ -> ()
            | SemanticKind.TupleExpr elements ->
                for elem in elements do enqueue elem
            | SemanticKind.RecordExpr(fields, copyFrom) ->
                for _, v in fields do enqueue v
                copyFrom |> Option.iter enqueue
            | SemanticKind.Application(callee, args) when not args.IsEmpty ->
                match graph.Nodes.TryFind callee with
                | Some { Kind = SemanticKind.Intrinsic info }
                    when info.Module = IntrinsicModule.Array &&
                         (info.FullName = "ReadOnlyView.ofArray" || info.FullName = "ReadOnlyView.ofString" || info.FullName = "ReadOnlyView.slice") ->
                    enqueue args.Head
                | _ when isTupleAccessorIntrinsic graph callee && args.Length = 1 ->
                    enqueue args.Head
                | _ -> ()
            | SemanticKind.Sequential items ->
                if not items.IsEmpty then enqueue (List.last items)
            | SemanticKind.IfThenElse(_, t, e) ->
                enqueue t
                e |> Option.iter enqueue
            | SemanticKind.Match(_, cases) ->
                for c in cases do enqueue c.Body
            | SemanticKind.CaseElimination(_, arms) ->
                for arm in arms do enqueue arm.Body
            | SemanticKind.TryWith(body, handler) ->
                enqueue body
                enqueue handler
            | SemanticKind.TryFinally(body, _) ->
                enqueue body
            | _ -> ()
        | None -> ()
    Set.ofSeq visited

let private callableTargets
    (graph: SemanticGraph)
    (setsByTarget: System.Collections.Generic.Dictionary<NodeId, NodeId list>)
    (patternScrutinees: System.Collections.Generic.Dictionary<NodeId, NodeId list>)
    (startId: NodeId) : Set<NodeId> =
    let seen = System.Collections.Generic.HashSet<NodeId>()
    let result = System.Collections.Generic.HashSet<NodeId>()
    let queue = System.Collections.Generic.Queue<NodeId>()
    let enqueue id =
        if seen.Add id then queue.Enqueue id
    enqueue startId
    while queue.Count > 0 do
        let cur = queue.Dequeue ()
        for origin in possibleOrigins graph setsByTarget patternScrutinees cur do
            match graph.Nodes.TryFind origin with
            | Some { Kind = SemanticKind.Lambda _ | SemanticKind.LazyExpr _ | SemanticKind.SeqExpr _ } ->
                result.Add origin |> ignore
            | Some { Kind = SemanticKind.Application(callee, _) }
                when not (isTupleAccessorIntrinsic graph callee) && not (isNonInvokingIntrinsic graph callee) ->
                for targetOrigin in possibleOrigins graph setsByTarget patternScrutinees callee do
                    match graph.Nodes.TryFind targetOrigin with
                    | Some { Kind = SemanticKind.Lambda(_, body, _, _, _) } -> enqueue body
                    | _ -> ()
            | _ -> ()
    Set.ofSeq result

let private ancestorChain (graph: SemanticGraph) (id: NodeId) : NodeId list =
    let rec walk acc seen cur =
        if Set.contains cur seen then List.rev acc else
        let seen = Set.add cur seen
        match graph.Nodes.TryFind cur |> Option.bind _.Parent with
        | Some p -> walk (p :: acc) seen p
        | None -> List.rev acc
    walk [id] Set.empty id

let private isControlFlowBoundaryKind = function
    | SemanticKind.IfThenElse _
    | SemanticKind.Match _
    | SemanticKind.CaseElimination _
    | SemanticKind.WhileLoop _
    | SemanticKind.ForLoop _
    | SemanticKind.ForEach _
    | SemanticKind.TryWith _
    | SemanticKind.TryFinally _
    | SemanticKind.Lambda _
    | SemanticKind.LazyExpr _
    | SemanticKind.SeqExpr _
    | SemanticKind.ContinuationDispatch _ -> true
    | _ -> false

let private enclosingLoops (graph: SemanticGraph) (id: NodeId) : Set<NodeId> =
    ancestorChain graph id
    |> List.filter (fun aid ->
        match graph.Nodes.TryFind aid with
        | Some { Kind = SemanticKind.WhileLoop _ | SemanticKind.ForLoop _ | SemanticKind.ForEach _ } -> true
        | _ -> false)
    |> Set.ofList

let private findLcaAndSuffixes (graph: SemanticGraph) (a: NodeId) (b: NodeId) =
    let aChain = ancestorChain graph a
    let bChain = ancestorChain graph b
    let aSet = Set.ofList aChain
    match bChain |> List.tryFind aSet.Contains with
    | None -> None
    | Some lca ->
        let prefixBefore chain = chain |> List.takeWhile ((<>) lca)
        Some(lca, prefixBefore aChain, prefixBefore bChain)

let private dominatesOnUnconditionalSpine (graph: SemanticGraph) (siteId: NodeId) (candId: NodeId) : bool =
    match findLcaAndSuffixes graph siteId candId with
    | None -> false
    | Some(lca, sitePrefix, candPrefix) ->
        let lcaIsBranchOrLoop =
            lca <> candId &&
            (graph.Nodes.TryFind lca |> Option.exists (fun n -> isControlFlowBoundaryKind n.Kind))
        let sitePrefixHasControlBoundary =
            sitePrefix |> List.exists (fun pid ->
                pid <> siteId &&
                (graph.Nodes.TryFind pid |> Option.exists (fun n -> isControlFlowBoundaryKind n.Kind)))
        let candPrefixHasControlBoundary =
            candPrefix |> List.exists (fun pid ->
                pid <> candId &&
                (graph.Nodes.TryFind pid |> Option.exists (fun n -> isControlFlowBoundaryKind n.Kind)))
        not lcaIsBranchOrLoop &&
        not sitePrefixHasControlBoundary &&
        not candPrefixHasControlBoundary &&
        Set.isSubset (enclosingLoops graph candId) (enclosingLoops graph siteId)

let private subtreeContains (graph: SemanticGraph) (root: NodeId) (target: NodeId) : bool =
    ancestorChain graph target |> List.contains root

let private canPrecedeInExecution (graph: SemanticGraph) (earlierId: NodeId) (laterId: NodeId) : bool =
    match findLcaAndSuffixes graph earlierId laterId with
    | None -> true
    | Some(lca, _, _) ->
        match graph.Nodes.TryFind lca with
        | Some { Kind = SemanticKind.IfThenElse(_, t, e) } ->
            let inT n = subtreeContains graph t n
            let inE n = e |> Option.exists (fun eb -> subtreeContains graph eb n)
            not ((inT earlierId && inE laterId) || (inE earlierId && inT laterId))
        | Some { Kind = SemanticKind.Match(_, cases) } ->
            let armOf n = cases |> List.tryFindIndex (fun c -> subtreeContains graph c.Body n)
            match armOf earlierId, armOf laterId with
            | Some i, Some j -> i = j
            | _ -> true
        | Some { Kind = SemanticKind.CaseElimination(_, arms) } ->
            let armOf n = arms |> List.tryFindIndex (fun a -> subtreeContains graph a.Body n)
            match armOf earlierId, armOf laterId with
            | Some i, Some j -> i = j
            | _ -> true
        | _ -> true

let private isOptionType (ty: NativeType) =
    match Clef.Compiler.NativeTypedTree.UnionFind.applySubst ty with
    | NativeType.TApp(tc, [_]) -> tc.Name = "option" || tc.Name = "Option"
    | _ -> false

let private isNominalMarkerPointee (ty: NativeType) =
    match Clef.Compiler.NativeTypedTree.UnionFind.applySubst ty with
    | NativeType.TApp(tc, []) ->
        tc.NTUKind.IsNone && tc.Name <> "unit" && tc.Name <> "option" && tc.Name <> "Option"
    | _ -> false

let rec private isNominalCHandleType (nullable: bool) (ty: NativeType) =
    match Clef.Compiler.NativeTypedTree.UnionFind.applySubst ty with
    | NativeType.TApp(tc, [inner]) when tc.Name = "option" || tc.Name = "Option" ->
        nullable && isNominalCHandleType false inner
    | NativeType.TApp(tc, [marker]) as substituted ->
        not nullable && tc.Name = "CHandle" && Types.tryGetNTUKind substituted = Some NTUKind.NTUptr && isNominalMarkerPointee marker
    | _ -> false

let private resolveBufferAbsenceChoice (graph: SemanticGraph) (absences: Declarations.DeclaredBufferAbsence list)
                                       (site: SemanticNode) (declarationBinding: NodeId) (nativeOrdinal: int) (tagOrdinal: int) (actual: NodeId) =
    match graph.Nodes.TryFind actual with
    | None -> Ok(None, Set.empty, false, Some actual)
    | Some actualNode when not (isOptionType actualNode.Type) ->
        Ok(None, Set.empty, false, Some actual)
    | Some _ ->
        let absenceMatches =
            absences |> List.filter (fun row -> row.Declaration.Binding = declarationBinding && row.Contract.Parameter = nativeOrdinal)
        match absenceMatches with
        | [] -> Error "CCS8427: An optional foreign buffer argument requires an explicit BufferAbsenceContract."
        | [absence] ->
            let directConstruction id =
                let rec walk seen current path =
                    if Set.contains current seen then None else
                    let seen = Set.add current seen
                    let path = current :: path
                    match graph.Nodes.TryFind current with
                    | Some { Kind = SemanticKind.DUConstruct(_, caseOrdinal, payload, _) }
                    | Some { Kind = SemanticKind.UnionCase(_, caseOrdinal, payload) }
                        when (caseOrdinal = 0 && payload.IsNone) || (caseOrdinal = 1 && payload.IsSome) ->
                        Some(current, caseOrdinal, payload, path)
                    | Some { Kind = SemanticKind.VarRef(_, Some inner) }
                    | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> walk seen inner path
                    | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> walk seen value path
                    | _ -> None
                walk Set.empty id []
            match directConstruction actual with
            | Some(construction, caseOrdinal, payload, transport) ->
                let selected: BoundaryBufferAbsenceSelection =
                    { Construction = construction; CaseOrdinal = caseOrdinal; Payload = payload
                      Absence = absence.Quote; Transport = transport; Obligation = NodeId 0 }
                let support = Set.union (Set.ofList transport) (Set.ofList absence.Participants)
                Ok(Some(BoundaryBufferAbsenceChoice.Direct selected), support, (caseOrdinal = 0), payload)
            | None ->
                match Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.current graph actual with
                | Ok account ->
                    let selects =
                        account.Values |> List.filter (fun row ->
                            row.Occurrence = actual && row.Operation = CallableAggregateOperation.Select && row.Selection.IsSome)
                    match selects with
                    | [select] when select.Selection.IsSome ->
                        let sel = select.Selection.Value
                        match directConstruction sel.WhenTrue, directConstruction sel.WhenFalse with
                        | Some(tCons, tOrd, tPay, tTr), Some(fCons, fOrd, fPay, fTr) when Set.ofList [tOrd; fOrd] = Set.ofList [0; 1] ->
                            let attachedProjection =
                                site.Children |> List.tryFind (fun child ->
                                    match graph.Nodes.TryFind child with
                                    | Some pNode ->
                                        match pNode.Kind, pNode.Metadata.TryFind "Baker.BoundaryOptionalTagProjection", pNode.Metadata.TryFind "Baker.BoundaryOptionalTagParameter" with
                                        | SemanticKind.DUGetTag(ta, _), Some(MetadataValue.NodeIdList [callId; ma]), Some(MetadataValue.Int pOrd) ->
                                            callId = site.Id && pOrd = tagOrdinal && ta = actual && ma = actual
                                        | _ -> false
                                    | None -> false)
                            match attachedProjection with
                            | Some tagProj ->
                                let mkLeaf cons ord pay tr =
                                    { Construction = cons; CaseOrdinal = ord; Payload = pay; Absence = absence.Quote
                                      Transport = List.distinct (actual :: tr); Obligation = NodeId 0 }
                                let choice = BoundaryBufferAbsenceChoice.Conditional(select.Occurrence, tagProj, mkLeaf tCons tOrd tPay tTr, mkLeaf fCons fOrd fPay fTr)
                                let support = Set.unionMany [Set.ofList absence.Participants; Set.ofList tTr; Set.ofList fTr; Set.ofList [actual; tagProj]]
                                let payloadOpt =
                                    match tPay, fPay with
                                    | Some p, None | None, Some p -> Some p
                                    | _ -> None
                                Ok(Some choice, support, false, payloadOpt)
                            | None -> Error "The conditional optional buffer lacks its Baker-authored option-tag projection."
                        | _ -> Error "The conditional optional buffer arms lost their None/Some constructors."
                    | _ -> Error "CCS8427: The optional foreign buffer argument lost its source Option construction or BufferAbsenceContract."
                | Error _ -> Error "CCS8427: The optional foreign buffer argument lost its source Option construction."
        | _ -> Error "CCS8427: Ambiguous BufferAbsenceContract declarations for the same parameter."

let private demandedAbsences (calls:BoundaryCall list) (rows:Map<NodeId,BoundaryCallbackAbsence>) =
    rows |> Map.filter(fun _ row -> calls |> List.exists(fun call -> call.Import=row.Import && (call.Arguments |> List.indexed |> List.exists(fun(ordinal,operand)->ordinal=row.Parameter && operand.Abi=BoundaryScalar.Entry row.Invocation && (operand.OptionalEntry |> Option.toList |> List.collect BoundaryOptionalEntryChoice.leaves |> List.exists(fun selected->selected.Payload.IsNone))))))

let private sameDuringCallAbi (left:BoundaryCallbackInvocation) (right:BoundaryCallbackInvocation) =
    left.Extent=BoundaryCallbackExtent.DuringCall && right.Extent=BoundaryCallbackExtent.DuringCall &&
    left.Signature=right.Signature && left.Signature.CallingConvention="CDecl"

/// The formation owns code; every receiving use still owns its own activation.
let private optionalOnlyUses (invocations:Map<NodeId,BoundaryCallbackInvocation>) (calls:BoundaryCall list) (entry:BoundaryClosedEntry) =
    calls |> List.forall(fun call -> call.Arguments |> List.forall(fun operand ->
        let uses=entry.Transport.Contains operand.Actual || (operand.OptionalEntry |> Option.toList |> List.collect BoundaryOptionalEntryChoice.leaves |> List.exists(fun selected->selected.Formation=Some entry.Formation))
        not uses ||
        match operand.OptionalEntry,operand.Abi with
        | Some choice,BoundaryScalar.Entry identity when choice |> BoundaryOptionalEntryChoice.leaves |> List.exists(fun selected -> selected.CaseOrdinal=1 && selected.Formation=Some entry.Formation && selected.Payload.IsSome) ->
            invocations.TryFind identity |> Option.exists(fun invocation->invocation.Extent=BoundaryCallbackExtent.DuringCall)
        | _ -> false))

let private optionalCodeWitness invocations calls (entry: BoundaryClosedEntry) (receiving: BoundaryCallbackInvocation) =
    match Map.tryFind entry.Invocation invocations with
    | Some witness when sameDuringCallAbi witness receiving && entry.Registrations.IsEmpty ->
        entry.Invocation=receiving.Identity || optionalOnlyUses invocations calls entry
    | _ -> false

let private currentOptionalInvocation graph (call:BoundaryCall) ordinal (receiving:BoundaryCallbackInvocation) =
    let declarations=Declarations.readDescriptors graph
    match declarations.CallbackInvocations |> List.filter(fun source->source.Quote=receiving.Identity) with
    | [source] ->
        receiving.Import=call.Import && receiving.Parameter=ordinal && receiving.Formal=call.Arguments[ordinal].Formal &&
        receiving.Extent=BoundaryCallbackExtent.DuringCall && source.Parameter=ordinal && source.Formal=receiving.Formal &&
        source.Scope=receiving.Scope && source.Contract=receiving.Contract
    | _ -> false

let private optionalSupport accounts (imports:Map<NodeId,BoundaryImport>) (invocations:Map<NodeId,BoundaryCallbackInvocation>) (absences:Map<NodeId,BoundaryCallbackAbsence>) (call:BoundaryCall) ordinal (selected:BoundaryOptionalEntry) =
    Ingredients.optionalEntrySourceSupport accounts call ordinal selected |> Result.bind(fun own ->
        let operand = call.Arguments[ordinal]
        match imports.TryFind call.Import, operand.Abi with
        | Some imported, BoundaryScalar.Entry identity ->
            match invocations.TryFind identity with
            | Some invocation ->
                let absent = if selected.Payload.IsSome then [] else absences.Values |> Seq.filter(fun row -> row.Import=call.Import && row.Parameter=ordinal && row.Invocation=identity) |> Seq.toList
                let extra = absent |> List.collect(fun row -> row.Quote::row.DescriptorBinding::row.Record::row.SourcePath @ (row.Inputs |> List.collect snd) @ (row.DeclarationFacts |> Map.keys |> Seq.toList)) |> Set.ofList
                Ok(Set.unionMany [own;imported.Participants;invocation.Participants;extra])
            | _ -> Error "An optional-entry claim lost its current receiving invocation descriptor."
        | _ -> Error "An optional-entry claim lost its current import.")

/// Validate the original per-use citizen before admitting its exact relation
/// rows to the boundary census or the Pending dispatch partition.
let optionalEntryClaimRows (graph: SemanticGraph) (calls: BoundaryCall list) (id: NodeId, info: ObligationInfo) =
    let body =
        match info.Body with
        | ObligationBody.Pending reasons -> Some(Choice1Of3 reasons)
        | ObligationBody.OptionalEntryArgumentConversion model -> Some(Choice2Of3 model)
        | ObligationBody.OptionalEntryAbsenceArgumentConversion model -> Some(Choice3Of3 model)
        | _ -> None
    match body with
    | Some body ->
        let accounts =
            calls |> List.collect (fun call ->
                call.Arguments |> List.mapi (fun ordinal operand -> call, ordinal, operand)
                |> List.collect (fun (call, ordinal, operand) ->
                    operand.OptionalEntry |> Option.toList |> List.collect BoundaryOptionalEntryChoice.leaves |> List.choose (fun selected ->
                        if selected.Obligation = id then Some(call, ordinal, selected) else None)))
        match accounts with
        | [call, ordinal, selected] ->
            let role = $"foreign-optional-entry-conversion-{ordinal}"
            let identityRole =
                match call.Arguments[ordinal].OptionalEntry with
                | Some (BoundaryOptionalEntryChoice.Conditional _) -> $"{role}-case-{selected.CaseOrdinal}"
                | _ -> role
            let expectedReason =
                if selected.Payload.IsNone then "Selected-target optional-entry conversion and the foreign nullable-acceptance premise remain Pending."
                else "Selected-target optional-entry conversion remains Pending."
            let imports = graph.Edges |> List.choose(fun edge -> match edge.Role with EdgeRole.BoundaryImport row->Some(row.Identity,row) | _->None) |> Map.ofList
            let invocations = graph.Edges |> List.choose(fun edge -> match edge.Role with EdgeRole.BoundaryCallbackInvocation row->Some(row.Identity,row) | _->None) |> Map.ofList
            let heldAbsences = graph.Edges |> List.choose(fun edge -> match edge.Role with EdgeRole.BoundaryCallbackAbsence row->Some(row.Quote,row) | _->None) |> Map.ofList
            let observed = absenceAccounts graph (Declarations.readDescriptors graph) imports invocations
            observed |> Result.bind(fun observed ->
                let absences=demandedAbsences calls observed
                let ownAbsences=if selected.Payload.IsSome then Map.empty else absences |> Map.filter(fun _ row->row.Import=call.Import && row.Parameter=ordinal)
                let current =
                    match body with
                    | Choice3Of3 model -> ownAbsences.TryFind model.Absence |> Option.exists(fun row->heldAbsences.TryFind model.Absence=Some row)
                    | _ -> true
                if not current || (ownAbsences |> Map.exists(fun key row -> heldAbsences.TryFind key <> Some row)) then Error "An absence conversion account is stale or withdrawn."
                else optionalSupport graph.Codata.Value.CallableAggregateDependencies imports invocations absences call ordinal selected)
            |> Result.bind (fun support ->
                [call.Arguments[ordinal]] |> List.fold (fun state operand ->
                    state |> Result.bind (fun () ->
                        match operand.OptionalEntry with
                        | None -> Ok ()
                        | Some _ -> Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.current graph operand.Actual |> Result.map ignore)) (Ok ())
                |> Result.map (fun () -> support))
            |> Result.bind (fun support ->
                let sources = List.distinct (call.Site :: Set.toList support)
                let expected = {Class=EdgeClass.Obligation; Role=EdgeRole.Constrains; Ordinal=0; Sources=sources; Target=id}
                let residence = Ingredients.row EdgeRole.EnrichedWith 0 sources id
                let edges = graph.Edges |> List.filter (fun edge -> edge.Role=EdgeRole.Constrains && edge.Target=id)
                let heldResidence = graph.Edges |> List.filter (fun edge -> edge.Target=id && edge.Role=EdgeRole.EnrichedWith)
                let key (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target
                let bodyCurrent =
                    match body with
                    | Choice1Of3 reasons ->
                        if reasons=[expectedReason] then Ok ()
                        else Error "The optional-entry Pending claim has different conversion reasons."
                    | Choice2Of3 model ->
                        let entry = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryClosedEntry entry when entry.Formation=model.Formation -> Some entry | _ -> None)
                        let source = graph.Nodes.TryFind selected.Construction |> Option.exists (fun node ->
                            match node.Kind with
                            | SemanticKind.UnionCase(_, ordinal, payload)
                            | SemanticKind.DUConstruct(_, ordinal, payload, _) -> ordinal=model.SourceCase && payload=Some model.Payload
                            | _ -> false)
                        let arms = [{CaseOrdinal=0;Choice=OptionalEntryPlanChoice.PendingAbsence;Formation=None}
                                    {CaseOrdinal=1;Choice=OptionalEntryPlanChoice.ClosedEntry;Formation=Some model.Formation}]
                        if model.Call=call.Site && model.Parameter=ordinal && model.Actual=(List.item ordinal call.Arguments).Actual &&
                           model.Construction=selected.Construction && model.SourceCase=1 && selected.CaseOrdinal=1 && source &&
                           selected.Payload=Some model.Payload && selected.Formation=Some model.Formation &&
                           (List.item ordinal call.Arguments).Abi=BoundaryScalar.Entry model.Invocation && model.Arms=arms &&
                           Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.resultRetirement graph model.Actual model.Call=Ok model.ResultRetirement &&
                           (match entry,invocations.TryFind model.Invocation with
                            | [entry: BoundaryClosedEntry],Some receiving ->
                                currentOptionalInvocation graph call ordinal receiving &&
                                optionalCodeWitness invocations calls entry receiving && entry.Transport.IsSupersetOf selected.Transport
                            | _ -> false) &&
                           info.Logic="QF_LIA" && info.Statement="The exact source Some selection has complete finite native-choice plan correspondence; target realization remains an artifact obligation." then Ok ()
                        else Error "The optional-entry conversion claim lost its exact current Some source plan."
                    | Choice3Of3 model ->
                        let account = heldAbsences.TryFind model.Absence
                        let arms=[{OptionalEntryAbsencePlanArm.CaseOrdinal=0;Choice=OptionalEntryAbsencePlanChoice.AbsentEntry};{OptionalEntryAbsencePlanArm.CaseOrdinal=1;Choice=OptionalEntryAbsencePlanChoice.RequiresClosedEntry}]
                        if model.Call=call.Site && model.Parameter=ordinal && model.Actual=call.Arguments[ordinal].Actual &&
                           model.Construction=selected.Construction && model.SourceCase=0 && selected.CaseOrdinal=0 && selected.Payload.IsNone && selected.Formation.IsNone && model.Arms=arms &&
                           Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.resultRetirement graph model.Actual model.Call=Ok model.ResultRetirement &&
                           (account |> Option.exists(fun account -> account.Import=call.Import && account.Parameter=ordinal && account.Formal=call.Arguments[ordinal].Formal && call.Arguments[ordinal].Abi=BoundaryScalar.Entry account.Invocation)) &&
                           info.Logic="QF_LIA" && info.Statement="The exact source None selection has complete finite absence-choice correspondence under its external binding hypothesis; target realization remains an artifact obligation." then Ok ()
                        else Error "The optional-entry absence conversion claim lost its exact current quoted promise or None source plan."
                if info.Kind <> role then Error "The optional-entry Pending claim has a different original argument ordinal."
                elif Result.isError bodyCurrent then bodyCurrent |> Result.map (fun () -> [expected;residence])
                elif (graph.Nodes.TryFind call.Site |> Option.bind (sourceClaimId identityRole)) <> Some info.Id then
                    Error "The optional-entry Pending claim lost its source-owned claim identity."
                elif not (graph.Nodes.TryFind id |> Option.exists (fun node ->
                    Ingredients.ownedNode node && match node.Kind with SemanticKind.Obligation claim -> claim = info | _ -> false)) then
                    Error "The optional-entry Pending claim lacks its exact owned ledger node."
                elif not (match edges with [edge] -> key edge = key expected | _ -> false) then
                    Error "The optional-entry Pending claim lost its exact ordered Constrains incidence."
                elif not (match heldResidence with [held] -> key held = key residence | _ -> false) then
                    Error "The optional-entry Pending claim lost its exact EnrichedWith residence."
                else Ok [expected; residence])
        | _ -> Error "The optional-entry Pending claim lacks one exact current operand owner."
    | _ -> Error "The optional-entry conversion claim no longer has its Pending body."

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
    | BoundaryScalar.Entry _ -> invalidOp "A native entry has no scalar numeric range."
    | BoundaryScalar.ResourceHandle _ -> invalidOp "An opaque resource handle has no scalar numeric range."
    | BoundaryScalar.WritableBytes _ -> invalidOp "A writable byte buffer has no scalar numeric range."
    | BoundaryScalar.ReadOnlyBytes _ -> invalidOp "A read-only byte buffer has no scalar numeric range."
    | BoundaryScalar.BorrowedBytes _ -> invalidOp "A borrowed result view has no scalar numeric range."

let private scalarBits = function
    | BoundaryScalar.Boolean -> 1
    | BoundaryScalar.Integer(bits, _) -> bits
    | BoundaryScalar.Entry _ -> invalidOp "A native entry has no scalar numeric width."
    | BoundaryScalar.ResourceHandle _ -> invalidOp "An opaque resource handle requires its exact resource conversion account."
    | BoundaryScalar.WritableBytes _ -> invalidOp "A writable byte buffer has no scalar numeric width."
    | BoundaryScalar.ReadOnlyBytes _ -> invalidOp "A read-only byte buffer has no scalar numeric width."
    | BoundaryScalar.BorrowedBytes _ -> invalidOp "A borrowed result view has no scalar numeric width."

let private supportedType scalar ty =
    match scalar, Types.tryGetNTUKind ty with
    | BoundaryScalar.Boolean, Some NTUKind.NTUbool -> true
    | BoundaryScalar.Entry _, Some NTUKind.NTUfnptr -> true
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

let private readImport (graph: SemanticGraph) (descriptors: Declarations.Descriptors)
                       (resources: Map<NodeId, BoundaryResourceDeclaration>)
                       (writables:Map<NodeId,BoundaryWritableBufferDeclaration>)
                       (readOnlyBuffers: Map<NodeId, BoundaryReadOnlyBufferDeclaration>)
                       (borrowedViews: Map<NodeId, BoundaryBorrowedResultViewDeclaration>) (binding: SemanticNode) library symbol =
    checked' {
        let! scope =
            binding.Parent |> needed "The external binding has no source module owner."

        do!
            require
                (graph.Nodes.TryFind scope
                 |> Option.exists (fun node ->
                     match node.Kind with
                     | SemanticKind.ModuleDef(_, members) -> List.contains binding.Id members
                     | _ -> false))
                "The external binding is not a structural member of its declared module occurrence."

        let! declarationPath, sourceFormals, body = bindingPath graph binding.Id

        let! descriptor =
            match
                descriptors.Functions
                |> List.filter (fun descriptor -> descriptor.Body = Some body)
            with
            | [ descriptor ] -> Ok descriptor
            | [] -> Error "The external binding has no matching FunctionDescriptor."
            | _ -> Error "The external binding has duplicate FunctionDescriptor declarations."

        let! _, fields =
            Declarations.recordOf graph descriptor.Node
            |> needed "The FunctionDescriptor no longer names a source record."

        let! callingId =
            field "CallingConvention" fields
            |> needed "The FunctionDescriptor has no declared calling convention."

        let! convention =
            Declarations.caseOf graph callingId
            |> Option.map (fun (_, name, _) -> name)
            |> needed "The calling convention is not a declared case."

        do! require (convention = "CDecl") $"Calling convention '{convention}' is not admitted by the scalar C contract."
        do! require (descriptor.CName = symbol) "FunctionDescriptor.CName disagrees with FidelityExtern.Symbol."

        let writable = writables.Values |> Seq.filter(fun row -> row.Declaration=binding.Id && row.Descriptor=descriptor.Node) |> Seq.toList
        let writable =
            match writable with
            | [row] when row.Parameter >= 0 && row.CountParameter >= 0 && row.Parameter <> row.CountParameter &&
                         descriptor.ParameterOrdinals.TryFind row.Parameter = Some row.BufferFormal &&
                         descriptor.ParameterOrdinals.TryFind row.CountParameter = Some row.CountFormal -> Some row
            | _ -> None
        let readOnlyRows =
            readOnlyBuffers.Values
            |> Seq.filter (fun row ->
                row.Declaration = binding.Id && row.Descriptor = descriptor.Node &&
                row.Parameter >= 0 &&
                descriptor.ParameterOrdinals.TryFind row.Parameter = Some row.BufferFormal &&
                (match row.CountParameter, row.CountFormal with
                 | None, None -> true
                 | Some cp, Some cf -> cp >= 0 && cp <> row.Parameter && descriptor.ParameterOrdinals.TryFind cp = Some cf
                 | _ -> false))
            |> Seq.toList
        do!
            require
                ((descriptor.References.IsEmpty || writable.IsSome || not readOnlyRows.IsEmpty)
                 && descriptor.PointerReferences.IsEmpty
                 && descriptor.RecordReferences.IsEmpty)
                "Reference arguments require source-settled boundary adapters; scalar C publication cannot substitute a pointer."

        let! parameterRecords =
            field "Parameters" fields
            |> Option.bind (Declarations.elementsOf graph)
            |> needed "The boundary descriptor has no complete ordered ParameterInfo vector."

        do!
            require
                (parameterRecords.Length = descriptor.Parameters.Length + descriptor.FixedSentinels.Length)
                "The boundary descriptor's native ordinal vector is incomplete."

        let sortedOrdinals = descriptor.ParameterOrdinals |> Map.toList |> List.sortBy fst
        do!
            require
                (List.map snd sortedOrdinals = List.map fst descriptor.Parameters)
                "The boundary descriptor's parameter ordinal map differs from its formal order."

        do!
            require
                (descriptor.FixedSentinels |> List.forall (fun (ordinal, _, _) ->
                    List.tryItem ordinal parameterRecords
                    |> Option.bind (Declarations.recordOf graph)
                    |> Option.bind (snd >> field "PassBy")
                    |> Option.bind (Declarations.caseOf graph)
                    |> Option.exists (fun (_, name, payload) -> name = "Fixed" && payload.IsSome)))
                "A fixed sentinel ABI parameter lost its Fixed PassBy contract."

        let parameters =
            List.zip sortedOrdinals descriptor.Parameters
            |> List.map (fun ((ordinal, _), (formal, declared)) ->
                checked' {
                    let! _, parameterFields =
                        Declarations.recordOf graph parameterRecords[ordinal]
                        |> needed "A boundary parameter declaration is missing."

                    let! passing =
                        field "PassBy" parameterFields
                        |> needed "A boundary parameter must explicitly declare PassBy.Value."

                    let writableParameter = writable |> Option.filter(fun row -> row.Parameter=ordinal && row.BufferFormal=formal)
                    let readOnlyParameter = readOnlyRows |> List.tryFind(fun row -> row.Parameter=ordinal && row.BufferFormal=formal)
                    do!
                        require
                            (Declarations.caseOf graph passing
                             |> Option.exists (fun (_, name, _) ->
                                 if writableParameter.IsSome then name = "Reference"
                                 elif readOnlyParameter.IsSome then name = "Value" || name = "ReadOnlyReference"
                                 else name = "Value"))
                            "A boundary parameter must explicitly declare PassBy.Value."

                    let! typeId =
                        field "Type" parameterFields |> needed "A boundary parameter has no TypeRef."

                    let! formalNode =
                        graph.Nodes.TryFind formal
                        |> needed "A boundary formal is absent from the source graph."

                    match Declarations.readTypeRef graph typeId |> Result.mapError _.Message with
                    | Ok _ when writableParameter.IsSome ->
                        return formal, BoundaryScalar.WritableBytes writableParameter.Value.Identity
                    | Ok _ when readOnlyParameter.IsSome ->
                        return formal, BoundaryScalar.ReadOnlyBytes readOnlyParameter.Value.Identity
                    | Ok(Declarations.DeclaredTypeRef.Entry selector) ->
                        let! invocation =
                            match
                                descriptors.CallbackInvocations
                                |> List.filter (fun invocation ->
                                    invocation.Declaration.Binding = binding.Id
                                    && invocation.AbiDescriptor = descriptor.Node
                                    && invocation.Parameter = ordinal
                                    && invocation.Formal = formal
                                    && (graph.Nodes.TryFind invocation.DescriptorBinding
                                        |> Option.bind (Declarations.qualifiedExportName graph))
                                        =
                                        Some selector)
                            with
                            | [ invocation ] -> Ok invocation
                            | _ ->
                                Error
                                    "TypeRef.Entry requires one exact current receiving callback invocation contract at its original native ordinal."

                        do!
                            require
                                (Types.tryGetNTUKind formalNode.Type = Some NTUKind.NTUfnptr ||
                                 (Declarations.optionalEntrySignature formalNode.Type |> Option.isSome))
                                "The receiving callback formal must be a nonnullable typed FnPtr."

                        return formal, BoundaryScalar.Entry invocation.Quote
                    | Error reason -> return! Error reason
                    | _ when resources.Values |> Seq.exists (fun row -> row.Release = binding.Id && row.ReleaseDescriptor = descriptor.Node && row.ReleaseFormal = formal && row.ReleaseOrdinal = ordinal) ->
                        let! resource =
                            resources.Values |> Seq.filter (fun row -> row.Release = binding.Id && row.ReleaseDescriptor = descriptor.Node)
                            |> Seq.toList |> function [row] -> Ok row | _ -> Error "The release declaration has ambiguous resource ownership."
                        do! require (Clef.Compiler.NativeTypedTree.TypeIdentities.ofType formalNode.Type = resource.HandleType)
                                "The exact release formal no longer has its declared opaque handle identity."
                        return formal, BoundaryScalar.ResourceHandle(resource.Identity, false)
                    | Ok(Declarations.DeclaredTypeRef.Pointer width) ->
                        let formalTypeId = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType formalNode.Type
                        let matchingResources =
                            resources.Values
                            |> Seq.choose (fun row ->
                                if row.PointerBits = width && formalTypeId = row.HandleType then Some(row, false)
                                elif row.PointerBits = width && formalTypeId = row.ResultType then Some(row, true)
                                else None)
                            |> Seq.toList
                        match matchingResources with
                        | [resource, nullable] -> return formal, BoundaryScalar.ResourceHandle(resource.Identity, nullable)
                        | _ :: _ :: _ -> return! Error "CCS8403: Ambiguous resource declarations for boundary resource handle parameter."
                        | [] ->
                            if isNominalCHandleType false formalNode.Type then
                                return formal, BoundaryScalar.ResourceHandle(formal, false)
                            elif isNominalCHandleType true formalNode.Type then
                                return formal, BoundaryScalar.ResourceHandle(formal, true)
                            else
                                return! Error "A boundary parameter has no admitted integer or boolean declaration; pointer and aggregate values require a source-settled adapter."
                    | _ ->
                        let! declared =
                            declared
                            |> needed
                                "A boundary parameter has no admitted integer or boolean declaration; pointer and aggregate values require a source-settled adapter."

                        let! scalar = typeRef graph typeId

                        let! scalar =
                            scalar |> needed "Void is a result convention, not a boundary parameter."

                        do!
                            require
                                (supportedType scalar formalNode.Type)
                                "A boundary formal's source kind disagrees with its declared scalar ABI."

                        do!
                            require
                                (declared.Bits = scalarBits scalar && declared.Range = scalarRange scalar)
                                "The descriptor's scalar range and TypeRef disagree."

                        return formal, scalar
                })
            |> collect

        let! parameters = parameters
        let retainedFormals = sourceFormals |> List.map (fun (_, _, id) -> id)

        let erasedUnitFormals =
            match sourceFormals, parameters with
            | [ (_, ty, id) ], [] when Types.tryGetNTUKind ty = Some NTUKind.NTUunit -> [ id ]
            | _ -> []

        do!
            require
                ((parameters |> List.map fst) @ erasedUnitFormals = retainedFormals)
                "The descriptor's formal order differs from its exact source function declaration."

        let! returnId =
            field "ReturnType" fields |> needed "The FunctionDescriptor has no ReturnType."

        let! result =
            match resources.Values |> Seq.filter (fun row -> row.Acquisition = binding.Id && row.AcquisitionDescriptor = descriptor.Node) |> Seq.toList with
            | [resource] -> Ok(Some(BoundaryScalar.ResourceHandle(resource.Identity, true)))
            | [] ->
                match borrowedViews.Values |> Seq.filter (fun row -> row.Declaration = binding.Id && row.Descriptor = descriptor.Node) |> Seq.toList with
                | [view] -> Ok(Some(BoundaryScalar.BorrowedBytes view.Identity))
                | [] -> typeRef graph returnId
                | _ -> Error "The borrowed result view declaration has ambiguous binding ownership."
            | _ -> Error "The acquisition declaration has ambiguous resource ownership."

        // A release import publishes its declared result unchanged: None for Void,
        // Integer(32, true) for the signed 32-bit C status. The status is an ordinary
        // scalar result and states no resource fact; the cleanup account is attached
        // to the ResourceHandle parameter only.
        do! require (not (resources.Values |> Seq.exists (fun row -> row.Release = binding.Id && row.ReleaseDescriptor = descriptor.Node)) ||
                     (match result with
                      | None | Some(BoundaryScalar.Integer(32, true)) -> true
                      | _ -> false))
                "A resource release result must be declared Void or a signed 32-bit integer status."

        let paramByNativeOrdinal = List.zip (List.map fst sortedOrdinals) parameters |> Map.ofList
        do! require (writable |> Option.forall (fun row ->
                        paramByNativeOrdinal.TryFind row.Parameter = Some(row.BufferFormal, BoundaryScalar.WritableBytes row.Identity) &&
                        (paramByNativeOrdinal.TryFind row.CountParameter |> Option.exists (function f, BoundaryScalar.Integer _ -> f = row.CountFormal | _ -> false)) &&
                        (match result with None | Some(BoundaryScalar.Integer(64, true)) -> true | _ -> false)))
                "The writable buffer adapter requires matching buffer/count ordinals with Void or signed-64 result."

        do! require (readOnlyRows |> List.forall (fun row ->
                        paramByNativeOrdinal.TryFind row.Parameter = Some(row.BufferFormal, BoundaryScalar.ReadOnlyBytes row.Identity) &&
                        (match row.CountParameter, row.CountFormal with
                         | None, None -> true
                         | Some cp, Some cf -> paramByNativeOrdinal.TryFind cp |> Option.exists (function f, BoundaryScalar.Integer _ -> f = cf | _ -> false)
                         | _ -> false)))
                "The read-only buffer adapter requires matching buffer and optional count parameter ordinals."

        let! bodyNode =
            graph.Nodes.TryFind body
            |> needed "The external binding body is absent from the source graph."

        do!
            require
                (match result with
                 | Some(BoundaryScalar.ResourceHandle(identity, true)) ->
                     resources.TryFind identity |> Option.exists (fun row -> Clef.Compiler.NativeTypedTree.TypeIdentities.ofType bodyNode.Type = row.ResultType)
                 | Some(BoundaryScalar.BorrowedBytes _) -> isOptionType bodyNode.Type
                 | Some scalar -> supportedType scalar bodyNode.Type
                 | None -> Types.tryGetNTUKind bodyNode.Type = Some NTUKind.NTUunit)
                "The binding result's source kind disagrees with its declared boundary result."

        let descriptorBindings =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                match node.Kind, node.Children with
                | SemanticKind.Binding _, children when node.Parent = Some scope ->
                    children
                    |> List.tryLast
                    |> Option.bind (Declarations.recordOf graph)
                    |> Option.bind (fun (record, _) -> if record.Id = descriptor.Node then Some node.Id else None)
                | _ -> None)
            |> Set.ofSeq

        let! descriptorBinding =
            match Set.toList descriptorBindings with
            | [ binding ] -> Ok binding
            | _ -> Error "The FunctionDescriptor must retain exactly one source declaration binding."

        do!
            require
                (graph.Nodes.TryFind scope
                 |> Option.exists (fun node ->
                     match node.Kind with
                     | SemanticKind.ModuleDef(_, members) -> List.contains descriptorBinding members
                     | _ -> false))
                "The FunctionDescriptor binding is not a member of its exact source module occurrence."

        let invocationRoots =
            descriptors.CallbackInvocations
            |> List.filter (fun invocation -> invocation.Declaration.Binding = binding.Id)
            |> List.collect (fun invocation -> [ invocation.DescriptorBinding; invocation.ScopeBinding ])
        let writableRoots =
            descriptors.WritableBuffers |> List.filter(fun row -> writable |> Option.exists(fun current->row.Quote=current.Identity))
            |> List.map _.DescriptorBinding
        let readOnlyRoots =
            descriptors.ReadOnlyBuffers |> List.filter(fun row -> readOnlyRows |> List.exists(fun current -> row.Quote = current.Identity))
            |> List.map _.DescriptorBinding
        let callbackContextRoots =
            match Declarations.qualifiedExportName graph binding with
            | None -> []
            | Some bindingName ->
                graph.Nodes.Values
                |> Seq.choose (fun node ->
                    match node.Kind, node.Children with
                    | SemanticKind.Binding _, [bodyId] ->
                        match graph.Nodes.TryFind bodyId with
                        | Some { Kind = SemanticKind.Quote(recordId, _) } ->
                            match Declarations.recordOf graph recordId with
                            | Some(recNode, recFields) when Declarations.typeName recNode = Some "CallbackContextDescriptor" ->
                                match field "Binding" recFields |> Option.bind (Declarations.stringOf graph) with
                                | Some declaredBinding when declaredBinding = bindingName -> Some node.Id
                                | _ -> None
                            | _ -> None
                        | _ -> None
                    | _ -> None)
                |> Seq.toList
        let! byteRoots =
            if writable.IsNone then Ok [] else
                Bytes.byteRepresentation graph |> needed "The writable import lacks its current offered byte representation."
                |> Result.map(fun (_,declaration)->[declaration])

        let! facts =
            (descriptorBinding :: invocationRoots @ writableRoots @ readOnlyRoots @ callbackContextRoots @ byteRoots)
            |> List.distinct
            |> List.fold
                (fun state root ->
                    state
                    |> Result.bind (fun facts ->
                        declarationFacts graph root
                        |> Result.map (fun next -> Map.fold (fun facts id fact -> Map.add id fact facts) facts next)))
                (Ok Map.empty)

        // The original immutable binding's name/parent are declaration facts,
        // even when an optional anchor has no executable source occurrence.
        let! original = (declarationPath @ retainedFormals) |> List.distinct |> List.map(fun id ->
            graph.Nodes.TryFind id |> needed "The original external declaration path was withdrawn."
            |> Result.bind declarationFact |> Result.map(fun fact -> id,fact)) |> collect
        let facts = original |> List.fold(fun facts (id,fact) -> Map.add id fact facts) facts

        let participants =
            Set.unionMany
                [
                    facts |> Map.keys |> Set.ofSeq
                    descriptorBindings
                    Set.ofList (scope :: body :: retainedFormals @ declarationPath)
                ]

        let! types = sourceTypes graph (declarationPath @ (body :: retainedFormals))

        return
            {
                Identity = descriptor.Node
                Binding = binding.Id
                Scope = scope
                Library = library
                Symbol = symbol
                CallingConvention = convention
                DeclarationPath = declarationPath
                Parameters = parameters
                Result = result
                Participants = participants
                SourceTypes = types
                DeclarationFacts = facts
            }
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
    | BoundaryScalar.Entry _ -> Error "Native entry arguments require their declared code signature, not a numeric width."
    | BoundaryScalar.ResourceHandle _ -> Error "An opaque resource handle has no source numeric width."
    | BoundaryScalar.WritableBytes _ -> Error "A writable byte buffer has no source numeric width."
    | BoundaryScalar.ReadOnlyBytes _ -> Error "A read-only byte buffer has no source numeric width."
    | BoundaryScalar.BorrowedBytes _ -> Error "A borrowed result view has no source numeric width."
    | BoundaryScalar.Integer _ -> checked' {
        let! representation = RangeAnalysis.selectedRepresentation graph id |> needed "The scalar occurrence has no source-selected offered integer representation."
        do! require (NumericRepresentation.isOffered representation && (representation.Family = "int" || representation.Family = "uint"))
                "The scalar occurrence's selected representation is not an offered integer representation."
        do! require (RangeAnalysis.heldWidth graph id = Some representation.Bits)
                "The scalar occurrence's held width disagrees with its selected offered representation."
        return representation.Bits }

let private readCall (graph: SemanticGraph) (site: SemanticNode) callee args path (import: BoundaryImport)
                     (entry:NodeId option) (resource:BoundaryResourceUse option) (writable:BoundaryWritableBufferUse option)
                     (readOnlyBuffers: Map<NodeId, BoundaryReadOnlyBufferDeclaration>)
                     (readOnlyUses: Map<NodeId * int, BoundaryReadOnlyBufferUse>)
                     (resources: Map<NodeId, BoundaryResourceDeclaration>)
                     (resolveBufferAbsence: int -> NodeId -> NodeId -> Result<BoundaryBufferAbsenceChoice option * Set<NodeId>, string>) = checked' {
    let resourceResultAbi = import.Result |> Option.exists (function BoundaryScalar.ResourceHandle _ -> true | _ -> false)
    do! require (not resourceResultAbi || (resource.IsSome && entry.IsNone))
            "A resource-acquiring call requires its exact direct acquisition/conversion account; scalar and indirect calls grant no such authority."
    let hasResourceHandleArg = import.Parameters |> List.exists (snd >> function BoundaryScalar.ResourceHandle _ -> true | _ -> false)
    do! require (not hasResourceHandleArg || entry.IsNone)
            "An indirect entry call cannot take opaque resource handle parameters directly without a boundary declaration."
    do! require (import.Parameters |> List.forall(fun (_,abi)->
                    match abi with
                    | BoundaryScalar.WritableBytes declaration -> writable |> Option.exists(fun row->row.Call=site.Id && row.Declaration=declaration && entry.IsNone && resource.IsNone)
                    | _ -> true))
            "A writable byte ABI requires its exact direct application, allocation and current count/storage proof account."
    let baseChildren =
        site.Children
        |> List.filter (fun child -> not (graph.Nodes.TryFind child |> Option.exists BoundaryDeclarations.isOptionalTagProjection))
    let attachedProjections =
        site.Children
        |> List.skip baseChildren.Length
    let ordered =
        match entry, site.Kind with
        | None, _ ->
            baseChildren = callee :: args
            && site.Children = baseChildren @ attachedProjections
        | Some _, SemanticKind.Application(intrinsic, operands) ->
            operands = callee :: args
            && baseChildren = intrinsic :: operands
            && site.Children = baseChildren @ attachedProjections
            && (target graph intrinsic |> Option.exists (fun (node, _) ->
                match node.Kind with SemanticKind.Intrinsic { Module = IntrinsicModule.FnPtr; Operation = "invoke" } -> true | _ -> false))
        | _ -> false
    do! require ordered "The boundary application's ordered operands disagree with its source structural children."
    let operands, erased =
        match import.Parameters, args with
        | [], [unit] when graph.Nodes.TryFind unit |> Option.exists (fun node -> Types.tryGetNTUKind node.Type = Some NTUKind.NTUunit) -> [], [unit]
        | _ -> args, []
    do! require (operands.Length = import.Parameters.Length) "The external call does not supply exactly the declared ordered scalar arguments."
    let! supportedArguments =
        List.zip operands import.Parameters |> List.indexed |> List.map (fun (ordinal, (actual, (formal, abi))) -> checked' {
            let! node = graph.Nodes.TryFind actual |> needed "An actual boundary argument is absent from the source graph."
            let! optionalEntry, optionalSupport =
                match abi with
                | BoundaryScalar.Entry identity when Declarations.optionalEntrySignature node.Type |> Option.isSome -> checked' {
                    let selections =
                        (CallbackDeclarations.read graph).OptionalReceiving |> List.filter(fun row ->
                            row.Call=site.Id && row.Operand=actual && row.Invocation.Quote=identity && row.Invocation.Formal=formal)
                    let! account = Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.current graph actual
                    let! selected, branch =
                        match selections with
                        | [row] -> Ok(row, None)
                        | [first; second] ->
                            let candidates = account.Values |> List.filter (fun row ->
                                row.Operation = CallableAggregateOperation.Select && row.Selection.IsSome &&
                                Set.ofList [row.Selection.Value.WhenTrue; row.Selection.Value.WhenFalse] = Set.ofList [first.Construction; second.Construction])
                            match candidates with
                            | [row] -> Ok(first, Some(row, first, second))
                            | _ -> Error "The optional callback has no unique current selection account for both constructor arms."
                        | _ -> Error "The optional callback lost its exact current selection account."
                    let! construction =
                        account.Values |> List.filter(fun row -> row.Occurrence=selected.Construction && row.Operation=CallableAggregateOperation.Construct)
                        |> function [row] -> Ok row | _ -> Error "The optional callback lost its exact current Option construction account."
                    do! require (construction.Value=selected.Payload &&
                                 (construction.Tag |> Option.exists(fun tag -> tag.Constructor=selected.Construction && tag.CaseOrdinal=selected.CaseOrdinal && tag.Payload=selected.Payload)))
                            "The optional callback case ordinal or payload differs from its current Option account."
                    let own = account.Values |> List.filter(fun row->row.Occurrence=actual && row.Slot=construction.Slot)
                    let instance =
                        match own with
                        | [row] when branch.IsSome ->
                            let select, _, _ = branch.Value
                            row.Slot = select.Slot &&
                            ((row.Operation = CallableAggregateOperation.Select && row.Occurrence = select.Occurrence) ||
                             (row.Operation = CallableAggregateOperation.Transport && row.Aggregate = select.Occurrence &&
                              List.tryLast row.FormationInputs = Some select.Occurrence))
                        | [row] when row.Aggregate=selected.Construction -> true
                        | [row] ->
                            let supplier = if row.Operation=CallableAggregateOperation.Result then Some row.Occurrence
                                           elif row.Operation=CallableAggregateOperation.Transport then Some row.Aggregate else None
                            match supplier |> Option.map(fun supplier->account.Values |> List.filter(fun result->
                                result.Occurrence=supplier && result.Aggregate=supplier && result.Slot=construction.Slot &&
                                result.Operation=CallableAggregateOperation.Result)) with
                            | Some [result] ->
                                let returned =
                                    match result.FormationInputs,selected.Payload with
                                    | [_;_;_;_;_;original],None -> original=selected.Construction
                                    | [_;_;_;_;_;original;payload],Some expected -> original=selected.Construction && payload=expected
                                    | _ -> false
                                returned && result.Value=construction.Value && result.Tag=construction.Tag &&
                                result.Alternatives=construction.Alternatives && row.Tag=result.Tag && row.Alternatives=result.Alternatives
                            | _ -> false
                        | _ -> false
                    do! require instance "The optional callback lost its exact application result instance account."
                    let! formation =
                        match selected.Payload, selected.Receiving with
                        | None, None -> Ok None
                        | Some _, Some receiving ->
                            Clef.Compiler.Baker.Ingredients.CompilerOwnedEntries.tryFormation graph receiving.Address
                            |> needed "The optional callback payload has no current closed formation." |> Result.map (fun row -> Some row.Formation)
                        | _ -> Error "The optional callback presence differs from its closed receiving evidence."
                    let participants =
                        Set.unionMany [Set.ofList selected.Transport; Set.ofList selected.Invocation.Participants
                                       account.Sources |> List.map _.Node |> Set.ofList
                                       Set.ofList [site.Id;actual;formal;import.Identity;selected.Construction]]
                    let direct = {Construction=selected.Construction;CaseOrdinal=selected.CaseOrdinal;Payload=selected.Payload
                                  Formation=formation;Transport=Set.ofList selected.Transport;Obligation=NodeId 0}
                    match branch with
                    | None -> return Some (BoundaryOptionalEntryChoice.Direct direct), participants
                    | Some (select, first, second) ->
                        let! selection = select.Selection |> needed "The optional branch lost its immutable source selection."
                        let! transport =
                            match own with
                            | [row] when row.Operation = CallableAggregateOperation.Select && row.Occurrence = select.Occurrence -> Ok [actual]
                            | [row] when row.Operation = CallableAggregateOperation.Transport && row.Aggregate = select.Occurrence -> Ok (actual :: row.FormationInputs)
                            | _ -> Error "The optional branch actual lacks its exact immutable transport path."
                        let leaf (source: CallbackDeclarations.OptionalReceivingCallback) = checked' {
                            let! sourceRow = account.Values |> List.filter (fun row -> row.Occurrence = source.Construction && row.Slot = select.Slot && row.Operation = CallableAggregateOperation.Construct)
                                             |> function [row] -> Ok row | _ -> Error "The optional branch arm has no exact current constructor account."
                            let current = sourceRow.Value = source.Payload &&
                                          (sourceRow.Tag |> Option.exists (fun tag -> tag.Constructor = source.Construction && tag.CaseOrdinal = source.CaseOrdinal && tag.Payload = source.Payload))
                            do! require current "The optional branch arm differs from its current constructor tag or payload."
                            let! formed =
                                match source.Payload, source.Receiving with
                                | None, None -> Ok None
                                | Some _, Some receiving -> Clef.Compiler.Baker.Ingredients.CompilerOwnedEntries.tryFormation graph receiving.Address
                                                            |> needed "The optional branch payload has no current closed formation." |> Result.map (fun row -> Some row.Formation)
                                | _ -> Error "The optional branch presence differs from its closed receiving evidence."
                            return { Construction = source.Construction; CaseOrdinal = source.CaseOrdinal; Payload = source.Payload
                                     Formation = formed; Transport = Set.ofList (source.Construction :: transport); Obligation = NodeId 0 } }
                        let! left = leaf first
                        let! right = leaf second
                        let! whenTrue, whenFalse =
                            if first.Construction = selection.WhenTrue && second.Construction = selection.WhenFalse then Ok(left, right)
                            elif second.Construction = selection.WhenTrue && first.Construction = selection.WhenFalse then Ok(right, left)
                            else Error "The optional branch leaves differ from their source condition order."
                        do! require (Set.ofList [whenTrue.CaseOrdinal; whenFalse.CaseOrdinal] = Set.ofList [0; 1])
                                "The optional branch requires distinct present and absent cases."
                        let expectedIdentity = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type
                        let! tagProjection =
                            attachedProjections
                            |> List.filter (fun child ->
                                match graph.Nodes.TryFind child with
                                | Some projectionNode ->
                                    match
                                        projectionNode.Kind,
                                        projectionNode.Metadata.TryFind "Baker.BoundaryOptionalTagProjection",
                                        projectionNode.Metadata.TryFind "Baker.BoundaryOptionalTagParameter"
                                    with
                                    | SemanticKind.DUGetTag(targetActual, targetType),
                                      Some(MetadataValue.NodeIdList [callId; metaActual]),
                                      Some(MetadataValue.Int paramOrdinal) ->
                                        callId = site.Id
                                        && paramOrdinal = ordinal
                                        && targetActual = actual
                                        && metaActual = actual
                                        && projectionNode.Children = [actual]
                                        && Clef.Compiler.NativeTypedTree.TypeIdentities.ofType targetType = expectedIdentity
                                    | _ -> false
                                | None -> false)
                            |> function
                                | [projectionId] -> Ok projectionId
                                | _ -> Error "The conditional optional callback lacks its Baker-authored option-tag projection."
                        let support = Set.unionMany [participants; whenTrue.Transport; whenFalse.Transport; Set.ofList [tagProjection; whenTrue.Construction; whenFalse.Construction]]
                        return Some (BoundaryOptionalEntryChoice.Conditional(select.Occurrence, tagProjection, whenTrue, whenFalse)), support }
                | _ -> Ok (None, Set.empty)
            let! bufferAbsence, absenceSupport =
                match abi with
                | BoundaryScalar.ReadOnlyBytes _ | BoundaryScalar.WritableBytes _ ->
                    resolveBufferAbsence ordinal actual formal
                | _ -> Ok(None, Set.empty)
            let optionalNullBuffer =
                bufferAbsence |> Option.exists (fun choice ->
                    BoundaryBufferAbsenceChoice.leaves choice |> List.forall (fun leaf -> leaf.CaseOrdinal = 0 && leaf.Payload.IsNone))
            let readOnlyRow =
                match abi with
                | BoundaryScalar.ReadOnlyBytes declId ->
                    readOnlyBuffers.TryFind declId
                    |> Option.bind (fun roDecl -> readOnlyUses.TryFind(site.Id, roDecl.Parameter))
                | _ -> None
            do! require (match abi with
                         | BoundaryScalar.Entry _ when optionalEntry.IsSome -> true
                         | BoundaryScalar.ResourceHandle(decl, nullable) ->
                             resource.IsSome ||
                             (resources.TryFind decl |> Option.exists (fun res ->
                                 let actualType = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type
                                 if nullable then actualType = res.ResultType else actualType = res.HandleType)) ||
                             (decl = formal && isNominalCHandleType nullable node.Type &&
                              import.SourceTypes.TryFind formal = Some (Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type))
                         | BoundaryScalar.WritableBytes _ ->
                             writable |> Option.exists (fun row -> row.Buffer = actual) || optionalNullBuffer
                         | BoundaryScalar.ReadOnlyBytes _ ->
                             (readOnlyRow |> Option.exists (fun row -> row.Buffer = actual)) || optionalNullBuffer
                         | _ -> supportedType abi node.Type)
                    "An actual boundary argument's source kind disagrees with the declared formal."
            do! require (import.SourceTypes.TryFind formal = Some (Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type))
                    "The actual boundary argument does not retain its formal's native kind and dimension identity."
            let! meet =
                match abi with
                | BoundaryScalar.Entry _ | BoundaryScalar.ResourceHandle _ | BoundaryScalar.WritableBytes _ | BoundaryScalar.ReadOnlyBytes _ -> Ok None
                | _ -> checked' {
                    let! range = match abi with BoundaryScalar.Boolean -> Ok ValueRange.boolean | _ -> node.ValueRange |> needed "The actual scalar argument lacks an established source range."
                    let! sourceBits = sourceWidth graph actual abi
                    return! adaptation graph site.Id actual sourceBits (scalarBits abi) range }
            return { Actual = actual; Formal = formal; Abi = abi; Adaptation = meet; OptionalEntry = optionalEntry; BufferAbsence = bufferAbsence }, Set.union optionalSupport absenceSupport }) |> collect
    let arguments = supportedArguments |> List.map fst
    let expectedProjections =
        arguments
        |> List.collect (fun argument ->
            let entryProj =
                match argument.OptionalEntry with
                | Some(BoundaryOptionalEntryChoice.Conditional(_, tagProjection, _, _)) -> [tagProjection]
                | _ -> []
            let bufferProj =
                match argument.BufferAbsence with
                | Some(BoundaryBufferAbsenceChoice.Conditional(_, tagProjection, _, _)) -> [tagProjection]
                | _ -> []
            entryProj @ bufferProj)
    do! require (attachedProjections = expectedProjections) "The boundary application's attached option-tag projections disagree with its conditional optional arguments."
    let! resultAdaptation =
        match import.Result with
        | None -> checked' {
            do! require (Types.tryGetNTUKind site.Type = Some NTUKind.NTUunit) "A void foreign call cannot publish a non-unit source result."
            return None }
        | Some(BoundaryScalar.ResourceHandle _) -> Ok None
        | Some(BoundaryScalar.BorrowedBytes _) -> checked' {
            do! require (isOptionType site.Type) "The borrowed result view call result must retain its nullable Option type."
            return None }
        | Some abi -> checked' {
            do! require (supportedType abi site.Type) "The call result's source kind disagrees with its boundary declaration."
            let! targetBits = sourceWidth graph site.Id abi
            let input = match abi with BoundaryScalar.Integer _ -> site.ValueRange |> Option.defaultValue ValueRange.Unbounded | _ -> scalarRange abi
            return! adaptation graph site.Id site.Id (scalarBits abi) targetBits input }
    let! types = sourceTypes graph (site.Id :: args)
    return { Site = site.Id; Import = import.Identity; Callee = callee; Entry = entry; Arguments = arguments; ErasedUnitArguments = erased
             Result = import.Result; ResultAdaptation = resultAdaptation; Resource = resource
             Participants = Set.unionMany [import.Participants; path; Set.ofList (site.Id :: callee :: args)
                                           supportedArguments |> List.map snd |> Set.unionMany]
             SourceTypes = types }
}

/// Compose the existing evaluation owner's finite relations. Source syntax is
/// consulted only to bind the recorded event/read/case incidence; it does not
/// discover a second control-flow graph.
let private resourceFlow (graph: SemanticGraph) (resource: BoundaryResourceDeclaration)
                         (conversion: ResourceConversionModel) (conversionClaim:NodeId) (cleanupClaim:NodeId) = checked' {
    let! implementation = MemoryAccessRecipes.nearestLambda graph conversion.Acquisition
                          |> needed "Resource cleanup requires one exact ordinary callable activation."
    let! lambda = graph.Nodes.TryFind implementation |> needed "The resource activation was withdrawn."
    let! owner, body =
        match lambda.Kind, lambda.Parent with
        | SemanticKind.Lambda(_, body, [], _, _), Some owner -> Ok(owner, body)
        | _ -> Error "Resource handles cannot cross captured or unknown callable frames."
    let expected = SequenceEvaluationRecipes.forOrdinaryRoot graph owner implementation body
    let evaluation =
        { Enrichment.empty with
            NewEdges = graph.Edges |> List.filter (fun edge ->
                edge.Class = EdgeClass.Evaluation && List.tryHead edge.Sources = Some owner) }
    let incidence (edge:Hyperedge) = edge.Class,edge.Role,edge.Ordinal,edge.Sources,edge.Target
    do! require (List.map incidence evaluation.NewEdges = List.map incidence expected.NewEdges)
            "Resource cleanup requires the current pre-numeric ordinary evaluation census."
    let! relations = evaluation.NewEdges |> List.map (fun edge ->
        let role =
            match edge.Role with
            | EdgeRole.EvaluationRoot -> Some ResourceEvaluationRole.Root
            | EdgeRole.EvaluationOperand access -> Some(ResourceEvaluationRole.Operand access)
            | EdgeRole.EvaluationFlow(fromPort, toPort, transfer) -> Some(ResourceEvaluationRole.Flow(fromPort, toPort, transfer))
            | EdgeRole.EvaluationPending reason -> Some(ResourceEvaluationRole.Pending reason)
            | _ -> None
        role |> needed "Resource cleanup does not admit captured evaluation operands."
        |> Result.map (fun role -> { Role=role; Ordinal=edge.Ordinal; Sources=edge.Sources; Target=edge.Target }:ResourceEvaluationRelation)) |> collect
    do! require (relations |> List.forall (fun relation ->
        match relation.Role with ResourceEvaluationRole.Pending _ | ResourceEvaluationRole.Operand EvaluationAccess.Storage -> false | _ -> true)) "Resource cleanup has an unresolved evaluation relation or mutable storage flow."
    let operands site =
        relations |> List.choose (fun row ->
            match row.Role, row.Sources with
            | ResourceEvaluationRole.Operand EvaluationAccess.Value, [actualOwner; value] when actualOwner=owner && row.Target=site -> Some(row.Ordinal,value)
            | _ -> None) |> List.sortBy fst
    let siteIds = relations |> List.map _.Target |> Set.ofList
    let identity id = graph.Nodes.TryFind id |> Option.map (fun node -> Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type)
    let forwarded (node:SemanticNode) =
        match node.Kind,node.Children with
        | SemanticKind.VarRef(_,Some binding),_ -> Some binding
        | SemanticKind.Binding(_,false,false,_),[initializer] -> Some initializer
        | SemanticKind.TypeAnnotation(inner,_),[actual] when actual=inner -> Some inner
        | _ -> None
    // A monotone lineage fold over the finite evaluation census; no recursive
    // callee/body walk or name-based resource supplier completion.
    let optionSites,handleSites =
        (Set.singleton conversion.Acquisition,Set.empty,true)
        |> Seq.unfold(fun (optionSites,handleSites,changed) ->
            if not changed then None else
            let optionNext,handleNext =
                siteIds |> Set.fold (fun (options:Set<NodeId>,handles:Set<NodeId>) id ->
                    let node=graph.Nodes[id]
                    match identity id,forwarded node,node.Kind with
                    | Some ty,Some source,_ when ty=resource.ResultType && options.Contains source -> options.Add id,handles
                    | Some ty,Some source,_ when ty=resource.HandleType && handles.Contains source -> options,handles.Add id
                    | Some ty,_,SemanticKind.DUEliminate(source,ordinal,name,_) when ty=resource.HandleType && ordinal=conversion.SomeCase && name="Some" && options.Contains source -> options,handles.Add id
                    | _ -> options,handles) (optionSites,handleSites)
            Some((optionNext,handleNext),(optionNext,handleNext,optionNext<>optionSites || handleNext<>handleSites)))
        |> Seq.last
    do! require (siteIds |> Set.forall (fun id ->
        match identity id with
        | Some ty when ty=resource.ResultType -> optionSites.Contains id
        | Some ty when ty=resource.HandleType -> handleSites.Contains id
        | _ -> true)) "Resource handle lineage is ambiguous, merged or crosses an unsupported frame."
    do! require (identity body<>Some resource.ResultType && identity body<>Some resource.HandleType) "Resource Option or handle values cannot escape through a callable result."
    let! cases = siteIds |> Set.toList |> List.choose (fun id ->
        match graph.Nodes[id].Kind with
        | SemanticKind.CaseElimination(subject,arms) -> Some(checked' {
            do! require (optionSites.Contains subject) "Resource cleanup cannot settle an unrelated or uncorrelated case guard."
            let! arms = arms |> List.map (fun arm -> checked' {
                do! require (arm.Guard.IsNone && arm.Bindings.IsEmpty) "A resource case requires the existing shallow guard-free arm account."
                let! ordinal = match arm.Pattern with
                               | Pattern.Union(_,ordinal,_,_) -> Ok(Some ordinal)
                               | Pattern.Wildcard -> Ok None
                               | _ -> Error "A resource case pattern is outside the exact Option profile."
                let result=match graph.Nodes.TryFind arm.Body with Some {Kind=SemanticKind.Literal(NativeLiteral.Bool value)} -> Some value | _ -> None
                return { Ordinal=ordinal; Body=arm.Body; BooleanResult=result }:ResourceFlowCaseArm }) |> collect
            return {Site=id;Subject=subject;Domain=[conversion.NoneCase;conversion.SomeCase];Arms=arms}:ResourceFlowCase })
        | _ -> None) |> collect
    let caseMap = cases |> List.map (fun row -> row.Site,row) |> Map.ofList
    let literals = siteIds |> Set.toList |> List.choose (fun id ->
        match graph.Nodes[id].Kind with SemanticKind.Literal(NativeLiteral.Bool value) -> Some(id,value) | _ -> None)
    let knownGuard id =
        literals |> List.exists(fst>>(=)id) ||
        (caseMap.TryFind id |> Option.exists(fun row->row.Arms |> List.forall(fun arm->arm.BooleanResult.IsSome)))
    do! require (relations |> List.forall(fun row->
        match row.Role with
        | ResourceEvaluationRole.Flow(_,_,EvaluationTransfer.WhenTrue)
        | ResourceEvaluationRole.Flow(_,_,EvaluationTransfer.WhenFalse) ->
            operands row.Target |> List.tryFind(fst>>(=)0) |> Option.exists(snd>>knownGuard)
        | ResourceEvaluationRole.Flow(_,_,EvaluationTransfer.Resume) -> false
        | _ -> true)) "Resource cleanup has unknown or uncorrelated guard feasibility."
    let descriptors = Declarations.readDescriptors graph
    let declaredReleases = descriptors.Resources |> List.map (fun row -> row.Release.Binding) |> Set.ofList
    let isBorrowedHandleCall (binding: SemanticNode) (args: NodeId list) =
        Declarations.lambdaOfBinding graph binding.Id
        |> Option.bind (fun (_, body) -> descriptors.Functions |> List.tryFind (fun f -> f.Body = Some body))
        |> Option.exists (fun declaredFn ->
            let isBorrowed =
                Declarations.recordOf graph declaredFn.Node
                |> Option.bind (fun (_, fields) -> field "OwnershipTransfer" fields)
                |> Option.bind (Declarations.caseOf graph)
                |> Option.exists (fun (_, name, _) -> name = "Borrowed")
            isBorrowed &&
            args.Length = declaredFn.Parameters.Length &&
            (List.zip args declaredFn.Parameters
             |> List.forall (fun (actual, (formalId, _)) ->
                 not (handleSites.Contains actual) ||
                 (not (List.exists (fst >> (=) formalId) declaredFn.References) &&
                  not (List.exists (fst >> (=) formalId) declaredFn.PointerReferences) &&
                  not (List.exists (fst >> (=) formalId) declaredFn.RecordReferences)))))
    let! siteActions =
        siteIds |> Set.toList |> List.choose (fun id ->
            match graph.Nodes[id].Kind with
            | SemanticKind.Application(callee, args)
                when id <> conversion.Acquisition &&
                     (args |> List.exists (fun actual -> handleSites.Contains actual || optionSites.Contains actual)) -> Some(checked' {
                let! binding, _ = target graph callee |> needed "A resource path contains an unresolved call."
                do! require (BoundaryDeclarations.isExternal binding) "Interprocedural resource use is outside the admitted local profile."
                if declaredReleases.Contains binding.Id then
                    let! actual = match args with [actual] when handleSites.Contains actual -> Ok actual | _ -> Error "A resource path permits only its explicit unary handle release call."
                    return Choice1Of2 (id, (actual, binding.Id))
                elif isBorrowedHandleCall binding args then
                    return Choice2Of2 id
                else
                    let! actual = match args with [actual] when handleSites.Contains actual -> Ok actual | _ -> Error "A resource path permits only its explicit unary handle release call."
                    let _ = actual
                    return! Error "A handle can be passed only to an exact current declared resource release." })
            | _ -> None) |> collect
    let releaseSites = siteActions |> List.choose (function Choice1Of2 item -> Some item | Choice2Of2 _ -> None) |> Map.ofList
    let borrowedSites = siteActions |> List.choose (function Choice2Of2 id -> Some id | Choice1Of2 _ -> None) |> Set.ofList
    let contained =
        relations
        |> List.forall (fun row ->
            match row.Role, row.Sources with
            | ResourceEvaluationRole.Operand EvaluationAccess.Value, [ _; actual ] when
                optionSites.Contains actual || handleSites.Contains actual
                ->
                let parent = graph.Nodes[row.Target]

                match parent.Kind with
                | SemanticKind.Sequential _ -> true
                | SemanticKind.CaseElimination(subject, _) -> subject = actual && optionSites.Contains actual
                | SemanticKind.DUEliminate(subject, ordinal, _, _) ->
                    subject = actual && optionSites.Contains actual && ordinal = conversion.SomeCase
                | SemanticKind.Application _ ->
                    (releaseSites.TryFind row.Target
                     |> Option.exists (fun (operand, _) -> operand = actual && handleSites.Contains actual))
                    || (borrowedSites.Contains row.Target && handleSites.Contains actual)
                | _ ->
                    forwarded parent = Some actual
                    && (optionSites.Contains parent.Id || handleSites.Contains parent.Id)
            | _ -> true)

    do!
        require
            contained
            "A resource Option or handle cannot enter a tuple, record, collection, storage, or unsupported value consumer."

    let event site =
        let node=graph.Nodes[site]
        if site=conversion.Acquisition then Some ResourceFlowEvent.Acquisition
        elif releaseSites.ContainsKey site then let actual,release=releaseSites[site] in Some(ResourceFlowEvent.Release(actual,release))
        elif handleSites.Contains site then
            match node.Kind,forwarded node with
            | SemanticKind.DUEliminate(source,_,_,_),_ -> Some(ResourceFlowEvent.Payload source)
            | _,Some source -> Some(ResourceFlowEvent.HandleAlias source)
            | _ -> None
        elif optionSites.Contains site then forwarded node |> Option.map ResourceFlowEvent.OptionAlias
        else None
    // Expand original operand incidences, retaining the ordinal context of
    // each demand. Sharing a subject never joins its separate evaluations.
    let initialExpansion=Ok([],[body,[],Set.empty])
    let! occurrences =
        initialExpansion |> Seq.unfold(fun state ->
            match state with
            | Error _ | Ok(_,[]) -> None
            | Ok(seen,(site,context,ancestors)::rest) ->
                let next =
                    if List.length seen>=4096 then Error "Resource evaluation exceeds the bounded finite occurrence profile."
                    elif Set.contains site ancestors then Error "Resource cleanup requires acyclic evaluation."
                    else
                        let children=operands site |> List.map (fun (ordinal,child) -> child,context@[ordinal],Set.add site ancestors)
                        Ok((site,context)::seen,children@rest)
                Some(next,next))
        |> Seq.tryLast |> Option.defaultValue initialExpansion |> Result.map(fun (seen,_)->List.rev seen)
    let! rawEdges = occurrences |> List.collect (fun (site,context) ->
        relations |> List.mapi (fun index row -> index,row) |> List.choose (fun (index,row) ->
            if row.Target<>site then None else
            match row.Role,row.Sources with
            | ResourceEvaluationRole.Flow(fromPort,toPort,transfer),_ ->
                Some(Ok[((site,context,fromPort),(site,context,toPort),index,ResourceFlowConnection.Local,transfer)])
            | ResourceEvaluationRole.Operand EvaluationAccess.Value,[_;child] ->
                Some(Ok[((site,context,EvaluationPort.OperandEntry row.Ordinal),(child,context@[row.Ordinal],EvaluationPort.Entry),index,ResourceFlowConnection.OperandEntry,EvaluationTransfer.Continue)
                        ((child,context@[row.Ordinal],EvaluationPort.Exit),(site,context,EvaluationPort.OperandExit row.Ordinal),index,ResourceFlowConnection.OperandExit,EvaluationTransfer.Continue)])
            | ResourceEvaluationRole.Root,_ -> None
            | _ -> Some(Error "Resource evaluation has an unexpanded relation."))) |> collect |> Result.map List.concat
    let pointKeys = rawEdges |> List.collect(fun (source,target,_,_,_)->[source;target]) |> Set.ofList
    let initialCounts = pointKeys |> Set.toList |> List.map(fun key -> key,rawEdges |> List.filter(fun (_,target,_,_,_)->target=key) |> List.length) |> Map.ofList
    let initialRank=Ok([],initialCounts,initialCounts |> Map.toList |> List.choose(fun (key,count)->if count=0 then Some key else None))
    let! ranked =
        initialRank |> Seq.unfold(fun state ->
            match state with
            | Error _ | Ok(_,_,[]) -> None
            | Ok(ranked,counts,key::rest) ->
                let counts=counts.Remove key
                let counts,ready =
                    rawEdges |> List.filter(fun (source,_,_,_,_)->source=key)
                    |> List.fold(fun ((counts:Map<NodeId * int list * EvaluationPort,int>),ready) (_,target,_,_,_) ->
                        match counts.TryFind target with
                        | Some count -> let next=count-1 in counts.Add(target,next),(if next=0 then target::ready else ready)
                        | None -> counts,ready) (counts,rest)
                let next=Ok(key::ranked,counts,ready)
                Some(next,next))
        |> Seq.tryLast |> Option.defaultValue initialRank
        |> Result.bind(fun (ranked,counts,_)->
            if counts.IsEmpty then Ok(List.rev ranked)
            else Error "Resource evaluation contains a cycle or an incomplete operand expansion.")
    let labels=ranked |> List.mapi(fun index key->key,index) |> Map.ofList
    let points=ranked |> List.mapi(fun label (site,context,port)->
        {Label=label;Site=site;Context=context;Port=port;Event=if port=EvaluationPort.Exit then event site else None}:ResourceFlowPoint)
    let edges=rawEdges |> List.map(fun (source,target,relation,connection,transfer)->
        {From=labels[source];To=labels[target];Relation=relation;Connection=connection;Transfer=transfer}:ResourceFlowEdge)
    let exits=points |> List.choose(fun point ->
        if point.Port=EvaluationPort.FailureExit || (point.Site=body && point.Context.IsEmpty && point.Port=EvaluationPort.Exit) then Some point.Label else None)
    let model:ResourceCleanupModel =
        {Acquisition=conversion.Acquisition;Declaration=resource.Identity;Release=resource.Release;Conversion=conversionClaim
         ConversionModel=conversion;Entry=labels[body,[],EvaluationPort.Entry];Points=points;Relations=relations;Edges=edges
         Cases=cases;LiteralGuards=literals;Exits=exits}
    let support=Set.union resource.Participants (Set.ofList (conversionClaim::cleanupClaim::owner::implementation::body::(relations |> List.collect(fun row->row.Target::row.Sources))))
    let selections context =
        context |> List.mapi(fun index ordinal ->
            let parentContext=context |> List.take index
            occurrences |> List.tryFind(fun (_,actual)->actual=parentContext)
            |> Option.bind(fun (site,_)->caseMap.TryFind site)
            |> Option.bind(fun case->
                if ordinal>0 && ordinal<=case.Arms.Length then
                    let arm=case.Arms[ordinal-1]
                    Some {Decision=case.Site;Scrutinee=case.Subject;Arm=ordinal-1;CaseOrdinal=arm.Ordinal;Guard=None}
                else None)) |> List.choose id
    let! accesses = siteIds |> Set.toList |> List.choose(fun site ->
        let node=graph.Nodes[site]
        let access =
            match node.Kind,event site with
            | SemanticKind.CaseElimination(subject,_),_ when optionSites.Contains subject -> Some(subject,BoundaryResourceAccessKind.OptionTag,false)
            | SemanticKind.DUEliminate(source,_,_,_),Some(ResourceFlowEvent.Payload _) -> Some(source,BoundaryResourceAccessKind.OptionPayload,true)
            | _,Some(ResourceFlowEvent.OptionAlias source) -> Some(source,BoundaryResourceAccessKind.ImmutableAlias,false)
            | _,Some(ResourceFlowEvent.HandleAlias source) -> Some(source,BoundaryResourceAccessKind.ImmutableAlias,true)
            | _ -> None
        access |> Option.map(fun (source,kind,handle) -> checked' {
            let paths=occurrences |> List.filter(fst>>(=)site) |> List.map(snd>>selections) |> List.distinct
            do! require (not handle || paths.Length=1) "A handle read has ambiguous case-selection lineage."
            return {Site=site;Source=source;Acquisition=conversion.Acquisition;Declaration=resource.Identity;Kind=kind
                    Selection=(if handle then paths.Head else []);Cleanup=cleanupClaim;Participants=Set.add site (Set.add source support)}:BoundaryResourceAccess })) |> collect
    return model,accesses,Enrichment.empty,(owner,implementation,body),support,releaseSites
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

let private intrinsicWrites (retained: Ingredients.RetainedBoundaryNodes) enrichId anchor (graph: SemanticGraph) =
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
                let! minimum,maximum =
                    match countRange with
                    | ValueRange.Bounded(lo,hi) when 0I<=lo && lo<=hi && hi<=bigint System.Int64.MaxValue -> Ok(lo,hi)
                    | _ -> Error "A runtime string write requires its actual finite nonnegative descriptor count range."
                do! require (snapshot.Extent.Range=countRange && allocation.CountCarrier.Range=countRange &&
                             0I<=allocation.MinimumCount && allocation.MinimumCount<=allocation.MaximumCount)
                        "The runtime write count must equal its exact copied descriptor and allocation extent."
                do! require (copy.Count=copy.CountOperand.Actual && copy.CountCarrier.Site=copy.CountOperand.Actual &&
                             allocation.Count=copy.CountOperand.Reference)
                        "The runtime borrow lost its original copy count operand and allocation reference."
                let borrowProof =
                    if minimum=maximum then ObligationBody.InputBufferBound(int64 minimum,int64 minimum)
                    else ObligationBody.SnapshotBorrowBound(count,snapshot.Site,copy.Site,allocation.Site,minimum,maximum,bigint allocation.ElementBytes,allocation.MaximumCount * bigint allocation.ElementBytes)
                return borrowProof,
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
                              Statement =
                                match body with
                                | ObligationBody.SnapshotBorrowBound _ ->
                                    "source-checked snapshot/copy/allocation count correspondence; SMT establishes the finite nonnegative count domain"
                                | _ -> "the exact ordered intrinsic write has covered scalars and a count-contained immutable borrow"
                              Source = fmtRange node.Range; Refs = []; Body = body }
                        let obligation = Ingredients.ownedObligationNode retained node enrichId info
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
let private elaborateCore (retained: Ingredients.RetainedBoundaryNodes) (graph: SemanticGraph) : Enrichment =
    let enrichId = Elaboration.freshId ()
    let anchor = Ingredients.anchorWithRetained retained enrichId graph
    let intrinsic = intrinsicWrites retained enrichId anchor.Id graph
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
                        | Some { Kind=SemanticKind.Sequential [buffer;index;required;continuation]; Children=children }
                            when buffer=view && index=construction.Current && children=[buffer;index;required;continuation] ->
                            memory.Operations.TryFind continuation |> Option.bind (function
                                | MemoryWitnessOperation.ArrayAccess fact when fact.Bounds.Requirement.Site=required -> Some fact
                                | _ -> None)
                        | _ -> None
                        |> needed "The string comparison read lacks its exact guarded access continuation."
                    do! require (access.Buffer=view && access.Index=construction.Current && access.Value.IsNone && access.Bounds.Requirement.Frontier=frontier)
                            "The string comparison borrow is not read by its exact source guard and index occurrence."
                    let allowed = Set.ofList [frontier;access.Site;access.Bounds.Length]
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
    // Declaration accounts are source observations, not resource/conversion proofs.
    let resourceDeclarations, resourceErrors =
        descriptors.Resources |> List.fold (fun (rows, errors) resource ->
            let roots = [resource.DescriptorBinding;resource.AcquisitionDescriptorBinding;resource.ReleaseDescriptorBinding]
            let observed = roots |> List.fold (fun state root -> state |> Result.bind (fun facts ->
                declarationFacts graph root |> Result.map (fun current -> Map.fold (fun all id value -> Map.add id value all) facts current))) (Ok Map.empty)
            match observed with
            | Error reason -> rows,(resource.Node,Set.ofList resource.Participants,reason)::errors
            | Ok declared ->
                let support = resource.Acquisition.Path @ resource.Acquisition.Formals @ [resource.Acquisition.Body] @ resource.Release.Path @ resource.Release.Formals @ [resource.Release.Body]
                let facts = support |> List.fold (fun facts id ->
                    match graph.Nodes.TryFind id with
                    | Some node when not (Map.containsKey id facts) -> Map.add id (Ingredients.premise node).Shape facts
                    | _ -> facts) declared
                if support |> List.exists (fun id -> not (facts.ContainsKey id)) then
                    rows,(resource.Node,Set.ofList support,"A resource declaration lost its exact source declaration support.")::errors
                else
                    let row: BoundaryResourceDeclaration =
                        { Identity = resource.Quote; Acquisition = resource.Acquisition.Binding; AcquisitionBody = resource.Acquisition.Body
                          AcquisitionDescriptor = resource.AcquisitionDescriptor; Release = resource.Release.Binding; ReleaseBody = resource.Release.Body
                          ReleaseDescriptor = resource.ReleaseDescriptor; ReleaseFormal = resource.ReleaseFormal; ReleaseOrdinal = 0
                          PointerBits = resource.PointerBits; AcquisitionType = resource.AcquisitionType; ResultType = resource.ResultType; HandleType = resource.HandleType
                          Contract = resource.Contract; DeclarationFacts = facts; Participants = Map.keys facts |> Set.ofSeq }
                    Map.add row.Identity row rows,errors) (Map.empty,[])
    let numeric =
        lazy
            (NumericPublication.project graph
             |> Result.mapError (fun _ -> "A closed C entry requires current source numeric carrier and proof settlement."))
    let writableApplications = StringByteStorageRecipes.writableApplications graph
    let writableResult (application:StringByteStorageRecipes.WritableApplication) result resultCount = checked' {
        match result with
        | None -> return Set.empty
        | Some(BoundaryScalar.Integer(64,true)) ->
            let! count=resultCount |> needed "The relational writable result lacks its checked positive singleton count."
            let! projection=numeric.Value |> Result.mapError(fun _->"The writable result requires its current numeric application and proof inventory.")
            let! account=projection.ForeignResultUses |> List.filter(fun account->
                account.Application.Call=application.Site && account.Application.Declaration=application.Declaration.Declaration.Binding)
                         |> List.tryExactlyOne |> needed "The writable result requires one exact current foreign-result call/context account."
            let! hypothesis=account.Application.Hypothesis |> needed "The writable result requires its current declared -1..count behavior hypothesis."
            let! countSourceIdx =
                application.Declaration.Declaration.Formals
                |> List.tryFindIndex ((=) application.Declaration.CountFormal)
                |> needed "The writable result lost its count formal ordinal in its source declaration."
            do! require (hypothesis.Lower=ForeignResultBound.Constant -1I && hypothesis.Upper=ForeignResultBound.Argument countSourceIdx &&
                         (account.Application.Arguments |> List.map(fun argument->argument.Index,argument.Node)) = (application.Arguments |> List.indexed))
                    "The writable result hypothesis or ordered actuals differ from this call's exact -1..count relation."
            do! require (descriptors.ResultRanges |> List.exists(fun declared->
                declared.Declaration.Binding=account.Application.Declaration && declared.AbiDescriptor=application.Declaration.AbiDescriptor && declared.Hypothesis=hypothesis))
                    "The writable result hypothesis is absent from the current declaration census."
            do! require (List.map fst account.Claims=[ForeignResultProofRole.LogicalCoverage;ForeignResultProofRole.AbiNarrowing] &&
                         (account.Claims |> List.map snd |> List.distinct).Length=2 &&
                         (account.Claims |> List.forall(fun(role,citizen)->
                             graph.Nodes.TryFind citizen |> Option.exists(fun node->
                                 match node.Kind with
                                 | SemanticKind.Obligation info ->
                                     match info.Body with
                                     | ObligationBody.ForeignResultCoverage model ->
                                         info.Kind="foreign-result-coverage" && model.Application=account.Application && model.Role=role &&
                                         model.Abi=Some application.Declaration.AbiDescriptor && model.AbiRange=ValueRange.twosComplement 64 &&
                                         model.ResultRange=ValueRange.bounded -1I count
                                     | _ -> false
                                 | _ -> false))))
                    "The writable result lacks its own current logical coverage and signed ABI narrowing claim citizens."
            let! support=match account.Participants with
                         | ParticipantEvidence.Established rows->Ok(rows |> List.map _.Node |> Set.ofList)
                         | ParticipantEvidence.Pending _->Error "The writable result has pending source application support."
            return Set.union support (account.Claims |> List.map snd |> Set.ofList)
        | _ -> return! Error "The writable result requires its separately supported signed-64 scalar declaration." }
    let writableStorage (application:StringByteStorageRecipes.WritableApplication) = checked' {
        let declaration=application.Declaration
        let bufferSourceIdx = declaration.Declaration.Formals |> List.tryFindIndex ((=) declaration.BufferFormal)
        let countSourceIdx = declaration.Declaration.Formals |> List.tryFindIndex ((=) declaration.CountFormal)
        do! require (declaration.Parameter >= 0 && declaration.CountParameter >= 0 &&
                     declaration.Parameter <> declaration.CountParameter &&
                     match bufferSourceIdx, countSourceIdx with
                     | Some bIdx, Some cIdx ->
                         bIdx <> cIdx &&
                         bIdx < application.Arguments.Length &&
                         cIdx < application.Arguments.Length
                     | _ -> false)
                "The writable adapter requires distinct in-range buffer and count ordinals."
        let! rep,format=Bytes.byteRepresentation graph |> needed "The writable application lost its selected unsigned-8 byte declaration."
        do! require (rep.Name=application.Representation) "The writable storage analysis and byte declaration disagree."
        let! memory=MemoryPublication.project graph |> Result.mapError(fun failures->failures |> List.map _.Reason |> String.concat "; ")
        let! storage=memory.Operations.TryFind application.Allocation |> Option.bind(function MemoryWitnessOperation.ArrayAllocation row->Some row | _->None)
                     |> needed "The writable application lacks its current source allocation witness."
        let! _,fields=Declarations.recordOf graph application.Declaration.AbiDescriptor
                      |> needed "The writable result lost its current FunctionDescriptor."
        let! returnId=field "ReturnType" fields |> needed "The writable result declaration lacks ReturnType."
        let! result=typeRef graph returnId
        let originalStorage=
            storage.Element=SettledSlot.Integer(8,Some rep.Name) && storage.ElementBytes=1 &&
            storage.Construction.Count.Actual=application.Capacity
        let! resultCount=
            match result with
            | Some(BoundaryScalar.Integer(64,true)) -> checked' {
                let capacity=storage.MinimumCount
                do! require (originalStorage && capacity>0I && storage.MaximumCount=capacity &&
                             application.CapacityRange=ValueRange.point capacity)
                        "The relational writable adapter requires its exact fixed positive initialized unsigned-8 byte capacity."
                match application.CountRange with
                | ValueRange.Bounded(lo,hi) when lo=hi && 0I<lo && hi<=capacity -> return Some lo
                | _ -> return! Error "The relational writable adapter requires one exact positive count within its initialized byte capacity." }
            | _ -> checked' {
                do! require (originalStorage && storage.MinimumCount=4I && storage.MaximumCount=4I)
                        "The first writable adapter requires its original four explicitly unsigned-8 byte slots."
                do! match application.CountRange with
                    | ValueRange.Bounded(lo,hi) when lo=hi && 0I<=lo && hi<=4I -> Ok()
                    | _ -> Error "The first writable adapter requires one exact nonnegative count within four byte slots."
                return None }
        let! resultSupport=writableResult application result resultCount
        return format,storage,resultSupport }
    // Coverage citizens retain the source effect account independently of the
    // physical adapter. Only the complete finite direct profile drops Pending.
    let writableRequirements, writableRequirementErrors, writableUses =
        writableApplications
        |> Map.fold(fun (enrichment,errors,uses) site observed ->
            let node=graph.Nodes[site]
            let anchor (declaration:Declarations.DeclaredWritableBuffer) role =
                // Current source anchor, not a numeric citizen identity or a
                // cross-revision/reuse key. Premises and proposition remain separate.
                let owners=List.unfold(fun (parent,seen) ->
                    parent |> Option.filter(fun id -> not(Set.contains id seen)) |> Option.bind(fun id ->
                        graph.Nodes.TryFind id |> Option.map(fun owner -> owner,(owner.Parent,Set.add id seen)))) (node.Parent,Set.empty)
                           |> List.choose(fun owner -> match owner.Kind with SemanticKind.Binding(name,_,_,_) | SemanticKind.ModuleDef(name,_) -> Some name | _ -> None)
                           |> List.rev
                let segments=owners@[declaration.Contract.Binding;fmtRange node.Range;role]
                let address=segments |> List.map(fun value -> string value.Length+":"+value) |> String.concat ""
                "foreign_writable_"+System.Convert.ToHexString(System.Text.Encoding.UTF8.GetBytes address)
            let refs (declaration:Declarations.DeclaredWritableBuffer) =
                [declaration.Contract.Hypothesis.Identity;declaration.Contract.Hypothesis.Version;declaration.Contract.Hypothesis.Source]
            let pending declaration participants reason =
                let info={Id=anchor declaration "adapter";Kind="foreign-writable-buffer-adapter";Logic="QF_LIA"
                          Statement="A declared writable byte application requires its exact source storage/count coverage and a separately settled native reference adapter."
                          Source=fmtRange node.Range;Refs=refs declaration;Body=ObligationBody.Pending [reason]}
                let citizen=Ingredients.ownedObligationNode retained node enrichId info
                Enrichment.combine enrichment {NewNodes=[citizen];Annotated=[];NewEdges=[constrains participants citizen]},errors
            let coverage declaration participants role body =
                let info={Id=anchor declaration role;Kind="foreign-writable-buffer-"+role;Logic="QF_LIA"
                          Statement=(if role="storage" then "The complete inferred local-store and declared foreign-ingress value domain fits the explicitly offered unsigned-8 representation."
                                     else "The inferred count domain is contained in the original allocation's byte-slot capacity; exact source incidence is a separate premise, not a solver pointer claim.")
                          Source=fmtRange node.Range;Refs=refs declaration;Body=body}
                let citizen=Ingredients.ownedObligationNode retained node enrichId info
                {NewNodes=[citizen];Annotated=[];NewEdges=[constrains participants citizen]}
            match observed with
            | Error failure ->
                let current,errors=pending failure.Declaration failure.Participants failure.Reason
                let bound=failure.CountCoverage |> Option.map(coverage failure.Declaration failure.Participants "count") |> Option.defaultValue Enrichment.empty
                Enrichment.combine current bound,errors,uses
            | Ok application ->
                let bodies =
                    match application.CountRange,application.CapacityRange,application.StorageRange with
                    | ValueRange.Bounded(lo,hi),ValueRange.Bounded(capacityLo,_),ValueRange.Bounded(storageLo,storageHi) ->
                        ["count",ObligationBody.IntegerRepresentationCoverage(lo,hi,0I,capacityLo)
                         "storage",ObligationBody.IntegerRepresentationCoverage(storageLo,storageHi,0I,255I)]
                    | _ -> ["count",ObligationBody.Pending ["The exact writable count/storage source domains are not established."]]
                let covered=bodies |> List.fold(fun current (role,body) ->
                    Enrichment.combine current (coverage application.Declaration application.Participants role body)) Enrichment.empty
                match writableStorage application with
                | Error reason ->
                    let current,errors=pending application.Declaration application.Participants reason
                    Enrichment.combine current covered,errors,uses
                | Ok(format,storage,resultSupport) ->
                    let citizen role=covered.NewNodes |> List.find(fun node->match node.Kind with SemanticKind.Obligation info->info.Kind="foreign-writable-buffer-"+role | _->false) |> _.Id
                    let count,values=citizen "count",citizen "storage"
                    let row:BoundaryWritableBufferUse =
                        {Call=site;Declaration=application.Declaration.Quote;Parameter=application.Declaration.Parameter;CountParameter=application.Declaration.CountParameter
                         Buffer=application.Buffer;Count=application.Count;Allocation=application.Allocation;Capacity=application.Capacity;ByteFormat=format
                         CountCoverage=count;StorageCoverage=values
                         Participants=Set.unionMany [storage.Participants;resultSupport;Set.ofList(count::values::application.Participants)]}
                    Enrichment.combine enrichment covered,errors,Map.add (site,row.Parameter) row uses) (Enrichment.empty,[],Map.empty)
    let writableDeclarations, writableErrors =
        descriptors.WritableBuffers |> List.fold (fun (rows,errors) writable ->
            let roots=[writable.DescriptorBinding;writable.AbiDescriptorBinding]
            let observed=roots |> List.fold(fun state root -> state |> Result.bind(fun facts ->
                declarationFacts graph root |> Result.map(fun current -> Map.fold(fun all id fact -> Map.add id fact all) facts current))) (Ok Map.empty)
            match observed with
            | Error reason -> rows,(writable.Node,Set.ofList writable.Participants,reason)::errors
            | Ok declared ->
                let declaration=writable.Declaration
                let support=declaration.Path@declaration.Formals@[declaration.Body]
                let facts=support |> List.fold(fun (facts:Map<NodeId,BoundaryDeclarationFact>) id ->
                    match graph.Nodes.TryFind id with
                    | Some node when not(facts.ContainsKey id) -> Map.add id (Ingredients.premise node).Shape facts
                    | _ -> facts) declared
                if support |> List.exists(fun id -> not(facts.ContainsKey id)) then
                    rows,(writable.Node,Set.ofList support,"A writable buffer declaration lost its exact source declaration support.")::errors
                else
                    let row:BoundaryWritableBufferDeclaration =
                        {Identity=writable.Quote;Declaration=declaration.Binding;Body=declaration.Body;Formals=declaration.Formals
                         Descriptor=writable.AbiDescriptor;Parameter=writable.Parameter;CountParameter=writable.CountParameter
                         BufferFormal=writable.BufferFormal;CountFormal=writable.CountFormal;Contract=writable.Contract
                         DeclarationFacts=facts;Participants=Map.keys facts |> Set.ofSeq}
                    Map.add row.Identity row rows,errors) (Map.empty,[])
    let readOnlyDeclarations, readOnlyDeclarationErrors =
        descriptors.ReadOnlyBuffers |> List.fold (fun (rows, errors) ro ->
            let roots = [ro.DescriptorBinding; ro.AbiDescriptorBinding]
            let observed = roots |> List.fold (fun state root -> state |> Result.bind (fun facts ->
                declarationFacts graph root |> Result.map (fun current -> Map.fold (fun all id fact -> Map.add id fact all) facts current))) (Ok Map.empty)
            match observed with
            | Error reason -> rows, (ro.Node, Set.ofList ro.Participants, reason) :: errors
            | Ok declared ->
                let declaration = ro.Declaration
                let support = declaration.Path @ declaration.Formals @ [declaration.Body]
                let facts = support |> List.fold (fun (facts: Map<NodeId, BoundaryDeclarationFact>) id ->
                    match graph.Nodes.TryFind id with
                    | Some node when not (facts.ContainsKey id) -> Map.add id (Ingredients.premise node).Shape facts
                    | _ -> facts) declared
                if support |> List.exists (fun id -> not (facts.ContainsKey id)) then
                    rows, (ro.Node, Set.ofList support, "A read-only buffer declaration lost its exact source declaration support.") :: errors
                else
                    let evidence =
                        [ { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = ro.Quote; Ordinal = ro.Parameter; Group = ro.Quote }
                          { Role = ParticipantRole.ReadOnlyBufferFormal; Node = ro.BufferFormal; Ordinal = ro.Parameter; Group = ro.Quote } ] @
                        (match ro.CountParameter, ro.CountFormal with
                         | Some cp, Some cf -> [ { Role = ParticipantRole.ReadOnlyBufferFormal; Node = cf; Ordinal = cp; Group = ro.Quote } ]
                         | _ -> [])
                    let row: BoundaryReadOnlyBufferDeclaration =
                        { Identity = ro.Quote; Declaration = declaration.Binding; Body = declaration.Body; Formals = declaration.Formals
                          Descriptor = ro.AbiDescriptor; Parameter = ro.Parameter; CountParameter = ro.CountParameter
                          BufferFormal = ro.BufferFormal; CountFormal = ro.CountFormal; Contract = ro.Contract
                          DeclarationFacts = facts; Participants = ParticipantEvidence.Established evidence }
                    Map.add row.Identity row rows, errors) (Map.empty, [])
    let borrowedViewDeclarations, borrowedViewDeclarationErrors =
        descriptors.BorrowedResultViews |> List.fold (fun (rows, errors) view ->
            let roots = [view.DescriptorBinding; view.AbiDescriptorBinding]
            let observed = roots |> List.fold (fun state root -> state |> Result.bind (fun facts ->
                declarationFacts graph root |> Result.map (fun current -> Map.fold (fun all id fact -> Map.add id fact all) facts current))) (Ok Map.empty)
            match observed with
            | Error reason -> rows, (view.Node, Set.ofList view.Participants, reason) :: errors
            | Ok declared ->
                let declaration = view.Declaration
                let support = declaration.Path @ declaration.Formals @ [declaration.Body]
                let facts = support |> List.fold (fun (facts: Map<NodeId, BoundaryDeclarationFact>) id ->
                    match graph.Nodes.TryFind id with
                    | Some node when not (facts.ContainsKey id) -> Map.add id (Ingredients.premise node).Shape facts
                    | _ -> facts) declared
                if support |> List.exists (fun id -> not (facts.ContainsKey id)) then
                    rows, (view.Node, Set.ofList support, "A borrowed result view declaration lost its exact source declaration support.") :: errors
                else
                    let evidence =
                        [ { Role = ParticipantRole.BorrowedResultViewDeclaration; Node = view.Quote; Ordinal = view.OwnerParameter; Group = view.Quote }
                          { Role = ParticipantRole.BorrowedResultViewOwner; Node = view.OwnerFormal; Ordinal = view.OwnerParameter; Group = view.Quote } ]
                    let row: BoundaryBorrowedResultViewDeclaration =
                        { Identity = view.Quote; Declaration = declaration.Binding; Body = declaration.Body; Formals = declaration.Formals
                          Descriptor = view.AbiDescriptor; OwnerParameter = view.OwnerParameter; OwnerFormal = view.OwnerFormal
                          Contract = view.Contract; DeclarationFacts = facts
                          Participants = ParticipantEvidence.Established evidence }
                    Map.add row.Identity row rows, errors) (Map.empty, [])
    let programOrders = computeProgramOrders graph
    let nativeToSourceArg, sourceToNativeArg, mutableRefOrdinalsByBinding =
        let byBody = descriptors.Functions |> List.choose (fun f -> f.Body |> Option.map (fun b -> b, f)) |> Map.ofList
        let declPairs =
            graph.Edges |> List.choose (fun e ->
                match e.Class, e.Role with
                | EdgeClass.Boundary, EdgeRole.BoundaryDeclaration decl ->
                    byBody.TryFind decl.Body |> Option.map (fun abi ->
                        let ordPairs =
                            abi.ParameterOrdinals |> Map.toSeq |> Seq.choose (fun (nativeOrd, formal) ->
                                decl.Formals |> List.tryFindIndex ((=) formal) |> Option.map (fun idx -> nativeOrd, idx))
                            |> Seq.toList
                        let ordMap = ordPairs |> Map.ofList
                        let revOrdMap = ordPairs |> List.map (fun (nativeOrd, idx) -> idx, nativeOrd) |> Map.ofList
                        let mutableFormalIds =
                            (abi.References |> List.map fst) @
                            (abi.PointerReferences |> List.map fst) @
                            (abi.RecordReferences |> List.choose (fun (fid, isRo) -> if not isRo then Some fid else None))
                            |> Set.ofList
                        let mutableOrds =
                            decl.Formals
                            |> List.indexed
                            |> List.choose (fun (idx, formal) -> if mutableFormalIds.Contains formal then Some idx else None)
                            |> Set.ofList
                        (decl.Binding, ordMap), (decl.Binding, revOrdMap), (decl.Binding, mutableOrds))
                | _ -> None)
        (declPairs |> List.map (fun (a, _, _) -> a) |> Map.ofList),
        (declPairs |> List.map (fun (_, b, _) -> b) |> Map.ofList),
        (declPairs |> List.map (fun (_, _, c) -> c) |> Map.ofList)
    let argAt (binding: NodeId) (args: NodeId list) (nativeOrd: int) =
        nativeToSourceArg.TryFind binding
        |> Option.bind (Map.tryFind nativeOrd)
        |> Option.bind (fun sourceIdx -> List.tryItem sourceIdx args)
    let memoryLazy = lazy (MemoryPublication.project graph)
    let setsByTarget, patternScrutinees = buildAliasEnv graph
    let allReadsAndWritesInScope =
        let writes = System.Collections.Generic.List<NodeId * Set<NodeId> * int>()
        let callsInGraph = System.Collections.Generic.List<SemanticNode * NodeId * NodeId list * int>()
        let appCallables = System.Collections.Generic.List<NodeId * Set<NodeId> * int>()
        let localLambdaCalls = System.Collections.Generic.List<NodeId * Set<NodeId> * NodeId list * int>()
        let callGraph = System.Collections.Generic.Dictionary<NodeId, Set<NodeId>>()
        let addWrite siteId exprId order =
            writes.Add(siteId, possibleOrigins graph setsByTarget patternScrutinees exprId, order)
        let isUnderExternalBinding nid =
            ancestorChain graph nid
            |> List.exists (fun aid -> graph.Nodes.TryFind aid |> Option.exists BoundaryDeclarations.isExternal)
        let isKnownLocalCallableTarget oid =
            match graph.Nodes.TryFind oid with
            | Some node ->
                match node.Kind with
                | SemanticKind.Lambda _ | SemanticKind.LazyExpr _ | SemanticKind.SeqExpr _ ->
                    not (isUnderExternalBinding oid)
                | SemanticKind.Binding _ ->
                    not (BoundaryDeclarations.isExternal node) && not node.Children.IsEmpty
                | SemanticKind.VarRef(_, Some _) -> true
                | SemanticKind.ClosureValue _ | SemanticKind.EnvironmentRead _
                | SemanticKind.TypeAnnotation _ | SemanticKind.EagerExpr _
                | SemanticKind.Sequential _ | SemanticKind.IfThenElse _
                | SemanticKind.Match _ | SemanticKind.CaseElimination _
                | SemanticKind.TupleExpr _ | SemanticKind.TupleGet _
                | SemanticKind.RecordExpr _ | SemanticKind.FieldGet _
                | SemanticKind.UnionCase _ | SemanticKind.DUConstruct _
                | SemanticKind.DUEliminate _ | SemanticKind.TryWith _
                | SemanticKind.TryFinally _ -> true
                | SemanticKind.PatternBinding _ ->
                    DirectCaptures.sourceDefinition graph oid <> oid || patternScrutinees.ContainsKey oid
                | SemanticKind.Application(innerCallee, _) ->
                    isTupleAccessorIntrinsic graph innerCallee
                | _ -> false
            | None -> false
        for node in graph.Nodes.Values do
            if node.IsReachable then
                match programOrders.TryFind node.Id with
                | None -> invalidOp (sprintf "Reachable node %d missing from boundary programOrders." (NodeId.value node.Id))
                | Some order ->
                match node.Kind with
                | SemanticKind.IndexSet(buf, _, _) ->
                    addWrite node.Id buf order
                | SemanticKind.FieldSet(expr, _, _) ->
                    addWrite node.Id expr order
                | SemanticKind.Application(callee, args) ->
                    let calleeLambdas = callableTargets graph setsByTarget patternScrutinees callee
                    let argLambdas =
                        if isNonInvokingIntrinsic graph callee then Set.empty
                        else args |> List.map (callableTargets graph setsByTarget patternScrutinees) |> Set.unionMany
                    let allAppLambdas = Set.union calleeLambdas argLambdas
                    if not (Set.isEmpty allAppLambdas) then
                        appCallables.Add(node.Id, allAppLambdas, order)
                        match enclosingCallable graph node.Id with
                        | Some callerId ->
                            match callGraph.TryGetValue callerId with
                            | true, existing -> callGraph[callerId] <- Set.union existing allAppLambdas
                            | false, _ -> callGraph[callerId] <- allAppLambdas
                        | None -> ()
                    match writableApplications.TryFind node.Id with
                    | Some(Ok wApp) ->
                        addWrite node.Id wApp.Buffer order
                        addWrite node.Id wApp.Allocation order
                    | Some(Error _) ->
                        for a in args do addWrite node.Id a order
                    | None -> ()
                    match target graph callee with
                    | Some(binding, _) when BoundaryDeclarations.isExternal binding ->
                        callsInGraph.Add(node, binding.Id, args, order)
                        match mutableRefOrdinalsByBinding.TryFind binding.Id with
                        | Some mutableOrds ->
                            args |> List.iteri (fun idx arg ->
                                if mutableOrds.Contains idx then addWrite node.Id arg order)
                        | None ->
                            for a in args do addWrite node.Id a order
                    | Some({ Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Array; Operation = ("set" | "fill") } }, _) ->
                        match args with
                        | buf :: _ -> addWrite node.Id buf order
                        | _ -> ()
                    | Some({ Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Array; Operation = "blit" } }, _) ->
                        match List.tryItem 2 args with
                        | Some targetBuf -> addWrite node.Id targetBuf order
                        | None -> ()
                    | Some({ Kind = SemanticKind.Intrinsic _ }, _) -> ()
                    | Some _ | None ->
                        let calleeOrigins = possibleOrigins graph setsByTarget patternScrutinees callee
                        let allTargetsKnownLambdas =
                            not (Set.isEmpty calleeLambdas) &&
                            (calleeOrigins |> Set.forall isKnownLocalCallableTarget)
                        if allTargetsKnownLambdas then
                            localLambdaCalls.Add(node.Id, calleeLambdas, args, order)
                        else
                            for a in args do addWrite node.Id a order
                | _ -> ()
        let callableWrites = System.Collections.Generic.Dictionary<NodeId, Set<NodeId>>()
        let mergeWrites cid originSet =
            if not (Set.isEmpty originSet) then
                match callableWrites.TryGetValue cid with
                | true, existing -> callableWrites[cid] <- Set.union existing originSet
                | false, _ -> callableWrites[cid] <- originSet
        for wSite, wOrigins, _ in writes do
            match enclosingCallable graph wSite with
            | Some cid -> mergeWrites cid wOrigins
            | None -> ()
        let mutable changed = true
        while changed do
            changed <- false
            for KeyValue(callerId, callees) in callGraph do
                let beforeCount =
                    match callableWrites.TryGetValue callerId with
                    | true, s -> s.Count
                    | false, _ -> 0
                for targetId in callees do
                    match callableWrites.TryGetValue targetId with
                    | true, targetOrigins -> mergeWrites callerId targetOrigins
                    | false, _ -> ()
                let afterCount =
                    match callableWrites.TryGetValue callerId with
                    | true, s -> s.Count
                    | false, _ -> 0
                if afterCount > beforeCount then changed <- true
            for appId, targets, args, _ in localLambdaCalls do
                match enclosingCallable graph appId with
                | Some callerId ->
                    let beforeCount =
                        match callableWrites.TryGetValue callerId with
                        | true, s -> s.Count
                        | false, _ -> 0
                    for targetId in targets do
                        match graph.Nodes.TryFind targetId, callableWrites.TryGetValue targetId with
                        | Some { Kind = SemanticKind.Lambda(parameters, _, _, _, _) }, (true, targetOrigins) ->
                            parameters |> List.iteri (fun idx (_, _, formalId) ->
                                if idx < args.Length && targetOrigins.Contains formalId then
                                    mergeWrites callerId (possibleOrigins graph setsByTarget patternScrutinees args[idx]))
                        | _ -> ()
                    let afterCount =
                        match callableWrites.TryGetValue callerId with
                        | true, s -> s.Count
                        | false, _ -> 0
                    if afterCount > beforeCount then changed <- true
                | None -> ()
        let closureWrites =
            appCallables |> Seq.toList |> List.collect (fun (appId, targets, appOrder) ->
                targets |> Set.toList |> List.choose (fun t ->
                    match callableWrites.TryGetValue t with
                    | true, s when not (Set.isEmpty s) -> Some(appId, s, Some t, appOrder)
                    | _ -> None))
        let paramWrites =
            localLambdaCalls |> Seq.toList |> List.collect (fun (appId, targets, args, appOrder) ->
                targets |> Set.toList |> List.collect (fun t ->
                    match graph.Nodes.TryFind t, callableWrites.TryGetValue t with
                    | Some { Kind = SemanticKind.Lambda(parameters, _, _, _, _) }, (true, targetOrigins) ->
                        parameters |> List.mapi (fun idx (_, _, formalId) ->
                            if idx < args.Length && targetOrigins.Contains formalId then
                                Some(appId, possibleOrigins graph setsByTarget patternScrutinees args[idx], Some t, appOrder)
                            else None)
                        |> List.choose id
                    | _ -> []))
        (writes |> Seq.map (fun (s, o, ord) -> s, o, None, ord) |> Seq.toList) @ closureWrites @ paramWrites,
        callsInGraph |> Seq.toList,
        appCallables |> Seq.toList,
        callGraph
    let allWrites, allExternalCalls, applicationCallableTargets, callableCallGraph = allReadsAndWritesInScope
    let readOnlyRequirements, readOnlyErrors, readOnlyUses =
        let anchorFor (ro: Declarations.DeclaredReadOnlyBuffer) (node: SemanticNode) (role: string) =
            let addr = sprintf "%s:%d:%s:%s" ro.Contract.Binding ro.Parameter (fmtRange node.Range) role
            "foreign_readonly_" + System.Convert.ToHexString(System.Text.Encoding.UTF8.GetBytes addr)
        let roByBinding = descriptors.ReadOnlyBuffers |> List.groupBy (fun r -> r.Declaration.Binding) |> Map.ofList
        let classifyView = lazy (Clef.Compiler.Baker.Ingredients.ArrayShapes.readOnlyViewClassifier graph)
        allExternalCalls |> List.fold (fun (enrichment, errors, uses) (site, calleeBinding, args, acquireOrder) ->
            match roByBinding.TryFind calleeBinding with
            | None -> enrichment, errors, uses
            | Some roContracts ->
                roContracts |> List.fold (fun (enrichment, errors, uses) ro ->
                    match nativeToSourceArg.TryFind calleeBinding |> Option.bind (Map.tryFind ro.Parameter) with
                    | None -> enrichment, (site.Id, Set.singleton site.Id, "Foreign read-only buffer parameter lacks a native-to-source ordinal mapping.") :: errors, uses
                    | Some roSourceOrd ->
                    match List.tryItem roSourceOrd args with
                    | None -> enrichment, errors, uses
                    | Some actual ->
                        match resolveBufferAbsenceChoice graph descriptors.BufferAbsences site calleeBinding ro.Parameter roSourceOrd actual with
                        | Error msg -> enrichment, (site.Id, Set.singleton actual, msg) :: errors, uses
                        | Ok(_, _, true, _) -> enrichment, errors, uses
                        | Ok(_, _, false, None) ->
                            enrichment, (site.Id, Set.singleton actual, "CCS8424: Foreign optional read-only buffer lacks payload target.") :: errors, uses
                        | Ok(_, absenceParticipants, false, Some inspectTarget) ->
                            let originNode = canonicalExprOrigin graph Set.empty inspectTarget
                            let refs = [ro.Contract.Hypothesis.Identity; ro.Contract.Hypothesis.Version; ro.Contract.Hypothesis.Source]
                            let outcome = checked' {
                                // Discover buffer residence & capacity
                                let poolOpt =
                                    graph.StaticStringPool |> Option.bind (fun pool ->
                                        pool.Entries |> List.indexed |> List.tryPick (fun (idx, entry) ->
                                            if List.contains originNode entry.NodeIds then Some(pool, idx, entry, originNode) else
                                            match graph.Nodes.TryFind originNode, entry.NodeIds with
                                            | Some { Kind = SemanticKind.Literal(NativeLiteral.String content) }, staticNode :: _ when entry.Content = content ->
                                                Some(pool, idx, entry, staticNode)
                                            | _ -> None))
                                let! residence, residenceNode, extentCapacity, elemBytes, staticPoolInfo, runtimeByteLenOpt, literalZeroCheck, extraSupport =
                                    match poolOpt with
                                    | Some(pool, idx, entry, staticOrigin) ->
                                        let hasInteriorZero =
                                            seq { for i in entry.Offset .. entry.Offset + entry.Length - 1 -> pool.Bytes[i] }
                                            |> Seq.exists ((=) 0uy)
                                        let validTrailing = entry.Offset + entry.StorageLength <= pool.Bytes.Length && pool.Bytes[entry.Offset + entry.Length] = 0uy
                                        Ok(MemoryResidence.ImmutableProgram pool.DeclarationNode, pool.DeclarationNode, bigint entry.Length, 1I, Some(pool, idx, entry, staticOrigin), Some(bigint entry.Length), hasInteriorZero || not validTrailing, Set.singleton pool.DeclarationNode)
                                    | None ->
                                        match memoryLazy.Value with
                                        | Error _ -> Error "CCS8424: Foreign read-only buffer requires an established storage residence and finite extent."
                                        | Ok memory ->
                                            let allocOpt =
                                                match memory.Operations.TryFind originNode with
                                                | Some(MemoryWitnessOperation.ArrayAllocation a) -> Some a
                                                | _ ->
                                                    memory.Operations.Values |> Seq.tryPick (function
                                                        | MemoryWitnessOperation.ArrayAllocation a when canonicalExprOrigin graph Set.empty a.Site = originNode -> Some a
                                                        | _ -> None)
                                            let viewLenOpt =
                                                match StringViewRecipes.localLineage graph memory originNode with
                                                | Ok(snapshots, _, _) ->
                                                    snapshots |> List.tryHead |> Option.bind (fun s ->
                                                        match s.Extent.Range with
                                                        | ValueRange.Bounded(lo, hi) when lo = hi && lo >= 0I -> Some lo
                                                        | _ -> None)
                                                | _ -> None
                                            let litOpt =
                                                match memory.Operations.TryFind originNode with
                                                | Some(MemoryWitnessOperation.ArrayLiteral l) -> Some l
                                                | _ ->
                                                    memory.Operations.Values |> Seq.tryPick (function
                                                        | MemoryWitnessOperation.ArrayLiteral l when canonicalExprOrigin graph Set.empty l.Site = originNode -> Some l
                                                        | _ -> None)
                                            match allocOpt, litOpt with
                                            | Some alloc, _ ->
                                                let cap = alloc.MinimumCount * bigint alloc.ElementBytes
                                                Ok(alloc.Residence, alloc.Site, cap, bigint alloc.ElementBytes, None, viewLenOpt, false, alloc.Participants)
                                            | None, Some lit ->
                                                let hasZero =
                                                    lit.Initializers |> Option.exists (List.exists (function
                                                        | NativeLiteral.Int(0L, _) | NativeLiteral.UInt(0UL, _) | NativeLiteral.Char '\000' -> true
                                                        | _ -> false))
                                                let cap = bigint lit.Length * bigint lit.ElementBytes
                                                Ok(lit.Residence, lit.Site, cap, bigint lit.ElementBytes, None, Some cap, hasZero, lit.Participants)
                                            | None, None ->
                                                Error "CCS8424: Foreign read-only buffer lacks static or memory-settled backing storage."
                                do! require (elemBytes > 0I) "CCS8424: Foreign read-only buffer requires positive element byte width."
                                let rec collectSliceChain seen id =
                                    if Set.contains id seen then [] else
                                    let seen = Set.add id seen
                                    match graph.Nodes.TryFind id with
                                    | Some { Kind = SemanticKind.TypeAnnotation(inner, _) }
                                    | Some { Kind = SemanticKind.EagerExpr inner }
                                    | Some { Kind = SemanticKind.VarRef(_, Some inner) } -> collectSliceChain seen inner
                                    | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> collectSliceChain seen value
                                    | Some { Kind = SemanticKind.Sequential items } when not items.IsEmpty -> collectSliceChain seen (List.last items)
                                    | Some { Kind = SemanticKind.Application(callee, args) } ->
                                        match graph.Nodes.TryFind callee with
                                        | Some { Kind = SemanticKind.Intrinsic info }
                                            when info.Module = IntrinsicModule.Array && info.FullName = "ReadOnlyView.slice" && args.Length = 3 ->
                                            collectSliceChain seen args[0] @ [id, args[1], args[2]]
                                        | _ -> []
                                    | _ -> []
                                let sliceSteps = collectSliceChain Set.empty inspectTarget
                                do!
                                    if not sliceSteps.IsEmpty && ro.Contract.Extent = BAREWire.Descriptors.ReadOnlyBufferExtent.UncountedNulTerminated then
                                        let fullLiteralSlice =
                                            match sliceSteps with
                                            | [_, offArg, cntArg] ->
                                                match graph.Nodes.TryFind offArg |> Option.bind _.ValueRange,
                                                      graph.Nodes.TryFind cntArg |> Option.bind _.ValueRange with
                                                | Some(ValueRange.Bounded(oLo, oHi)), Some(ValueRange.Bounded(cLo, cHi)) ->
                                                    oLo = 0I && oHi = 0I && cLo * elemBytes = extentCapacity && cHi * elemBytes = extentCapacity
                                                | _ -> false
                                            | _ -> false
                                        require fullLiteralSlice "CCS8424: Uncounted NUL-terminated buffer cannot accept a partial ReadOnlyView.slice."
                                    else Ok ()
                                let! slicedCapacity, slicedRuntimeByteLen, sliceParticipants =
                                    sliceSteps |> List.fold (fun acc (sliceSite, offArg, cntArg) -> checked' {
                                        let! curCapBytes, curRuntimeLen, sup = acc
                                        let! offHi =
                                            match graph.Nodes.TryFind offArg |> Option.bind _.ValueRange with
                                            | Some(ValueRange.Bounded(lo, hi)) when lo >= 0I && lo <= hi -> Ok hi
                                            | _ -> Error "CCS8424: ReadOnlyView.slice offset requires a finite nonnegative domain."
                                        let! cntLo, cntHi =
                                            match graph.Nodes.TryFind cntArg |> Option.bind _.ValueRange with
                                            | Some(ValueRange.Bounded(lo, hi)) when lo >= 0I && lo <= hi -> Ok(lo, hi)
                                            | _ -> Error "CCS8424: ReadOnlyView.slice count requires a finite nonnegative domain."
                                        do! require ((offHi + cntHi) * elemBytes <= curCapBytes)
                                                (sprintf "CCS8424: ReadOnlyView.slice bounds [%s..%s) exceed parent buffer capacity %s." (string offHi) (string (offHi + cntHi)) (string (curCapBytes / elemBytes)))
                                        let narrowedBytes = cntLo * elemBytes
                                        let nextRuntimeLen =
                                            match curRuntimeLen with
                                            | Some _ when cntLo = cntHi -> Some narrowedBytes
                                            | _ -> None
                                        return narrowedBytes, nextRuntimeLen, Set.union sup (Set.ofList [sliceSite; offArg; cntArg])
                                    }) (Ok(extentCapacity, runtimeByteLenOpt, extraSupport))
                                // Determine retirements & retention mode
                                let callScope = MemoryAccessRecipes.nearestLambda graph site.Id
                                let! retirements, retirementOrders, retentionMode =
                                    match ro.Contract.Retention with
                                    | BAREWire.Descriptors.BufferRetention.DuringCall ->
                                        let dominates =
                                            match residence with
                                            | MemoryResidence.ImmutableProgram _ | MemoryResidence.Program _ | MemoryResidence.Heap _ -> true
                                            | MemoryResidence.Stack(ownerScope, _) ->
                                                match callScope with
                                                | Some scope ->
                                                    let rec encloses cur =
                                                        if cur = ownerScope then true
                                                        else
                                                            match graph.Nodes.TryFind cur |> Option.bind _.Parent with
                                                            | Some p -> encloses p
                                                            | None -> false
                                                    encloses scope
                                                | None -> false
                                        if not dominates then Error "CCS8425: Read-only buffer storage does not dominate the foreign call."
                                        else Ok([], [], BufferRetentionMode.DuringCall)
                                    | BAREWire.Descriptors.BufferRetention.RetainedUntil(ownerParam, releases) -> checked' {
                                        let! ownerArg = argAt calleeBinding args ownerParam |> needed "CCS8425: Retained buffer contract owner ordinal is out of range."
                                        let ownerOrigin = immutableExprOrigin graph Set.empty ownerArg
                                        let matchesRelease (_, callBinding, callArgs, callOrder) =
                                            callOrder > acquireOrder &&
                                            (releases |> Array.exists (function
                                                | BAREWire.Descriptors.RetentionRelease.OwnerRelease rel ->
                                                    let matchesName =
                                                        graph.Nodes.TryFind callBinding
                                                        |> Option.bind (Declarations.qualifiedExportName graph)
                                                        |> Option.exists ((=) rel.Binding)
                                                    matchesName &&
                                                    (argAt callBinding callArgs rel.Parameter |> Option.exists (fun a -> immutableExprOrigin graph Set.empty a = ownerOrigin))
                                                | BAREWire.Descriptors.RetentionRelease.Redefinition keys ->
                                                    callBinding = calleeBinding &&
                                                    (keys |> Array.forall (fun k ->
                                                        match argAt calleeBinding args k, argAt callBinding callArgs k with
                                                        | Some a1, Some a2 -> immutableExprOrigin graph Set.empty a1 = immutableExprOrigin graph Set.empty a2
                                                        | _ -> false))))
                                        let matched =
                                            allExternalCalls
                                            |> List.filter (fun (retSite, cBind, cArgs, cOrder) ->
                                                matchesRelease (retSite, cBind, cArgs, cOrder) &&
                                                dominatesOnUnconditionalSpine graph site.Id retSite.Id)
                                            |> List.sortBy (fun (_, _, _, o) -> o)
                                        let retNodes = matched |> List.map (fun (n, _, _, _) -> n.Id)
                                        let retOrders = matched |> List.map (fun (_, _, _, o) -> o)
                                        if retNodes.IsEmpty then
                                            return! Error "CCS8425: Retained read-only buffer lacks a dominating release or redefinition retirement."
                                        else
                                            match residence with
                                            | MemoryResidence.Stack(ownerScope, _) ->
                                                let allEnclosed =
                                                    retNodes |> List.forall (fun rn ->
                                                        match MemoryAccessRecipes.nearestLambda graph rn with
                                                        | Some s ->
                                                            let rec encloses cur = if cur = ownerScope then true else match graph.Nodes.TryFind cur |> Option.bind _.Parent with Some p -> encloses p | None -> false
                                                            encloses s
                                                        | None -> false)
                                                if not allEnclosed then return! Error "CCS8425: Stack-resident retained buffer escapes its defining activation before retirement."
                                                else return (retNodes, retOrders, BufferRetentionMode.RetainedUntilOwner(ownerParam, retNodes.Length))
                                            | _ -> return (retNodes, retOrders, BufferRetentionMode.RetainedUntilOwner(ownerParam, retNodes.Length)) }
                                // Check exclusivity (CCS8426)
                                let originSet =
                                    possibleOrigins graph setsByTarget patternScrutinees inspectTarget
                                    |> Set.add originNode
                                let maxOrder = if retirementOrders.IsEmpty then acquireOrder else List.max retirementOrders
                                let siteLoops = enclosingLoops graph site.Id
                                let borrowsAcrossLoopBackEdge =
                                    siteLoops |> Set.exists (fun l ->
                                        retirements |> List.exists (fun retNode -> not ((enclosingLoops graph retNode).Contains l)))
                                let sameCallWritableOverlap =
                                    writableApplications.TryFind site.Id |> Option.exists (function
                                        | Ok wApp ->
                                            let wSet =
                                                Set.union
                                                    (possibleOrigins graph setsByTarget patternScrutinees wApp.Buffer)
                                                    (possibleOrigins graph setsByTarget patternScrutinees wApp.Allocation)
                                                |> Set.add wApp.Allocation
                                            not (Set.isEmpty (Set.intersect originSet wSet))
                                        | Error _ -> false)
                                let mutatedWhileBorrowed =
                                    allWrites |> List.exists (fun (wSite, wOriginSet, targetCallableOpt, wOrder) ->
                                        wSite <> site.Id &&
                                        (match targetCallableOpt with
                                         | Some targetId -> not (subtreeContains graph targetId site.Id)
                                         | None -> true) &&
                                        not (Set.isEmpty (Set.intersect originSet wOriginSet)) &&
                                        ((wOrder >= acquireOrder && wOrder <= maxOrder) ||
                                         (borrowsAcrossLoopBackEdge &&
                                          not (Set.isEmpty (Set.intersect siteLoops (enclosingLoops graph wSite))))))
                                do! require (not sameCallWritableOverlap && not mutatedWhileBorrowed)
                                        "CCS8426: Foreign read-only buffer aliases mutable storage or is mutated while borrowed."
                                // Check extent and element range, and emit obligations
                                let! elemCoverageEnrich =
                                    match ro.ElementRange with
                                    | None -> checked' {
                                        do! require (ro.Contract.Content = BAREWire.Descriptors.BorrowedContent.RawBytes)
                                                "CCS8424: Non-RawBytes read-only buffer requires an element integer range."
                                        return Enrichment.empty }
                                    | Some(ValueRange.Bounded(minDecl, maxDecl)) -> checked' {
                                        do! require (elemBytes = 1I)
                                                "CCS8424: Byte-ranged read-only buffer requires single-byte element representation."
                                        let viewProv = classifyView.Value inspectTarget
                                        do! require (viewProv <> Clef.Compiler.Baker.Ingredients.ArrayShapes.ReadOnlyViewProvenance.MixedConflict)
                                                "CCS8424: ReadOnlyView mixes byte-backed and array-backed sources."
                                        let! srcLo, srcHi =
                                            match staticPoolInfo with
                                            | Some(pool, _, entry, _) ->
                                                if entry.Length = 0 then Ok(0I, 0I)
                                                else
                                                    let mutable minB = bigint pool.Bytes[entry.Offset]
                                                    let mutable maxB = minB
                                                    for i in entry.Offset + 1 .. entry.Offset + entry.Length - 1 do
                                                        let b = bigint pool.Bytes[i]
                                                        if b < minB then minB <- b
                                                        if b > maxB then maxB <- b
                                                    Ok(minB, maxB)
                                            | None ->
                                                if viewProv = Clef.Compiler.Baker.Ingredients.ArrayShapes.ReadOnlyViewProvenance.ByteBacked ||
                                                   (match graph.Nodes.TryFind inspectTarget with
                                                    | Some n -> Types.isStringType (Clef.Compiler.NativeTypedTree.UnionFind.applySubst n.Type)
                                                    | None -> false) then
                                                    Ok(0I, 255I)
                                                else
                                                    match graph.Nodes.TryFind inspectTarget |> Option.map (fun n -> Clef.Compiler.NativeTypedTree.UnionFind.applySubst n.Type) with
                                                    | Some(NativeType.TApp(tc, [elem])) when Types.isReadOnlyViewTypeCon tc || tc.NTUKind = Some NTUKind.NTUarray ->
                                                        if Types.isIntegerType elem then
                                                            match graph.ElementRanges.Value.TryFind (Clef.Compiler.NativeTypedTree.TypeIdentities.ofType elem) with
                                                            | Some(ValueRange.Bounded(lo, hi)) when lo <= hi -> Ok(lo, hi)
                                                            | _ -> Error "CCS8424: Read-only buffer requires a bounded element integer range matching the boundary descriptor."
                                                        else
                                                            Error "CCS8424: Integer boundary descriptor cannot accept a non-integer read-only buffer element type."
                                                    | _ -> Error "CCS8424: Read-only buffer requires a settled element type matching the boundary descriptor."
                                        do! require (minDecl <= srcLo && srcLo <= srcHi && srcHi <= maxDecl)
                                                (sprintf "CCS8424: Read-only buffer element range [%s..%s] exceeds boundary descriptor integer range [%s..%s]." (string srcLo) (string srcHi) (string minDecl) (string maxDecl))
                                        let elemInfo =
                                            { Id = anchorFor ro site "element-coverage"; Kind = "foreign-readonly-buffer-element-coverage"; Logic = "QF_LIA"
                                              Statement = "The read-only buffer element range is covered by the declared boundary descriptor integer range."
                                              Source = fmtRange site.Range; Refs = refs
                                              Body = ObligationBody.IntegerRepresentationCoverage(srcLo, srcHi, minDecl, maxDecl) }
                                        let elemCitizen = Ingredients.ownedObligationNode retained site enrichId elemInfo
                                        let eCovSupport = Set.union sliceParticipants (Set.ofList [site.Id; ro.Quote; actual])
                                        return { NewNodes = [elemCitizen]; Annotated = []; NewEdges = [constrains (Set.toList eCovSupport) elemCitizen] } }
                                    | Some _ -> Error "CCS8424: Boundary descriptor integer range must be finite."
                                let retentionInfo =
                                    let model: BufferRetentionDominationModel =
                                        { Call = site.Id; Declaration = ro.Quote; Buffer = actual; Residence = residenceNode
                                          Mode = retentionMode; AcquireOrder = acquireOrder; RetirementOrders = retirementOrders }
                                    let rSupport = Set.unionMany [sliceParticipants; absenceParticipants; Set.ofList (site.Id :: actual :: residenceNode :: retirements)]
                                    let info =
                                        { Id = anchorFor ro site "retention"; Kind = "foreign-buffer-retention-domination"; Logic = "QF_LIA"
                                          Statement = "The read-only buffer residence dominates the foreign call and all declared retentions until retirement."
                                          Source = fmtRange site.Range; Refs = refs; Body = ObligationBody.BufferRetentionDomination model }
                                    let citizen = Ingredients.ownedObligationNode retained site enrichId info
                                    citizen, Enrichment.combine elemCoverageEnrich { NewNodes = [citizen]; Annotated = []; NewEdges = [constrains (Set.toList rSupport) citizen] }
                                let retCitizen, retEnrich = retentionInfo
                                match ro.Contract.Extent with
                                | BAREWire.Descriptors.ReadOnlyBufferExtent.ExplicitCount countParam ->
                                    let! countArg = argAt calleeBinding args countParam |> needed "CCS8424: ExplicitCount parameter ordinal is out of range."
                                    let! lo, hi =
                                        match graph.Nodes.TryFind countArg |> Option.bind _.ValueRange with
                                        | Some(ValueRange.Bounded(lo, hi)) when lo >= 0I && lo <= hi -> Ok(lo, hi)
                                        | _ -> Error "CCS8424: ExplicitCount argument requires a finite nonnegative count domain."
                                    do! require (hi * elemBytes <= slicedCapacity)
                                            (sprintf "CCS8424: ExplicitCount upper bound %s (%s bytes) exceeds buffer capacity %s." (string hi) (string (hi * elemBytes)) (string slicedCapacity))
                                    let extentClaimId =
                                        match retained.Obligations.TryFind (anchorFor ro site "extent") with
                                        | Some existing -> existing
                                        | None -> NodeId.fresh ()
                                    let extentModel: ZeroCopyBufferExtentModel =
                                        { Call = site.Id; Declaration = ro.Quote; Parameter = ro.Parameter; CountParameter = countParam
                                          Buffer = actual; Count = countArg; MinimumCount = lo; MaximumCount = hi
                                          ExtentCapacity = slicedCapacity; ElementBytes = int elemBytes; CountCoverage = extentClaimId }
                                    let extentInfo =
                                        { Id = anchorFor ro site "extent"; Kind = "foreign-readonly-buffer-extent"; Logic = "QF_LIA"
                                          Statement = "The foreign explicit-count read stays within the established read-only buffer byte extent with zero copies."
                                          Source = fmtRange site.Range; Refs = refs; Body = ObligationBody.ZeroCopyBufferExtent extentModel }
                                    let extentCitizen = { (Ingredients.ownedObligationNode retained site enrichId extentInfo) with Id = extentClaimId }
                                    let eSupport = Set.unionMany [sliceParticipants; absenceParticipants; Set.ofList [site.Id; actual; countArg]]
                                    let combined = Enrichment.combine retEnrich { NewNodes = [extentCitizen]; Annotated = []; NewEdges = [constrains (Set.toList eSupport) extentCitizen] }
                                    let participants =
                                        [ { Role = ParticipantRole.ReadOnlyBufferCall; Node = site.Id; Ordinal = 0; Group = site.Id }
                                          { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = ro.Quote; Ordinal = ro.Parameter; Group = site.Id }
                                          { Role = ParticipantRole.ReadOnlyBufferActual; Node = actual; Ordinal = ro.Parameter; Group = site.Id }
                                          { Role = ParticipantRole.ReadOnlyBufferResidence; Node = residenceNode; Ordinal = ro.Parameter; Group = site.Id } ] @
                                        (retirements |> List.mapi (fun i r -> { Role = ParticipantRole.ReadOnlyBufferRetirement; Node = r; Ordinal = i; Group = site.Id }))
                                    let row: BoundaryReadOnlyBufferUse =
                                        { Call = site.Id; Declaration = ro.Quote; Parameter = ro.Parameter; Buffer = actual
                                          Residence = residenceNode; Crossing = BoundaryReadOnlyBufferCrossing.ExplicitZeroCopy(countParam, countArg, slicedCapacity, extentCitizen.Id)
                                          Copies = 0; RetentionProof = retCitizen.Id; AccessExclusivityProof = None; Retirements = retirements
                                          Participants = ParticipantEvidence.Established participants }
                                    return row, combined
                                | BAREWire.Descriptors.ReadOnlyBufferExtent.UncountedNulTerminated ->
                                    do! require (elemBytes = 1I) "CCS8424: NUL-terminated foreign buffer requires single-byte element representation."
                                    do! require (not literalZeroCheck) "CCS8424: NUL-terminated foreign buffer contains an interior NUL byte or lacks trailing NUL."
                                    match staticPoolInfo with
                                    | Some(_, poolIdx, entry, staticOrigin) ->
                                        let termModel: UncountedPathTerminationModel =
                                            { Call = site.Id; Declaration = ro.Quote; Parameter = ro.Parameter; Source = actual
                                              Mode = UncountedPathStagingMode.StaticImageZeroCopy poolIdx
                                              ByteLength = bigint entry.Length; RequiresNoInteriorNul = true; RequiresTrailingNul = true }
                                        let termInfo =
                                            { Id = anchorFor ro site "termination"; Kind = "foreign-uncounted-path-termination"; Logic = "QF_LIA"
                                              Statement = "The uncounted NUL-terminated path borrows an immutable static string entry with verified zero interior NULs."
                                              Source = fmtRange site.Range; Refs = refs; Body = ObligationBody.UncountedPathTermination termModel }
                                        let termCitizen = Ingredients.ownedObligationNode retained site enrichId termInfo
                                        let tSupport = Set.unionMany [sliceParticipants; absenceParticipants; Set.ofList [site.Id; actual; staticOrigin]]
                                        let combined = Enrichment.combine retEnrich { NewNodes = [termCitizen]; Annotated = []; NewEdges = [constrains (Set.toList tSupport) termCitizen] }
                                        let participants =
                                            [ { Role = ParticipantRole.ReadOnlyBufferCall; Node = site.Id; Ordinal = 0; Group = site.Id }
                                              { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = ro.Quote; Ordinal = ro.Parameter; Group = site.Id }
                                              { Role = ParticipantRole.ReadOnlyBufferActual; Node = actual; Ordinal = ro.Parameter; Group = site.Id }
                                              { Role = ParticipantRole.ReadOnlyBufferResidence; Node = residenceNode; Ordinal = ro.Parameter; Group = site.Id } ] @
                                            (retirements |> List.mapi (fun i r -> { Role = ParticipantRole.ReadOnlyBufferRetirement; Node = r; Ordinal = i; Group = site.Id }))
                                        let row: BoundaryReadOnlyBufferUse =
                                            { Call = site.Id; Declaration = ro.Quote; Parameter = ro.Parameter; Buffer = actual
                                              Residence = residenceNode
                                              Crossing = BoundaryReadOnlyBufferCrossing.StaticImageNulBorrowed(poolIdx, staticOrigin, bigint entry.Length, termCitizen.Id)
                                              Copies = 0; RetentionProof = retCitizen.Id; AccessExclusivityProof = None; Retirements = retirements
                                              Participants = ParticipantEvidence.Established participants }
                                        return row, combined
                                    | None ->
                                        let! byteLen = slicedRuntimeByteLen |> needed "CCS8424: Runtime NUL-terminated buffer requires a known finite byte length without interior NULs."
                                        let cap = int (byteLen + 1I)
                                        let stagingId, stagingNodes =
                                            if residenceNode <> actual then residenceNode, []
                                            else
                                                let n =
                                                    { Id = NodeId.fresh ()
                                                      Kind = SemanticKind.Literal NativeLiteral.Unit
                                                      Range = site.Range
                                                      Type = Types.unitType
                                                      SRTPResolution = None
                                                      ArenaAffinity = ArenaAffinity.CurrentActor
                                                      LayoutHint = None
                                                      Children = []
                                                      Parent = None
                                                      IsReachable = true
                                                      EmissionStrategy = EmissionStrategy.Inline
                                                      ValueRange = None
                                                      Metadata = Map.ofList [ ("Baker.BoundaryOwned", MetadataValue.Bool true); (ElaborationMetadata.For, MetadataValue.String "BoundaryStaging"); (ElaborationMetadata.Id, MetadataValue.Int enrichId) ] }
                                                n.Id, [n]
                                        let termModel: UncountedPathTerminationModel =
                                            { Call = site.Id; Declaration = ro.Quote; Parameter = ro.Parameter; Source = actual
                                              Mode = UncountedPathStagingMode.CallScopedStaged(stagingId, cap)
                                              ByteLength = byteLen; RequiresNoInteriorNul = true; RequiresTrailingNul = true }
                                        let termInfo =
                                            { Id = anchorFor ro site "termination"; Kind = "foreign-uncounted-path-termination"; Logic = "QF_LIA"
                                              Statement = "The uncounted NUL-terminated path uses a call-scoped [len + 1] staged NUL-terminated buffer."
                                              Source = fmtRange site.Range; Refs = refs; Body = ObligationBody.UncountedPathTermination termModel }
                                        let termCitizen = Ingredients.ownedObligationNode retained site enrichId termInfo
                                        let extraNodes = termCitizen :: stagingNodes
                                        let tSupport = Set.unionMany [sliceParticipants; absenceParticipants; Set.ofList [site.Id; actual; stagingId]]
                                        let combined = Enrichment.combine retEnrich { NewNodes = extraNodes; Annotated = []; NewEdges = [constrains (Set.toList tSupport) termCitizen] }
                                        let participants =
                                            [ { Role = ParticipantRole.ReadOnlyBufferCall; Node = site.Id; Ordinal = 0; Group = site.Id }
                                              { Role = ParticipantRole.ReadOnlyBufferDeclaration; Node = ro.Quote; Ordinal = ro.Parameter; Group = site.Id }
                                              { Role = ParticipantRole.ReadOnlyBufferActual; Node = actual; Ordinal = ro.Parameter; Group = site.Id }
                                              { Role = ParticipantRole.ReadOnlyBufferResidence; Node = residenceNode; Ordinal = ro.Parameter; Group = site.Id } ] @
                                            (retirements |> List.mapi (fun i r -> { Role = ParticipantRole.ReadOnlyBufferRetirement; Node = r; Ordinal = i; Group = site.Id }))
                                        let row: BoundaryReadOnlyBufferUse =
                                            { Call = site.Id; Declaration = ro.Quote; Parameter = ro.Parameter; Buffer = actual
                                              Residence = residenceNode
                                              Crossing = BoundaryReadOnlyBufferCrossing.CallScopedNulStaged(stagingId, cap, byteLen, termCitizen.Id)
                                              Copies = 0; RetentionProof = retCitizen.Id; AccessExclusivityProof = None; Retirements = retirements
                                              Participants = ParticipantEvidence.Established participants }
                                        return row, combined }
                            match outcome with
                            | Ok(row, rowEnrich) ->
                                Enrichment.combine enrichment rowEnrich, errors, Map.add (site.Id, ro.Parameter) row uses
                            | Error reason ->
                                enrichment, (site.Id, Set.ofList (site.Id :: actual :: ro.Participants), reason) :: errors, uses) (enrichment, errors, uses))
            (Enrichment.empty, [], Map.empty)
    let borrowedViewRequirements, borrowedViewUseErrors, borrowedViewUses =
        let bvByBinding = descriptors.BorrowedResultViews |> List.groupBy (fun b -> b.Declaration.Binding) |> Map.ofList
        allExternalCalls |> List.fold (fun (enrichment, errors, uses) (site, calleeBinding, args, callOrder) ->
            match bvByBinding.TryFind calleeBinding with
            | None -> enrichment, errors, uses
            | Some [bv] ->
                let outcome = checked' {
                    do! require (isOptionType site.Type) "CCS8425: Borrowed result view requires nullable-to-Option boundary representation."
                    let! ownerArg = argAt calleeBinding args bv.OwnerParameter |> needed "Borrowed result view owner ordinal is out of range."
                    let ownerOrigin = immutableExprOrigin graph Set.empty ownerArg
                    let viewOrigin = canonicalExprOrigin graph Set.empty site.Id
                    let viewDerivedNodes =
                        let derived = System.Collections.Generic.HashSet<NodeId>()
                        let add id = derived.Add id |> ignore
                        add site.Id
                        add viewOrigin
                        let rec bindingTargets seen id =
                            if Set.contains id seen then [] else
                            let seen = Set.add id seen
                            match graph.Nodes.TryFind id with
                            | Some { Kind = SemanticKind.VarRef(_, Some t) } -> t :: bindingTargets seen t
                            | Some { Kind = SemanticKind.CellAddress b } -> b :: bindingTargets seen b
                            | Some { Kind = SemanticKind.TypeAnnotation(inner, _) }
                            | Some { Kind = SemanticKind.EagerExpr inner }
                            | Some { Kind = SemanticKind.Deref inner }
                            | Some { Kind = SemanticKind.Reborrow inner } -> bindingTargets seen inner
                            | _ -> []
                        let mutable changed = true
                        while changed do
                            changed <- false
                            for node in graph.Nodes.Values do
                                if node.IsReachable then
                                    let before = derived.Count
                                    match node.Kind with
                                    | SemanticKind.TypeAnnotation(inner, _)
                                    | SemanticKind.EagerExpr inner
                                    | SemanticKind.StringByteBorrow inner
                                    | SemanticKind.Reborrow inner
                                    | SemanticKind.Deref inner
                                    | SemanticKind.AddressOf(inner, _)
                                    | SemanticKind.TupleGet(inner, _)
                                    | SemanticKind.FieldGet(inner, _)
                                    | SemanticKind.DUEliminate(inner, _, _, _)
                                    | SemanticKind.UnionCase(_, _, Some inner)
                                    | SemanticKind.DUConstruct(_, _, Some inner, _) ->
                                        if derived.Contains inner then add node.Id
                                    | SemanticKind.VarRef(_, Some targetId) ->
                                        if derived.Contains targetId then add node.Id
                                    | SemanticKind.Binding _ ->
                                        if node.Children |> List.exists derived.Contains then add node.Id
                                    | SemanticKind.TupleExpr elements ->
                                        if elements |> List.exists derived.Contains then add node.Id
                                    | SemanticKind.RecordExpr(fields, copyFrom) ->
                                        if (fields |> List.exists (snd >> derived.Contains)) || (copyFrom |> Option.exists derived.Contains) then
                                            add node.Id
                                    | SemanticKind.Application(callee, args) ->
                                        match graph.Nodes.TryFind callee with
                                        | Some { Kind = SemanticKind.Intrinsic info }
                                            when info.Module = IntrinsicModule.Array &&
                                                 not args.IsEmpty &&
                                                 (info.FullName = "ReadOnlyView.ofArray" || info.FullName = "ReadOnlyView.ofString" || info.FullName = "ReadOnlyView.slice") ->
                                            if derived.Contains args.Head then add node.Id
                                        | _ when args.Length = 1 && isTupleAccessorIntrinsic graph callee ->
                                            if derived.Contains args.Head then add node.Id
                                        | _ -> ()
                                    | SemanticKind.Set(target, rhs)
                                    | SemanticKind.FieldSet(target, _, rhs) ->
                                        if derived.Contains rhs then
                                            for t in bindingTargets Set.empty target do add t
                                    | SemanticKind.Sequential items when not items.IsEmpty ->
                                        if derived.Contains (List.last items) then add node.Id
                                    | SemanticKind.IfThenElse(_, t, e) ->
                                        if derived.Contains t || (e |> Option.exists derived.Contains) then add node.Id
                                    | SemanticKind.Match(scrutinee, cases) ->
                                        if derived.Contains scrutinee then
                                            for c in cases do
                                                for pb in c.PatternBindings do add pb
                                        if cases |> List.exists (fun c -> derived.Contains c.Body) then add node.Id
                                    | SemanticKind.CaseElimination(scrutinee, arms) ->
                                        if derived.Contains scrutinee then
                                            for arm in arms do
                                                for b in arm.Bindings do add b
                                        if arms |> List.exists (fun a -> derived.Contains a.Body) then add node.Id
                                    | SemanticKind.TryWith(body, handler) ->
                                        if derived.Contains body || derived.Contains handler then add node.Id
                                    | SemanticKind.TryFinally(body, _) ->
                                        if derived.Contains body then add node.Id
                                    | _ -> ()
                                    if derived.Count > before then changed <- true
                        Set.ofSeq derived
                    let directReads =
                        graph.Nodes.Values |> Seq.choose (fun n ->
                            if not n.IsReachable || n.Id = site.Id then None else
                            match programOrders.TryFind n.Id with
                            | None -> invalidOp (sprintf "Reachable node %d missing from boundary programOrders." (NodeId.value n.Id))
                            | Some order ->
                            let touchesView =
                                match n.Kind with
                                | SemanticKind.VarRef(_, Some targetId) -> viewDerivedNodes.Contains targetId || viewDerivedNodes.Contains n.Id
                                | SemanticKind.DUEliminate(subj, _, _, _)
                                | SemanticKind.FieldGet(subj, _)
                                | SemanticKind.IndexGet(subj, _)
                                | SemanticKind.Deref subj
                                | SemanticKind.Reborrow subj -> viewDerivedNodes.Contains subj
                                | SemanticKind.Set(_, rhs)
                                | SemanticKind.FieldSet(_, _, rhs) -> viewDerivedNodes.Contains rhs
                                | SemanticKind.Application(_, args) -> args |> List.exists viewDerivedNodes.Contains
                                | SemanticKind.Lambda(_, _, captures, _, _)
                                | SemanticKind.LazyExpr(_, captures)
                                | SemanticKind.SeqExpr(_, captures) ->
                                    captures |> List.exists (fun c -> c.SourceNodeId |> Option.exists viewDerivedNodes.Contains)
                                | _ -> false
                            if touchesView then Some(n.Id, order) else None)
                        |> Seq.toList
                    let callableReadsView =
                        let readers = System.Collections.Generic.HashSet<NodeId>()
                        for rdNode, _ in directReads do
                            match graph.Nodes.TryFind rdNode with
                            | Some { Kind = SemanticKind.Lambda _ | SemanticKind.LazyExpr _ | SemanticKind.SeqExpr _ } ->
                                if not (subtreeContains graph rdNode site.Id) then
                                    readers.Add rdNode |> ignore
                            | _ ->
                                match enclosingCallable graph rdNode with
                                | Some cId when not (subtreeContains graph cId site.Id) ->
                                    readers.Add cId |> ignore
                                | _ -> ()
                        let mutable changed = true
                        while changed do
                            changed <- false
                            for KeyValue(callerId, callees) in callableCallGraph do
                                if not (subtreeContains graph callerId site.Id) &&
                                   not (readers.Contains callerId) &&
                                   (callees |> Set.exists readers.Contains) then
                                    readers.Add callerId |> ignore
                                    changed <- true
                        Set.ofSeq readers
                    let closureReadCalls =
                        applicationCallableTargets |> List.choose (fun (appId, targets, appOrder) ->
                            if appId <> site.Id && appOrder >= callOrder && (targets |> Set.exists callableReadsView.Contains) then
                                Some(appId, appOrder)
                            else None)
                    let reads =
                        ((directReads |> List.filter (fun (_, o) -> o >= callOrder)) @ closureReadCalls)
                        |> List.distinctBy fst
                        |> List.sortBy snd
                    let allInvalidations =
                        allExternalCalls |> List.filter (fun (_, cBind, cArgs, cOrder) ->
                            cOrder > callOrder &&
                            (bv.Contract.InvalidatedBy |> Array.exists (function
                                | BAREWire.Descriptors.BorrowInvalidation.AnyOwnerCall ->
                                    cArgs |> List.exists (fun a -> immutableExprOrigin graph Set.empty a = ownerOrigin)
                                | BAREWire.Descriptors.BorrowInvalidation.OwnerCall rel ->
                                    let matchesName =
                                        graph.Nodes.TryFind cBind |> Option.bind (Declarations.qualifiedExportName graph) |> Option.exists ((=) rel.Binding)
                                    matchesName && (argAt cBind cArgs rel.Parameter |> Option.exists (fun a -> immutableExprOrigin graph Set.empty a = ownerOrigin)))))
                        |> List.sortBy (fun (_, _, _, o) -> o)
                    do! require (not allInvalidations.IsEmpty) "CCS8425: Borrowed result view requires a matching owner invalidation call."
                    let invalidations =
                        allInvalidations |> List.filter (fun (invSite, _, _, _) -> dominatesOnUnconditionalSpine graph site.Id invSite.Id)
                    do! require (not invalidations.IsEmpty) "CCS8425: Borrowed result view owner invalidation does not dominate the borrow site."
                    let invNodes = invalidations |> List.map (fun (n, _, _, _) -> n.Id)
                    let invOrders = invalidations |> List.map (fun (_, _, _, o) -> o)
                    let readNodes = reads |> List.map fst
                    let readOrders = reads |> List.map snd
                    let siteLoops = enclosingLoops graph site.Id
                    let invalidatesBeforeUse (useNode: NodeId) (useOrder: int) (invSite: SemanticNode) (invOrder: int) =
                        let sharedNonEnclosingLoop =
                            not (Set.isEmpty (Set.difference (Set.intersect (enclosingLoops graph useNode) (enclosingLoops graph invSite.Id)) siteLoops))
                        (useOrder >= invOrder && canPrecedeInExecution graph invSite.Id useNode) ||
                        sharedNonEnclosingLoop
                    let readAfterInvalidation =
                        reads |> List.exists (fun (rdNode, rdOrder) ->
                            allInvalidations |> List.exists (fun (invSite, _, _, invOrder) ->
                                invalidatesBeforeUse rdNode rdOrder invSite invOrder))
                    do! require (not readAfterInvalidation)
                            "CCS8425: Borrowed result view read exceeds owner invalidation frontier."
                    let! companionCall, companionArgs =
                        match bv.Contract.Extent with
                        | BAREWire.Descriptors.BorrowedExtent.NulTerminated -> Ok(None, [])
                        | BAREWire.Descriptors.BorrowedExtent.CompanionCall(compBinding, argOrdinals) ->
                            let expectedArgs = argOrdinals |> Array.toList |> List.choose (argAt calleeBinding args)
                            let found =
                                allExternalCalls |> List.tryFind (fun (cNode, cBind, cArgs, cOrder) ->
                                    let nameMatches =
                                        graph.Nodes.TryFind cBind
                                        |> Option.bind (Declarations.qualifiedExportName graph) = Some compBinding
                                    let actualArgOrigins =
                                        argOrdinals |> Array.toList
                                        |> List.map (fun i -> argAt cBind cArgs i |> Option.map (immutableExprOrigin graph Set.empty))
                                    let expectedArgOrigins =
                                        expectedArgs |> List.map (immutableExprOrigin graph Set.empty >> Some)
                                    cOrder >= callOrder &&
                                    dominatesOnUnconditionalSpine graph site.Id cNode.Id &&
                                    not (allInvalidations |> List.exists (fun (invSite, _, _, invOrder) ->
                                        invalidatesBeforeUse cNode.Id cOrder invSite invOrder)) &&
                                    nameMatches &&
                                    actualArgOrigins = expectedArgOrigins)
                            match found with
                            | Some(cNode, cBind, cArgs, _) ->
                                let selectedArgs = argOrdinals |> Array.toList |> List.choose (argAt cBind cArgs)
                                Ok(Some cNode.Id, selectedArgs)
                            | None -> Error "CCS8424: Borrowed result view lacks its companion extent measurement before invalidation."
                    let scopeModel: BorrowedResultViewScopeModel =
                        { Call = site.Id; Declaration = bv.Quote; Owner = ownerArg; View = site.Id
                          CallOrder = callOrder; InvalidationOrders = invOrders; ReadOrders = readOrders; NullToNoneBoundary = true }
                    let addr = sprintf "%s:%s:scope" bv.Contract.Binding (fmtRange site.Range)
                    let scopeInfo =
                        { Id = "foreign_borrowed_view_" + System.Convert.ToHexString(System.Text.Encoding.UTF8.GetBytes addr)
                          Kind = "foreign-borrowed-view-scope"; Logic = "QF_LIA"
                          Statement = "The borrowed result view is null-to-None bounded and read strictly before owner invalidation."
                          Source = fmtRange site.Range; Refs = [bv.Contract.Hypothesis.Identity; bv.Contract.Hypothesis.Version; bv.Contract.Hypothesis.Source]
                          Body = ObligationBody.BorrowedResultViewScope scopeModel }
                    let scopeCitizen = Ingredients.ownedObligationNode retained site enrichId scopeInfo
                    let support = Set.ofList (site.Id :: ownerArg :: invNodes @ readNodes @ bv.Participants)
                    let participants =
                        [ { Role = ParticipantRole.BorrowedResultViewCall; Node = site.Id; Ordinal = 0; Group = site.Id }
                          { Role = ParticipantRole.BorrowedResultViewDeclaration; Node = bv.Quote; Ordinal = bv.OwnerParameter; Group = site.Id }
                          { Role = ParticipantRole.BorrowedResultViewOwner; Node = ownerArg; Ordinal = bv.OwnerParameter; Group = site.Id } ] @
                        (invNodes |> List.mapi (fun i n -> { Role = ParticipantRole.BorrowedResultViewInvalidation; Node = n; Ordinal = i; Group = site.Id })) @
                        (readNodes |> List.mapi (fun i n -> { Role = ParticipantRole.BorrowedResultViewRead; Node = n; Ordinal = i; Group = site.Id }))
                    let row: BoundaryBorrowedResultViewUse =
                        { Call = site.Id; Declaration = bv.Quote; Owner = ownerArg; View = site.Id
                          CompanionCall = companionCall; CompanionArguments = companionArgs
                          CallOrder = callOrder; Invalidations = invNodes; InvalidationOrders = invOrders
                          Reads = readNodes; ReadOrders = readOrders; NullToNoneBoundary = true
                          ScopeProof = scopeCitizen.Id; Participants = ParticipantEvidence.Established participants }
                    return row, { NewNodes = [scopeCitizen]; Annotated = []; NewEdges = [constrains (Set.toList support) scopeCitizen] } }
                match outcome with
                | Ok(row, rowEnrich) ->
                    Enrichment.combine enrichment rowEnrich, errors, Map.add site.Id row uses
                | Error reason ->
                    enrichment, (site.Id, Set.ofList (site.Id :: bv.Participants), reason) :: errors, uses
            | _ -> enrichment, errors, uses) (Enrichment.empty, [], Map.empty)
    // Requirements belong to the exact source application, before any native
    // adapter exists. Neither a matching release call nor an unused argument
    // establishes conversion, alias retirement or complete exit coverage.
    let resourceRequirements, resourceRequirementErrors =
        graph.Nodes |> Map.fold (fun (enrichment, errors) _ node ->
            match node.Kind with
            | SemanticKind.Application(callee, arguments) when node.IsReachable ->
                match target graph callee with
                | Some(binding, transport) when BoundaryDeclarations.isExternal binding ->
                    match resourceDeclarations.Values |> Seq.filter(fun row -> row.Acquisition=binding.Id) |> Seq.toList with
                    | [resource] ->
                        let platform =
                            runtime.Platform |> Option.map(fun selected ->
                                selected.Node :: (selected.Core |> Option.map _.Node |> Option.toList))
                            |> Option.defaultValue []
                        let participants =
                            Set.unionMany [transport;resource.Participants;Set.ofList(callee::arguments @ platform)]
                            |> Set.toList
                        let requirements =
                            [ ("foreign-resource-nullable-conversion",
                              $"The exact foreign acquisition requires conversion at the selected target's established pointer width, agreeing with its declared {resource.PointerBits}-bit ABI: NativeNull to None with no resource, and NonNull to Some of its declared CHandle.",
                              "The source-owned nullable-result conversion account is not established.")
                              ("foreign-resource-cleanup",
                              "After a nonnull acquisition, its exact release must retire every alias on every admitted exit, including later failures; a null result creates no release demand.",
                              "Complete source-owned resource alias retirement and exit coverage are not established.") ]
                        requirements |> List.fold(fun (enrichment, errors) (role, statement, reason) ->
                            match Ingredients.requirementWithRetained retained enrichId node role statement reason participants with
                            | Ok requirement -> Enrichment.combine enrichment requirement, errors
                            | Error reason -> enrichment,(node.Id,Set.ofList participants,reason)::errors) (enrichment,errors)
                    | _ -> enrichment,errors
                | _ -> enrichment,errors
            | _ -> enrichment,errors) (Enrichment.empty,[])
    let initialErrors = writableRequirementErrors @ writableErrors @ readOnlyDeclarationErrors @ readOnlyErrors @ borrowedViewDeclarationErrors @ borrowedViewUseErrors @ resourceRequirementErrors @ resourceErrors @ intrinsic.Errors @ (descriptors.Findings |> List.map (fun finding -> finding.Node, Set.singleton finding.Node, finding.Message))
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
            do!
                if library = "c" then Ok() else
                    Declarations.readLoading graph
                    |> Result.mapError (fun findings -> findings |> List.map _.Message |> String.concat "; ")
                    |> Result.bind (fun selected ->
                        require
                            (selected |> Option.exists (fun selected -> selected.Contract.Library = library))
                            "This C library requires its exact explicitly selected source process-link loading contract.")
            let! import = readImport graph descriptors resourceDeclarations writableDeclarations readOnlyDeclarations borrowedViewDeclarations binding library symbol

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
            do! require (not ((import.Result |> Option.toList) @ (import.Parameters |> List.map snd) |> List.exists (function BoundaryScalar.ResourceHandle _ | BoundaryScalar.WritableBytes _ -> true | _ -> false)))
                    "A resource-bearing ABI cannot form an indirect native entry without per-invocation conversion and cleanup lineage."
            let! loading = loading
            do! require (import.Library = loading.Contract.Library)
                    "The imported entry library differs from its explicitly selected process-link loading contract."

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

    let resolveAbsence site bindingId ordinal actual _ =
        match sourceToNativeArg.TryFind bindingId |> Option.bind (Map.tryFind ordinal) with
        | None ->
            Error "Foreign buffer parameter lacks an established source-to-native ordinal mapping."
        | Some nativeOrd ->
            resolveBufferAbsenceChoice graph descriptors.BufferAbsences site bindingId nativeOrd ordinal actual
            |> Result.map (fun (choice, support, _, _) -> choice, support)
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
                                if resourceDeclarations.Values |> Seq.exists (fun r -> r.Acquisition = binding.Id || r.Release = binding.Id) then
                                    return import, None
                                else
                                    let writable=
                                        import.Parameters |> List.indexed |> List.choose(fun (ordinal,(_,abi))->
                                            match abi with BoundaryScalar.WritableBytes _->Some ordinal | _->None)
                                        |> List.tryExactlyOne |> Option.bind(fun ordinal->writableUses.TryFind(node.Id,ordinal))
                                    let! call = readCall graph node callee args path import None None writable readOnlyDeclarations readOnlyUses resourceDeclarations (resolveAbsence node import.Binding)
                                    return import, Some call
                            }

                        match result with
                        | Ok(import, call) -> Map.add import.Identity import imports, (call |> Option.map (fun call -> Map.add node.Id call calls) |> Option.defaultValue calls), entries, errors
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
                                                None
                                                None
                                                readOnlyDeclarations
                                                readOnlyUses
                                                resourceDeclarations
                                                (resolveAbsence node import.Binding)

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

    // Requirements retain their original source claim IDs. A typed body is
    // issued only from actual current conversion/layout and complete finite
    // evaluation evidence; issuing it is not a discharge or execution permit.
    let claimAt site role =
        resourceRequirements.NewNodes |> List.filter(fun node ->
            match node.Kind with
            | SemanticKind.Obligation info when info.Kind=role ->
                resourceRequirements.NewEdges |> List.exists(fun edge -> edge.Role=EdgeRole.Constrains && edge.Target=node.Id && edge.Sources |> List.tryHead = Some site)
            | _ -> false)
        |> function [node] -> Ok node | _ -> Error "A resource application lost its unique source-issued requirement citizen."
    let refine (requirement:SemanticNode) body (support:Set<NodeId>) refs (enrichment:Enrichment) =
        let nodes=enrichment.NewNodes |> List.map(fun node ->
            if node.Id<>requirement.Id then node else
            match node.Kind with
            | SemanticKind.Obligation info -> {node with Kind=SemanticKind.Obligation {info with Body=body;Logic="QF_LIA";Refs=refs}}
            | _ -> node)
        let edges=enrichment.NewEdges |> List.map(fun edge ->
            if edge.Target=requirement.Id then {edge with Sources=List.distinct(edge.Sources@Set.toList support)} else edge)
        {enrichment with NewNodes=nodes;NewEdges=edges}
    let imports,calls,resourceAccesses,resourceRoots,resourceRelations,resourceEvaluation,resourceRequirements,errors =
        graph.Nodes |> Map.fold(fun ((imports:Map<NodeId,BoundaryImport>),(calls:Map<NodeId,BoundaryCall>),(accesses:Map<NodeId,BoundaryResourceAccess>),roots,relations,evaluation,requirements,errors) _ site ->
            match site.Kind with
            | SemanticKind.Application(callee,arguments) when site.IsReachable ->
                match target graph callee with
                | Some(binding,path) ->
                    match resourceDeclarations.Values |> Seq.filter(fun row->row.Acquisition=binding.Id) |> Seq.toList with
                    | [resource] ->
                        let result=checked' {
                            let! import=imports.TryFind resource.AcquisitionDescriptor |> needed "Resource conversion requires its exact current import."
                            let! conversionClaim=claimAt site.Id "foreign-resource-nullable-conversion"
                            let! cleanupClaim=claimAt site.Id "foreign-resource-cleanup"
                            let! platform=runtime.Platform |> needed "Resource conversion has no selected source platform."
                            let! core=platform.Core |> needed "Resource conversion has no selected target declaration."
                            let! selectedBits=graph.Platform |> needed "Resource conversion has no established target layout."
                                              |> Result.bind(fun platform->PlatformContext.tryWidth platform "Pointer")
                            let! handle=Placement.handleSlot graph resource.HandleType
                            let! handleBits,handleAlignment =
                                match handle with
                                | SettledSlot.CHandle(ty,bits,alignment) when ty=resource.HandleType -> Ok(bits,alignment)
                                | _ -> Error "Resource conversion lacks its dedicated nonspatial handle slot."
                            let! tag,noneCase,someCase=Placement.optionDiscriminant graph site.Type
                            let! tagBits=match tag with SettledSlot.Integer(bits,_) -> Ok bits | _ -> Error "Resource Option has no established integer discriminant."
                            let! offset,bytes,alignment =
                                match graph.Layouts.Value.TryFind resource.ResultType with
                                | Some(SettledLayout.Union([("None",None);("Some",Some payload)],Some offset,Some bytes,Some alignment)) when payload=handle -> Ok(offset,bytes,alignment)
                                | _ -> Error "Resource conversion lost its original complete Option placement."
                            do! require (Clef.Compiler.NativeTypedTree.TypeIdentities.ofType site.Type=resource.ResultType)
                                    "The exact acquisition result no longer has its declared logical Option identity."
                            let conversion:ResourceConversionModel =
                                {Acquisition=site.Id;Declaration=resource.Identity;Import=import.Identity;OptionType=resource.ResultType;HandleType=resource.HandleType
                                 Core=core.Node;PointerBits=resource.PointerBits;SelectedPointerBits=selectedBits;HandleBytes=handleBits/8;HandleAlignment=handleAlignment
                                 TagBits=tagBits;TagBytes=tagBits/8;NoneCase=noneCase;SomeCase=someCase;CaseCount=2
                                 PayloadOffset=offset;OptionBytes=bytes;OptionAlignment=alignment
                                 Arms=[{NativeNonNull=false;CaseOrdinal=noneCase;PayloadOrigin=None}
                                       {NativeNonNull=true;CaseOrdinal=someCase;PayloadOrigin=Some site.Id}]}
                            let! cleanup,accessRows,flow,root,support,releaseSites=resourceFlow graph resource conversion conversionClaim.Id cleanupClaim.Id
                            let resourceUse=BoundaryResourceUse.AcquireNullable
                                                {Declaration=resource.Identity;Tag=tag;NoneCase=noneCase;SomeCase=someCase;Conversion=conversionClaim.Id;Cleanup=cleanupClaim.Id}
                            let! acquisitionCall=readCall graph site callee arguments path import None (Some resourceUse) None readOnlyDeclarations readOnlyUses resourceDeclarations (resolveAbsence site import.Binding)
                            let! releaseCalls=releaseSites |> Map.toList |> List.map(fun (releaseSite,(_,releaseBinding))->checked' {
                                let! releaseNode=graph.Nodes.TryFind releaseSite |> needed "The release call was withdrawn."
                                let! releaseCallee,actuals=match releaseNode.Kind with SemanticKind.Application(callee,args)->Ok(callee,args) | _->Error "The release event is not an application."
                                let! releaseImport=imports.Values |> Seq.filter(fun row->row.Binding=releaseBinding) |> Seq.toList
                                                   |> function [row]->Ok row | _->Error "The explicit release lost its exact native import."
                                let! _,releasePath=target graph releaseCallee |> needed "The explicit release lost its actual declaration transport."
                                let resourceUse=BoundaryResourceUse.ReleaseOwned {Declaration=resource.Identity;Acquisition=site.Id;Cleanup=cleanupClaim.Id}
                                return! readCall graph releaseNode releaseCallee actuals releasePath releaseImport None (Some resourceUse) None readOnlyDeclarations readOnlyUses resourceDeclarations (resolveAbsence releaseNode releaseImport.Binding) }) |> collect
                            let support=Set.union support (Set.ofList [platform.Node;core.Node;site.Id;import.Identity])
                            let hypothesis=resource.Contract.Hypothesis
                            let refs=[sprintf "external-execution-hypothesis identity=%s version=%s source=%s" hypothesis.Identity hypothesis.Version hypothesis.Source]
                            let conversionSupport=support.Remove(conversionClaim.Id).Remove(cleanupClaim.Id)
                            let cleanupSupport=support.Remove cleanupClaim.Id
                            let requirements=requirements |> refine conversionClaim (ObligationBody.ResourceConversion conversion) conversionSupport refs
                                                          |> refine cleanupClaim (ObligationBody.ResourceCleanup cleanup) cleanupSupport refs
                            return acquisitionCall,releaseCalls,accessRows,flow,root,support,requirements,cleanup.Relations }
                        match result with
                        | Ok(acquisition,releases,accessRows,flow,root,support,requirements,currentRelations) ->
                            let acquisition={acquisition with Participants=Set.union acquisition.Participants support}
                            let calls=(acquisition::releases) |> List.fold(fun (calls:Map<NodeId,BoundaryCall>) call->calls.Add(call.Site,{call with Participants=Set.union call.Participants support})) calls
                            imports,calls,(accessRows |> List.fold(fun rows row->rows.Add(row.Site,row)) accesses),root::roots,
                            List.distinct(relations@currentRelations),Enrichment.combine evaluation flow,requirements,errors
                        | Error reason -> imports,calls,accesses,roots,relations,evaluation,requirements,(site.Id,Set.add site.Id resource.Participants,reason)::errors
                    | _ -> imports,calls,accesses,roots,relations,evaluation,requirements,errors
                | _ -> imports,calls,accesses,roots,relations,evaluation,requirements,errors
            | _ -> imports,calls,accesses,roots,relations,evaluation,requirements,errors)
            (imports,calls,Map.empty,[],[],Enrichment.empty,resourceRequirements,errors)

    let callbacks = CallbackDeclarations.read graph
    let scoped = ScopedDeclarations.read graph

    // An optional anchor is a selected declaration premise, never an invocation
    // or a source-wide noreturn fact. Preserve it even when it has no call site.
    let imports, errors =
        scoped.Activations.Values |> Seq.fold(fun (imports, errors) activation ->
            match activation.Extent with
            | BoundaryCallbackExtent.ProcessExit(Some anchor, _) ->
                let admitted = checked' {
                    let! binding = graph.Nodes.TryFind anchor |> needed "The normal-exit anchor declaration was withdrawn."
                    do! require (BoundaryDeclarations.isExternal binding &&
                                 (graph.Nodes.TryFind activation.Binding |> Option.exists(fun receiver -> receiver.Parent=binding.Parent)))
                            "The normal-exit anchor must be an exact extern selected beside its registration declaration."
                    let! imported = imported binding
                    do! require (imported.Result.IsNone && imported.CallingConvention="CDecl" &&
                                 (imported.Parameters |> List.map snd)=[BoundaryScalar.Integer(32,true)])
                            "The selected normal-exit anchor requires its signed32 status and void CDecl ABI."
                    return imported }
                match admitted with
                | Ok anchor -> Map.add anchor.Identity anchor imports, errors
                | Error reason -> imports, (activation.Scope,activation.Participants,reason)::errors
            | _ -> imports, errors) (imports, errors)

    let invocationAt (import: BoundaryImport) identity =
        checked' {
            let! source =
                match
                    descriptors.CallbackInvocations
                    |> List.filter (fun source -> source.Quote = identity && source.AbiDescriptor = import.Identity)
                with
                | [ source ] -> Ok source
                | _ -> Error "The receiving invocation quote no longer matches its exact import."

            let! activation = scoped.Activations.TryFind source.ScopeBinding
                              |> needed "The receiving invocation lost its current source activation declaration."
            do!
                require
                    (scoped.Findings.IsEmpty && activation.Scope=source.Scope && activation.Parameter=source.Formal &&
                     activation.Binding=source.Declaration.Binding &&
                     Set.isSubset (Set.ofList [source.ScopeBinding;source.Scope;source.Declaration.Binding]) activation.Participants)
                    "The receiving invocation requires its exact current activation declaration and native formal."

            let integer =
                function
                | BAREWire.Descriptors.TypeRef.Integer(signed, bits) ->
                    Ok(BoundaryScalar.Integer(bits, (signed = BAREWire.Descriptors.Signedness.Signed)))
                | _ -> Error "The closed C entry profile requires scalar integer parameters and result."

            let rec extractCallbackArgTypes ty =
                match Clef.Compiler.NativeTypedTree.UnionFind.applySubst ty with
                | NativeType.TApp(tc, [inner]) when tc.Name = "option" || tc.Name = "Option" -> extractCallbackArgTypes inner
                | NativeType.TApp(tc, [inner]) when tc.Name = "FnPtr" -> extractCallbackArgTypes inner
                | NativeType.TFun(dom, cod) -> dom :: extractCallbackArgTypes cod
                | _ -> []
            let! formalNode =
                graph.Nodes.TryFind source.Formal
                |> needed "CCS8403: A callback parameter formal is absent from the source graph."
            let formalCallbackTypes = extractCallbackArgTypes formalNode.Type
            let! parameters =
                source.Contract.Signature.Parameters
                |> Array.toList
                |> List.mapi (fun argOrd parameter ->
                    match parameter.Type with
                    | BAREWire.Descriptors.TypeRef.Pointer width ->
                        let formalArgTy = List.tryItem argOrd formalCallbackTypes
                        let countedMatch =
                            descriptors.CountedEntryArrays
                            |> List.tryFind (fun a -> a.Invocation.Quote = source.Quote && a.Contract.Argument = argOrd)
                        match countedMatch with
                        | Some counted ->
                            match formalArgTy with
                            | Some ty when (match Clef.Compiler.NativeTypedTree.UnionFind.applySubst ty with
                                            | NativeType.TApp(tc, [_]) when Types.isReadOnlyViewTypeCon tc -> true
                                            | substituted -> Types.tryGetNTUKind substituted = Some NTUKind.NTUptr) ->
                                Ok(BoundaryScalar.ReadOnlyBytes counted.Quote)
                            | _ ->
                                Error "CCS8403: A CountedEntryArrayDescriptor callback parameter requires a ReadOnlyView or pointer formal."
                        | None ->
                            let isCallbackContextDescriptorType (ty: TypeIdentity) =
                                match ty with
                                | TypeIdentity.Application(constructor, []) ->
                                    (constructor.Declaration.Module = ["BAREWire"; "Descriptors"] && constructor.Declaration.Name = "CallbackContextDescriptor") ||
                                    (constructor.Declaration.Module = ["BAREWire"] && constructor.Declaration.Name = "Descriptors.CallbackContextDescriptor")
                                | _ -> false
                            let quoteOwnedByBinding quoteId =
                                import.DeclarationFacts.Values |> Seq.exists (fun fact ->
                                    fact.Form = "binding" && List.tryLast fact.Children = Some quoteId)
                            let hasContextContract =
                                import.DeclarationFacts |> Map.exists (fun quoteId quote ->
                                    quoteOwnedByBinding quoteId &&
                                    match quote.Form, quote.References with
                                    | "quotation", [recordId] when quote.Children = quote.References ->
                                        match import.DeclarationFacts.TryFind recordId with
                                        | Some recFact when recFact.Form = "record" && isCallbackContextDescriptorType recFact.SourceType && recFact.References.Length = recFact.Text.Length ->
                                            let fields = List.zip recFact.Text recFact.References |> Map.ofList
                                            let strMatches name (expected: string) =
                                                fields.TryFind name
                                                |> Option.bind import.DeclarationFacts.TryFind
                                                |> Option.exists (fun v -> v.Form = "string" && v.References.IsEmpty && v.Children.IsEmpty && v.Text = [expected])
                                            let intMatches name predicate =
                                                fields.TryFind name
                                                |> Option.bind import.DeclarationFacts.TryFind
                                                |> Option.exists (fun v ->
                                                    (v.Form = "integer" || v.Form = "unsigned-integer") &&
                                                    v.References.IsEmpty && v.Children.IsEmpty &&
                                                    match v.Numbers with [n] -> predicate n | _ -> false)
                                            strMatches "Binding" source.Contract.Binding &&
                                            intMatches "Parameter" ((=) (bigint source.Parameter)) &&
                                            intMatches "Argument" ((=) (bigint argOrd)) &&
                                            intMatches "ContextParameter" (fun cp -> cp >= 0I && cp <> bigint source.Parameter)
                                        | _ -> false
                                    | _ -> false)
                            if hasContextContract then
                                Ok(BoundaryScalar.Integer(width, false))
                            else
                                match formalArgTy with
                                | Some ty when isNominalCHandleType false ty ->
                                    let formalTypeId = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType ty
                                    match resourceDeclarations.Values |> Seq.filter (fun r -> r.HandleType = formalTypeId) |> Seq.toList with
                                    | [r] -> Ok(BoundaryScalar.ResourceHandle(r.Identity, false))
                                    | [] -> Ok(BoundaryScalar.ResourceHandle(source.Formal, false))
                                    | _ -> Error "CCS8403: Ambiguous resource declarations for callback CHandle parameter."
                                | Some ty when isNominalCHandleType true ty ->
                                    let innerId =
                                        match Clef.Compiler.NativeTypedTree.UnionFind.applySubst ty with
                                        | NativeType.TApp(_, [inner]) -> Clef.Compiler.NativeTypedTree.TypeIdentities.ofType inner
                                        | _ -> Clef.Compiler.NativeTypedTree.TypeIdentities.ofType ty
                                    match resourceDeclarations.Values |> Seq.filter (fun r -> r.HandleType = innerId) |> Seq.toList with
                                    | [r] -> Ok(BoundaryScalar.ResourceHandle(r.Identity, true))
                                    | [] -> Ok(BoundaryScalar.ResourceHandle(source.Formal, true))
                                    | _ -> Error "CCS8403: Ambiguous resource declarations for callback CHandle parameter."
                                | _ ->
                                    Error "CCS8403: A callback Pointer parameter requires a nominal CHandle<'T>, CountedEntryArrayDescriptor, or CallbackContextDescriptor contract."
                    | other -> integer other)
                |> collect

            let! result =
                match source.Contract.Signature.ReturnType with
                | BAREWire.Descriptors.TypeRef.Void -> Ok None
                | result -> integer result |> Result.map Some

            do!
                require
                    ((not parameters.IsEmpty || source.Contract.Signature.ReturnType = BAREWire.Descriptors.TypeRef.Void)
                     && source.Contract.Signature.CallingConvention = BAREWire.Descriptors.CallConv.CDecl)
                    "The closed C entry profile requires scalar integer native formals or exact zero-argument void, and CDecl."

            do!
                match activation.Extent with
                | BoundaryCallbackExtent.DuringCall ->
                    require (scoped.Parameters.Contains source.Formal) "A during-call declaration lost its synchronous parameter."
                | BoundaryCallbackExtent.ProcessExit _ ->
                    require (parameters.IsEmpty && result.IsNone && import.Result=Some(BoundaryScalar.Integer(32,true)))
                        "A process-exit callback requires exact zero-argument void and a signed32 registration result."
                | BoundaryCallbackExtent.Retained(owner, releases) ->
                    let ownerSourceIdx =
                        nativeToSourceArg.TryFind import.Binding
                        |> Option.bind (Map.tryFind owner)
                    require (owner >= 0 && ownerSourceIdx.IsSome && owner <> source.Parameter && not (Array.isEmpty releases))
                        "A retained callback requires a valid foreign owner ordinal and non-empty retirement contract."
            let participants = Set.union (Set.ofList source.Participants) activation.Participants

            return source, ({
                Identity = source.Quote
                Import = import.Identity
                Parameter = source.Parameter
                Formal = source.Formal
                Scope = source.Scope
                Contract = source.Contract
                Signature = { Parameters = parameters; Result = result; CallingConvention = "CDecl" }
                Extent = activation.Extent
                Participants = participants
            }: BoundaryCallbackInvocation)
        }

    let closedAt (call: BoundaryCall) (operand: BoundaryOperand) identity =
        checked' {
            let! import =
                imports.TryFind call.Import
                |> needed "The receiving call lost its admitted import."

            let! source, invocation = invocationAt import identity

            do!
                require
                    (source.Formal = operand.Formal
                     && (import.Parameters |> List.tryFindIndex (fst >> (=) source.Formal) |> Option.bind (fun idx -> call.Arguments |> List.tryItem idx)) = Some operand)
                    "The receiving callback actual differs from its original native formal and ordinal."

            let! evidence, suppliedActual =
                match
                    operand.OptionalEntry
                with
                | Some choice ->
                    let present = choice |> BoundaryOptionalEntryChoice.leaves |> List.filter (fun selected -> selected.Payload.IsSome)
                    match present with
                    | [selected] ->
                        callbacks.OptionalReceiving |> List.filter(fun row -> row.Call=call.Site && row.Operand=operand.Actual && row.Invocation.Quote=identity &&
                                                                              row.Construction=selected.Construction && row.CaseOrdinal=selected.CaseOrdinal && row.Payload=selected.Payload)
                        |> function
                           | [{ Receiving=Some evidence; Payload=Some payload }] -> Ok(evidence,payload)
                           | _ -> Error "The optional Some callback lost its exact current selection account."
                    | _ -> Error "The optional callback requires exactly one present closed entry."
                | None ->
                    callbacks.Receiving |> List.filter(fun evidence -> evidence.Call=call.Site && evidence.Operand=operand.Actual && evidence.Invocation.Quote=identity)
                    |> function [evidence] -> Ok(evidence,operand.Actual) | _ -> Error "The receiving callback lost its exact current call, source entry and signature association."

            let! formation =
                Clef.Compiler.Baker.Ingredients.CompilerOwnedEntries.tryFormation graph evidence.Address
                |> needed "A receiving callback requires current FnPtr.ofFunction of a capture-free immutable module declaration."

            do!
                match Clef.Compiler.Baker.Ingredients.CompilerOwnedEntries.tryFormation graph suppliedActual with
                | Some direct when direct.Formation = formation.Formation -> Ok ()
                | _ ->
                    match PlatformResolution.valuePath graph suppliedActual with
                    | Some({ Kind = SemanticKind.FieldGet _; Id = projection }, _) ->
                        Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.nativeProjection graph projection formation.Formation
                    | _ -> Error "The receiving callback lost its exact immutable formation or admitted record projection."

            let! originalOperand =
                match graph.Nodes.TryFind formation.Formation with
                | Some { Kind = SemanticKind.Application(_, [argument]) } -> Ok argument
                | _ -> Error "The closed entry lost its original ofFunction operand."
            let entry = formation.Entry
            let implementation = entry.Lifetime.Implementation
            let formals = entry.Parameters |> List.map (fun (_, _, formal) -> formal)
            let unitParameterOmission =
                invocation.Contract.Signature.Parameters.Length = 0 &&
                invocation.Contract.Signature.ReturnType = BAREWire.Descriptors.TypeRef.Void &&
                invocation.Signature.Parameters.IsEmpty && invocation.Signature.Result.IsNone &&
                (match entry.Parameters with
                 | [(_, ty, formal)] ->
                     Types.tryGetNTUKind ty = Some NTUKind.NTUunit &&
                     (graph.Nodes.TryFind formal |> Option.exists (fun node -> Types.tryGetNTUKind node.Type = Some NTUKind.NTUunit)) &&
                     (graph.Nodes.TryFind entry.Result |> Option.exists (fun node -> Types.tryGetNTUKind node.Type = Some NTUKind.NTUunit))
                 | _ -> false)

            do!
                require
                    (evidence.Declaration = entry.Lifetime.Binding
                     && evidence.Lambda = implementation
                     && evidence.Signature.Body = Some entry.Result
                     && (evidence.Signature.Parameters |> List.map fst) = (if unitParameterOmission then [] else formals))
                    "The receiving callback differs from its original complete module declaration."

            let entryPurposes =
                purposes.TryFind formation.Formation |> Option.defaultValue Set.empty

            do!
                require
                    (entryPurposes |> Set.exists (snd >> (=) DeclRoot.LibraryExport) |> not)
                    "A closed C callback exposed through an exported library requires an L3 host entry contract."

            do!
                require
                    (entryPurposes |> Set.exists (snd >> (=) DeclRoot.EntryPoint))
                    "The closed C callback requires a hosted executable program entry activation."

            let! carrier =
                graph.Codata.Value.CallableCarriers.TryFind formation.Formation
                |> needed "The source closed entry has no current native callable carrier."

            let! contractId =
                carrier.Contract
                |> Result.mapError (fun reason -> "The source closed entry has no current callable contract: " + reason)

            let! contract =
                graph.Codata.Value.CallableContracts.TryFind contractId
                |> needed "The source closed entry callable contract was withdrawn."

            do!
                require
                    (carrier.Kind = CallableKind.NativeEntry
                     && carrier.Formation = formation.Formation
                     && carrier.Implementation = implementation
                     && carrier.OmittedParameters = (if unitParameterOmission then Set.ofList formals else Set.empty)
                     && (carrier.Parameters |> List.map (fun (_, _, formal) -> formal)) = formals
                     && Clef.Compiler.Baker.Ingredients.CallableContracts.sourcePremisesCurrent graph contract
                     && (match contract.Convention with
                         | CallableConvention.CompilerOwnedPortable convention -> convention.CodeLifetime = entry.Lifetime
                         | _ -> false))
                    "The closed entry lost its existing source-owned code lifetime or complete native formal convention."

            let! numericProjection = numeric.Value

            let currentCarrier id =
                match
                    graph.Edges
                    |> List.choose (fun edge ->
                        match edge.Role with
                        | EdgeRole.NumericCarrier value when value.Site = id -> Some value
                        | _ -> None)
                with
                | [ carrier ] -> Ok carrier
                | _ -> Error "A native entry boundary lost its complete current source numeric carrier."

            do!
                require
                    (unitParameterOmission || formals.Length = invocation.Signature.Parameters.Length)
                    "The closed callback native signature differs from its complete source formal vector."

            let nativeFormals = if unitParameterOmission then [] else formals
            let! parameterAdaptations =
                List.zip nativeFormals invocation.Signature.Parameters
                |> List.map (fun (formal, abi) ->
                    checked' {
                        match abi with
                        | BoundaryScalar.ResourceHandle _ | BoundaryScalar.ReadOnlyBytes _ -> return None
                        | _ ->
                            let! carrier = currentCarrier formal
                            let! bits = sourceWidth graph formal abi

                            let! capacity =
                                carrier.Representation
                                |> Option.bind Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources.declaredRange
                                |> needed "A native incoming formal has no selected finite representation."

                            do!
                                require
                                    (carrier.Range = scalarRange abi
                                     && ValueRange.contains capacity (scalarRange abi))
                                    "A native incoming formal must retain its full declared ABI domain, independent of observed source callers."

                            return! adaptation graph implementation formal (scalarBits abi) bits (scalarRange abi)
                    })
                |> collect

            let resultAdaptation = graph.Codata.Value.ReturnMeets.TryFind implementation

            do!
                match invocation.Contract.Signature.ReturnType, invocation.Signature.Result with
                | BAREWire.Descriptors.TypeRef.Void, None ->
                    require
                        ((graph.Nodes.TryFind entry.Result |> Option.exists (fun body -> Types.tryGetNTUKind body.Type = Some NTUKind.NTUunit))
                         && evidence.Signature.Return.IsNone
                         && resultAdaptation.IsNone)
                        "A void native callback requires its actual unit source body and no numeric return adaptation."
                | _, Some returned ->
                    checked' {
                        let! resultCarrier = currentCarrier entry.Result

                        do!
                            require
                                (ValueRange.contains (scalarRange returned) resultCarrier.Range)
                                "The closed callback result does not fit its declared native return ABI."

                        let! resultBits = sourceWidth graph entry.Result returned

                        return!
                            require
                                (resultBits = scalarBits returned)
                                "The closed callback result requires its source-settled native return slot, not a guessed extension."
                    }
                | _ -> Error "The closed C profile requires an exact integer or void native return."

            let transport =
                Set.union (Set.ofList (formation.Formation :: originalOperand :: operand.Actual :: evidence.Transport))
                          (operand.OptionalEntry |> Option.toList |> List.collect BoundaryOptionalEntryChoice.leaves |> List.filter (fun leaf -> leaf.Payload.IsSome) |> List.map _.Transport |> Set.unionMany)

            let participants =
                Set.unionMany
                    [
                        Set.singleton invocation.Identity
                        Set.singleton call.Site
                        transport
                        Set.ofList (
                            entry.Result :: implementation :: formals
                            @ Clef.Compiler.Baker.Ingredients.CompilerOwnedEntries.lifetimeNodes entry.Lifetime
                        )
                        Set.singleton contract.Identity
                    ]

            let! registrations =
                match invocation.Extent with
                | BoundaryCallbackExtent.DuringCall | BoundaryCallbackExtent.Retained _ -> Ok Map.empty
                | BoundaryCallbackExtent.ProcessExit _ ->
                    checked' {
                        let contexts = numericProjection.ForeignResultUses |> List.filter(fun sourceUse ->
                            sourceUse.Application.Call=call.Site && sourceUse.Application.Declaration=import.Binding)
                        do! require (not contexts.IsEmpty) "A process-exit registration lost its current per-application result context."
                        let! rows = contexts |> List.map(fun sourceUse -> checked' {
                            let context=sourceUse.Application.Context
                            let! support =
                                match sourceUse.Participants with
                                | ParticipantEvidence.Established rows -> Ok(rows |> List.map(fun row -> row.Node) |> Set.ofList)
                                | ParticipantEvidence.Pending _ -> Error "A process-exit registration has pending source application support."
                            return (call.Site,source.Parameter,context),
                            { Call=call.Site; Parameter=source.Parameter; Formation=formation.Formation; Invocation=invocation.Identity
                              Result=call.Site; Context=context
                              // Call/import retain their own nested declaration
                              // premises; this use holds their exact identities
                              // and the complete issued application support.
                              Participants=Set.unionMany [participants;support;Set.ofList (import.Identity::context)] } }) |> collect
                        do! require (rows |> List.map fst |> List.distinct |> List.length = rows.Length)
                                "A process-exit registration has duplicate source application contexts."
                        return Map.ofList rows
                    }

            return
                invocation,
                ({
                    Formation = formation.Formation
                    Operand = originalOperand
                    Declaration = entry.Lifetime.Binding
                    Implementation = implementation
                    Formals = formals
                    Body = entry.Result
                    Lifetime = entry.Lifetime
                    Invocation = identity
                    ParameterAdaptations = if unitParameterOmission then [None] else parameterAdaptations
                    ResultAdaptation = resultAdaptation
                    Registrations = registrations
                    Transport = transport
                    Participants = Set.union participants (registrations.Values |> Seq.map _.Participants |> Set.unionMany)
                }
                : BoundaryClosedEntry)
        }

    // Reconcile once, then inspect every receiving use before any representative
    // is chosen. A preceding ordinary use cannot disappear behind a later Some.
    let receivingUses =
        calls.Values |> Seq.collect(fun call ->
            call.Arguments |> List.choose(fun operand ->
                match operand.Abi with
                | BoundaryScalar.Entry identity ->
                    let admitted =
                        match operand.OptionalEntry with
                        | Some (BoundaryOptionalEntryChoice.Direct selected) when selected.Payload.IsNone ->
                            imports.TryFind call.Import |> needed "The optional callback lost its admitted import."
                            |> Result.bind(fun import -> invocationAt import identity)
                            |> Result.bind(fun (_,invocation) ->
                                if invocation.Extent=BoundaryCallbackExtent.DuringCall then Ok(invocation,None)
                                else Error "Optional native entries require a during-call activation.")
                        | _ -> closedAt call operand identity |> Result.map(fun(invocation,entry)->invocation,Some entry)
                    Some(call,operand,admitted)
                | _ -> None)) |> Seq.toList
    let shareable formation =
        receivingUses |> List.forall(fun(_,operand,admitted) ->
            match admitted with
            | Ok(invocation,Some entry) when entry.Formation=formation ->
                entry.Registrations.IsEmpty && invocation.Extent=BoundaryCallbackExtent.DuringCall &&
                (operand.OptionalEntry |> Option.toList |> List.collect BoundaryOptionalEntryChoice.leaves |> List.exists(fun selected->
                    selected.CaseOrdinal=1 && selected.Payload.IsSome && selected.Formation=Some formation))
            | _ -> true)
    let sameCode (left:BoundaryClosedEntry) (right:BoundaryClosedEntry) =
        {left with Invocation=right.Invocation;Transport=right.Transport;Participants=right.Participants;Registrations=right.Registrations}=right
    let callbackInvocations, (closedEntries: Map<NodeId, BoundaryClosedEntry>), errors =
        receivingUses |> List.fold(fun(invocations,entries,errors) (call,_,admitted: Result<BoundaryCallbackInvocation * BoundaryClosedEntry option, string>) ->
            match admitted with
            | Ok(invocation,None) -> Map.add invocation.Identity invocation invocations,entries,errors
            | Ok(invocation,Some (entry: BoundaryClosedEntry)) ->
                match Map.tryFind entry.Formation entries with
                | Some (previous: BoundaryClosedEntry) when previous.Invocation<>entry.Invocation ->
                    match Map.tryFind previous.Invocation invocations with
                    | Some witness when shareable entry.Formation && previous.Registrations.IsEmpty && entry.Registrations.IsEmpty &&
                                        sameCode previous entry && sameDuringCallAbi witness invocation ->
                        // The least invocation identity is a deterministic ABI
                        // witness only; per-use claims retain their own identity.
                        let representative=if NodeId.value previous.Invocation<NodeId.value entry.Invocation then previous else entry
                        let merged: BoundaryClosedEntry =
                            { representative with
                                Transport=Set.union previous.Transport entry.Transport
                                Participants=Set.union previous.Participants entry.Participants }
                        Map.add invocation.Identity invocation invocations,Map.add entry.Formation merged entries,errors
                    | _ ->
                        invocations,entries,(call.Site,call.Participants,"One closed entry formation cannot acquire different receiving invocation contracts.")::errors
                | Some (previous: BoundaryClosedEntry) ->
                    let merged: BoundaryClosedEntry =
                        { entry with
                            Transport=Set.union previous.Transport entry.Transport
                            Participants=Set.union previous.Participants entry.Participants
                            Registrations=Map.fold(fun rows key value->Map.add key value rows) previous.Registrations entry.Registrations }
                    Map.add invocation.Identity invocation invocations,Map.add entry.Formation merged entries,errors
                | None -> Map.add invocation.Identity invocation invocations,Map.add entry.Formation entry entries,errors
            | Error reason -> invocations,entries,(call.Site,call.Participants,reason)::errors) (Map.empty,(Map.empty: Map<NodeId, BoundaryClosedEntry>),errors)

    let bufferAbsences, errors =
        match bufferAbsenceAccounts graph descriptors imports with
        | Ok rows ->
            let referenced =
                calls.Values
                |> Seq.collect _.Arguments
                |> Seq.choose _.BufferAbsence
                |> Seq.collect BoundaryBufferAbsenceChoice.leaves
                |> Seq.map _.Absence
                |> Set.ofSeq
            rows |> Map.filter (fun id _ -> referenced.Contains id), errors
        | Error reason -> Map.empty, (anchor.Id, Set.singleton anchor.Id, reason) :: errors
    let countedEntryArrays, errors =
        descriptors.CountedEntryArrays |> List.fold (fun (rows, errors) source ->
            match callbackInvocations.TryFind source.Invocation.Quote with
            | Some invocation ->
                match declarationFacts graph source.DescriptorBinding with
                | Ok facts ->
                    let row: BoundaryCountedEntryArray =
                        { Identity = source.Quote; Import = invocation.Import; Parameter = invocation.Parameter
                          Invocation = invocation.Identity; Contract = source.Contract; DeclarationFacts = facts
                          Participants = ParticipantEvidence.Established [ { Role = ParticipantRole.CountedEntryArrayDeclaration; Node = source.Quote; Ordinal = invocation.Parameter; Group = source.Quote }; { Role = ParticipantRole.CountedEntryArrayInvocation; Node = invocation.Identity; Ordinal = invocation.Parameter; Group = source.Quote } ] }
                    Map.add row.Identity row rows, errors
                | Error reason -> rows, (source.Node, Set.ofList source.Participants, reason) :: errors
            | None -> rows, errors) (Map.empty, errors)
    let callbackAbsences, errors =
        match absenceAccounts graph descriptors imports callbackInvocations with
        | Ok rows ->
            demandedAbsences (calls.Values |> Seq.toList) rows, errors
        | Error reason -> Map.empty,(anchor.Id,Set.singleton anchor.Id,reason)::errors
    let calls = calls |> Map.map(fun _ call ->
        let extra=callbackAbsences.Values |> Seq.filter(fun row->row.Import=call.Import && (call.Arguments |> List.indexed |> List.exists(fun(ordinal,operand)->ordinal=row.Parameter && (operand.OptionalEntry |> Option.toList |> List.collect BoundaryOptionalEntryChoice.leaves |> List.exists(fun selected->selected.Payload.IsNone)))))
                  |> Seq.collect(fun row -> row.DeclarationFacts |> Map.keys) |> Set.ofSeq
        {call with Participants=Set.union call.Participants extra})
    let calls, optionalRequirements, errors =
        calls |> Map.fold (fun (updated, enrichment, errors) _ call ->
            let arguments, enrichment, errors =
                call.Arguments |> List.mapi (fun ordinal operand -> ordinal,operand)
                |> List.fold (fun (arguments, enrichment, errors) (ordinal,operand) ->
                    match operand.OptionalEntry with
                    | None -> operand::arguments,enrichment,errors
                    | Some choice ->
                        let issue (selection: BoundaryOptionalEntry) =
                            let role = $"foreign-optional-entry-conversion-{ordinal}"
                            let identityRole =
                                match choice with
                                | BoundaryOptionalEntryChoice.Conditional _ -> $"{role}-case-{selection.CaseOrdinal}"
                                | BoundaryOptionalEntryChoice.Direct _ -> role
                            let reason =
                                if selection.Payload.IsNone then "Selected-target optional-entry conversion and the foreign nullable-acceptance premise remain Pending."
                                else "Selected-target optional-entry conversion remains Pending."
                            match optionalSupport graph.Codata.Value.CallableAggregateDependencies imports callbackInvocations callbackAbsences call ordinal selection
                                  |> Result.bind (fun support ->
                                      Ingredients.requirementWithIdentityRoleAndRetained retained enrichId graph.Nodes[call.Site] identityRole role
                                        "The exact source Option selection requires an admitted target boundary conversion." reason
                                        (Set.toList support)) with
                            | Error reason -> Error reason
                            | Ok requirement ->
                                let issued =
                                    match requirement.NewNodes with
                                    | [citizen] -> Ok citizen
                                    | _ -> Error "An optional-entry application lost its unique source-issued requirement citizen."
                                let issued = issued |> Result.map (fun citizen ->
                                    let refined =
                                        match selection.Payload, selection.Formation, graph.Nodes.TryFind selection.Construction,
                                              Clef.Compiler.Baker.Ingredients.CallableAggregateAccounts.resultRetirement graph operand.Actual call.Site with
                                        | Some payload, Some formation, Some construction, Ok retirement ->
                                            let sourceCase =
                                                match construction.Kind with
                                                | SemanticKind.UnionCase(_, ordinal, Some original)
                                                | SemanticKind.DUConstruct(_, ordinal, Some original, _) when original=payload -> Some ordinal
                                                | _ -> None
                                            match sourceCase, closedEntries.TryFind formation, operand.Abi with
                                            | Some sourceCase, Some entry, BoundaryScalar.Entry invocation when sourceCase=1 &&
                                                (callbackInvocations.TryFind invocation |> Option.exists(fun receiving->
                                                    currentOptionalInvocation graph call ordinal receiving &&
                                                    optionalCodeWitness callbackInvocations (calls.Values |> Seq.toList) entry receiving)) ->
                                                let model:OptionalEntryArgumentConversionModel =
                                                    {Call=call.Site;Parameter=ordinal;Actual=operand.Actual;Construction=selection.Construction
                                                     SourceCase=sourceCase;Payload=payload;Formation=formation;Invocation=invocation;ResultRetirement=retirement
                                                     Arms=[{CaseOrdinal=0;Choice=OptionalEntryPlanChoice.PendingAbsence;Formation=None}
                                                           {CaseOrdinal=1;Choice=OptionalEntryPlanChoice.ClosedEntry;Formation=Some formation}]}
                                                let support = requirement.NewEdges |> List.find(fun edge->edge.Role=EdgeRole.Constrains) |> _.Sources |> Set.ofList
                                                let refined = refine citizen (ObligationBody.OptionalEntryArgumentConversion model) support [] requirement
                                                let nodes = refined.NewNodes |> List.map (fun node ->
                                                    match node.Kind with
                                                    | SemanticKind.Obligation info ->
                                                        {node with Kind=SemanticKind.Obligation {info with Statement="The exact source Some selection has complete finite native-choice plan correspondence; target realization remains an artifact obligation."}}
                                                    | _ -> node)
                                                {refined with NewNodes=nodes}
                                            | _ -> requirement
                                        | None, None, Some _, Ok retirement when selection.CaseOrdinal=0 ->
                                            let rows=callbackAbsences.Values |> Seq.filter(fun row->row.Import=call.Import && row.Parameter=ordinal) |> Seq.toList
                                            match rows with
                                            | [absence] ->
                                                let model:OptionalEntryAbsenceArgumentConversionModel =
                                                    {Call=call.Site;Parameter=ordinal;Actual=operand.Actual;Construction=selection.Construction;SourceCase=selection.CaseOrdinal;Absence=absence.Quote;ResultRetirement=retirement
                                                     Arms=[{CaseOrdinal=0;Choice=OptionalEntryAbsencePlanChoice.AbsentEntry};{CaseOrdinal=1;Choice=OptionalEntryAbsencePlanChoice.RequiresClosedEntry}]}
                                                let support=requirement.NewEdges |> List.find(fun edge->edge.Role=EdgeRole.Constrains) |> _.Sources |> Set.ofList
                                                let refined=refine citizen (ObligationBody.OptionalEntryAbsenceArgumentConversion model) support [] requirement
                                                {refined with NewNodes=refined.NewNodes |> List.map(fun node -> match node.Kind with SemanticKind.Obligation info -> {node with Kind=SemanticKind.Obligation {info with Statement="The exact source None selection has complete finite absence-choice correspondence under its external binding hypothesis; target realization remains an artifact obligation."}} | _->node)}
                                            | _ -> requirement
                                        | _ -> requirement
                                    let selected = {selection with Obligation=citizen.Id}
                                    selected, refined)
                                issued
                        let issued = choice |> BoundaryOptionalEntryChoice.leaves |> List.map issue |> collect
                        match choice, issued with
                        | BoundaryOptionalEntryChoice.Direct _, Ok [selected, requirement] ->
                            {operand with OptionalEntry=Some (BoundaryOptionalEntryChoice.Direct selected)}::arguments,Enrichment.combine enrichment requirement,errors
                        | BoundaryOptionalEntryChoice.Conditional(select, tagProjection, _, _), Ok [whenTrue, trueRequirement; whenFalse, falseRequirement] ->
                            {operand with OptionalEntry=Some (BoundaryOptionalEntryChoice.Conditional(select, tagProjection, whenTrue, whenFalse))}::arguments,
                            Enrichment.combine (Enrichment.combine enrichment trueRequirement) falseRequirement,errors
                        | _, Error reason -> operand::arguments,enrichment,(call.Site,call.Participants,reason)::errors
                        | _ -> operand::arguments,enrichment,(call.Site,call.Participants,"The optional-entry choice lost an arm requirement.")::errors)
                    ([],enrichment,errors)
            let arguments = List.rev arguments
            let arguments, enrichment, errors =
                arguments |> List.mapi (fun ordinal operand -> ordinal, operand)
                |> List.fold (fun (argsOut, enrichment, errors) (ordinal, operand) ->
                    match operand.BufferAbsence with
                    | None -> operand :: argsOut, enrichment, errors
                    | Some choice ->
                        let issue (selection: BoundaryBufferAbsenceSelection) =
                            let role = $"foreign-buffer-absence-conversion-{ordinal}"
                            let identityRole =
                                match choice with
                                | BoundaryBufferAbsenceChoice.Conditional _ -> $"{role}-case-{selection.CaseOrdinal}"
                                | BoundaryBufferAbsenceChoice.Direct _ -> role
                            let support = Set.union (Set.ofList selection.Transport) (Set.ofList [call.Site; operand.Actual; selection.Construction; selection.Absence])
                            match Ingredients.requirementWithIdentityRoleAndRetained retained enrichId graph.Nodes[call.Site] identityRole role
                                    "The exact source Option<Buffer> selection converts strictly at the foreign call boundary under BufferAbsenceContract."
                                    "BufferAbsenceContract conversion remains Pending."
                                    (Set.toList support) with
                            | Error reason -> Error reason
                            | Ok requirement ->
                                match requirement.NewNodes with
                                | [citizen] ->
                                    let model: BufferAbsenceArgumentConversionModel =
                                        { Call = call.Site; Parameter = ordinal; Actual = operand.Actual; Construction = selection.Construction
                                          SourceCase = selection.CaseOrdinal; Absence = selection.Absence
                                          Arms =
                                            [ { BufferAbsencePlanArm.CaseOrdinal = 0; Choice = BufferAbsencePlanChoice.AbsentNull }
                                              { BufferAbsencePlanArm.CaseOrdinal = 1; Choice = BufferAbsencePlanChoice.RequiresNonNullBuffer } ] }
                                    let cSupport = requirement.NewEdges |> List.find (fun edge -> edge.Role = EdgeRole.Constrains) |> _.Sources |> Set.ofList
                                    let refined = refine citizen (ObligationBody.BufferAbsenceArgumentConversion model) cSupport [] requirement
                                    Ok({ selection with Obligation = citizen.Id }, refined)
                                | _ -> Error "A buffer-absence application lost its unique source-issued requirement citizen."
                        let issued = choice |> BoundaryBufferAbsenceChoice.leaves |> List.map issue |> collect
                        match choice, issued with
                        | BoundaryBufferAbsenceChoice.Direct _, Ok [selected, requirement] ->
                            { operand with BufferAbsence = Some(BoundaryBufferAbsenceChoice.Direct selected) } :: argsOut, Enrichment.combine enrichment requirement, errors
                        | BoundaryBufferAbsenceChoice.Conditional(select, tagProjection, _, _), Ok [whenTrue, trueReq; whenFalse, falseReq] ->
                            { operand with BufferAbsence = Some(BoundaryBufferAbsenceChoice.Conditional(select, tagProjection, whenTrue, whenFalse)) } :: argsOut,
                            Enrichment.combine (Enrichment.combine enrichment trueReq) falseReq, errors
                        | _, Error reason -> operand :: argsOut, enrichment, (call.Site, call.Participants, reason) :: errors
                        | _ -> operand :: argsOut, enrichment, (call.Site, call.Participants, "The buffer-absence choice lost an arm requirement.") :: errors)
                    ([], enrichment, errors)
            let arguments = List.rev arguments
            let optionalParticipants = arguments |> List.choose _.OptionalEntry |> List.collect BoundaryOptionalEntryChoice.leaves |> List.map _.Obligation
            let absenceParticipants = arguments |> List.choose _.BufferAbsence |> List.collect BoundaryBufferAbsenceChoice.leaves |> List.map _.Obligation
            let participants = optionalParticipants @ absenceParticipants |> Set.ofList |> Set.union call.Participants
            Map.add call.Site {call with Arguments=arguments;Participants=participants} updated,enrichment,errors)
            (Map.empty,Enrichment.empty,errors)

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
            match operand.Abi with
            | BoundaryScalar.Entry _ | BoundaryScalar.ResourceHandle _ | BoundaryScalar.WritableBytes _ | BoundaryScalar.ReadOnlyBytes _ -> None
            | _ ->
                let input = match operand.Abi with BoundaryScalar.Boolean -> ValueRange.boolean | _ -> graph.Nodes[operand.Actual].ValueRange |> Option.defaultValue ValueRange.Unbounded
                Some(ordinal, operand.Actual, input, scalarRange operand.Abi)) |> List.choose id
        // Integer result narrowing belongs to Numeric's conditional foreign
        // account. The C carrier is an ABI premise, not a behavioral enclosure.
        let resultRange = call.Result |> Option.toList |> List.filter (function BoundaryScalar.Integer _ | BoundaryScalar.ResourceHandle _ | BoundaryScalar.BorrowedBytes _ -> false | _ -> true) |> List.map (fun abi ->
            let destination =
                match abi with
                | BoundaryScalar.Boolean -> ValueRange.boolean
                | _ -> RangeAnalysis.selectedRepresentation graph call.Site
                       |> Option.bind Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources.declaredRange
                       |> Option.defaultValue ValueRange.Unbounded
            -1, call.Site, scalarRange abi, destination)
        argumentRanges @ resultRange |> List.fold (fun (enrichment, errors) (ordinal, operand, input, destination) ->
            match Ingredients.coverageWithRetained retained enrichId graph call ordinal operand input destination with
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
    let boundaryPremises=Ingredients.premises graph
    let resourceEvidence,errors =
        if resourceRoots.IsEmpty then None,errors else
        let retained=checked' {
            let! platform=runtime.Platform |> needed "Resource source evidence has no exact selected platform."
            let! core=platform.Core |> needed "Resource source evidence has no exact selected core."
            let! targetFacts=[platform.Node;core.Node] |> List.map(declarationFacts graph) |> collect
            let targetIds=targetFacts |> List.collect(Map.keys>>Seq.toList) |> Set.ofList
            let accessIds=resourceAccesses.Values |> Seq.map _.Participants |> Set.unionMany
            let callIds=calls.Values |> Seq.filter(fun call->call.Resource.IsSome) |> Seq.map _.Participants |> Set.unionMany
            let ids=Set.unionMany [targetIds;accessIds;callIds]
            // Retain exact metadata incidence named by the held source rows.
            // This is one finite projection, not transitive body discovery:
            // lexical declarations, original lambda formals, and context
            // wrappers remain metadata rather than executable body roots.
            let metadataIds =
                let rec context (seen: Set<NodeId>) id =
                    match boundaryPremises.TryFind id with
                    | Some premise ->
                        match premise.Shape.Parent with
                        | Some parent when not (seen.Contains parent) ->
                            match graph.Nodes.TryFind parent with
                            | Some { Kind = SemanticKind.TypeAnnotation _ | SemanticKind.Quote _ | SemanticKind.Binding _ | SemanticKind.ModuleDef _ } ->
                                parent :: context (Set.add parent seen) parent
                            | _ -> []
                        | _ -> []
                    | None -> []

                ids
                |> Set.toList
                |> List.collect (fun id ->
                    match boundaryPremises.TryFind id with
                    | None -> []
                    | Some premise ->
                        let shape = premise.Shape

                        let members =
                            match shape.Form, shape.Numbers with
                            | "module", _ -> List.take (shape.References.Length - shape.Children.Length) shape.References
                            | "lambda", arity :: _ when arity >= 0I && arity <= bigint shape.References.Length ->
                                List.take (int arity) shape.References
                            | _ -> []

                        members @ ((id :: members) |> List.collect (fun memberId -> context (Set.singleton memberId) memberId)))
                |> Set.ofList

            let ids = Set.union ids metadataIds

            let owned=resourceRequirements.NewNodes |> List.map _.Id |> Set.ofList |> Set.add anchor.Id
            do! require (ids |> Set.forall(fun id->boundaryPremises.ContainsKey id || owned.Contains id))
                        "A resource source premise was withdrawn before publication."
            return {Platform=platform.Node;Core=core.Node;Premises=boundaryPremises |> Map.filter(fun id _->ids.Contains id)
                    Roots=List.distinct resourceRoots;Relations=resourceRelations;Accesses=Map.keys resourceAccesses |> Seq.toList}:BoundaryResourceEvidence }
        match retained with
        | Ok evidence -> Some evidence,errors
        | Error reason -> None,(anchor.Id,Set.singleton anchor.Id,reason)::errors
    let domain =
        { ResourceEvidence = resourceEvidence
          Premises = boundaryPremises; Platform = Ingredients.platformPremise graph.Platform; Meets = graph.Codata.Value.Meets
          Declarations = graph.Edges |> List.choose (fun edge -> match edge.Role with EdgeRole.BoundaryDeclaration declaration -> Some declaration | _ -> None)
          ResultHypotheses = descriptors.ResultRanges |> List.map _.Hypothesis
          WritableBufferDeclarations = Map.keys writableDeclarations |> Seq.toList
          WritableBufferUses = Map.keys writableUses |> Seq.toList
          ReadOnlyBufferDeclarations = Map.keys readOnlyDeclarations |> Seq.toList
          ReadOnlyBufferUses = Map.keys readOnlyUses |> Seq.toList
          BorrowedResultViewDeclarations = Map.keys borrowedViewDeclarations |> Seq.toList
          BorrowedResultViewUses = Map.keys borrowedViewUses |> Seq.toList
          BufferAbsences = Map.keys bufferAbsences |> Seq.toList
          CountedEntryArrays = Map.keys countedEntryArrays |> Seq.toList
          ResourceDeclarations = Map.keys resourceDeclarations |> Seq.toList
          ResourceAccesses = Map.keys resourceAccesses |> Seq.toList
          ResourceEvaluationRoots = List.distinct resourceRoots
          ResourceEvaluationRelations = resourceRelations
          Imports = Map.keys imports |> Seq.toList; Calls = Map.keys calls |> Seq.toList
          // Native entries and callback accounts require their selected source loading
          // even when every import is libc; ordinary direct libc calls keep no account.
          Loading = if entries.IsEmpty && closedEntries.IsEmpty && callbackInvocations.IsEmpty && (imports.Values |> Seq.forall (fun import -> import.Library = "c"))
                       && not (loading |> Result.toOption |> Option.exists (fun account -> account.Contract.Runtime = "win32" && account.Contract.Os = "windows"))
                    then None else loading |> Result.toOption
          Entries = Map.keys entries |> Seq.toList
          CallbackInvocations = Map.keys callbackInvocations |> Seq.toList
          CallbackAbsences = Map.keys callbackAbsences |> Seq.toList
          ClosedEntries = Map.keys closedEntries |> Seq.toList
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
    let evidenceNodes = function
        | ParticipantEvidence.Established rows -> rows |> List.map _.Node |> List.distinct
        | ParticipantEvidence.Pending early -> early.Derived |> List.map _.Node |> List.distinct
    let sources = Map.keys domain.Premises |> Seq.toList
    let rows =
        [Ingredients.row (EdgeRole.BoundaryDomain domain) 0 sources anchor.Id
         { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = 0; Sources = sources; Target = anchor.Id }]
        @ (resourceDeclarations.Values |> Seq.map (fun row -> Ingredients.row (EdgeRole.BoundaryResourceDeclaration row) 0 (Set.toList row.Participants) row.Identity) |> Seq.toList)
        @ (writableDeclarations.Values |> Seq.map (fun row -> Ingredients.row (EdgeRole.BoundaryWritableBufferDeclaration row) 0 (Set.toList row.Participants) row.Identity) |> Seq.toList)
        @ (writableUses.Values |> Seq.map(fun row->Ingredients.row (EdgeRole.BoundaryWritableBufferUse row) 0 (Set.toList row.Participants) row.Call) |> Seq.toList)
        @ (readOnlyDeclarations.Values |> Seq.map (fun row -> Ingredients.row (EdgeRole.BoundaryReadOnlyBufferDeclaration row) 0 (evidenceNodes row.Participants) row.Identity) |> Seq.toList)
        @ (readOnlyUses.Values |> Seq.map (fun row -> Ingredients.row (EdgeRole.BoundaryReadOnlyBufferUse row) 0 (evidenceNodes row.Participants) row.Call) |> Seq.toList)
        @ (borrowedViewDeclarations.Values |> Seq.map (fun row -> Ingredients.row (EdgeRole.BoundaryBorrowedResultViewDeclaration row) 0 (evidenceNodes row.Participants) row.Identity) |> Seq.toList)
        @ (borrowedViewUses.Values |> Seq.map (fun row -> Ingredients.row (EdgeRole.BoundaryBorrowedResultViewUse row) 0 (evidenceNodes row.Participants) row.Call) |> Seq.toList)
        @ (bufferAbsences.Values |> Seq.map (fun row -> Ingredients.row (EdgeRole.BoundaryBufferAbsence row) 0 (row.DeclarationFacts |> Map.keys |> Seq.toList) row.Quote) |> Seq.toList)
        @ (countedEntryArrays.Values |> Seq.map (fun row -> Ingredients.row (EdgeRole.BoundaryCountedEntryArray row) 0 (evidenceNodes row.Participants) row.Identity) |> Seq.toList)
        @ (resourceAccesses.Values |> Seq.map (fun row -> Ingredients.row (EdgeRole.BoundaryResourceAccess row) 0 (Set.toList row.Participants) row.Site) |> Seq.toList)
        @ (imports.Values |> Seq.map Ingredients.importRow |> Seq.toList)
        @ (entries.Values |> Seq.map (fun entry -> Ingredients.row (EdgeRole.BoundaryEntry entry) 0 (Set.toList entry.Participants) entry.Formation) |> Seq.toList)
        @ (callbackInvocations.Values |> Seq.map (fun invocation -> Ingredients.row (EdgeRole.BoundaryCallbackInvocation invocation) 0 (Set.toList invocation.Participants) invocation.Identity) |> Seq.toList)
        @ (callbackAbsences.Values |> Seq.map(fun row -> Ingredients.row (EdgeRole.BoundaryCallbackAbsence row) 0 (row.DeclarationFacts |> Map.keys |> Seq.toList) row.Quote) |> Seq.toList)
        @ (closedEntries.Values |> Seq.map (fun (entry: BoundaryClosedEntry) -> Ingredients.row (EdgeRole.BoundaryClosedEntry entry) 0 (Set.toList entry.Participants) entry.Formation) |> Seq.toList)
        @ (calls.Values |> Seq.collect (fun call -> Ingredients.callRow call :: Ingredients.operandRows call) |> Seq.toList)
        @ (domain.IntrinsicImports |> List.map Bytes.importRow)
        @ (domain.IntrinsicCalls |> List.collect Bytes.callRows)
    Enrichment.combine readOnlyRequirements (Enrichment.combine borrowedViewRequirements (Enrichment.combine optionalRequirements (Enrichment.combine writableRequirements (Enrichment.combine (Enrichment.combine resourceRequirements resourceEvaluation)
        (Enrichment.combine (Enrichment.combine { NewNodes = [anchor]; Annotated = []; NewEdges = rows } proofs) intrinsic.Enrichment)
    ))))

let elaborateWithRetained (retained: Ingredients.RetainedBoundaryNodes) graph =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> elaborateCore retained graph)

let elaborate graph =
  elaborateWithRetained Ingredients.RetainedBoundaryNodes.empty graph
