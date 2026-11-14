// SPDX-License-Identifier: MIT
/// Exact array extent dependencies. Counts remain source operands; ranges only
/// enclose their values and never replace a descriptor's runtime extent.
module Clef.Compiler.Baker.Ingredients.ArrayShapes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Origins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
module Boundaries = Clef.Compiler.Baker.Recipes.BoundaryDeclarations
module DirectCaptures = Clef.Compiler.PSGSaturation.SemanticGraph.DirectCaptures
module PlatformResolution = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

[<RequireQualifiedAccess>]
type ReadOnlyViewProvenance =
    | ByteBacked
    | ArrayBacked
    | MixedConflict
    | Unknown

[<RequireQualifiedAccess>]
type Length = Constant of bigint | Count of NodeId
type Extent = { Sources:Length list; StringSources:Set<NodeId>; Participants:Set<NodeId> }

let intrinsicApplication (graph:SemanticGraph) start =
    let rec follow seen id arguments =
        if Set.contains id seen then None else
        let seen=Set.add id seen
        match graph.Nodes.TryFind id with
        | Some {Kind=SemanticKind.Application(callee,actuals)} -> follow seen callee (actuals@arguments)
        | _ ->
            match Boundaries.target graph id with
            | Some({Kind=SemanticKind.Intrinsic info},path) -> Some(info,arguments,Set.union seen path)
            | _ -> None
    follow Set.empty start []

/// Source-only logical extent, not byte storage, immutable residency or a borrow.
/// A private inline constant array has no intervening writes. Its whole UTF-8
/// payload must be valid; the descriptor length counts bytes, not characters.
/// The consumer/absence census is reread from the current graph. Participants
/// are direct support, not a sufficient key for selective proof reuse.
let private inlineStringExtent (graph:SemanticGraph) site input =
    let arrayType = NativeType.TApp(Types.arrayTyCon, [Types.intType])
    let live id = graph.Nodes.TryFind id |> Option.filter _.IsReachable
    let sourceEdge (edge:Hyperedge) = edge.Class=EdgeClass.Structural || edge.Class=EdgeClass.Reference
    let key (edge:Hyperedge) = edge.Class,edge.Role,edge.Ordinal,edge.Target,edge.Sources
    let intact (node:SemanticNode) =
        let actual = graph.Edges |> List.filter (fun edge -> edge.Target=node.Id && sourceEdge edge) |> List.map key |> List.sort
        let expected = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence node |> List.filter sourceEdge |> List.map key |> List.sort
        // Native F stores explicit enrichments. Kind/Children provide current
        // syntax incidence; optional recorded copies must be unique and agree.
        actual.Length=(List.distinct actual).Length && List.forall (fun row -> List.contains row expected) actual
    let onlyArgument (edge:Hyperedge) =
        edge.Class=EdgeClass.Structural && edge.Role=EdgeRole.Argument &&
        edge.Ordinal=0 && edge.Target=site && edge.Sources=[input]
    let privateInput () =
        let capturesInput (capture:CaptureInfo) =
            match capture.SourceNodeId with
            | Some source -> source=input
            | None -> applySubst capture.Type=arrayType
        let active = graph.Nodes.Values |> Seq.filter _.IsReachable |> Seq.toList
        let uncaptured =
            active |> List.forall (fun node ->
                let captures =
                    match node.Kind with
                    | SemanticKind.Lambda(_,_,captures,_,_)
                    | SemanticKind.LazyExpr(_,captures) | SemanticKind.SeqExpr(_,captures) -> captures
                    | _ -> []
                not (List.exists capturesInput captures))
        let implied =
            active |> List.collect Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence
            |> List.filter (fun edge -> List.contains input edge.Sources)
        let recorded =
            graph.Edges |> List.filter (fun edge ->
                (edge.Class=EdgeClass.Structural || edge.Class=EdgeClass.Reference) &&
                List.contains input edge.Sources && (live edge.Target |> Option.isSome))
        uncaptured && implied.Length=1 && List.forall onlyArgument implied &&
        recorded.Length<=1 && List.forall onlyArgument recorded
    match graph.Platform, live site, live input with
    | None, Some call, Some array when applySubst call.Type=Types.stringType && applySubst array.Type=arrayType ->
        match call.Kind, array.Kind with
        | SemanticKind.Application(callee,[argument]), SemanticKind.ArrayExpr values
            when argument=input && call.Children=[callee;input] && array.Children=values && array.Parent=Some site &&
                 intact call && intact array ->
            match live callee with
            | Some ({Kind=SemanticKind.Intrinsic {Module=IntrinsicModule.String;Operation="fromBytes"};Children=[];Type=ty} as target)
                when applySubst ty=NativeType.TFun(arrayType,Types.stringType) && intact target && privateInput () ->
                let bytes = values |> List.map (fun value ->
                    match live value with
                    | Some ({Kind=SemanticKind.Literal(NativeLiteral.Int(number,kind));Children=[];Parent=Some parent;Type=ty} as literal)
                        when parent=input && applySubst ty=Types.intType &&
                             Some kind=Types.tryGetNTUKind Types.intType && 0L<=number && number<=255L && intact literal -> Some(byte number)
                    | _ -> None)
                if List.exists Option.isNone bytes then None else
                try
                    System.Text.UTF8Encoding(false,true).GetCharCount(bytes |> List.choose id |> List.toArray) |> ignore
                    Some {Sources=[Length.Constant(bigint values.Length)]; StringSources=Set.singleton site
                          Participants=Set.ofList(site::callee::input::values)}
                with :? System.Text.DecoderFallbackException -> None
            | _ -> None
        | _ -> None
    | _ -> None

let reader (graph:SemanticGraph) =
    let flow=Origins.resolve graph
    let inputs=FormalDemand.reader graph flow
    let stringOrigins = lazy (Clef.Compiler.Baker.Recipes.StringComparisonRecipes.stringOrigins graph flow)
    let combine values =
        if List.isEmpty values || values |> List.exists Option.isNone then None else
        let values=List.choose id values
        Some { Sources=values |> List.collect _.Sources; StringSources=values |> List.map _.StringSources |> Set.unionMany
               Participants=values |> List.map _.Participants |> Set.unionMany }
    let rec follow seen id =
        if Set.contains id seen then None else
        let seen=Set.add id seen
        let add (value:Extent option)=value |> Option.map(fun value -> {value with Participants=Set.add id value.Participants})
        let constant value=Some {Sources=[Length.Constant value];StringSources=Set.empty;Participants=Set.singleton id}
        let count value=Some {Sources=[Length.Count value];StringSources=Set.empty;Participants=Set.ofList[id;value]}
        match graph.Nodes.TryFind id with
        | Some {Kind=SemanticKind.Literal(NativeLiteral.String text)} ->
            constant(bigint(System.Text.Encoding.UTF8.GetByteCount text)) |> Option.map(fun extent -> {extent with StringSources=Set.singleton id})
        | Some {Kind=SemanticKind.ArrayExpr values} -> constant(bigint values.Length)
        | Some {Kind=SemanticKind.ArrayAllocate value} -> count value
        | Some {Kind=SemanticKind.VarRef(_,Some value) | SemanticKind.TypeAnnotation(value,_) | SemanticKind.EagerExpr value} -> follow seen value |> add
        | Some {Kind=SemanticKind.Binding(_,false,_,_);Children=[value]} -> follow seen value |> add
        | Some {Kind=SemanticKind.EnvironmentRead _;Type=ty} when Types.isStringType ty ->
            // Logical bytes follow the same scoped capture and complete input
            // authority as string origins. This grants no storage or borrow.
            match stringOrigins.Value id id with
            | Ok(Some(identity,origins,participants)) when not origins.IsEmpty ->
                Some {Sources=origins.Values |> Seq.map Length.Constant |> Seq.toList
                      StringSources=origins.Keys |> Set.ofSeq
                      Participants=Set.ofList(id::identity::(participants |> List.collect (fun p -> [p.Node;p.Group])))}
            | _ -> None
        | Some {Kind=SemanticKind.Sequential values} -> List.tryLast values |> Option.bind(follow seen) |> add
        | Some {Kind=SemanticKind.IfThenElse(_,yes,Some no)} -> combine[follow seen yes;follow seen no] |> add
        | Some {Kind=SemanticKind.PatternBinding _} ->
            match inputs id with
            | Some formal when formal.UsedLazyForces.IsEmpty ->
                // Array extent/memory domains do not yet retain the complete
                // lazy protocol relation census. Closing those callers alone
                // cannot grant this owner a reusable finite extent. String
                // origins have a separate, explicitly retained protocol scope.
                // A call in an omitted actual supplies no extent; the omission relations that contain it are premises.
                let omitted (input: FormalDemand.OmittedInput) =
                    Some {Sources=[];StringSources=Set.empty;Participants=input.Omissions |> List.collect (fun omission -> [omission.Site;omission.Actual]) |> Set.ofList}
                (formal.Demanded |> List.map(fun input -> input.Call,follow seen input.Actual))
                @ (formal.Omitted |> List.map(fun input -> input.Input.Call,omitted input))
                |> List.map(fun (call,supplied) -> supplied |> Option.map(fun extent ->
                    {extent with Participants=Set.union formal.Participants (extent.Participants.Add call)})) |> combine |> add
            | _ -> None
        | Some {Kind=SemanticKind.Application _} ->
            match intrinsicApplication graph id with
            | Some({Module=IntrinsicModule.Array;Operation=("zeroCreate"|"create"|"init")},value::_,_) -> count value
            | Some({Module=IntrinsicModule.Array;Operation=("sub" | "slice")},[_;_;value],_) -> count value
            | Some({Module=IntrinsicModule.Array;Operation=("ofArray" | "ofString")},[source],_) ->
                follow seen source |> add
            | Some({Module=IntrinsicModule.String;Operation="toBytes"},[source],_) ->
                follow seen source |> add
            | Some({Module=IntrinsicModule.String;Operation="fromBytes"},[snapshot],_) ->
                let rows=graph.Edges |> List.filter(fun edge ->
                    edge.Role=EdgeRole.StringByteSnapshot &&
                    (match edge.Sources with [_;copy] -> copy=snapshot | _ -> false))
                match rows with
                | [row] -> follow seen snapshot |> Option.map(fun extent ->
                    {extent with StringSources=Set.singleton id; Participants=Set.union extent.Participants (Set.ofList(id::row.Target::row.Sources))})
                | [] -> inlineStringExtent graph id snapshot
                | _ -> None
            | _ ->
                match flow.Calls.TryFind id with
                | Some {Complete=true;Unknown=false;Targets=targets} when not targets.IsEmpty ->
                    targets |> List.map(fun target -> follow seen target.Body |> Option.map(fun extent ->
                        {extent with Participants=Set.union extent.Participants (Set.ofList(target.Lambda::target.Body::target.Arguments))})) |> combine |> add
                | _ -> None
        | Some ({Kind=SemanticKind.StringByteBorrow source} as borrow) ->
            if graph.Platform.IsSome then follow seen source |> add else
            let sourceEdge (edge:Hyperedge) = edge.Class=EdgeClass.Structural || edge.Class=EdgeClass.Reference
            let key (edge:Hyperedge) = edge.Class,edge.Role,edge.Ordinal,edge.Target,edge.Sources
            let actual = graph.Edges |> List.filter (fun edge -> edge.Target=id && sourceEdge edge) |> List.map key |> List.sort
            let expected = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence borrow |> List.filter sourceEdge |> List.map key |> List.sort
            let agrees = actual.Length=(List.distinct actual).Length && List.forall (fun row -> List.contains row expected) actual
            match graph.Nodes.TryFind source with
            | Some value when borrow.IsReachable && value.IsReachable && borrow.Children=[source] && agrees &&
                              borrow.Type=Types.mkArrayType Types.intType && Types.isStringType value.Type ->
                // Reuse the owning source origin contract, including its lazy
                // protocol and complete formal-input validation. No new cache
                // semantics or physical byte-view authority is supplied here.
                match stringOrigins.Value id source with
                | Ok(Some(identity,origins,participants)) when not origins.IsEmpty ->
                    Some {Sources=origins.Values |> Seq.map Length.Constant |> Seq.toList
                          StringSources=origins.Keys |> Set.ofSeq
                          Participants=Set.ofList(id::source::identity::(participants |> List.collect (fun p -> [p.Node;p.Group])))}
                | Ok None -> follow seen source |> add
                // An origin error cannot fall back to weaker descriptor flow.
                // StringBorrowRecipes reports that exact error at its own site.
                | Error _ | Ok(Some _) -> None
            | _ -> None
        | _ -> None
    follow Set.empty

let observations (graph:SemanticGraph) =
    let read=reader graph
    graph.Nodes |> Map.fold(fun values id node ->
        let source=
            match node.Kind with
            | SemanticKind.FieldGet(buffer,"Length") -> Some buffer
            | SemanticKind.Application _ ->
                match intrinsicApplication graph id with
                | Some({Module=IntrinsicModule.Array | IntrinsicModule.String;Operation="length"},[buffer],_) -> Some buffer
                | _ -> None
            | _ -> None
        source |> Option.bind read |> Option.map(fun extent -> Map.add id extent values) |> Option.defaultValue values) Map.empty

type private ProvenanceState =
    | Unset
    | Resolved of ReadOnlyViewProvenance

let private joinState a b =
    match a, b with
    | Unset, x | x, Unset -> x
    | Resolved ReadOnlyViewProvenance.MixedConflict, _
    | _, Resolved ReadOnlyViewProvenance.MixedConflict -> Resolved ReadOnlyViewProvenance.MixedConflict
    | Resolved x, Resolved y when x = y -> Resolved x
    | Resolved _, Resolved _ -> Resolved ReadOnlyViewProvenance.MixedConflict

let private joinNonEmpty states =
    match states with
    | [] -> Resolved ReadOnlyViewProvenance.Unknown
    | _ -> List.fold joinState Unset states

/// Graph-flow classification of whether a ReadOnlyView<'T> originates from
/// UTF-8/byte storage (ReadOnlyView.ofString or byte BorrowedResultView),
/// an array (ReadOnlyView.ofArray), or a mixed conflict across branches/calls.
let readOnlyViewClassifier (graph: SemanticGraph) : NodeId -> ReadOnlyViewProvenance =
    let flow = Origins.resolve graph
    let inputs = FormalDemand.reader graph flow
    let descriptors = PlatformResolution.readDescriptors graph
    let borrowedByteBindings =
        descriptors.BorrowedResultViews
        |> List.choose (fun bv ->
            match graph.Nodes.TryFind bv.Declaration.Body with
            | Some bodyNode ->
                let viewTy =
                    match applySubst bodyNode.Type with
                    | NativeType.TApp(tc, [inner]) when tc.Name = "option" || tc.Name = "Option" -> inner
                    | ty -> ty
                match Types.tryGetReadOnlyViewElement viewTy |> Option.bind Types.tryGetNTUKind with
                | Some(NTUKind.NTUuint(NTUWidth.Fixed 8))
                | Some(NTUKind.NTUint(NTUWidth.Resolved WidthDimension.Register))
                | Some(NTUKind.NTUuint(NTUWidth.Resolved WidthDimension.Register)) -> Some bv.Declaration.Binding
                | _ -> None
            | None -> None)
        |> Set.ofList
    let setsByTarget = System.Collections.Generic.Dictionary<NodeId, NodeId list>()
    let fieldSetsByTarget = System.Collections.Generic.Dictionary<NodeId * string, NodeId list>()
    let indexSetsByTarget = System.Collections.Generic.Dictionary<NodeId, NodeId list>()
    let patternScrutinees = System.Collections.Generic.Dictionary<NodeId, NodeId list>()
    let addToDict (dict: System.Collections.Generic.Dictionary<'K, NodeId list>) (key: 'K) (value: NodeId) =
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
            | SemanticKind.Set(target, rhs) ->
                for t in targetRoots Set.empty target do
                    addToDict setsByTarget t rhs
            | SemanticKind.FieldSet(target, fieldName, rhs) ->
                for t in targetRoots Set.empty target do
                    addToDict fieldSetsByTarget (t, fieldName) rhs
            | SemanticKind.IndexSet(target, _, rhs) ->
                for t in targetRoots Set.empty target do
                    addToDict indexSetsByTarget t rhs
            | SemanticKind.Application _ ->
                match intrinsicApplication graph node.Id with
                | Some({ Module = IntrinsicModule.Array; Operation = "set" }, target :: _ :: rhs :: _, _) ->
                    for t in targetRoots Set.empty target do
                        addToDict indexSetsByTarget t rhs
                | _ -> ()
            | SemanticKind.Match(scrutinee, cases) ->
                for c in cases do
                    for pb in c.PatternBindings do
                        addToDict patternScrutinees pb scrutinee
            | SemanticKind.CaseElimination(scrutinee, arms) ->
                for arm in arms do
                    for b in arm.Bindings do
                        addToDict patternScrutinees b scrutinee
            | _ -> ()
    let dictLookup (dict: System.Collections.Generic.Dictionary<'K, NodeId list>) key =
        match dict.TryGetValue key with
        | true, xs -> xs
        | false, _ -> []
    let rec rootCallee nid =
        match graph.Nodes.TryFind nid with
        | Some { Kind = SemanticKind.Application(c, _) } -> rootCallee c
        | _ -> nid
    let memo = System.Collections.Generic.Dictionary<NodeId, ProvenanceState>()
    let rec walk seen seenFields seenTuples id =
        if Set.isEmpty seen && Set.isEmpty seenFields && Set.isEmpty seenTuples then
            match memo.TryGetValue id with
            | true, cached -> cached
            | false, _ ->
                let res = compute seen seenFields seenTuples id
                memo[id] <- res
                res
        else compute seen seenFields seenTuples id
    and computeFieldRead seen seenFields seenTuples fieldName recId =
        let key = recId, fieldName
        if Set.contains key seenFields then Unset else
        let seenFields = Set.add key seenFields
        let fieldStores = dictLookup fieldSetsByTarget key |> List.map (walk seen seenFields seenTuples)
        let recVal =
            match graph.Nodes.TryFind recId with
            | Some { Kind = SemanticKind.VarRef(_, Some inner) }
            | Some { Kind = SemanticKind.TypeAnnotation(inner, _) }
            | Some { Kind = SemanticKind.EagerExpr inner }
            | Some { Kind = SemanticKind.Deref inner }
            | Some { Kind = SemanticKind.Reborrow inner } -> computeFieldRead seen seenFields seenTuples fieldName inner
            | Some({ Kind = SemanticKind.Binding _ } as bnode) ->
                (bnode.Children @ dictLookup setsByTarget recId)
                |> List.map (computeFieldRead seen seenFields seenTuples fieldName)
                |> joinNonEmpty
            | Some({ Kind = SemanticKind.PatternBinding _ } as pnode) ->
                let sources =
                    match inputs recId with
                    | Some formal -> formal.Demanded |> List.map _.Actual
                    | None ->
                        let sourceDef = DirectCaptures.sourceDefinition graph recId
                        let captures = if sourceDef <> recId then [sourceDef] else []
                        pnode.Children @ captures @ dictLookup patternScrutinees recId @ dictLookup setsByTarget recId
                sources |> List.map (computeFieldRead seen seenFields seenTuples fieldName) |> joinNonEmpty
            | Some { Kind = SemanticKind.Sequential items } ->
                match List.tryLast items with
                | Some lastId -> computeFieldRead seen seenFields seenTuples fieldName lastId
                | None -> Resolved ReadOnlyViewProvenance.Unknown
            | Some { Kind = SemanticKind.IfThenElse(_, yes, Some no) } ->
                joinState (computeFieldRead seen seenFields seenTuples fieldName yes) (computeFieldRead seen seenFields seenTuples fieldName no)
            | Some { Kind = SemanticKind.IfThenElse(_, yes, None) } ->
                computeFieldRead seen seenFields seenTuples fieldName yes
            | Some { Kind = SemanticKind.Match(_, cases) } ->
                cases |> List.map (fun c -> computeFieldRead seen seenFields seenTuples fieldName c.Body) |> joinNonEmpty
            | Some { Kind = SemanticKind.CaseElimination(_, arms) } ->
                arms |> List.map (fun arm -> computeFieldRead seen seenFields seenTuples fieldName arm.Body) |> joinNonEmpty
            | Some { Kind = SemanticKind.RecordExpr(fields, copyFrom) } ->
                match fields |> List.tryPick (fun (fname, fval) -> if fname = fieldName then Some fval else None) with
                | Some fval -> walk seen seenFields seenTuples fval
                | None ->
                    match copyFrom with
                    | Some baseRec -> computeFieldRead seen seenFields seenTuples fieldName baseRec
                    | None -> Resolved ReadOnlyViewProvenance.Unknown
            | Some { Kind = SemanticKind.Application _ } ->
                match flow.Calls.TryFind recId with
                | Some { Complete = true; Unknown = false; Targets = targets } when not targets.IsEmpty ->
                    targets |> List.map (fun t -> computeFieldRead seen seenFields seenTuples fieldName t.Body) |> joinNonEmpty
                | _ -> Resolved ReadOnlyViewProvenance.Unknown
            | _ -> Resolved ReadOnlyViewProvenance.Unknown
        fieldStores |> List.fold joinState recVal
    and computeTupleRead seen seenFields seenTuples index tupId =
        let key = tupId, index
        if Set.contains key seenTuples then Unset else
        let seenTuples = Set.add key seenTuples
        let tupleStores = dictLookup setsByTarget tupId |> List.map (computeTupleRead seen seenFields seenTuples index)
        let tupVal =
            match graph.Nodes.TryFind tupId with
            | Some { Kind = SemanticKind.VarRef(_, Some inner) }
            | Some { Kind = SemanticKind.TypeAnnotation(inner, _) }
            | Some { Kind = SemanticKind.EagerExpr inner }
            | Some { Kind = SemanticKind.Deref inner }
            | Some { Kind = SemanticKind.Reborrow inner } -> computeTupleRead seen seenFields seenTuples index inner
            | Some({ Kind = SemanticKind.Binding _ } as bnode) ->
                (bnode.Children @ dictLookup setsByTarget tupId)
                |> List.map (computeTupleRead seen seenFields seenTuples index)
                |> joinNonEmpty
            | Some({ Kind = SemanticKind.PatternBinding _ } as pnode) ->
                let sources =
                    match inputs tupId with
                    | Some formal -> formal.Demanded |> List.map _.Actual
                    | None ->
                        let sourceDef = DirectCaptures.sourceDefinition graph tupId
                        let captures = if sourceDef <> tupId then [sourceDef] else []
                        pnode.Children @ captures @ dictLookup patternScrutinees tupId @ dictLookup setsByTarget tupId
                sources |> List.map (computeTupleRead seen seenFields seenTuples index) |> joinNonEmpty
            | Some { Kind = SemanticKind.Sequential items } ->
                match List.tryLast items with
                | Some lastId -> computeTupleRead seen seenFields seenTuples index lastId
                | None -> Resolved ReadOnlyViewProvenance.Unknown
            | Some { Kind = SemanticKind.IfThenElse(_, yes, Some no) } ->
                joinState (computeTupleRead seen seenFields seenTuples index yes) (computeTupleRead seen seenFields seenTuples index no)
            | Some { Kind = SemanticKind.IfThenElse(_, yes, None) } ->
                computeTupleRead seen seenFields seenTuples index yes
            | Some { Kind = SemanticKind.Match(_, cases) } ->
                cases |> List.map (fun c -> computeTupleRead seen seenFields seenTuples index c.Body) |> joinNonEmpty
            | Some { Kind = SemanticKind.CaseElimination(_, arms) } ->
                arms |> List.map (fun arm -> computeTupleRead seen seenFields seenTuples index arm.Body) |> joinNonEmpty
            | Some { Kind = SemanticKind.TupleExpr items } ->
                match List.tryItem index items with
                | Some item -> walk seen seenFields seenTuples item
                | None -> Resolved ReadOnlyViewProvenance.Unknown
            | Some { Kind = SemanticKind.Application _ } ->
                match flow.Calls.TryFind tupId with
                | Some { Complete = true; Unknown = false; Targets = targets } when not targets.IsEmpty ->
                    targets |> List.map (fun t -> computeTupleRead seen seenFields seenTuples index t.Body) |> joinNonEmpty
                | _ -> Resolved ReadOnlyViewProvenance.Unknown
            | _ -> Resolved ReadOnlyViewProvenance.Unknown
        tupleStores |> List.fold joinState tupVal
    and compute seen seenFields seenTuples id =
        if Set.contains id seen then Unset else
        let seen = Set.add id seen
        let joinAll items = items |> List.map (walk seen seenFields seenTuples) |> joinNonEmpty
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.VarRef(_, Some inner) }
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) }
        | Some { Kind = SemanticKind.EagerExpr inner }
        | Some { Kind = SemanticKind.DUEliminate(inner, _, _, _) }
        | Some { Kind = SemanticKind.EnvironmentRead(_, inner) }
        | Some { Kind = SemanticKind.DUConstruct(_, _, Some inner, _) } -> walk seen seenFields seenTuples inner
        | Some { Kind = SemanticKind.DUConstruct(_, _, None, _) } -> Unset
        | Some { Kind = SemanticKind.FieldGet(receiver, fieldName) } ->
            computeFieldRead seen seenFields seenTuples fieldName receiver
        | Some { Kind = SemanticKind.TupleGet(tupleId, index) } ->
            computeTupleRead seen seenFields seenTuples index tupleId
        | Some { Kind = SemanticKind.ArrayExpr elements } ->
            match elements with
            | [] -> Unset
            | _ -> elements |> List.map (walk seen seenFields seenTuples) |> List.fold joinState Unset
        | Some { Kind = SemanticKind.IndexGet(buffer, _) } ->
            let elemStores =
                [ for t in targetRoots Set.empty buffer do yield! dictLookup indexSetsByTarget t ]
                |> List.map (walk seen seenFields seenTuples)
            elemStores |> List.fold joinState (walk seen seenFields seenTuples buffer)
        | Some({ Kind = SemanticKind.Binding _ } as node) ->
            (node.Children @ dictLookup setsByTarget id) |> joinAll
        | Some { Kind = SemanticKind.Sequential items } ->
            match List.tryLast items with
            | Some lastId -> walk seen seenFields seenTuples lastId
            | None -> Resolved ReadOnlyViewProvenance.Unknown
        | Some { Kind = SemanticKind.IfThenElse(_, yes, Some no) } ->
            joinState (walk seen seenFields seenTuples yes) (walk seen seenFields seenTuples no)
        | Some { Kind = SemanticKind.IfThenElse(_, yes, None) } ->
            walk seen seenFields seenTuples yes
        | Some { Kind = SemanticKind.Match(_, cases) } ->
            cases |> List.map _.Body |> joinAll
        | Some { Kind = SemanticKind.CaseElimination(_, arms) } ->
            arms |> List.map _.Body |> joinAll
        | Some({ Kind = SemanticKind.PatternBinding _ } as node) ->
            match inputs id with
            | Some formal ->
                formal.Demanded |> List.map _.Actual |> joinAll
            | None ->
                let sourceDef = DirectCaptures.sourceDefinition graph id
                let captures = if sourceDef <> id then [sourceDef] else []
                let scrutinees = dictLookup patternScrutinees id
                let stores = dictLookup setsByTarget id
                (node.Children @ captures @ scrutinees @ stores) |> joinAll
        | Some { Kind = SemanticKind.Application(callee, _) } ->
            match intrinsicApplication graph id with
            | Some({ Module = IntrinsicModule.Array; FullName = "ReadOnlyView.ofString" }, _, _) ->
                Resolved ReadOnlyViewProvenance.ByteBacked
            | Some({ Module = IntrinsicModule.Array; FullName = "ReadOnlyView.ofArray" }, _, _) ->
                Resolved ReadOnlyViewProvenance.ArrayBacked
            | Some({ Module = IntrinsicModule.Array; FullName = "ReadOnlyView.slice" }, sourceId :: _, _) ->
                walk seen seenFields seenTuples sourceId
            | Some({ Module = IntrinsicModule.Array; Operation = "get" }, buffer :: _, _) ->
                let elemStores =
                    [ for t in targetRoots Set.empty buffer do yield! dictLookup indexSetsByTarget t ]
                    |> List.map (walk seen seenFields seenTuples)
                elemStores |> List.fold joinState (walk seen seenFields seenTuples buffer)
            | _ ->
                let isBorrowedExternal =
                    match Boundaries.target graph (rootCallee callee) with
                    | Some(binding, _) -> Set.contains binding.Id borrowedByteBindings
                    | None -> false
                if isBorrowedExternal then
                    Resolved ReadOnlyViewProvenance.ByteBacked
                else
                    match flow.Calls.TryFind id with
                    | Some { Complete = true; Unknown = false; Targets = targets } when not targets.IsEmpty ->
                        targets |> List.map _.Body |> joinAll
                    | _ -> Resolved ReadOnlyViewProvenance.Unknown
        | _ -> Resolved ReadOnlyViewProvenance.Unknown
    fun id ->
        match walk Set.empty Set.empty Set.empty id with
        | Unset -> ReadOnlyViewProvenance.Unknown
        | Resolved p -> p
