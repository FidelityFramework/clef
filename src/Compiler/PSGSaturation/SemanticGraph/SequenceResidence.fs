// SPDX-License-Identifier: MIT
/// Prove bounded residence for exact sequence allocation sites. Containment
/// comes from canonical structural incidence; value flow follows resolved
/// references. An unproved escape never selects a heap or static fallback.
module Clef.Compiler.PSGSaturation.SemanticGraph.SequenceResidence

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

[<RequireQualifiedAccess>]
type ResidualReason =
    | MissingActivation
    | AmbiguousActivation of NodeId list
    | DeferredActivation of NodeId
    | ReturnsFrom of NodeId
    | StoredAt of NodeId
    | UnsupportedConsumer of NodeId
    | CrossesActivation of NodeId
    | FactoryResult of NodeId
    | UnknownInputRegion of NodeId
    | RecursiveValueFlow of NodeId

type Unresolved = { Site: NodeId; Reason: ResidualReason }
type Reading = {
    Sites: Map<NodeId, EscapeKind>
    Regions: Map<NodeId, NodeId>
    Evidence: Hyperedge list
    Unresolved: Unresolved list
}

type private Use =
    | Alias of NodeId
    | Consumed of NodeId
    | Captured of owner: NodeId * generator: NodeId * declaration: NodeId
    | Refused of ResidualReason

let private analyzeCore allowGenerators environmentSites (graph: SemanticGraph) (destinations: Map<NodeId, NodeId>) (factoryCalls: Map<NodeId, NodeId>) : Reading =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let edges node =
        let derived = kindEdges node.Id node.Kind
        let contained = derived |> List.filter Hyperedge.isStructural |> List.collect _.Sources |> Set.ofList
        derived @ (node.Children |> List.filter (fun id -> not (contained.Contains id))
                   |> List.mapi (fun ordinal id -> Hyperedge.edge1 EdgeClass.Structural EdgeRole.Attached ordinal id node.Id))
    let incidence = nodes.Values |> Seq.collect edges |> Seq.toList
    let parents =
        incidence |> List.filter Hyperedge.isStructural
        |> List.collect (fun edge -> edge.Sources |> List.map (fun source -> source, edge.Target))
        |> List.groupBy fst |> Map.ofList |> Map.map (fun _ pairs -> pairs |> List.map snd |> List.distinct)
    let activation id =
        let rec walk seen pending found missing =
            match pending with
            | [] -> found, missing
            | current :: rest when Set.contains current seen -> walk seen rest found missing
            | current :: rest ->
                let seen = Set.add current seen
                match nodes.TryFind current with
                | Some { Kind = SemanticKind.Lambda _ } -> walk seen rest (Set.add current found) missing
                | Some { Kind = SemanticKind.ModuleDef _ } -> walk seen rest found true
                | _ ->
                    match parents.TryFind current with
                    | Some enclosing when not enclosing.IsEmpty -> walk seen (enclosing @ rest) found missing
                    | _ -> walk seen rest found true
        let found, missing = walk Set.empty [id] Set.empty false
        match Set.toList found with
        | [owner] when not missing ->
            match nodes[owner].Kind with
            | SemanticKind.Lambda(_, _, _, _, LambdaContext.SeqGenerator) when allowGenerators -> Ok owner
            | SemanticKind.Lambda(_, _, _, _, (LambdaContext.SeqGenerator | LambdaContext.LazyThunk)) ->
                Error (ResidualReason.DeferredActivation owner)
            | _ -> Ok owner
        | [] -> Error ResidualReason.MissingActivation
        | owners -> Error (ResidualReason.AmbiguousActivation owners)
    let rec intrinsic seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.Intrinsic info } -> Some info
        | Some { Kind = SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _) } -> intrinsic seen source
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> intrinsic seen value
        | _ -> None
    let getEnumerator node =
        match node.Kind with
        | SemanticKind.Application(callee, [input]) ->
            match intrinsic Set.empty callee with
            | Some { Module = IntrinsicModule.Seq; Operation = "getEnumerator" } -> Some input
            | _ -> None
        | _ -> None
    let sites = nodes |> Map.filter (fun _ node ->
        if environmentSites then match node.Kind with SemanticKind.EnvironmentCreate _ -> true | _ -> false
        else
            match node.Kind with
            | SemanticKind.SeqExpr _ -> not (destinations.ContainsKey node.Id)
            | SemanticKind.ContinuationAllocate _ -> true
            | _ -> getEnumerator node |> Option.isSome)
    let environmentArguments = ClosureEnvironments.callEnvironments graph
    let programActivations = lazy (ProgramActivation.analyze graph)
    let rec storageSource seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.ContinuationAllocate _ } -> Some id
        | Some { Kind = SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _) } -> storageSource seen source
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> storageSource seen value
        | _ -> None
    // A generator's repeated capture metadata describes the same constructor,
    // not a second owner. Missing/shared ownership never acquires a borrow.
    let generatorOwners =
        nodes |> Map.toList |> List.choose (fun (id, node) ->
            match node.Kind with SemanticKind.SeqExpr(generator, _) -> Some(generator, id) | _ -> None)
        |> List.groupBy fst |> Map.ofList |> Map.map (fun _ pairs -> pairs |> List.map snd)
    let sequenceOwner generator =
        match generatorOwners.TryFind generator, nodes.TryFind generator with
        | Some [owner], Some { Kind = SemanticKind.Lambda(_, _, _, _, LambdaContext.SeqGenerator) } -> Some owner
        | _ -> None
    let captures owner =
        match nodes.TryFind owner with Some { Kind = SemanticKind.SeqExpr(_, captures) } -> captures | _ -> []
    let borrowable (capture: CaptureInfo) =
        not capture.IsMutable &&
        (match applySubst capture.Type with
         | NativeType.TSeq _ -> true
         | NativeType.TFun _ when environmentSites -> capture.SourceNodeId |> Option.bind (ClosureEnvironments.tryKnown graph) |> Option.isSome
         | _ -> false)
    let rec sourceAllocations seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.SeqExpr _ | SemanticKind.ContinuationAllocate _ | SemanticKind.EnvironmentCreate _ } -> Some (Set.singleton id)
        | Some { Kind = SemanticKind.ClosureValue(_, environment) | SemanticKind.EnvironmentReference environment } -> sourceAllocations seen environment
        | Some { Kind = SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _) } -> sourceAllocations seen source
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> sourceAllocations seen value
        | Some { Kind = SemanticKind.Sequential values } -> List.tryLast values |> Option.bind (sourceAllocations seen)
        | Some { Kind = SemanticKind.IfThenElse(_, yes, Some no) } ->
            Option.map2 Set.union (sourceAllocations seen yes) (sourceAllocations seen no)
        | Some { Kind = SemanticKind.Application _ } -> factoryCalls.TryFind id |> Option.bind (sourceAllocations seen)
        | _ -> None
    let mutable uses: Map<NodeId, Use list> = Map.empty
    let useValue source usage = uses <- uses.Add(source, usage :: (uses.TryFind source |> Option.defaultValue []))
    for node in nodes.Values do
        let structural = edges node |> List.filter Hyperedge.isStructural
        for edge in structural do
            for source in edge.Sources do
                let usage =
                    match node.Kind, edge.Role with
                    | SemanticKind.Binding(_, false, _, _), _ -> Alias node.Id
                    | SemanticKind.Binding _, _ -> Refused (ResidualReason.StoredAt node.Id)
                    | SemanticKind.TypeAnnotation _, _ -> Alias node.Id
                    | SemanticKind.ClosureValue(_, environment), _ when source = environment -> Alias node.Id
                    | SemanticKind.EnvironmentReference _, _ -> Alias node.Id
                    | SemanticKind.Sequential values, _ ->
                        if List.tryLast values = Some source then Alias node.Id else Consumed node.Id
                    | SemanticKind.IfThenElse _, (EdgeRole.ThenBranch | EdgeRole.ElseBranch)
                    | SemanticKind.Match _, EdgeRole.CaseBody
                    | SemanticKind.CaseElimination _, EdgeRole.CaseBody
                    | SemanticKind.TryWith _, (EdgeRole.Body | EdgeRole.Handler)
                    | SemanticKind.TryFinally _, EdgeRole.Body -> Alias node.Id
                    | SemanticKind.TryFinally _, EdgeRole.Cleanup -> Consumed node.Id
                    | SemanticKind.Lambda _, EdgeRole.Body -> Refused (ResidualReason.ReturnsFrom node.Id)
                    | SemanticKind.Application _, EdgeRole.Argument
                        when edge.Ordinal = 0 && factoryCalls.TryFind node.Id = storageSource Set.empty source
                             && factoryCalls.ContainsKey node.Id -> Alias node.Id
                    | SemanticKind.Application(callee, _), EdgeRole.Argument ->
                        match intrinsic Set.empty callee, edge.Ordinal with
                        | _, ordinal when environmentArguments.TryFind node.Id = Some(ordinal, source) -> Consumed node.Id
                        | Some { Module = IntrinsicModule.Seq; Operation = "getEnumerator" }, 0 -> Alias node.Id
                        | Some { Module = IntrinsicModule.SeqEnumerator; Operation = ("moveNext" | "current") }, 0
                        | Some { Module = IntrinsicModule.Operators; Operation = "ignore" }, _ -> Consumed node.Id
                        | _ -> Refused (ResidualReason.UnsupportedConsumer node.Id)
                    | SemanticKind.RecordExpr _, _ | SemanticKind.TupleExpr _, _ | SemanticKind.ArrayExpr _, _
                    | SemanticKind.ListExpr _, _ | SemanticKind.DUConstruct _, _ | SemanticKind.UnionCase _, _
                    | SemanticKind.Set _, _ | SemanticKind.FieldSet _, _ | SemanticKind.IndexSet _, _
                    | SemanticKind.FrameWrite _, _ -> Refused (ResidualReason.StoredAt node.Id)
                    | _ -> Refused (ResidualReason.UnsupportedConsumer node.Id)
                useValue source usage
        match node.Kind with
        | SemanticKind.EnvironmentCreate(_, initializers) ->
            // Capturing a separately allocated sequence or callable requires
            // its own retained-view residence contract; ordinary scalar/cell
            // captures are checked against this environment's covering scope.
            for _, source in initializers do
                useValue source (Refused (ResidualReason.StoredAt node.Id))
        | SemanticKind.VarRef(_, Some source) -> useValue source (Alias node.Id)
        | SemanticKind.SeqExpr(generator, captured) ->
            for capture in captured do
                capture.SourceNodeId |> Option.iter (fun source ->
                    let usage =
                        if allowGenerators && borrowable capture && sequenceOwner generator = Some node.Id then
                            Captured(node.Id, generator, source)
                        else Refused (ResidualReason.StoredAt node.Id)
                    useValue source usage)
        | SemanticKind.Lambda(_, _, captured, _, LambdaContext.SeqGenerator) ->
            for capture in captured do
                capture.SourceNodeId |> Option.iter (fun source ->
                    let duplicate = sequenceOwner node.Id |> Option.exists (fun owner ->
                        captures owner |> List.exists (fun original ->
                            original.SourceNodeId = Some source && original.IsMutable = capture.IsMutable))
                    if not duplicate then useValue source (Refused (ResidualReason.StoredAt node.Id)))
        | SemanticKind.Lambda(_, _, captured, _, _) | SemanticKind.LazyExpr(_, captured) ->
            for capture in captured do
                capture.SourceNodeId |> Option.iter (fun source -> useValue source (Refused (ResidualReason.StoredAt node.Id)))
        | _ -> ()
    let combine left right = left |> Result.bind (fun first -> right () |> Result.map (fun second -> first @ second))
    if environmentSites then
        // Independent reference incidence is not erased by structural recipes.
        // Unknown consumers prevent a complete-use environment residence proof.
        for edge in graph.Edges do
            if edge.Class = EdgeClass.Reference then
                match nodes.TryFind edge.Target with
                | Some { Kind = SemanticKind.VarRef(_, Some source) }
                    when edge.Sources = [source] -> ()
                | Some { Kind = SemanticKind.EnvironmentCreate(_, initializers) }
                    when edge.Role = EdgeRole.EnvironmentInitializer &&
                         (List.tryItem edge.Ordinal initializers |> Option.exists (fun (_, value) -> edge.Sources = [value])) -> ()
                | Some { Kind = SemanticKind.ModuleDef(_, members) }
                    when edge.Role = EdgeRole.Member &&
                         (List.tryItem edge.Ordinal members |> Option.exists (fun source -> edge.Sources = [source])) -> ()
                | Some _ ->
                    for source in edge.Sources do useValue source (Refused(ResidualReason.UnsupportedConsumer edge.Target))
                | None -> ()
    // Coverage follows complete value use, not lexical nesting. Each crossed
    // deferred activation must have exactly one constructor whose own complete
    // use is bounded in an already covered activation.
    let rec activationCovered covering proving actual =
        if actual = covering then Ok []
        elif ProgramActivation.coverage programActivations.Value covering actual |> Option.isSome then
            let coverage = ProgramActivation.coverage programActivations.Value covering actual |> Option.get
            if Set.contains actual proving then Error (ResidualReason.RecursiveValueFlow actual)
            else
                coverage.Dependencies |> List.fold (fun proof dependency ->
                    combine proof (fun () -> activationCovered covering (Set.add actual proving) dependency)) (Ok coverage.Evidence)
        elif not allowGenerators then Error (ResidualReason.CrossesActivation actual)
        else
            match sequenceOwner actual with
            | Some constructor when not (Set.contains constructor proving) ->
                activation constructor |> Result.bind (fun enclosing ->
                    combine (activationCovered covering (Set.add constructor proving) enclosing) (fun () ->
                        bounded constructor enclosing (Set.add constructor proving) Set.empty constructor))
            | _ -> Error (ResidualReason.CrossesActivation actual)
    and borrow allocation covering proving constructor generator declaration =
        let selected = captures constructor |> List.exists (fun capture ->
            capture.SourceNodeId = Some declaration && borrowable capture)
        let knownSource = sourceAllocations Set.empty declaration |> Option.exists (Set.contains allocation)
        if not selected || not knownSource || sequenceOwner generator <> Some constructor then
            Error (ResidualReason.UnknownInputRegion declaration)
        elif Set.contains constructor proving then Error (ResidualReason.RecursiveValueFlow constructor)
        else
            activation constructor |> Result.bind (fun enclosing ->
                let proving = Set.add constructor proving
                combine (activationCovered covering proving enclosing) (fun () ->
                    bounded constructor enclosing proving Set.empty constructor)
                |> Result.map (fun evidence ->
                    { Class = EdgeClass.Provenance; Role = EdgeRole.SequenceTemplateBorrow
                      Sources = [allocation; covering; declaration; generator]; Target = constructor; Ordinal = 0 } :: evidence))
    and scopeUse allocation covering proving id =
        activation id |> Result.bind (fun actual ->
            if actual = covering then Ok []
            elif ProgramActivation.coverage programActivations.Value covering actual |> Option.isSome then
                activationCovered covering proving actual
            elif not allowGenerators then Error (ResidualReason.CrossesActivation id)
            else
                match sequenceOwner actual with
                | Some constructor ->
                    let declarations =
                        captures constructor
                        |> List.choose (fun capture ->
                            match capture.SourceNodeId with
                            | Some declaration when borrowable capture && (sourceAllocations Set.empty declaration |> Option.exists (Set.contains allocation)) -> Some declaration
                            | _ -> None)
                        |> List.distinct
                    match declarations with
                    | [] -> Error (ResidualReason.CrossesActivation id)
                    | _ -> declarations |> List.fold (fun result declaration ->
                        combine result (fun () -> borrow allocation covering proving constructor actual declaration)) (Ok [])
                | None -> Error (ResidualReason.CrossesActivation id))
    and bounded allocation covering proving seen id =
        if Set.contains id seen then Error (ResidualReason.RecursiveValueFlow id) else
        let seen = Set.add id seen
        uses.TryFind id |> Option.defaultValue []
        |> List.fold (fun result usage -> combine result (fun () ->
            match usage with
            | Refused reason -> Error reason
            | Captured(constructor, generator, declaration) -> borrow allocation covering proving constructor generator declaration
            | Consumed consumer -> scopeUse allocation covering proving consumer
            | Alias other -> combine (scopeUse allocation covering proving other) (fun () -> bounded allocation covering proving seen other))) (Ok [])
    // The iterator's input must have a source allocation, with complete bounded
    // use and an exact capture relation when it crosses a generator boundary.
    // Factory/opaque inputs retain their residual unless preparation supplied
    // the exact caller-owned allocation identity.
    let rec inputRegion owner useSite seen id =
        if Set.contains id seen then Error (ResidualReason.RecursiveValueFlow id) else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.SeqExpr _ | SemanticKind.ContinuationAllocate _ } ->
            activation id |> Result.bind (fun sourceActivation ->
                if sourceActivation = owner then Ok []
                else combine (scopeUse id sourceActivation (Set.singleton id) useSite) (fun () ->
                    bounded id sourceActivation (Set.singleton id) Set.empty id))
        | Some { Kind = SemanticKind.VarRef(_, Some source) | SemanticKind.TypeAnnotation(source, _) } -> inputRegion owner useSite seen source
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> inputRegion owner useSite seen value
        | Some { Kind = SemanticKind.Sequential values } ->
            match List.tryLast values with Some last -> inputRegion owner useSite seen last | None -> Error (ResidualReason.UnknownInputRegion id)
        | Some { Kind = SemanticKind.IfThenElse(_, yes, Some no) } ->
            combine (inputRegion owner useSite seen yes) (fun () -> inputRegion owner useSite seen no)
        | Some { Kind = SemanticKind.Application _ } ->
            match factoryCalls.TryFind id with
            | Some allocation -> inputRegion owner useSite seen allocation
            | None -> Error (ResidualReason.FactoryResult id)
        | _ -> Error (ResidualReason.UnknownInputRegion id)
    sites |> Map.fold (fun result id node ->
        let proof = activation id |> Result.bind (fun owner ->
            let capturedCells =
                match node.Kind with
                | SemanticKind.EnvironmentCreate(layout, _) ->
                    ClosureEnvironments.captures graph layout |> List.filter _.IsMutable
                    |> List.fold (fun proof capture ->
                        combine proof (fun () ->
                            activation capture.SourceNodeId.Value |> Result.bind (fun cellOwner ->
                                activationCovered cellOwner (Set.singleton id) owner))) (Ok [])
                | _ -> Ok []
            combine (combine capturedCells (fun () ->
                        match getEnumerator node with Some input -> inputRegion owner id Set.empty input | None -> Ok []))
                (fun () -> bounded id owner (Set.singleton id) Set.empty id)
            |> Result.map (fun evidence -> owner, evidence))
        match proof with
        | Ok(owner, evidence) ->
            let evidence =
                match node.Kind with
                | SemanticKind.EnvironmentCreate(layout, initializers) ->
                    let values = nodes |> Map.toList |> List.choose (fun (value, _) ->
                        if sourceAllocations Set.empty value |> Option.exists (Set.contains id) then Some value else None)
                    { Sources = List.distinct (id :: owner :: (initializers |> List.collect (fun (slot, value) -> [slot; value])) @ values)
                      Target = layout; Class = EdgeClass.Provenance; Role = EdgeRole.EnvironmentResidence; Ordinal = 0 } :: evidence
                | _ -> evidence
            let result = { result with Evidence = evidence @ result.Evidence }
            match nodes[owner].Kind with
            | SemanticKind.Lambda(_, _, _, _, LambdaContext.SeqGenerator) -> { result with Regions = result.Regions.Add(id, owner) }
            | _ -> { result with Sites = result.Sites.Add(id, EscapeKind.StackScoped) }
        | Error reason -> { result with Unresolved = { Site = id; Reason = reason } :: result.Unresolved })
        { Sites = Map.empty; Regions = Map.empty; Evidence = []; Unresolved = [] }
    |> fun result ->
        { result with
            Unresolved = List.rev result.Unresolved
            Evidence = result.Evidence |> List.distinctBy (fun edge -> edge.Class, edge.Role, edge.Sources, edge.Target, edge.Ordinal) }

/// Scope-only form retains the original conservative admission boundary.
let analyze graph = analyzeCore false false graph Map.empty Map.empty

/// Destination-backed constructors do not allocate in the factory activation.
let analyzePrepared graph destinations factoryCalls = analyzeCore false false graph destinations factoryCalls

/// Generator-local values whose complete use stays within that generator can
/// be assigned subregions of its frame. This returns a requirement, not a
/// selected offset or permission to use activation-local stack storage.
let analyzeWithRegions graph destinations factoryCalls = analyzeCore true false graph destinations factoryCalls

/// The same complete-use covering proof for known callable environments.
/// Generator-local results are requirements for owned regions, not permission
/// to allocate backing storage in a single MoveNext activation.
let analyzeEnvironments graph = analyzeCore true true graph Map.empty Map.empty
