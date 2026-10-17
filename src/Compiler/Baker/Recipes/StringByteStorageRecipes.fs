// SPDX-License-Identifier: MIT
/// Closed array storage families at a byte-unit string boundary. Logical array
/// element types stay unchanged. Neither global element ranges nor source names
/// supply the representation proof.
module Clef.Compiler.Baker.Recipes.StringByteStorageRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.NativeTypedTree.Expressions.Intrinsics
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.Baker.Ingredients.Obligations
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Recipes.Decomposition
module C = Clef.Compiler.Baker.Ingredients.Continuations
module PlatformResolution = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

type Plan = { Site: SemanticNode; Input: NodeId; Origin: NodeId; Members: NodeId list; Premises: NodeId list; Range: ValueRange; Representation: string; Text: EdgeRole option; Checked: bool }

/// Applied source evidence only. Physical reference/count/result adapters remain
/// separate requirements; a declared foreign byte ingress does not establish text.
type WritableApplication = {
    Site: NodeId; Callee: NodeId; Arguments: NodeId list
    Declaration: PlatformResolution.DeclaredWritableBuffer
    Buffer: NodeId; Count: NodeId; Allocation: NodeId; Capacity: NodeId
    CountRange: ValueRange; CapacityRange: ValueRange; StorageRange: ValueRange
    Representation: string; Participants: NodeId list
}
type WritableFailure = {
    Declaration: PlatformResolution.DeclaredWritableBuffer
    Participants: NodeId list
    Reason: string
    CountCoverage: ObligationBody option
}

type private CheckedBuilder() =
    member _.Bind(value, next) = Result.bind next value
    member _.Return(value) = Ok value
let private checked' = CheckedBuilder()
let private needed reason = function Some value -> Ok value | None -> Result.Error reason

let private byteRepresentation = Clef.Compiler.Baker.Ingredients.StringBytes.byteRepresentation

let private arrayElement (node: SemanticNode) =
    match applySubst node.Type with
    | NativeType.TApp(tc, [elem]) when tc.NTUKind = Some NTUKind.NTUarray && Types.isIntegerType elem -> Some elem
    | _ -> None

let private diagnostic (site: SemanticNode) related reason : Diagnostic =
    { Severity = NativeDiagnosticSeverity.Error; Code = "CCS8404"
      Message = "String.fromBytes requires proved byte storage: " + reason
      Range = site.Range; RelatedNodes = List.distinct(site.Id :: related)
      Reachability = ReachabilityContext.Reachable }

let private analyze renew (graph: SemanticGraph) =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
    let sourceFacts = lazy (
        // These are the conclusions being renewed. They cannot seed the
        // independent source rules through an enclosing binding or operation.
        let edges = graph.Edges |> List.filter (fun edge ->
            match edge.Role with EdgeRole.StringByteRange _ -> false | _ -> true)
        let sourceGraph = { graph with Edges = edges }
        Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis.sourceFacts sourceGraph)
    let rec application seen id args =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.Application(fn, supplied) } -> application seen fn (supplied @ args)
        | Some { Kind = SemanticKind.Intrinsic info } -> Some(info, args)
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> application seen inner args
        | _ -> None
    let calls =
        nodes |> Map.toList |> List.choose (fun (id, node) ->
            match node.Kind with SemanticKind.Application _ -> application Set.empty id [] |> Option.map (fun call -> id, call) | _ -> None)
        |> Map.ofList
    let rec origin seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match nodes.TryFind id with
        | Some node when arrayElement node |> Option.isSome ->
            match node.Kind with
            | SemanticKind.ArrayExpr _ | SemanticKind.ArrayAllocate _ -> Some id
            | SemanticKind.VarRef(_, Some definition) -> origin seen definition
            | SemanticKind.Binding(_, false, _, _) when node.Children.Length = 1 -> origin seen node.Children.Head
            | SemanticKind.TypeAnnotation(inner, _) -> origin seen inner
            | SemanticKind.Sequential values -> List.tryLast values |> Option.bind (origin seen)
            | SemanticKind.Application _ ->
                match calls.TryFind id with
                | Some({ Module = IntrinsicModule.Array; Operation = "zeroCreate" }, [_])
                | Some({ Module = IntrinsicModule.Array; Operation = "create" }, [_; _]) -> Some id
                | Some({ Module = IntrinsicModule.Array; Operation = "sub" }, [input; _; _]) -> origin seen input
                | _ -> None
            | _ -> None
        | _ -> None
    let origins = nodes |> Map.toList |> List.choose (fun (id, _) -> origin Set.empty id |> Option.map (fun root -> id, root)) |> Map.ofList
    let families = origins |> Map.toList |> List.groupBy snd |> List.map (fun (root, entries) -> root, List.map fst entries) |> Map.ofList
    let members root = families[root]
    let roots = origins.Values |> Set.ofSeq
    let descriptors = PlatformResolution.readDescriptors graph
    let mutable blocked = Set.empty
    let initialization =
        roots |> Seq.map (fun root ->
            match nodes[root].Kind with
            | SemanticKind.ArrayAllocate _ ->
                match Clef.Compiler.Baker.Ingredients.ArrayInitialization.tryInitialization graph root with
                | Result.Ok support -> root, support
                | Result.Error _ -> blocked <- Set.add root blocked; root, []
            | _ -> root, []) |> Map.ofSeq
    let block id = origins.TryFind id |> Option.iter (fun root -> blocked <- Set.add root blocked)
    let representation = byteRepresentation graph
    let writable = nodes.Values |> Seq.choose(fun site ->
        match site.Kind with
        | SemanticKind.Application(callee, arguments) ->
            match BoundaryDeclarations.target graph callee with
            | Some(binding, path) when BoundaryDeclarations.isExternal binding ->
                match descriptors.WritableBuffers |> List.filter(fun row -> row.Declaration.Binding=binding.Id) with
                | [declaration] ->
                    let observed = checked' {
                        do! if descriptors.Findings.IsEmpty then Ok() else Result.Error "The writable descriptor census has unresolved findings."
                        do! if arguments.Length=declaration.Declaration.Formals.Length then Ok() else Result.Error "A writable application requires its complete ordered actual vector."
                        let! buffer=List.tryItem declaration.Parameter arguments |> needed "The writable buffer actual is absent."
                        let! count=List.tryItem declaration.CountParameter arguments |> needed "The writable count actual is absent."
                        let! allocation=origins.TryFind buffer |> needed "The writable buffer requires an exact local zeroCreate allocation and immutable aliases."
                        let! capacity =
                            match calls.TryFind allocation, nodes[allocation].Kind with
                            | Some({Module=IntrinsicModule.Array;Operation="zeroCreate"},[capacity]), _ -> Ok capacity
                            | _, SemanticKind.ArrayAllocate _ ->
                                match Clef.Compiler.Baker.Ingredients.ArrayInitialization.tryInitialization graph allocation with
                                | Ok _ -> graph.Edges |> List.choose(fun edge ->
                                    match edge.Role with
                                    | EdgeRole.ArrayAllocationConstruction construction when construction.Site=allocation -> Some construction.Count.Actual
                                    | _ -> None) |> List.tryExactlyOne |> needed "The writable allocation lost its original zeroCreate count."
                                | Result.Error reason -> Result.Error reason
                            | _ -> Result.Error "The first writable profile requires validated zeroCreate byte storage."
                        let! rep,format=representation |> needed "The writable allocation requires an explicit unsigned-8 storage format."
                        let range id=sourceFacts.Value.TryFind id |> Option.defaultValue ValueRange.Unbounded
                        let countRange,capacityRange=range count,range capacity
                        do! match countRange,capacityRange with
                            | ValueRange.Bounded(lo,hi),ValueRange.Bounded(capacityLo,capacityHi) when lo<=hi && capacityLo<=capacityHi -> Ok()
                            | _ -> Result.Error "The writable count domain must be finite, nonnegative and contained in the actual allocation's byte-slot capacity domain."
                        return {Site=site.Id;Callee=callee;Arguments=arguments;Declaration=declaration;Buffer=buffer;Count=count
                                Allocation=allocation;Capacity=capacity;CountRange=countRange;CapacityRange=capacityRange
                                StorageRange=ValueRange.Unbounded;Representation=rep.Name
                                Participants=List.distinct(site.Id::callee::buffer::count::allocation::capacity::format::(Set.toList path)@arguments@declaration.Participants@initialization[allocation])} }
                    let observed =
                        observed |> Result.mapError(fun reason ->
                            {Declaration=declaration;Participants=List.distinct(site.Id::callee::arguments@(Set.toList path)@declaration.Participants);Reason=reason;CountCoverage=None})
                        |> Result.bind(fun application ->
                            match application.CountRange,application.CapacityRange with
                            | ValueRange.Bounded(lo,hi),ValueRange.Bounded(capacityLo,_) when lo<0I || hi>capacityLo ->
                                Result.Error {Declaration=declaration;Participants=application.Participants
                                              Reason="The finite writable count domain is not covered by the actual allocation's byte-slot capacity."
                                              CountCoverage=Some(ObligationBody.IntegerRepresentationCoverage(lo,hi,0I,capacityLo))}
                            | _ -> Ok application)
                    Some(site.Id, observed)
                | _ -> None
            | _ -> None
        | _ -> None) |> Map.ofSeq
    // Every use must be covered, including references that do not occur in
    // Children. A known body is not permission to pass storage through its ABI.
    for node in nodes.Values do
        match node.Kind with
        | SemanticKind.Application(_, directArgs) ->
            match calls.TryFind node.Id with
            | Some(info, args) ->
                let allowed =
                    match info.Module, info.Operation, args.Length with
                    | IntrinsicModule.Array, ("get" | "set" | "length" | "sub"), _ -> true
                    | IntrinsicModule.String, ("fromBytes" | "tryFromBytes" | "validateUtf8" | "retireSnapshot"), 1 -> true
                    | _ -> false
                args |> List.iteri (fun index arg -> if not allowed || index <> 0 then block arg)
            | None ->
                match writable.TryFind node.Id with
                | Some(Ok application) -> directArgs |> List.iteri(fun ordinal actual -> if ordinal<>application.Declaration.Parameter then block actual)
                | _ -> directArgs |> List.iter block
        | SemanticKind.Binding(_, false, _, _) | SemanticKind.VarRef _ | SemanticKind.TypeAnnotation _ | SemanticKind.Sequential _ -> ()
        | SemanticKind.IndexGet _ | SemanticKind.IndexSet _ -> ()
        // Length observes the extent of this current native-array family; it
        // neither writes its storage nor passes it through another call's ABI.
        | SemanticKind.FieldGet(input, "Length")
            when origins.ContainsKey input &&
                 (nodes.TryFind input |> Option.bind arrayElement |> Option.isSome) &&
                 Types.isIntegerType (applySubst node.Type) -> ()
        | SemanticKind.Lambda(_, body, captures, _, _) ->
            block body
            captures |> List.iter (fun capture -> capture.SourceNodeId |> Option.iter block)
        | SemanticKind.LazyExpr(_, captures) | SemanticKind.SeqExpr(_, captures) ->
            captures |> List.iter (fun capture -> capture.SourceNodeId |> Option.iter block)
        | _ -> node.Children |> List.iter block
    let stores =
        nodes.Values |> Seq.collect (fun node ->
            match node.Kind with
            | SemanticKind.ArrayExpr values when roots.Contains node.Id -> values |> List.map (fun value -> node.Id, (node.Id, value)) |> Seq.ofList
            | SemanticKind.IndexSet(input, _, value) -> origins.TryFind input |> Option.map (fun root -> root, (node.Id, value)) |> Option.toList |> Seq.ofList
            | _ ->
                match calls.TryFind node.Id with
                | Some({ Module = IntrinsicModule.Array; Operation = "set" }, [input; _; value]) -> origins.TryFind input |> Option.map (fun root -> root, (node.Id, value)) |> Option.toList |> Seq.ofList
                | Some({ Module = IntrinsicModule.Array; Operation = "create" }, [_; value]) when roots.Contains node.Id -> Seq.singleton(node.Id, (node.Id, value))
                | _ -> Seq.empty)
        |> Seq.groupBy fst |> Seq.map (fun (root, writes) -> root, writes |> Seq.map snd |> Seq.toList) |> Map.ofSeq
    let stores = roots |> Seq.map (fun root -> root, stores.TryFind root |> Option.defaultValue []) |> Map.ofSeq
    let seeded root =
        let initial =
            match calls.TryFind root with
            | Some({ Module = IntrinsicModule.Array; Operation = "zeroCreate" }, [_]) -> ValueRange.point 0I
            | _ -> ValueRange.Empty
        writable.Values |> Seq.fold(fun range application ->
            match application with
            | Ok application when application.Allocation=root -> ValueRange.join range (ValueRange.bounded 0I 255I)
            | _ -> range) initial
    let readInput id =
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.IndexGet(input, _) } -> Some input
        | _ ->
            match calls.TryFind id with
            | Some({ Module = IntrinsicModule.Array; Operation = "get" }, [input; _]) -> Some input
            | _ -> None
    let rec value (ranges: Map<NodeId, ValueRange>) seen id =
        if Set.contains id seen then ValueRange.Unbounded else
        let seen = Set.add id seen
        let recurse = value ranges seen
        match nodes.TryFind id with
        | None -> ValueRange.Unbounded
        | Some node ->
            let existing =
                (if renew then sourceFacts.Value.TryFind id else node.ValueRange)
                |> Option.defaultValue ValueRange.Unbounded
            match readInput id |> Option.bind (fun input -> origins.TryFind input) with
            | Some root -> ranges.TryFind root |> Option.defaultValue ValueRange.Unbounded
            | None ->
                let inferred =
                    match node.Kind with
                    | SemanticKind.Literal(NativeLiteral.Int(actual, _)) -> ValueRange.point (bigint actual)
                    | SemanticKind.Literal(NativeLiteral.UInt(actual, _)) -> ValueRange.point (bigint actual)
                    | SemanticKind.Binding(_, false, _, _) when node.Children.Length = 1 -> recurse node.Children.Head
                    | SemanticKind.VarRef(_, Some definition) ->
                        match nodes.TryFind definition with
                        | Some { Kind = SemanticKind.Binding(_, false, _, _) } -> recurse definition
                        | _ -> existing
                    | SemanticKind.TypeAnnotation(inner, _) -> recurse inner
                    | SemanticKind.Sequential values -> List.tryLast values |> Option.map recurse |> Option.defaultValue ValueRange.Unbounded
                    | SemanticKind.IfThenElse(_, yes, no) -> ValueRange.join (recurse yes) (no |> Option.map recurse |> Option.defaultValue ValueRange.Empty)
                    | SemanticKind.Application _ ->
                        match calls.TryFind id with
                        | Some(info, args) ->
                            let arguments = args |> List.map (fun arg ->
                                let source = nodes[arg]
                                ({ Range = recurse arg; Type = source.Type
                                   Literal = match source.Kind with SemanticKind.Literal literal -> Some literal | _ -> None } : RangeSources.Argument))
                            match RangeSources.intrinsic graph.Platform info arguments with RangeSources.Result.Fact range -> range | _ -> ValueRange.Unbounded
                        | _ -> ValueRange.Unbounded
                    | _ -> existing
                // During renewal the independent source rules are recomputed,
                // including branch refinements. No cached parent can narrow a
                // changed child; a current guard can still prove a clamp.
                ValueRange.meet existing inferred
    let mutable ranges = roots |> Seq.map (fun root -> root, seeded root) |> Map.ofSeq
    let mutable stable = false
    let mutable rounds = 0
    while not stable && rounds <= roots.Count + nodes.Count do
        let next = ranges |> Map.map (fun root previous ->
            if blocked.Contains root then ValueRange.Unbounded else
            stores[root] |> List.fold (fun range (_, stored) -> ValueRange.join range (value ranges Set.empty stored)) (ValueRange.join previous (seeded root)))
        stable <- next = ranges
        ranges <- next
        rounds <- rounds + 1
    if not stable then ranges <- ranges |> Map.map (fun _ _ -> ValueRange.Unbounded)
    let writable = writable |> Map.map(fun _ observed -> observed |> Result.bind(fun application ->
        let range=ranges[application.Allocation]
        if ValueRange.contains (ValueRange.bounded 0I 255I) range && ValueRange.isObservable range then
            Ok {application with StorageRange=range}
        else Result.Error {Declaration=application.Declaration;Participants=application.Participants;
                    Reason="The writable allocation's complete local write family is not established within 0..255; narrowing cannot be replaced by masking.";CountCoverage=None}) )
    let rec constantBytes seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        let recurse = constantBytes seen
        match nodes.TryFind id with
        | Some { Kind = SemanticKind.ArrayExpr values } when stores[id] |> List.forall (fun (writer, _) -> writer = id) ->
            let bytes = values |> List.map (fun valueId ->
                match value ranges Set.empty valueId with
                | ValueRange.Bounded(lo, hi) when lo = hi && lo >= 0I && hi <= 255I -> Some(byte lo)
                | _ -> None)
            if bytes |> List.forall Option.isSome then Some(bytes |> List.choose (fun item -> item)) else None
        | Some { Kind = SemanticKind.VarRef(_, Some definition) } -> recurse definition
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [inner] }
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> recurse inner
        | Some { Kind = SemanticKind.Sequential values } -> List.tryLast values |> Option.bind recurse
        | Some _ ->
            match calls.TryFind id with
            | Some({ Module = IntrinsicModule.Array; Operation = "sub" }, [input; offset; length]) ->
                match recurse input, value ranges Set.empty offset, value ranges Set.empty length with
                | Some bytes, ValueRange.Bounded(lo, hi), ValueRange.Bounded(n, m)
                    when lo = hi && n = m && lo >= 0I && n >= 0I && lo + n <= bigint bytes.Length ->
                    Some(bytes |> List.skip (int lo) |> List.take (int n))
                | _ -> None
            | _ -> None
        | None -> None
    let validText input range =
        if ValueRange.contains (ValueRange.bounded 0I 127I) range then Some EdgeRole.StringAscii else
        match constantBytes Set.empty input with
        | None -> None
        | Some bytes ->
            try
                System.Text.UTF8Encoding(false, true).GetString(List.toArray bytes) |> ignore
                Some(EdgeRole.StringUtf8Constant bytes)
            with :? System.Text.DecoderFallbackException -> None
    // A temporary-buffer read depends on that buffer's complete write set,
    // even when only the final output buffer changes physical representation.
    let collectPremises root =
        let rec visitRoots seen pending accumulated =
            match pending with
            | [] -> List.distinct accumulated
            | current :: rest when Set.contains current seen -> visitRoots seen rest accumulated
            | current :: rest ->
                let writes = stores[current]
                let rec values seen pending dependencies nodesRead =
                    match pending with
                    | [] -> dependencies, nodesRead
                    | item :: tail when Set.contains item seen -> values seen tail dependencies nodesRead
                    | item :: tail ->
                        let seen = Set.add item seen
                        match nodes.TryFind item with
                        | None -> values seen tail dependencies nodesRead
                        | Some node ->
                            let dependency = readInput item |> Option.bind (fun input -> origins.TryFind input)
                            let more = match node.Kind with SemanticKind.VarRef(_, Some definition) -> definition :: node.Children | _ -> node.Children
                            values seen (more @ tail) (Option.toList dependency @ dependencies) (item :: nodesRead)
                let scalarInputs =
                    writable.Values
                    |> Seq.choose(function
                        | Ok application when application.Allocation=current -> Some [application.Count;application.Capacity]
                        | _ -> None)
                    |> Seq.toList |> List.concat
                let dependencies, valuesRead = values Set.empty ((writes |> List.map snd)@scalarInputs) [] []
                visitRoots (Set.add current seen) (dependencies @ rest)
                    (current :: members current @ initialization[current] @ (writes |> List.collect (fun (writer, stored) -> [writer; stored])) @
                     (writable.Values |> Seq.choose(function Ok application when application.Allocation=current -> Some application.Participants | _ -> None) |> Seq.toList |> List.concat) @ valuesRead @ accumulated)
        visitRoots Set.empty [root] []
    // Several reads can share one owning family. Compute its dependency closure
    // once in this analysis; no persistent temporal schema is introduced here.
    let premiseCache = System.Collections.Generic.Dictionary<NodeId, NodeId list>()
    let premises root =
        match premiseCache.TryGetValue root with
        | true, support -> support
        | _ -> let support = collectPremises root in premiseCache.Add(root, support); support
    let writable = writable |> Map.map(fun _ observed -> observed |> Result.map(fun application ->
        {application with Participants=List.distinct(application.Participants@premises application.Allocation)}))
    let sites =
        nodes.Values |> Seq.choose (fun node ->
            match calls.TryFind node.Id with
            | Some({ Module = IntrinsicModule.String; Operation = ("fromBytes" | "tryFromBytes") }, [input])
                when not (graph.Edges |> List.exists (fun edge ->
                    edge.Role = EdgeRole.StringByteSnapshot && (match edge.Sources with [_; copy] -> copy = input | _ -> false))) -> Some(node, input)
            | _ -> None)
        |> Seq.toList
    nodes, origins, members, blocked, ranges, representation, validText, premises, sites, readInput, writable

let writableApplications graph =
    let _,_,_,_,_,_,_,_,_,_,applications=analyze true graph
    applications

let recognize (graph: SemanticGraph) : Plan list * Enrichment * Diagnostic list =
    let nodes, origins, members, blocked, ranges, representation, validText, premises, sites, readInput, writable = analyze false graph
    let plans, diagnostics = sites |> List.fold (fun (plans, diagnostics) (site, input) ->
        let checkedText =
            match site.Kind with
            | SemanticKind.Application(fn, _) ->
                match nodes.TryFind fn with
                | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.String; Operation = "tryFromBytes" } } -> true
                | _ -> false
            | _ -> false
        match origins.TryFind input, representation with
        | Some root, Some(rep, declaration) when not (blocked.Contains root) ->
            let range = match ranges[root] with ValueRange.Empty -> ValueRange.point 0I | actual -> actual
            let text = validText input range
            if ValueRange.isObservable range && ValueRange.contains (ValueRange.bounded 0I 255I) range && (checkedText || text.IsSome) then
                let family = members root
                { Site = site; Input = input; Origin = root; Members = family; Premises = declaration :: premises root; Range = range; Representation = rep.Name; Text = text; Checked = checkedText } :: plans, diagnostics
            elif ValueRange.isObservable range && ValueRange.contains (ValueRange.bounded 0I 255I) range then
                plans, diagnostic site [input; root] "text must be proved ASCII or an immutable constant valid UTF-8 sequence." :: diagnostics
            elif checkedText && not(ValueRange.isObservable range) then plans, diagnostics
            else plans, diagnostic site [input; root] "every stored integer must be proved within 0..255." :: diagnostics
        | _, None when checkedText -> plans, diagnostics
        | _ when checkedText && (origins.TryFind input |> Option.isNone) -> plans, diagnostics
        | _, None -> plans, diagnostic site [input] "the platform must offer an unsigned 8-bit representation." :: diagnostics
        | _ -> plans, diagnostic site [input] "the array must have a closed allocation and known writes; an unknown origin or escaping alias is not admitted." :: diagnostics) ([], [])
    let admitted = Set.union
                       (plans |> List.collect (fun plan -> plan.Premises |> List.choose (fun id -> origins.TryFind id)) |> Set.ofList)
                       (writable.Values |> Seq.choose(function Ok application -> Some application.Allocation | _ -> None) |> Set.ofSeq)
    let reads = nodes.Values |> Seq.choose (fun node ->
        readInput node.Id |> Option.bind (fun input -> origins.TryFind input |> Option.bind (fun root ->
            if admitted.Contains root then Some(node, input, root) else None))) |> Seq.toList
    let annotations = reads |> List.map (fun (node, _, root) -> { node with ValueRange = Some ranges[root] })
    let edges = reads |> List.collect (fun (node, input, root) ->
        let declaration = representation |> Option.map (snd >> List.singleton) |> Option.defaultValue []
        let sources = List.distinct(root :: input :: (declaration @ premises root))
        let read = { Class = EdgeClass.Range; Role = EdgeRole.StringByteRead; Sources = sources; Target = node.Id; Ordinal = 0 }
        match ranges[root] with
        | ValueRange.Bounded(lo, hi) -> [read; { read with Role = EdgeRole.StringByteRange(lo, hi) }]
        | _ -> [read])
    List.rev plans, { Enrichment.empty with Annotated = annotations; NewEdges = edges }, List.rev diagnostics

/// Renew only the scalar producer's paired rows. A storage-backed range may
/// coexist at the same target and remains the responsibility of its own recipe.
let establishScalarRanges (graph: SemanticGraph) : Hyperedge list * Hyperedge list * Diagnostic list =
    let markers = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.StringByteRead)
    if markers.IsEmpty then [], [], [] else
    let nodes, origins, _, blocked, ranges, representation, _, premises, _, readInput, _ = analyze true graph
    let bounds = graph.Edges |> List.filter (fun edge -> match edge.Role with EdgeRole.StringByteRange _ -> true | _ -> false)
                 |> List.groupBy _.Target |> Map.ofList
    let missing = "The scalar range of this array read lacks its complete current allocation and write premises."
    let changed = "The scalar range of this array read changed after source range settlement."
    markers |> List.groupBy _.Target |> List.fold (fun (removed, renewed, diagnostics) (site, reads) ->
        let owned = bounds.TryFind site |> Option.defaultValue [] |> List.filter (fun edge ->
            reads |> List.exists (fun read ->
                edge.Class = read.Class && edge.Ordinal = read.Ordinal &&
                edge.Target = read.Target && edge.Sources = read.Sources))
        let fail reason =
            let diagnostic =
                { Severity = NativeDiagnosticSeverity.Error; Code = "CCS8404"; Message = reason
                  Range = graph.Nodes[site].Range; RelatedNodes = [site]
                  Reachability = ReachabilityContext.Reachable }
            // Retain the producer marker on failure, so a second establishment
            // cannot silently treat absence of a current range as success.
            owned @ removed, renewed, diagnostic :: diagnostics
        match reads, owned, nodes.TryFind site, representation with
        | [read], [previous], Some _, Some(_, declaration) ->
            match readInput site |> Option.bind (fun input -> origins.TryFind input |> Option.map (fun root -> input, root)) with
            | Some(input, root) when not (blocked.Contains root) ->
                match ranges[root], previous.Role with
                | ValueRange.Bounded(lo, hi), EdgeRole.StringByteRange(oldLo, oldHi) when lo <= hi ->
                    if lo <> oldLo || hi <> oldHi then fail changed else
                    let sources = List.distinct(root :: input :: declaration :: premises root)
                    previous :: read :: removed,
                    { read with Sources = sources } :: { previous with Sources = sources } :: renewed, diagnostics
                | _ -> fail missing
            | _ -> fail missing
        | _ -> fail missing) ([], [], [])

/// The immutable string owns a fresh snapshot. This uses the existing copying
/// Array.sub operation, not a reinterpretation of externally mutable storage.
let private expandCore (graph: SemanticGraph) (plan: Plan) =
    let sourceType = graph.Nodes[plan.Input].Type
    let point = { plan.Site.Range with End = plan.Site.Range.Start }
    let state = SaturationState.create point "String.fromBytes" (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId()) plan.Site.Id graph.Platform
    let intrinsic modl operation args types resultType = saturation {
        let info = { Module = modl; Operation = operation; FullName = string modl + "." + operation; Category = IntrinsicCategory.Memory }
        let! fn = createAndEmit (SemanticKind.Intrinsic info) (List.foldBack (fun arg result -> NativeType.TFun(arg, result)) types resultType)
        return! app fn args resultType }
    let parser = saturation {
        let! binding = letBind "__string_bytes" plan.Input sourceType
        let! input = varRef "__string_bytes" (Some binding) sourceType
        let! length = intrinsic IntrinsicModule.Array "length" [input] [sourceType] Types.intType
        let! zero = intLit 0
        let! snapshot = intrinsic IntrinsicModule.Array "sub" [input; zero; length] [sourceType; Types.intType; Types.intType] sourceType
        if plan.Checked then
            let resultType = NativeType.TApp(Types.voptionTyCon, [Types.stringType])
            let! validation = intrinsic IntrinsicModule.String "validateUtf8" [snapshot] [sourceType] Types.boolType
            let! text = intrinsic IntrinsicModule.String "fromBytes" [snapshot] [sourceType] Types.stringType
            let! success = duConstruct "ValueSome" 1 (Some text) None resultType
            let! retirement = intrinsic IntrinsicModule.String "retireSnapshot" [snapshot] [sourceType] Types.unitType
            let! failure = duConstruct "ValueNone" 0 None None resultType
            let! failed = evaluateBefore [retirement] failure resultType
            let! decision = createWithChildren (SemanticKind.IfThenElse(validation, success, Some failed)) resultType [validation; success; failed]
            let! root = evaluateBefore [binding; length; snapshot] decision resultType
            let construction =
                { Owner = plan.Site.Id; Input = input; Snapshot = snapshot; Length = length
                  Validation = validation; Decision = decision; Text = text; Success = success
                  Failure = failure; Retirement = retirement; Validator = "RFC3629-v1"; Returned = None }
            return root, snapshot, Some construction
        else
            let! result = intrinsic IntrinsicModule.String "fromBytes" [snapshot] [sourceType] Types.stringType
            let! root = evaluateBefore [binding; length; snapshot] result Types.stringType
            return root, snapshot, None }
    match run state parser with
    | Matched(root, snapshot, checkedConstruction), created ->
        let created = created |> List.map (fun node ->
            let range =
                match node.Kind with
                | SemanticKind.Literal(NativeLiteral.Int(value, _)) -> Some(ValueRange.point (bigint value))
                | SemanticKind.Application(_, [_]) when Types.isIntegerType node.Type ->
                    let info = { Module = IntrinsicModule.Array; Operation = "length"; Category = IntrinsicCategory.Memory; FullName = "Array.length" }
                    match RangeSources.intrinsic graph.Platform info [] with RangeSources.Result.Fact range -> Some range | _ -> None
                | _ -> node.ValueRange
            { node with Range = (if node.Id = root then plan.Site.Range else node.Range); ValueRange = range })
        let lo, hi = match plan.Range with ValueRange.Bounded(lo, hi) -> lo, hi | _ -> failwith "Unsettled byte plan"
        // The first three roles are positional even when a direct literal is
        // both input and origin. Remaining incidence is a finite unique set.
        let prefix = [plan.Site.Id; plan.Input; plan.Origin]
        let participants = prefix @ (plan.Premises |> List.distinct |> List.filter (fun id -> not (List.contains id prefix)))
        let targets = plan.Members @ (created |> List.choose (fun node -> if arrayElement node |> Option.isSome then Some node.Id else None))
        let storage = targets |> List.distinct |> List.map (fun target ->
            { Class = EdgeClass.Range; Role = EdgeRole.StringByteStorage(lo, hi, plan.Representation); Sources = participants; Target = target; Ordinal = 0 })
        let snapshotEdge = { Class = EdgeClass.Provenance; Role = EdgeRole.StringByteSnapshot; Sources = [plan.Input; snapshot]; Target = plan.Site.Id; Ordinal = 0 }
        let obligation = obligationNode plan.Site (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId())
                            { Id = "string-byte-storage-" + string(NodeId.value plan.Site.Id); Kind = "string-byte-storage"; Logic = "QF_LIA"
                              Statement = "Every reachable stored value in this closed array family fits its byte-unit storage."
                              Source = fmtRange plan.Site.Range; Refs = []
                              Body = ObligationBody.IntegerRepresentationCoverage(lo, hi, 0I, 255I) }
        let textEdges =
            if plan.Checked then [] else
            plan.Text |> Option.map (fun role -> { Class = EdgeClass.Range; Role = role; Sources = participants; Target = plan.Site.Id; Ordinal = 0 }) |> Option.toList
        let checkedEdges = checkedConstruction |> Option.map (fun construction ->
            let incidence = [construction.Owner; construction.Input; construction.Snapshot; construction.Length
                             construction.Validation; construction.Decision; construction.Text; construction.Success
                             construction.Failure; construction.Retirement]
            { Class = EdgeClass.Provenance; Role = EdgeRole.StringCheckedConstruction construction
              Sources = List.distinct(incidence @ participants); Target = plan.Site.Id; Ordinal = 0 }) |> Option.toList
        root, created @ [obligation], storage @ [snapshotEdge; constrains participants obligation] @ textEdges @ checkedEdges
    | NoMatch reason, _ -> failwithf "String byte storage recipe failed: %s" reason

let expand graph plan =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> expandCore graph plan)


/// The source exposes ordinary integers, so the fresh destination's element
/// representation follows every reachable write, including values above 255.
/// Only the inaccessible input view has the encoding's byte representation.
let private expandToBytesCore (graph: SemanticGraph) (source: SemanticNode) input =
    let point = { source.Range with End = source.Range.Start }
    let state = SaturationState.create point "String.toBytes" (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId()) source.Id graph.Platform
    let intrinsic modl operation args types resultType = saturation {
        let category =
            match modl, operation with
            | IntrinsicModule.Operators, "op_LessThan" -> IntrinsicCategory.Comparison
            | IntrinsicModule.Operators, "op_Addition" -> IntrinsicCategory.Arithmetic
            | _ -> IntrinsicCategory.Memory
        let info = { Module = modl; Operation = operation; FullName = string modl + "." + operation; Category = category }
        let! fn = createAndEmit (SemanticKind.Intrinsic info) (List.foldBack (fun arg result -> NativeType.TFun(arg, result)) types resultType)
        return! app fn args resultType }
    let parser = saturation {
        let! binding = letBind "__string_text" input Types.stringType
        let! reference = varRef "__string_text" (Some binding) Types.stringType
        let! view = intrinsic IntrinsicModule.String "toBytes" [reference] [Types.stringType] source.Type
        let! length = intrinsic IntrinsicModule.Array "length" [view] [source.Type] Types.intType
        let! zero = intLit 0
        let! snapshot = intrinsic IntrinsicModule.Array "sub" [view;zero;length] [source.Type;Types.intType;Types.intType] source.Type
        let! root = evaluateBefore [binding;view;length] snapshot source.Type
        return root,view,snapshot }
    match run state parser with
    | Matched(root, view, snapshot), created ->
        let created = created |> List.map (fun node ->
            let range =
                match node.Kind with
                | SemanticKind.Literal(NativeLiteral.Int(value, _)) -> Some(ValueRange.point (bigint value))
                | SemanticKind.Application(_, [_]) when Types.isIntegerType node.Type ->
                    let info = { Module = IntrinsicModule.Array; Operation = "length"; Category = IntrinsicCategory.Memory; FullName = "Array.length" }
                    match RangeSources.intrinsic graph.Platform info [] with RangeSources.Result.Fact range -> Some range | _ -> None
                | _ -> node.ValueRange
            { node with Range = (if node.Id = root then source.Range else node.Range); ValueRange = range })
        match byteRepresentation graph with
        | None -> None
        | Some(representation, declaration) ->
            let edge = { Class = EdgeClass.Provenance; Role = EdgeRole.StringToBytesSnapshot; Sources = [input; view; snapshot]; Target = source.Id; Ordinal = 0 }
            let storage = { Class = EdgeClass.Range; Role = EdgeRole.StringByteStorage(0I, 255I, representation.Name); Sources = [source.Id; input; view; declaration]; Target = view; Ordinal = 0 }
            Some(root, created, [edge; storage])
    | NoMatch reason, _ -> failwithf "String array snapshot recipe failed: %s" reason

let expandToBytes graph source input =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> expandToBytesCore graph source input)

/// Plan only this complete unit-helper result. Ordinary local constructions
/// retain their existing residence; a return never acquires a stack lifetime
/// merely because its caller consumes the value locally.
let returnedExpansions (graph:SemanticGraph) =
    let nodes=graph.Nodes |> Map.filter(fun _ node->node.IsReachable)
    let live id=nodes[id]
    let scope start =
        [1..nodes.Count] |> List.fold(fun (found,current) _ ->
            match found,current |> Option.bind nodes.TryFind with
            | Some _,_ | _,None -> found,None
            | None,Some node -> match node.Kind with SemanticKind.Lambda _ -> Some node.Id,None | _ -> None,node.Parent)
            (None,Some start) |> fst
    let straight start owner =
        [1..nodes.Count] |> List.fold(fun (okay,current) _ ->
            match current |> Option.bind nodes.TryFind with
            | None -> okay,None
            | Some node when node.Id=owner -> okay,None
            | Some node ->
                let allowed=match node.Kind with
                            | SemanticKind.Binding(_,false,false,_) | SemanticKind.Sequential _ | SemanticKind.TypeAnnotation _
                            | SemanticKind.EagerExpr _ | SemanticKind.Application _ -> true | _ -> false
                okay && allowed,node.Parent) (true,Some start) |> fst
    let aliases (initial:NodeId) =
        [1..nodes.Count] |> List.fold(fun family _ ->
            nodes.Values |> Seq.fold(fun (family:Set<NodeId>) node->
                let input=match node.Kind,node.Children with
                          | SemanticKind.Binding(_,false,false,_),[value] -> Some value
                          | SemanticKind.VarRef(_,Some definition),_ -> Some definition
                          | SemanticKind.TypeAnnotation(value,_),_ | SemanticKind.EagerExpr value,_ -> Some value
                          | _ -> None
                if input |> Option.exists family.Contains then Set.add node.Id family else family) family) (Set.singleton initial)
    let fail reason = raise(System.InvalidOperationException reason)
    let demand okay reason = if not okay then fail reason
    let only reason = function [value] -> value | _ -> fail reason
    let resolution=lazy(Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph)
    let mutable expansions=[]
    let mutable annotations=[]
    let mutable edges=graph.Edges
    let mutable diagnostics=[]
    for edge in graph.Edges do
      match edge.Role with
      | EdgeRole.StringCheckedConstruction construction when construction.Returned.IsNone && nodes.ContainsKey construction.Owner ->
        let helper=scope construction.Owner
        let calls=resolution.Value.Calls |> Map.toList |> List.filter(fun (_,call)->
            call.Targets |> List.exists(fun target->Some target.Lambda=helper && target.Body=construction.Owner))
        if not calls.IsEmpty then
          try
            let application,resolved=only "A returned checked string requires exactly one complete helper application." calls
            demand (resolved.Complete && not resolved.Unknown) "The checked helper call has unresolved alternatives."
            let target=only "A returned checked string requires one exact helper implementation." resolved.Targets
            let declaration,callee,argument,formal=
                match (live application).Kind,target.Parameters,(live target.Lambda).Kind with
                | SemanticKind.Application(callee,[argument]),[(_,parameterType,formal)],SemanticKind.Lambda([(_,_,held)],body,[],_,_)
                    when held=formal && body=construction.Owner && target.Arguments=[argument] &&
                         applySubst parameterType=Types.unitType && applySubst (live argument).Type=Types.unitType ->
                    match (live callee).Kind with
                    | SemanticKind.VarRef(_,Some declaration) ->
                        demand (match (live declaration).Kind,(live declaration).Children with
                                | SemanticKind.Binding(_,false,false,_),[implementation] -> implementation=target.Lambda | _ -> false)
                            "The checked helper has no exact immutable implementation declaration."
                        declaration,callee,argument,formal
                    | _ -> fail "The checked helper call requires its exact immutable declaration reference."
                | _ -> fail "The returned checked profile requires one noncapturing unit helper and its exact returned body."
            let caller=scope application |> Option.defaultWith(fun()->fail "The returned checked call lacks its caller activation.")
            demand (caller<>target.Lambda && straight application caller) "The returned checked application is conditional, captured or inside a loop."
            let original=
                graph.Edges |> List.choose(fun row->
                    match row.Role,row.Sources with
                    | EdgeRole.StringByteSnapshot,[input;snapshot] when row.Target=construction.Owner && snapshot=construction.Snapshot -> Some input
                    | _ -> None)
                |> only "The returned checked construction lost its original snapshot input."
            demand (match (live original).Kind with SemanticKind.ArrayExpr _ -> true | _ -> false)
                "The returned checked profile requires its exact literal snapshot input."
            let policy=graph.Platform |> Option.bind _.ProjectMemoryPolicy
                       |> Option.defaultWith(fun()->fail "Returned checked storage has no captured project memory policy.")
            let path,version,model,allowed=policy
            demand allowed "The selected project memory policy forbids returned checked storage."
            let platform=PlatformResolution.resolve graph |> Option.defaultWith(fun()->fail "Returned checked storage has no selected platform declaration.")
            let heap=platform.Spaces |> List.filter(fun space->space.Kind="heap" && space.Access.Contains("w"))
                     |> only "Returned checked storage requires exactly one declared writable heap space."
            let family=aliases application
            demand (family |> Set.forall(fun id->scope id=Some caller)) "A returned checked alias crosses its caller activation."
            let cases=
                nodes.Values |> Seq.choose(fun node->
                    match node.Kind with
                    | SemanticKind.CaseElimination(value,arms) when family.Contains value && Types.isIntegerType node.Type -> Some(node,value,arms)
                    | _ -> None) |> Seq.toList
            let arm name tag (_,_,arms)=arms |> List.tryFind(fun arm->match arm.Pattern with Pattern.Union(actual,index,_,_) -> actual=name && index=tag && arm.Guard.IsNone | _ -> false)
            let someCase,actual,someArms=cases |> List.filter(fun entry->(arm "ValueSome" 1 entry).IsSome) |> only "The returned checked value requires its exact Some elimination."
            let noneCase,_,noneArms=cases |> List.filter(fun entry->(arm "ValueNone" 0 entry).IsSome) |> only "The returned checked value requires its exact None elimination."
            let someArm=arm "ValueSome" 1 (someCase,actual,someArms) |> Option.get
            let noneArm=noneArms |> List.find(fun arm->match arm.Pattern with Pattern.Union("ValueNone",0,_,_) -> true | _ -> false)
            let remainder=
                match someArms,noneArms with
                | [{Pattern=Pattern.Union("ValueSome",1,Some Pattern.Wildcard,_);Guard=None};{Pattern=Pattern.Wildcard;Guard=None;Body=remainder}],
                  [{Pattern=Pattern.Union("ValueNone",0,None,_);Guard=None}] -> remainder
                | _ -> fail "The returned checked caller lost its exact closed Some/None case family."
            let nonePath=
                [1..nodes.Count] |> List.fold(fun (path,current) _ ->
                    match current |> Option.bind nodes.TryFind with
                    | Some node when node.Id<>someCase.Id -> Set.add node.Id path,node.Parent
                    | _ -> path,None) (Set.empty,Some noneCase.Id) |> fst
            demand (nonePath.Contains remainder && not(nonePath.Contains someArm.Body))
                "The returned checked None cleanup is not inside the same Some/None elimination."
            let someUse,payload,payloadBinding=
                match (live someArm.Body).Kind with
                | SemanticKind.Sequential [binding;body] ->
                    match (live binding).Kind,(live binding).Children,(live body).Kind with
                    | SemanticKind.Binding(_,false,false,_),[projection],SemanticKind.Application(fn,[payload]) ->
                        demand (match (live projection).Kind with SemanticKind.DUEliminate(value,1,"ValueSome",_) -> family.Contains value | _ -> false)
                            "The returned checked Some payload lost its exact elimination."
                        demand (match (live fn).Kind with SemanticKind.Intrinsic{Module=IntrinsicModule.String;Operation="length"} -> true | _ -> false)
                            "The returned checked Some arm must consume its payload through String.length."
                        demand (match (live payload).Kind with SemanticKind.VarRef(_,Some definition) -> definition=binding | _ -> false)
                            "The returned checked scalar consumes a different payload."
                        body,payload,binding
                    | _ -> fail "The returned checked Some arm has unsupported consumers."
                | _ -> fail "The returned checked Some arm requires one bound payload and one scalar length."
            let noneUse=noneArm.Body
            demand (match (live noneUse).Kind with SemanticKind.Literal(NativeLiteral.Int _) -> true | _ -> false)
                "The returned checked None arm requires one scalar literal result."
            let payloadFamily=aliases payload
            for node in nodes.Values do
                let referenced=node.Children |> List.filter(fun id->family.Contains id || payloadFamily.Contains id)
                if not referenced.IsEmpty && not(family.Contains node.Id || payloadFamily.Contains node.Id) then
                    demand (scope node.Id=Some caller) "A returned checked value is captured by another activation."
                    demand (match node.Kind with
                            | SemanticKind.CaseElimination(_,arms) -> arms |> List.forall(fun arm->arm.Guard.IsNone)
                            | SemanticKind.DUEliminate(_,1,"ValueSome",_) | SemanticKind.DUGetTag _ | SemanticKind.Sequential _ -> true
                            | SemanticKind.Application _ -> node.Id=someUse
                            | _ -> false) "The returned checked value has an extra or unsupported consumer."
            let makeArm original armBody backing =
                let source=live original
                let state=SaturationState.create source.Range "String.checkedResultRetirement" (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId()) source.Id graph.Platform
                let retire name value ty = saturation {
                    let info={Module=IntrinsicModule.String;Operation=name;FullName="String."+name;Category=IntrinsicCategory.Memory}
                    let! fn=createAndEmit (SemanticKind.Intrinsic info) (NativeType.TFun(ty,Types.unitType))
                    return! app fn [value] Types.unitType }
                let parser=saturation {
                    // The length operation already owns settled string-borrow
                    // evidence. Wrap its arm without replacing that operation.
                    let! scalar=
                        if original=armBody then createWithChildren source.Kind source.Type source.Children
                        else saturation {return original}
                    let! saved=letBind "__checked_scalar" scalar source.Type
                    let! backingSite=
                        if backing then saturation {
                            let! site=retire "retireCheckedBacking" payload Types.stringType
                            return Some site }
                        else saturation {return None}
                    let! carrierSite=retire "retireCheckedCarrier" actual (live actual).Type
                    let! result=varRef "__checked_scalar" (Some saved) source.Type
                    let items=[saved]@Option.toList backingSite@[carrierSite;result]
                    let! cleanup=createWithChildren (SemanticKind.Sequential items) source.Type items
                    let! root=
                        if backing then createWithChildren (SemanticKind.Sequential[payloadBinding;cleanup]) source.Type [payloadBinding;cleanup]
                        else saturation {return cleanup}
                    return root,scalar,backingSite,carrierSite }
                match run state parser with
                | Matched(root,scalar,backingSite,carrierSite),created ->
                    let created=created |> List.map(fun node->if node.Id=scalar then {node with ValueRange=source.ValueRange} else node)
                    expansions<-(armBody,(root,created,[]))::expansions
                    scalar,backingSite,carrierSite
                | NoMatch reason,_ -> fail reason
            let someScalar,backingRetirement,someRetirement=makeArm someUse someArm.Body true
            let noneScalar,_,noneRetirement=makeArm noneUse noneArm.Body false
            let capacity=obligationNode (live construction.Owner) (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId())
                            {Id="checked-result-"+string(NodeId.value application);Kind="checked-result-capacity";Logic="QF_LIA"
                             Statement="The simultaneously live checked snapshot and native outcome fit their declared heap space."
                             Source=fmtRange (live application).Range;Refs=[];Body=ObligationBody.Pending["The returned checked storage awaits its settled extent and layout."]}
            let lifetime={Application=application;Callee=callee;Declaration=declaration;Implementation=target.Lambda;Argument=argument;Formal=formal
                          Body=construction.Owner;Caller=caller;Actual=actual;Elimination=someCase.Id;SomeUse=someScalar;NoneUse=noneScalar
                          SomeBackingRetirement=Option.get backingRetirement;SomeCarrierRetirement=someRetirement;NoneCarrierRetirement=noneRetirement
                          Uses=Set.toList family;Policy={ProjectPath=path;SourceVersion=version;Model=model};Platform=platform.Node;Space=heap.Node
                          MaximumLiveBytes=0L;Capacity=capacity.Id}
            annotations<-capacity::annotations
            let construction={construction with Returned=Some lifetime}
            let support=Clef.Compiler.Baker.Ingredients.MemoryValues.resultIds lifetime |> Set.remove capacity.Id |> Set.toList
            edges<-edges |> List.map(fun old->
                if old.Target=edge.Target && old.Role=edge.Role && old.Sources=edge.Sources && old.Ordinal=edge.Ordinal then
                    {old with Role=EdgeRole.StringCheckedConstruction construction;Sources=List.distinct(old.Sources@support@[capacity.Id])}
                else old)
            edges<-constrains support capacity::edges
          with :? System.InvalidOperationException as error ->
            diagnostics<-{Severity=NativeDiagnosticSeverity.Error;Code="CCS8403";Message=error.Message;Range=(live construction.Owner).Range
                          RelatedNodes=[construction.Owner];Reachability=ReachabilityContext.Reachable}::diagnostics
      | _ -> ()
    {graph with Edges=edges;Nodes=annotations |> List.fold(fun all node->Map.add node.Id node all) graph.Nodes},Map.ofList expansions,List.rev diagnostics

/// Current reading of this recipe's own returned-instance contract. It does
/// not widen ordinary array use closure or manufacture a missing lifetime.
let returnedLifetime (graph:SemanticGraph) (construction:CheckedStringConstruction) =
    match construction.Returned with
    | None -> None
    | Some life ->
        let demand okay reason=if not okay then invalidOp reason
        let live id=graph.Nodes.TryFind id |> Option.filter _.IsReachable |> Option.defaultWith(fun()->invalidOp (sprintf "A returned checked lifetime participant %A was withdrawn." id))
        let current=graph.Platform |> Option.bind _.ProjectMemoryPolicy
        demand (current=Some(life.Policy.ProjectPath,life.Policy.SourceVersion,life.Policy.Model,true))
            "The returned checked allocation permission or captured policy changed."
        let platform=PlatformResolution.resolve graph |> Option.defaultWith(fun()->invalidOp "The returned checked platform is missing.")
        let space=platform.Spaces |> List.tryFind(fun row->row.Node=life.Space && row.Kind="heap" && row.Access.Contains("w"))
                  |> Option.defaultWith(fun()->invalidOp "The returned checked heap declaration changed.")
        if life.MaximumLiveBytes<=0L then
            match graph.Nodes.TryFind life.Capacity with
            | Some{Kind=SemanticKind.Obligation{Body=ObligationBody.Pending reasons}} -> invalidOp(String.concat "; " reasons)
            | _ -> invalidOp "The returned checked instance has no current positive settled lifetime."
        demand (platform.Node=life.Platform && life.Body=construction.Owner)
            "The returned checked instance has no current positive settled lifetime."
        // Proof citizens are held logical support, not executable values.
        // This exact role still needs its own current body and source incidence.
        demand (match graph.Nodes.TryFind life.Capacity with
                | Some{Kind=SemanticKind.Obligation info} -> info.Body=ObligationBody.CapacityFits(life.MaximumLiveBytes,space.Capacity)
                | _ -> false) "The returned checked combined capacity citizen changed."
        demand (graph.Edges |> List.exists(fun edge->
                    edge.Target=life.Capacity && edge.Role=EdgeRole.Constrains &&
                    ([life.Application;life.Platform;life.Space] |> List.forall(fun source->List.contains source edge.Sources))))
            "The returned checked capacity citizen lost its exact owning source support."
        let resolution=Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins.resolve graph
        demand (match resolution.Calls.TryFind life.Application with
                | Some{Complete=true;Unknown=false;Targets=[target]} ->
                    target.Lambda=life.Implementation && target.Body=life.Body && target.Arguments=[life.Argument] &&
                    (match target.Parameters with [(_,_,formal)] -> formal=life.Formal | _ -> false)
                | _ -> false) "The returned checked application lost its exact complete helper target."
        demand (match (live life.Application).Kind with SemanticKind.Application(fn,[argument]) -> fn=life.Callee && argument=life.Argument | _ -> false)
            "The returned checked application changed its callee or argument."
        demand (match (live life.Callee).Kind,(live life.Declaration).Kind,(live life.Declaration).Children,(live life.Implementation).Kind with
                | SemanticKind.VarRef(_,Some declaration),SemanticKind.Binding(_,false,false,_),[implementation],SemanticKind.Lambda([(_,_,formal)],body,[],_,_) ->
                    declaration=life.Declaration && implementation=life.Implementation && formal=life.Formal && body=life.Body
                | _ -> false) "The returned checked declaration, formal or body changed."
        for site,name in [life.SomeBackingRetirement,"retireCheckedBacking";life.SomeCarrierRetirement,"retireCheckedCarrier";life.NoneCarrierRetirement,"retireCheckedCarrier"] do
            match (live site).Kind with
            | SemanticKind.Application(fn,[_]) -> demand (match (live fn).Kind with SemanticKind.Intrinsic{Module=IntrinsicModule.String;Operation=actual} -> actual=name | _ -> false)
                                                    "The returned checked cleanup operation changed."
            | _ -> invalidOp "The returned checked cleanup citizen was withdrawn."
        Some(life,space)
