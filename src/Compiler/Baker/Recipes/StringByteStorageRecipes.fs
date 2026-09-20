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

type Plan = { Site: SemanticNode; Input: NodeId; Origin: NodeId; Members: NodeId list; Premises: NodeId list; Range: ValueRange; Representation: string; Text: EdgeRole }

let private byteRepresentation (graph: SemanticGraph) =
    let declarations =
        PlatformResolution.resolve graph |> Option.bind _.Core
        |> Option.map _.Representations |> Option.defaultValue []
    graph.Platform |> Option.bind (fun platform ->
        platform.Representations.Values |> Seq.tryPick (fun rep ->
            if rep.Bits = 8 && rep.Family = "uint" && NumericRepresentation.isOffered rep
               && (RangeSources.declaredRange rep |> Option.exists (fun range -> ValueRange.contains range (ValueRange.bounded 0I 255I))) then
                match declarations |> List.filter (fun declaration -> declaration.Representation = rep) with
                | [declaration] -> Some(rep, declaration.Node)
                | _ -> None
            else None))

let private arrayElement (node: SemanticNode) =
    match applySubst node.Type with
    | NativeType.TApp(tc, [elem]) when tc.NTUKind = Some NTUKind.NTUarray && Types.isIntegerType elem -> Some elem
    | _ -> None

let private diagnostic (site: SemanticNode) related reason : Diagnostic =
    { Severity = NativeDiagnosticSeverity.Error; Code = "CCS8404"
      Message = "String.fromBytes requires proved byte storage: " + reason
      Range = site.Range; RelatedNodes = List.distinct(site.Id :: related)
      Reachability = ReachabilityContext.Reachable }

let recognize (graph: SemanticGraph) : Plan list * Enrichment * Diagnostic list =
    let nodes = graph.Nodes |> Map.filter (fun _ node -> node.IsReachable)
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
            | SemanticKind.ArrayExpr _ -> Some id
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
    let members root = origins |> Map.toList |> List.choose (fun (id, actual) -> if actual = root then Some id else None)
    let roots = origins.Values |> Set.ofSeq
    let mutable blocked = Set.empty
    let block id = origins.TryFind id |> Option.iter (fun root -> blocked <- Set.add root blocked)
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
                    | IntrinsicModule.String, "fromBytes", 1 -> true
                    | _ -> false
                args |> List.iteri (fun index arg -> if not allowed || index <> 0 then block arg)
            | None -> directArgs |> List.iter block
        | SemanticKind.Binding(_, false, _, _) | SemanticKind.VarRef _ | SemanticKind.TypeAnnotation _ | SemanticKind.Sequential _ -> ()
        | SemanticKind.IndexGet _ | SemanticKind.IndexSet _ -> ()
        | SemanticKind.Lambda(_, body, captures, _, _) ->
            block body
            captures |> List.iter (fun capture -> capture.SourceNodeId |> Option.iter block)
        | SemanticKind.LazyExpr(_, captures) | SemanticKind.SeqExpr(_, captures) ->
            captures |> List.iter (fun capture -> capture.SourceNodeId |> Option.iter block)
        | _ -> node.Children |> List.iter block
    let writes root =
        nodes.Values |> Seq.collect (fun node ->
            match node.Kind with
            | SemanticKind.ArrayExpr values when node.Id = root -> values |> List.map (fun value -> node.Id, value) |> Seq.ofList
            | SemanticKind.IndexSet(input, _, value) when origins.TryFind input = Some root -> Seq.singleton(node.Id, value)
            | _ ->
                match calls.TryFind node.Id with
                | Some({ Module = IntrinsicModule.Array; Operation = "set" }, [input; _; value]) when origins.TryFind input = Some root -> Seq.singleton(node.Id, value)
                | Some({ Module = IntrinsicModule.Array; Operation = "create" }, [_; value]) when node.Id = root -> Seq.singleton(node.Id, value)
                | _ -> Seq.empty) |> Seq.toList
    let stores = roots |> Seq.map (fun root -> root, writes root) |> Map.ofSeq
    let seeded root =
        match calls.TryFind root with
        | Some({ Module = IntrinsicModule.Array; Operation = "zeroCreate" }, [_]) -> ValueRange.point 0I
        | _ -> ValueRange.Empty
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
            let existing = node.ValueRange |> Option.defaultValue ValueRange.Unbounded
            match readInput id |> Option.bind (fun input -> origins.TryFind input) with
            | Some root -> ranges.TryFind root |> Option.defaultValue ValueRange.Unbounded
            | None ->
                let inferred =
                    match node.Kind with
                    | SemanticKind.Binding(_, false, _, _) when node.Children.Length = 1 -> recurse node.Children.Head
                    | SemanticKind.VarRef(_, Some definition) ->
                        match nodes.TryFind definition with
                        | Some { Kind = SemanticKind.Binding(_, false, _, _) } -> recurse definition
                        | _ -> existing
                    | SemanticKind.TypeAnnotation(inner, _) -> recurse inner
                    | SemanticKind.Sequential values -> List.tryLast values |> Option.map recurse |> Option.defaultValue existing
                    | SemanticKind.IfThenElse(_, yes, no) -> ValueRange.join (recurse yes) (no |> Option.map recurse |> Option.defaultValue ValueRange.Empty)
                    | SemanticKind.Application _ ->
                        match calls.TryFind id with
                        | Some(info, args) ->
                            let arguments = args |> List.map (fun arg ->
                                let source = nodes[arg]
                                ({ Range = recurse arg; Type = source.Type
                                   Literal = match source.Kind with SemanticKind.Literal literal -> Some literal | _ -> None } : RangeSources.Argument))
                            match RangeSources.intrinsic graph.Platform info arguments with RangeSources.Result.Fact range -> range | _ -> existing
                        | _ -> existing
                    | _ -> existing
                // Existing guarded scalar facts remain valid; the local read
                // dependency can improve a type-wide array approximation.
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
    let representation = byteRepresentation graph
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
    let premises root =
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
                let dependencies, valuesRead = values Set.empty (writes |> List.map snd) [] []
                visitRoots (Set.add current seen) (dependencies @ rest)
                    (current :: members current @ (writes |> List.collect (fun (writer, stored) -> [writer; stored])) @ valuesRead @ accumulated)
        visitRoots Set.empty [root] []
    let sites =
        nodes.Values |> Seq.choose (fun node ->
            match calls.TryFind node.Id with
            | Some({ Module = IntrinsicModule.String; Operation = "fromBytes" }, [input])
                when not (graph.Edges |> List.exists (fun edge ->
                    edge.Role = EdgeRole.StringByteSnapshot && (match edge.Sources with [_; copy] -> copy = input | _ -> false))) -> Some(node, input)
            | _ -> None)
        |> Seq.toList
    let plans, diagnostics = sites |> List.fold (fun (plans, diagnostics) (site, input) ->
        match origins.TryFind input, representation with
        | Some root, Some(rep, declaration) when not (blocked.Contains root) ->
            let range = match ranges[root] with ValueRange.Empty -> ValueRange.point 0I | actual -> actual
            let text = validText input range
            if ValueRange.isObservable range && ValueRange.contains (ValueRange.bounded 0I 255I) range && text.IsSome then
                let family = members root
                { Site = site; Input = input; Origin = root; Members = family; Premises = declaration :: premises root; Range = range; Representation = rep.Name; Text = text.Value } :: plans, diagnostics
            elif ValueRange.isObservable range && ValueRange.contains (ValueRange.bounded 0I 255I) range then
                plans, diagnostic site [input; root] "text must be proved ASCII or an immutable constant valid UTF-8 sequence." :: diagnostics
            else plans, diagnostic site [input; root] "every stored integer must be proved within 0..255." :: diagnostics
        | _, None -> plans, diagnostic site [input] "the platform must offer an unsigned 8-bit representation." :: diagnostics
        | _ -> plans, diagnostic site [input] "the array must have a closed allocation and known writes; an unknown origin or escaping alias is not admitted." :: diagnostics) ([], [])
    let admitted = plans |> List.collect (fun plan -> plan.Premises |> List.choose (fun id -> origins.TryFind id)) |> Set.ofList
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

/// The immutable string owns a fresh snapshot. This uses the existing copying
/// Array.sub operation, not a reinterpretation of externally mutable storage.
let expand (graph: SemanticGraph) (plan: Plan) =
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
        let! result = intrinsic IntrinsicModule.String "fromBytes" [snapshot] [sourceType] Types.stringType
        let! root = evaluateBefore [binding; length; snapshot] result Types.stringType
        return root, snapshot }
    match run state parser with
    | Matched(root, snapshot), created ->
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
        let textEdge = { Class = EdgeClass.Range; Role = plan.Text; Sources = participants; Target = plan.Site.Id; Ordinal = 0 }
        root, created @ [obligation], storage @ [snapshotEdge; textEdge; constrains participants obligation]
    | NoMatch reason, _ -> failwithf "String byte storage recipe failed: %s" reason

/// The source exposes ordinary integers, so the fresh destination's element
/// representation follows every reachable write, including values above 255.
/// Only the inaccessible input view has the encoding's byte representation.
let expandToBytes (graph: SemanticGraph) (source: SemanticNode) input =
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
        let! allocation = intrinsic IntrinsicModule.Array "zeroCreate" [length] [Types.intType] source.Type
        let! destination = letBind "__string_array" allocation source.Type
        let! output = varRef "__string_array" (Some destination) source.Type
        let! index = C.mutableBinding "__string_index" zero Types.intType
        let! guardIndex = varRef "__string_index" (Some index) Types.intType
        let! guard = intrinsic IntrinsicModule.Operators "op_LessThan" [guardIndex; length] [Types.intType; Types.intType] Types.boolType
        let! currentIndex = varRef "__string_index" (Some index) Types.intType
        let! current = intrinsic IntrinsicModule.Array "get" [view; currentIndex] [source.Type; Types.intType] Types.intType
        let! store = intrinsic IntrinsicModule.Array "set" [output; currentIndex; current] [source.Type; Types.intType; Types.intType] Types.unitType
        let! one = intLit 1
        let! next = intrinsic IntrinsicModule.Operators "op_Addition" [currentIndex; one] [Types.intType; Types.intType] Types.intType
        let! advance = C.assign index "__string_index" Types.intType next
        let! body = C.block [currentIndex; current; store; advance] Types.unitType
        let! loop = createWithChildren (SemanticKind.WhileLoop(guard, body)) Types.unitType [guard; body]
        let! root = evaluateBefore [binding; view; length; destination; index; loop] output source.Type
        return root, view, output, current, allocation, loop, store }
    match run state parser with
    | Matched(root, view, snapshot, current, allocation, loop, store), created ->
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
            let read = { Class = EdgeClass.Range; Role = EdgeRole.StringByteRead; Sources = [view; input; declaration]; Target = current; Ordinal = 0 }
            let copy = { Class = EdgeClass.Provenance; Role = EdgeRole.CopyFrom; Sources = [view; current; loop; store; allocation; declaration]; Target = snapshot; Ordinal = 0 }
            Some(root, created, [edge; storage; read; { read with Role = EdgeRole.StringByteRange(0I, 255I) }; copy])
    | NoMatch reason, _ -> failwithf "String array snapshot recipe failed: %s" reason
