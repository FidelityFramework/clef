/// Synchronous callback contracts and bounded borrowed-value use. Declarations
/// are library obligations; inferred summaries accept only invocation, aliases,
/// and calls to other proven synchronous consumers. A returned function is bounded
/// only when every call immediately completes its argument chain; stores escape.
module Clef.Compiler.PSGSaturation.SemanticGraph.ScopedCallbacks

open System.Runtime.CompilerServices
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

type private Use =
    | Alias of NodeId
    | Declaration of NodeId
    | Argument of callable: NodeId * index: int * application: NodeId
    | Invoke of application: NodeId * arguments: int
    | Capture of NodeId
    | ReturnedFunction of NodeId
    | Escape
type Reading = { Parameters: Set<NodeId>; StackLambdas: Set<NodeId>; Findings: DeclarationFinding list }

let private readUncached (graph: SemanticGraph) =
    let mutable findings = (MappedBindings.read graph).Findings
    let finding (node: SemanticNode) message =
        findings <- { Node = node.Id; Range = node.Range; Defect = DeclarationDefect.Invalid; Message = message } :: findings
    let rec target seen id =
        if Set.contains id seen then None
        else
            let seen = Set.add id seen
            match SemanticGraph.tryGetNode id graph with
            | Some { Kind = SemanticKind.VarRef (_, Some other) }
            | Some { Kind = SemanticKind.TypeAnnotation (other, _) } -> target seen other
            | Some { Kind = SemanticKind.Binding _; Children = children } -> List.tryLast children |> Option.bind (target seen)
            | other -> other
    // Curry normalization runs after some readers. Retain the full source
    // lambda chain so argument positions have the same meaning in both forms.
    let parameters fn =
        let rec collect seen id =
            match target seen id with
            | Some { Id = lambda; Kind = SemanticKind.Lambda (parameters, body, _, _, _) } ->
                parameters @ collect (Set.add lambda seen) body
            | _ -> []
        collect Set.empty fn
    let mutable declared = (MappedBindings.read graph).Mappings |> List.map (fun m -> m.CallbackParameter) |> Set.ofList
    let annotatedScope ty =
        match applySubst ty with
        | NativeType.TApp (quote, [NativeType.TApp (descriptor, _)]) when quote.Name = "Expr" ->
            descriptor.Name.Split('.') |> Array.last = "ScopedCallbackDescriptor"
        | _ -> false
    for node in graph.Nodes.Values do
        match node.Kind, List.tryLast node.Children with
        | SemanticKind.Binding _, Some body ->
            match recordOf graph body with
            | Some (descriptor, fields) when typeName descriptor = Some "ScopedCallbackDescriptor" ->
                match field "Binding" fields |> Option.bind (stringOf graph), field "Parameter" fields |> Option.bind (stringOf graph) with
                | Some bindingName, Some parameterName ->
                    let matching = graph.Nodes.Values |> Seq.filter (fun n -> MappedBindings.qualifiedBindingName graph n = bindingName) |> Seq.toList
                    match matching with
                    | [binding] ->
                        match parameters binding.Id |> List.tryFind (fun (name, _, _) -> name = parameterName) with
                        | Some (_, ty, id) ->
                            match applySubst ty with
                            | NativeType.TFun _ -> declared <- Set.add id declared
                            | _ -> finding descriptor "A ScopedCallbackDescriptor must name a function-valued parameter."
                        | None -> finding descriptor (sprintf "Scoped callback parameter '%s.%s' is missing." bindingName parameterName)
                    | _ -> finding descriptor (sprintf "Scoped callback binding '%s' is missing or ambiguous." bindingName)
                | _ -> finding descriptor "ScopedCallbackDescriptor requires literal Binding and Parameter names."
            | _ when annotatedScope node.Type ->
                finding node "ScopedCallbackDescriptor requires a well-typed quoted record body; check that its record fields are in scope."
            | _ -> ()
        | _ -> ()

    let mutable users: Map<NodeId, Use list> = Map.empty
    let useValue source usage = users <- Map.add source (usage :: (Map.tryFind source users |> Option.defaultValue [])) users
    let moduleBinding node = node.Parent |> Option.bind (fun p -> SemanticGraph.tryGetNode p graph) |> Option.exists (fun p -> match p.Kind with SemanticKind.ModuleDef _ -> true | _ -> false)
    let namedDeclaration source =
        match SemanticGraph.tryGetNode source graph with
        | Some { Kind = SemanticKind.Lambda _; Metadata = metadata } ->
            Map.tryFind ClosureMetadata.LambdaExpression metadata <> Some (MetadataValue.Bool true)
            && Map.tryFind ClosureMetadata.RequiresClosurePair metadata <> Some (MetadataValue.Bool true)
        | _ -> false
    for node in graph.Nodes.Values do
        if node.IsReachable then
            match node.Kind with
            | SemanticKind.VarRef (_, Some source) | SemanticKind.TypeAnnotation (source, _) -> useValue source (Alias node.Id)
            | SemanticKind.Binding (_, mutableValue, _, _) ->
                List.tryLast node.Children |> Option.iter (fun source ->
                    let usage =
                        if mutableValue then Escape
                        elif moduleBinding node then
                            if namedDeclaration source then Declaration node.Id else Escape
                        else Alias node.Id
                    useValue source usage)
            | SemanticKind.Application (fn, arguments) ->
                useValue fn (Invoke (node.Id, arguments.Length))
                arguments |> List.iteri (fun index value -> useValue value (Argument (fn, index, node.Id)))
            | SemanticKind.Lambda (_, body, captures, _, _) ->
                let usage =
                    match SemanticGraph.tryGetNode body graph with
                    | Some { Kind = SemanticKind.Lambda _ } -> ReturnedFunction node.Id
                    | _ -> Escape
                useValue body usage
                captures |> List.iter (fun capture -> capture.SourceNodeId |> Option.iter (fun source -> useValue source (Capture node.Id)))
            | SemanticKind.Sequential nodes -> List.tryLast nodes |> Option.iter (fun source -> useValue source (Alias node.Id))
            | SemanticKind.IfThenElse (guard, yes, no) ->
                useValue guard Escape
                useValue yes (Alias node.Id)
                no |> Option.iter (fun source -> useValue source (Alias node.Id))
            | SemanticKind.Match (scrutinee, cases) ->
                useValue scrutinee Escape
                cases |> List.iter (fun case ->
                    case.Guard |> Option.iter (fun guard -> useValue guard Escape)
                    useValue case.Body (Alias node.Id))
            | SemanticKind.CaseElimination (scrutinee, arms) ->
                useValue scrutinee Escape
                arms |> List.iter (fun arm ->
                    arm.Guard |> Option.iter (fun guard -> useValue guard Escape)
                    useValue arm.Body (Alias node.Id))
            | SemanticKind.TryWith (body, handler) -> useValue body (Alias node.Id); useValue handler (Alias node.Id)
            | SemanticKind.TryFinally (body, cleanup) -> useValue body (Alias node.Id); useValue cleanup Escape
            | SemanticKind.RecordExpr (fields, _) -> fields |> List.iter (fun (_, value) -> useValue value Escape)
            | SemanticKind.TupleExpr values | SemanticKind.ArrayExpr values | SemanticKind.ListExpr values -> values |> List.iter (fun value -> useValue value Escape)
            | SemanticKind.DUConstruct (_, _, Some value, _) | SemanticKind.UnionCase (_, _, Some value) -> useValue value Escape
            | SemanticKind.Set (_, value) | SemanticKind.FieldSet (_, _, value) | SemanticKind.IndexSet (_, _, value) -> useValue value Escape
            | SemanticKind.PatternBinding _ | SemanticKind.Literal _ | SemanticKind.Intrinsic _ -> ()
            // Membership in a module names declarations; it does not consume
            // their values. The Binding rule above separately checks storage
            // of module values, including mutable slots and anonymous closures.
            | SemanticKind.ModuleDef _ -> ()
            // A new consuming syntax must opt in with a proved use rule. It
            // cannot silently make an unrecognized borrowed use non-escaping.
            | _ -> node.Children |> List.iter (fun child -> useValue child Escape)

    let intrinsicArgument fn index =
        match target Set.empty fn with
        | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.BorrowedView } } -> index = 0
        | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Operators; Operation = "ignore" } } -> true
        | _ -> false
    let parameterAt fn index = parameters fn |> List.tryItem index |> Option.map (fun (_, _, id) -> id)
    // Callable staging preserves an explicit returned `fun` as a separate
    // application. Follow only an immediate result-as-callee chain: aliases,
    // stores and unknown consumers of an intermediate result are not completion.
    let rec completes seen required consumed application =
        if Set.contains application seen then false
        else
            let seen = Set.add application seen
            match SemanticGraph.tryGetNode application graph with
            | Some node ->
                match applySubst node.Type with
                | NativeType.TFun _ ->
                    match Map.tryFind application users |> Option.defaultValue [] with
                    | [] -> false
                    | uses -> uses |> List.forall (function
                        | Invoke (next, arguments) -> completes seen required (consumed + arguments) next
                        | _ -> false)
                | _ -> consumed >= required
            | None -> false
    let callCompletes application = completes Set.empty 0 0 application
    // Discharge a returned function only when every use of its enclosing
    // callable immediately completes the known chain, whether represented as
    // one source application or several applications at settled boundaries.
    // A declaration edge is not a stored closure value; all other storage,
    // unknown consumers and recursive use chains remain unproved.
    let immediatelyCompleted callable =
        let rec arity seen id =
            match target seen id with
            | Some { Id = lambda; Kind = SemanticKind.Lambda (parameters, body, _, _, _) } ->
                // A unit domain binds no PatternBinding, but still consumes an
                // argument. This is source call arity, before unit ABI erasure.
                max 1 parameters.Length + arity (Set.add lambda seen) body
            | _ -> 0
        let required = arity Set.empty callable
        let rec everyUse seen value =
            if Set.contains value seen then false
            else
                let seen = Set.add value seen
                match Map.tryFind value users |> Option.defaultValue [] with
                | [] -> false
                | uses -> uses |> List.forall (function
                    | Alias other | Declaration other -> everyUse seen other
                    | Invoke (application, arguments) -> completes Set.empty required arguments application
                    | _ -> false)
        everyUse Set.empty callable
    let rec safe (scoped: Set<NodeId>) seen value =
        if Set.contains value seen then false
        else
            let seen = Set.add value seen
            Map.tryFind value users |> Option.defaultValue []
            |> List.forall (function
                | Invoke _ -> true
                | Alias other | Capture other -> safe scoped seen other
                | ReturnedFunction callable -> immediatelyCompleted callable
                | Argument (fn, index, application) ->
                    callCompletes application && (intrinsicArgument fn index ||
                        (parameterAt fn index |> Option.exists (fun p -> Set.contains p scoped)))
                | Declaration _ | Escape -> false)
    let candidates =
        graph.Nodes.Values |> Seq.collect (fun node ->
            match node.Kind with
            | SemanticKind.Lambda (parameters, _, _, _, _) -> parameters |> Seq.choose (fun (_, ty, id) ->
                match applySubst ty with NativeType.TFun _ -> Some id | _ when BorrowedViews.isView ty -> Some id | _ -> None)
            | _ -> Seq.empty) |> Set.ofSeq
    let mutable scoped = declared
    let mutable changed = true
    while changed do
        let next = candidates |> Set.filter (safe scoped Set.empty) |> Set.union scoped
        changed <- next <> scoped
        scoped <- next

    let rec reachesDeclared seen id =
        if Set.contains id seen then false
        else
            let seen = Set.add id seen
            Map.tryFind id users |> Option.defaultValue [] |> List.exists (function
                | Alias other -> reachesDeclared seen other
                | Argument (fn, index, application) ->
                    callCompletes application &&
                    (parameterAt fn index |> Option.exists (fun p -> Set.contains p declared))
                | _ -> false)
    let rec capturesView seen id =
        if Set.contains id seen then false
        else
            let seen = Set.add id seen
            match target Set.empty id with
            | Some { Kind = SemanticKind.Lambda (_, _, captures, _, _) } ->
                captures |> List.exists (fun c -> BorrowedViews.isView c.Type || (c.SourceNodeId |> Option.exists (capturesView seen)))
            | Some node -> BorrowedViews.isView node.Type
            | _ -> false
    let stack =
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind with
            | SemanticKind.Lambda _ when
                safe scoped Set.empty node.Id &&
                (reachesDeclared Set.empty node.Id || capturesView Set.empty node.Id) &&
                // Immediate application proves that the borrowed view remains
                // within its mapping scope, not that an environment may die in
                // the returning function's stack frame. Preserve escaping placement.
                not (Map.tryFind node.Id users |> Option.defaultValue [] |> List.exists (function ReturnedFunction _ -> true | _ -> false)) -> Some node.Id
            | _ -> None) |> Set.ofSeq

    let rec whyUnsafe seen value =
        if Set.contains value seen then "the consumer chain is recursive and has no proved lifetime summary"
        else
            let seen = Set.add value seen
            Map.tryFind value users |> Option.defaultValue [] |> List.tryPick (function
                | Alias other | Capture other when not (safe scoped Set.empty other) -> Some (whyUnsafe seen other)
                | ReturnedFunction callable when not (immediatelyCompleted callable) ->
                    Some (sprintf "returned function %A is not immediately completed at every use" value)
                | Argument (_, index, application) when not (callCompletes application) -> Some (sprintf "argument %d enters a function whose returned value is not immediately completed" index)
                | Argument (fn, index, _) when not (intrinsicArgument fn index || (parameterAt fn index |> Option.exists (fun p -> Set.contains p scoped))) ->
                    let name = match SemanticGraph.tryGetNode fn graph with Some { Kind = SemanticKind.VarRef (name, _) } -> name | _ -> string fn
                    Some (sprintf "argument %d enters '%s', whose callback lifetime is not proved synchronous" index name)
                | Declaration _ | Escape -> Some (sprintf "value %A is stored or returned" value)
                | _ -> None)
            |> Option.defaultValue "the consumer lifetime cannot be proved"

    // A default/factory cannot hide a manufactured view inside a record or
    // generic container and expose it later through an ordinary projection.
    let aggregateFields =
        graph.Nodes.Values |> Seq.choose (fun candidate ->
            match candidate.Kind with
            | SemanticKind.TypeDef (name, TypeDefKind.RecordDef fields, _) -> Some (name, List.map snd fields)
            | SemanticKind.TypeDef (name, TypeDefKind.UnionDef cases, _) -> Some (name, cases |> List.collect (snd >> List.map snd))
            | _ -> None)
        |> Seq.groupBy fst
        |> Seq.map (fun (name, definitions) -> name, definitions |> Seq.collect snd |> Seq.toList)
        |> Map.ofSeq
    let rec containsView seen ty =
        if BorrowedViews.isView ty then true
        else
            match applySubst ty with
            | NativeType.TTuple (elements, _) -> elements |> List.exists (containsView seen)
            | NativeType.TApp (tc, arguments) ->
                arguments |> List.exists (containsView seen) ||
                (not (Set.contains tc.Name seen) &&
                 (Map.tryFind tc.Name aggregateFields |> Option.defaultValue []
                  |> List.exists (containsView (Set.add tc.Name seen))))
            | _ -> false
    for node in graph.Nodes.Values do
        if node.IsReachable then
            match node.Kind with
            | SemanticKind.Application _ when containsView Set.empty node.Type ->
                finding node "Borrowed views are supplied only as parameters of declared mapping scopes; no source constructor or returning factory is available."
            | _ -> ()
            if BorrowedViews.isView node.Type then
                match BorrowedViews.layout graph node.Type with Error message -> finding node message | Ok _ -> ()
                match node.Kind with
                | SemanticKind.PatternBinding _ when not (safe scoped Set.empty node.Id) ->
                    finding node ("A borrowed view escapes its mapping scope through storage, return, or a consumer without a synchronous lifetime contract: " + whyUnsafe Set.empty node.Id + ".")
                | _ -> ()
            match BorrowedViews.operation graph node.Id with
            | Some (_, _, _, Error message) -> finding node message
            | Some ("get", _, _, Ok view) when view.Access = "WriteOnly" -> finding node "This mapped view does not declare read access."
            | Some ("set", _, _, Ok view) when view.Access = "ReadOnly" -> finding node "This mapped view does not declare write access."
            | _ -> ()
    { Parameters = scoped; StackLambdas = stack; Findings = List.rev findings }

let private cache = ConditionalWeakTable<SemanticGraph, Reading>()
let read graph = cache.GetValue(graph, fun graph -> readUncached graph)
let isStackLambda graph lambda = Set.contains lambda (read graph).StackLambdas
