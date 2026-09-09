/// Synchronous callback contracts and bounded borrowed-value use. Declarations
/// are library obligations; inferred summaries accept only invocation, aliases,
/// and calls to other proven synchronous consumers. Stores/returns are escapes.
module Clef.Compiler.PSGSaturation.SemanticGraph.ScopedCallbacks

open System.Runtime.CompilerServices
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

type private Use = Alias of NodeId | Argument of NodeId * int * bool | Invoke | Capture of NodeId | Escape
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
    for node in graph.Nodes.Values do
        if node.IsReachable then
            match node.Kind with
            | SemanticKind.VarRef (_, Some source) | SemanticKind.TypeAnnotation (source, _) -> useValue source (Alias node.Id)
            | SemanticKind.Binding (_, mutableValue, _, _) ->
                List.tryLast node.Children |> Option.iter (fun source -> useValue source (if mutableValue || moduleBinding node then Escape else Alias node.Id))
            | SemanticKind.Application (fn, arguments) ->
                useValue fn Invoke
                let complete = match applySubst node.Type with NativeType.TFun _ -> false | _ -> true
                arguments |> List.iteri (fun index value -> useValue value (Argument (fn, index, complete)))
            | SemanticKind.Lambda (_, body, captures, _, _) ->
                useValue body Escape
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
            // A new consuming syntax must opt in with a proved use rule. It
            // cannot silently make an unrecognized borrowed use non-escaping.
            | _ -> node.Children |> List.iter (fun child -> useValue child Escape)

    let intrinsicArgument fn index =
        match target Set.empty fn with
        | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.BorrowedView } } -> index = 0
        | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Operators; Operation = "ignore" } } -> true
        | _ -> false
    let parameterAt fn index = parameters fn |> List.tryItem index |> Option.map (fun (_, _, id) -> id)
    let rec safe (scoped: Set<NodeId>) seen value =
        if Set.contains value seen then false
        else
            let seen = Set.add value seen
            Map.tryFind value users |> Option.defaultValue []
            |> List.forall (function
                | Invoke -> true
                | Alias other | Capture other -> safe scoped seen other
                | Argument (fn, index, complete) ->
                    complete && (intrinsicArgument fn index ||
                        (parameterAt fn index |> Option.exists (fun p -> Set.contains p scoped)))
                | Escape -> false)
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
                | Argument (fn, index, complete) ->
                    complete &&
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
            | SemanticKind.Lambda _ when safe scoped Set.empty node.Id && (reachesDeclared Set.empty node.Id || capturesView Set.empty node.Id) -> Some node.Id
            | _ -> None) |> Set.ofSeq

    let rec whyUnsafe seen value =
        if Set.contains value seen then "the consumer chain is recursive and has no proved lifetime summary"
        else
            let seen = Set.add value seen
            Map.tryFind value users |> Option.defaultValue [] |> List.tryPick (function
                | Alias other | Capture other when not (safe scoped Set.empty other) -> Some (whyUnsafe seen other)
                | Argument (_, index, complete) when not complete -> Some (sprintf "argument %d enters a partially applied function" index)
                | Argument (fn, index, _) when not (intrinsicArgument fn index || (parameterAt fn index |> Option.exists (fun p -> Set.contains p scoped))) ->
                    let name = match SemanticGraph.tryGetNode fn graph with Some { Kind = SemanticKind.VarRef (name, _) } -> name | _ -> string fn
                    Some (sprintf "argument %d enters '%s', whose callback lifetime is not proved synchronous" index name)
                | Escape -> Some (sprintf "value %A is stored or returned" value)
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
