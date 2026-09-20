// SPDX-License-Identifier: MIT
/// Exact startup execution and storage intent, read from resident Baker incidence.
/// Lexical module membership never supplies execution ownership or residence.
module Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Platform = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

[<Literal>]
let EntrySymbol = "ProgramInitialization.EntrySymbol"

type Initializer = { Module: NodeId; Binding: NodeId; Initializer: NodeId; Ordinal: int }
type Plan = {
    EntryBinding: NodeId
    EntryLambda: NodeId
    SourceBinding: NodeId
    SourceLambda: NodeId
    OriginalBody: NodeId
    Spine: NodeId
    EntryCall: NodeId
    Symbol: string
    Initializers: Initializer list
    ValueBindings: Set<NodeId>
}

let private edges role (graph: SemanticGraph) =
    graph.Edges |> List.filter (fun edge -> edge.Class = EdgeClass.Provenance && edge.Role = role)

let private single = function [value] -> Some value | _ -> None

/// A malformed or incomplete joint relation is not a startup plan. Source
/// checking reports such residuals before native consumers use this projection.
let read (graph: SemanticGraph) : Plan option =
    match edges EdgeRole.ProgramInitialization graph |> single with
    | Some { Sources = [entry; source; sourceLambda; originalBody; entryLambda]; Target = spine } ->
        match graph.Nodes.TryFind entry, graph.Nodes.TryFind source, graph.Nodes.TryFind sourceLambda,
              graph.Nodes.TryFind entryLambda, graph.Nodes.TryFind spine with
        | Some ({ Kind = SemanticKind.Binding("__clef_program_entry", false, false, Some DeclRoot.EntryPoint); Children = [entryChild] } as entryNode),
          Some { Kind = SemanticKind.Binding(_, _, _, None); Children = [sourceChild] },
          Some { Kind = SemanticKind.Lambda(_, actualOriginalBody, _, _, _) },
          Some { Kind = SemanticKind.Lambda(_, actualSpine, [], _, LambdaContext.RegularClosure) },
          Some { Kind = SemanticKind.Sequential actions }
            when entryChild = entryLambda && sourceChild = sourceLambda && actualOriginalBody = originalBody
                 && actualSpine = spine && entryLambda <> sourceLambda
                 && (graph.DeclarationRoots |> List.contains (entry, DeclRoot.EntryPoint)) ->
            let calls = edges EdgeRole.ProgramEntryCall graph
                        |> List.filter (fun edge -> edge.Sources = [entry; source; sourceLambda; entryLambda])
            match calls |> single with
            | Some callEdge ->
                let rec executable seen id =
                    if Set.contains id seen then seen else
                    let seen = Set.add id seen
                    match graph.Nodes.TryFind id with
                    | Some { Kind = SemanticKind.Lambda _ | SemanticKind.SeqExpr _ | SemanticKind.LazyExpr _ } -> seen
                    | Some node ->
                        kindEdges id node.Kind |> List.filter Hyperedge.isStructural |> List.collect _.Sources
                        |> List.append (match node.Kind with SemanticKind.Binding _ | SemanticKind.Intrinsic _ -> node.Children | _ -> [])
                        |> List.fold executable seen
                    | None -> seen
                let callValid =
                    match graph.Nodes.TryFind callEdge.Target with
                    | Some { Kind = SemanticKind.Application(callee, arguments) } ->
                        match graph.Nodes.TryFind callee, graph.Nodes.TryFind sourceLambda with
                        | Some { Kind = SemanticKind.VarRef(_, Some target) },
                          Some { Kind = SemanticKind.Lambda(parameters, _, _, _, _) } ->
                            target = source && parameters.Length = arguments.Length
                            && (executable Set.empty spine).Contains callEdge.Target
                        | _ -> false
                    | _ -> false
                let rows = edges EdgeRole.ProgramInitializer graph |> List.filter (fun edge -> edge.Target = spine)
                let initializers =
                    rows |> List.choose (fun edge ->
                        match edge.Sources with
                        | [moduleId; binding; initializer; owner] when owner = entryLambda ->
                            match graph.Nodes.TryFind moduleId, graph.Nodes.TryFind binding with
                            | Some { Kind = SemanticKind.ModuleDef(_, members); Children = [] },
                              Some { Kind = SemanticKind.Binding _; Children = [value] }
                                when (members |> List.contains binding) && value = initializer ->
                                Some { Module = moduleId; Binding = binding; Initializer = initializer; Ordinal = edge.Ordinal }
                            | _ -> None
                        | _ -> None)
                    |> List.sortBy _.Ordinal
                let initializersValid =
                    let rec ordered seen id =
                        if Set.contains id seen then [] else
                        match graph.Nodes.TryFind id with
                        | Some { Kind = SemanticKind.Sequential values } -> values |> List.collect (ordered (Set.add id seen))
                        | _ -> [id]
                    let execution = actions |> List.collect (ordered Set.empty)
                    let expected = initializers |> List.map _.Binding
                    let actual = execution |> List.filter (fun id -> List.contains id expected)
                    let afterInitializers =
                        match List.tryLast expected with
                        | None -> execution
                        | Some last ->
                            execution |> List.tryFindIndex ((=) last)
                            |> Option.map (fun index -> List.skip (index + 1) execution) |> Option.defaultValue []
                    rows.Length = initializers.Length
                    && (initializers |> List.mapi (fun ordinal row -> row.Ordinal = ordinal) |> List.forall id)
                    && actual = expected
                    && (afterInitializers |> List.exists (fun id -> (executable Set.empty id).Contains callEdge.Target))
                let intents = edges EdgeRole.ProgramValueIntent graph
                              |> List.filter (fun edge -> edge.Sources |> List.contains spine)
                let values = intents |> List.choose (fun edge ->
                    initializers |> List.tryFind (fun row ->
                        row.Binding = edge.Target && row.Ordinal = edge.Ordinal && edge.Sources = [entryLambda; spine; row.Initializer])
                    |> Option.map _.Binding)
                let symbol = entryNode.Metadata.TryFind EntrySymbol |> Option.bind (function MetadataValue.String name when name <> "" -> Some name | _ -> None)
                if callValid && initializersValid && values.Length = intents.Length && symbol.IsSome then
                    Some { EntryBinding = entry; EntryLambda = entryLambda; SourceBinding = source
                           SourceLambda = sourceLambda; OriginalBody = originalBody; Spine = spine
                           EntryCall = callEdge.Target; Symbol = symbol.Value; Initializers = initializers
                           ValueBindings = Set.ofList values }
                else None
            | None -> None
        | _ -> None
    | _ -> None

/// Intent is separate from physical authority: missing authority cannot change
/// a program slot back into an activation-local binding in a witness.
let isSlotBinding (graph: SemanticGraph) binding =
    read graph |> Option.exists (fun plan -> plan.ValueBindings.Contains binding)

type ValueAuthority = { Plan: Plan; Initializer: Initializer; Platform: Platform.DeclaredPlatform; Space: Platform.DeclaredSpace; Evidence: Hyperedge }

let tryValueAuthority (graph: SemanticGraph) binding : ValueAuthority option =
    read graph |> Option.bind (fun plan ->
        plan.Initializers |> List.tryFind (fun row -> row.Binding = binding && plan.ValueBindings.Contains binding)
        |> Option.bind (fun row ->
            (Platform.read graph).Platform |> Option.bind (fun platform ->
                platform.ProgramLifetime |> Option.bind (fun designation ->
                    designation.Mutable |> Option.bind (fun mutableSpace ->
                        edges EdgeRole.ProgramValue graph
                        |> List.filter (fun edge ->
                            edge.Target = binding && edge.Ordinal = row.Ordinal
                            && edge.Sources = [plan.EntryLambda; plan.Spine; row.Initializer; platform.Node
                                               designation.Node; mutableSpace.Reference; mutableSpace.Space.Node])
                        |> single |> Option.map (fun evidence ->
                            { Plan = plan; Initializer = row; Platform = platform; Space = mutableSpace.Space; Evidence = evidence }))))))
