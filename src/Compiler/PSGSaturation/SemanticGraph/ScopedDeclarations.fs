// SPDX-License-Identifier: MIT
/// Source declarations of synchronous callback activation. These facts do not
/// infer a lifetime from observed callers; they name the library's obligation
/// and the graph participants on which that obligation depends.
module Clef.Compiler.PSGSaturation.SemanticGraph.ScopedDeclarations

open System.Runtime.CompilerServices
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

type Activation = {
    Scope: NodeId
    Binding: NodeId
    Parameter: NodeId
    Extent: BoundaryCallbackExtent
    Participants: Set<NodeId>
}

type Reading = {
    Parameters: Set<NodeId>
    Participants: Map<NodeId, Set<NodeId>>
    Activations: Map<NodeId, Activation>
    Findings: DeclarationFinding list
}

let private readUncached (graph: SemanticGraph) =
    let mappings = MappedBindings.read graph
    let mutable findings = mappings.Findings
    let mutable participants = Map.empty
    let mutable activations = Map.empty
    let rec dependencies seen pending =
        match pending with
        | [] -> seen
        | id :: rest when Set.contains id seen -> dependencies seen rest
        | id :: rest ->
            let children = graph.Nodes.TryFind id |> Option.map _.Children |> Option.defaultValue []
            dependencies (Set.add id seen) (children @ rest)
    let declare parameter roots =
        let related = dependencies Set.empty roots |> Set.add parameter
        let previous = participants.TryFind parameter |> Option.defaultValue Set.empty
        participants <- participants.Add(parameter, Set.union previous related)
    for mapping in mappings.Mappings do
        declare mapping.CallbackParameter [mapping.Node; mapping.Binding; mapping.AcquireBinding; mapping.ReleaseBinding]
    let finding (node: SemanticNode) message =
        findings <- { Node = node.Id; Range = node.Range; Defect = DeclarationDefect.Invalid; Message = message } :: findings
    let rec target seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.VarRef(_, Some other) | SemanticKind.TypeAnnotation(other, _) } -> target seen other
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> target seen value
        | other -> other
    let rec parameters seen id =
        match target seen id with
        | Some { Id = lambda; Kind = SemanticKind.Lambda(formals, body, _, _, _) } ->
            // Before curry normalization, only synthetic declaration tails
            // extend this boundary. An explicit returned function has its own
            // activation and cannot receive this declaration's callback contract.
            match graph.Nodes.TryFind body with
            | Some { Kind = SemanticKind.Lambda _; Metadata = metadata }
                when [ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
                     |> List.forall (fun key -> metadata.TryFind key <> Some(MetadataValue.Bool true)) ->
                formals @ parameters (Set.add lambda seen) body
            | _ -> formals
        | _ -> []
    let annotatedScope ty =
        match applySubst ty with
        | NativeType.TApp(quote, [NativeType.TApp(descriptor, _)]) when quote.Name = "Expr" ->
            ["ScopedCallbackDescriptor"; "ProcessExitCallbackDescriptor"] |> List.contains (descriptor.Name.Split('.') |> Array.last)
        | _ -> false
    for node in graph.Nodes.Values do
        match node.Kind, List.tryLast node.Children with
        | SemanticKind.Binding _, Some body ->
            match recordOf graph body with
            | Some(descriptor, fields) when typeName descriptor = Some "ScopedCallbackDescriptor" || typeName descriptor = Some "ProcessExitCallbackDescriptor" ->
                match field "Binding" fields |> Option.bind (stringOf graph), field "Parameter" fields |> Option.bind (stringOf graph) with
                | Some bindingName, Some parameterName ->
                    match graph.Nodes.Values |> Seq.filter (fun candidate -> MappedBindings.qualifiedBindingName graph candidate = bindingName) |> Seq.toList with
                    | [binding] ->
                        match parameters Set.empty binding.Id |> List.filter (fun (name, _, _) -> name = parameterName) with
                        | [(_, ty, id)] ->
                            let callable =
                                match applySubst ty with
                                | NativeType.TFun _ -> true
                                | NativeType.TApp(constructor, [signature]) when constructor.NTUKind = Some NTUKind.NTUfnptr ->
                                    match applySubst signature with NativeType.TFun _ -> true | _ -> false
                                | _ -> optionalEntrySignature ty |> Option.isSome
                            let scope = valuePath graph body |> Option.map snd |> Option.defaultValue [] |> List.filter(fun id ->
                                match graph.Nodes[id].Kind with SemanticKind.Quote _ -> true | _ -> false)
                            let extent =
                                if typeName descriptor = Some "ScopedCallbackDescriptor" then Some(BoundaryCallbackExtent.DuringCall, []) else
                                match field "SuccessStatus" fields |> Option.bind (int64Of graph), field "ExitBinding" fields |> Option.bind (optionOf graph) with
                                | Some status, Some selected when status >= int64 System.Int32.MinValue && status <= int64 System.Int32.MaxValue ->
                                    match selected with
                                    | None -> Some(BoundaryCallbackExtent.ProcessExit(None, int status), [])
                                    | Some source ->
                                        match stringOf graph source with
                                        | Some name ->
                                            match graph.Nodes.Values |> Seq.filter(fun candidate -> MappedBindings.qualifiedBindingName graph candidate = name) |> Seq.toList with
                                            | [{ Kind = SemanticKind.Binding(_, false, _, _); Id = anchor }] ->
                                                Some(BoundaryCallbackExtent.ProcessExit(Some anchor, int status), [source])
                                            | _ -> finding descriptor "ProcessExitCallbackDescriptor ExitBinding must resolve one current immutable declaration."; None
                                        | _ -> finding descriptor "ProcessExitCallbackDescriptor ExitBinding requires an exact literal declaration name."; None
                                | _ -> finding descriptor "ProcessExitCallbackDescriptor requires signed32 SuccessStatus and an explicit optional ExitBinding."; None
                            match callable, scope, extent with
                            | true, _, Some(BoundaryCallbackExtent.ProcessExit _, _) when optionalEntrySignature ty |> Option.isSome ->
                                finding descriptor "Optional native entries require a during-call activation; process-exit optional callbacks are not admitted."
                            | true, [quote], Some(extent, extra) ->
                                let related = dependencies Set.empty (node.Id :: descriptor.Id :: binding.Id :: extra) |> Set.add id
                                let related = match extent with BoundaryCallbackExtent.ProcessExit(Some anchor,_) -> related.Add anchor | _ -> related
                                activations <- activations.Add(node.Id, { Scope=quote; Binding=binding.Id; Parameter=id; Extent=extent; Participants=related })
                                match extent with
                                | BoundaryCallbackExtent.DuringCall -> declare id [node.Id; descriptor.Id; binding.Id]
                                | BoundaryCallbackExtent.ProcessExit _ -> ()
                            | false, _, _ -> finding descriptor "A callback activation descriptor must name a function-valued parameter."
                            | _, [_], None -> ()
                            | _ -> finding descriptor "A callback activation descriptor requires its exact immutable source quotation."
                        | [] -> finding descriptor (sprintf "Scoped callback parameter '%s.%s' is missing from the declared callable boundary." bindingName parameterName)
                        | _ -> finding descriptor (sprintf "Scoped callback parameter '%s.%s' is ambiguous." bindingName parameterName)
                    | _ -> finding descriptor (sprintf "Scoped callback binding '%s' is missing or ambiguous." bindingName)
                | _ -> finding descriptor "ScopedCallbackDescriptor requires literal Binding and Parameter names."
            | _ when annotatedScope node.Type ->
                finding node "ScopedCallbackDescriptor requires a well-typed quoted record body; check that its record fields are in scope."
            | _ -> ()
        | _ -> ()
    { Parameters = participants |> Map.keys |> Set.ofSeq; Participants = participants; Activations=activations; Findings = findings }

let private cache = ConditionalWeakTable<SemanticGraph, Reading>()
let read graph = cache.GetValue(graph, fun graph -> readUncached graph)
