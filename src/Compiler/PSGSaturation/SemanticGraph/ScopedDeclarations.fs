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

type Reading = {
    Parameters: Set<NodeId>
    Participants: Map<NodeId, Set<NodeId>>
    Findings: DeclarationFinding list
}

let private readUncached (graph: SemanticGraph) =
    let mappings = MappedBindings.read graph
    let mutable findings = mappings.Findings
    let mutable participants = Map.empty
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
            descriptor.Name.Split('.') |> Array.last = "ScopedCallbackDescriptor"
        | _ -> false
    for node in graph.Nodes.Values do
        match node.Kind, List.tryLast node.Children with
        | SemanticKind.Binding _, Some body ->
            match recordOf graph body with
            | Some(descriptor, fields) when typeName descriptor = Some "ScopedCallbackDescriptor" ->
                match field "Binding" fields |> Option.bind (stringOf graph), field "Parameter" fields |> Option.bind (stringOf graph) with
                | Some bindingName, Some parameterName ->
                    match graph.Nodes.Values |> Seq.filter (fun candidate -> MappedBindings.qualifiedBindingName graph candidate = bindingName) |> Seq.toList with
                    | [binding] ->
                        match parameters Set.empty binding.Id |> List.filter (fun (name, _, _) -> name = parameterName) with
                        | [(_, ty, id)] ->
                            match applySubst ty with
                            | NativeType.TFun _ -> declare id [node.Id; descriptor.Id; binding.Id]
                            | _ -> finding descriptor "A ScopedCallbackDescriptor must name a function-valued parameter."
                        | [] -> finding descriptor (sprintf "Scoped callback parameter '%s.%s' is missing from the declared callable boundary." bindingName parameterName)
                        | _ -> finding descriptor (sprintf "Scoped callback parameter '%s.%s' is ambiguous." bindingName parameterName)
                    | _ -> finding descriptor (sprintf "Scoped callback binding '%s' is missing or ambiguous." bindingName)
                | _ -> finding descriptor "ScopedCallbackDescriptor requires literal Binding and Parameter names."
            | _ when annotatedScope node.Type ->
                finding node "ScopedCallbackDescriptor requires a well-typed quoted record body; check that its record fields are in scope."
            | _ -> ()
        | _ -> ()
    { Parameters = participants |> Map.keys |> Set.ofSeq; Participants = participants; Findings = findings }

let private cache = ConditionalWeakTable<SemanticGraph, Reading>()
let read graph = cache.GetValue(graph, fun graph -> readUncached graph)
