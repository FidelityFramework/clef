// SPDX-License-Identifier: MIT
/// Immutable checker-issued measure instances, read before callable ingress.
/// Equal physical representations do not establish a source instantiation.
module Clef.Compiler.PSGSaturation.SemanticGraph.SchemeInstances

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

type Instance = {
    Occurrence: NodeId
    Declaration: NodeId
    Parameters: TypeParam list
    Arguments: NativeType list
    Signature: NativeType
    Participants: Set<NodeId>
}

let publicType (node: SemanticNode) =
    let ty =
        match node.Metadata.TryFind ClosureMetadata.SourceSignature with
        | Some(MetadataValue.Type ty) -> ty
        | _ -> node.Type
    match applySubst ty with NativeType.TForall(_, body) -> body | ty -> ty

let scheme (node: SemanticNode) =
    match node.Metadata.TryFind SchemeMetadata.Declaration with
    | Some(MetadataValue.Type(NativeType.TForall(parameters, body))) -> Some(parameters, body)
    | _ -> None

let measureParameters parameters =
    not (List.isEmpty parameters) &&
    (parameters |> List.map (fun (parameter: TypeParam) -> parameter.Id) |> Set.ofList).Count = parameters.Length &&
    (parameters |> List.forall (fun parameter -> parameter.Kind = TypeParamKind.Measure))

let private arguments (node: SemanticNode) (parameters: TypeParam list) =
    let expected = parameters |> List.indexed |> List.map (fun (ordinal, _) -> SchemeMetadata.argument ordinal) |> Set.ofList
    let actual = node.Metadata |> Map.keys |> Seq.filter (fun key -> key.StartsWith("Scheme.Argument.", System.StringComparison.Ordinal)) |> Set.ofSeq
    if actual <> expected then None else
    let values = parameters |> List.indexed |> List.map (fun (ordinal, parameter) ->
        match node.Metadata.TryFind (SchemeMetadata.argument ordinal) with
        | Some(MetadataValue.Type(NativeType.TMeasure _ as argument)) when parameter.Kind = TypeParamKind.Measure -> Some argument
        | _ -> None)
    if List.forall Option.isSome values then Some(List.choose id values) else None

let reader (graph: SemanticGraph) =
    let sourceDeclaration = ClosureEnvironments.trySourceDeclaration graph
    fun occurrence ->
        match graph.Nodes.TryFind occurrence with
        | Some ({ Kind = SemanticKind.VarRef(_, Some target) } as node) ->
            let declaration = sourceDeclaration occurrence |> Option.defaultValue target
            match node.Metadata.TryFind SchemeMetadata.Definition, scheme node, graph.Nodes.TryFind declaration with
            | Some(MetadataValue.NodeId recorded), Some(parameters, body), Some ({ Kind = SemanticKind.Binding(_, false, _, _) } as owner)
                when recorded = declaration && measureParameters parameters && scheme owner = Some(parameters, body) &&
                     publicType owner = applySubst body ->
                arguments node parameters |> Option.bind (fun values ->
                    if applySubst (instantiate parameters values body) <> publicType node then None else
                    Some { Occurrence = occurrence; Declaration = declaration; Parameters = parameters
                           Arguments = values; Signature = body; Participants = Set.ofList [occurrence; declaration; target] })
            | _ -> None
        | _ -> None
