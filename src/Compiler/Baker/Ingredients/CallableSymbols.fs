// SPDX-License-Identifier: MIT
/// Observe current callable names without declaring code or allocating identity.
/// Aggregate evidence and callable declaration settlement share this policy.
module Clef.Compiler.Baker.Ingredients.CallableSymbols

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let private bindingName (graph: SemanticGraph) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Binding(name, _, _, _) ->
        match node.Parent |> Option.bind graph.Nodes.TryFind with
        | Some { Kind = SemanticKind.ModuleDef(moduleName, _) } -> Some(CallableSymbolName.ModuleBinding(moduleName, name))
        | _ when node.Parent.IsSome -> Some(CallableSymbolName.LocalBinding(node.Id, name))
        | _ -> Some(CallableSymbolName.RootBinding name)
    | _ -> None

let rec nameOf (graph: SemanticGraph) identity =
    graph.Nodes.TryFind identity |> Option.bind (fun node ->
        match node.Kind with
        | SemanticKind.Binding _ -> bindingName graph node
        | SemanticKind.Lambda _ ->
            let anonymous =
                graph.Codata.Value.Closures.ContainsKey node.Id &&
                ([ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
                 |> List.exists (fun key -> node.Metadata.TryFind key = Some(MetadataValue.Bool true)))
            let inherited =
                if anonymous then None else
                node.Parent |> Option.bind graph.Nodes.TryFind |> Option.bind (fun parent ->
                    match parent.Kind with
                    | SemanticKind.Binding _ -> bindingName graph parent
                    // Preserve declaration settlement's prior ordered map fold:
                    // all bindings were present, and only earlier lambdas had
                    // supplied symbols. Descending identities also bound this
                    // local observation without a graph-wide declaration scan.
                    | SemanticKind.Lambda _ when parent.Id < node.Id -> nameOf graph parent.Id
                    | _ -> None)
            Some(inherited |> Option.defaultValue (CallableSymbolName.Anonymous node.Id))
        | _ -> None)

let observe (graph: SemanticGraph) =
    graph.Nodes |> Map.toSeq |> Seq.choose (fun (identity, _) ->
        nameOf graph identity |> Option.map (fun name -> identity, name)) |> Map.ofSeq
