// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// The lambda each declaration root names, with the root's flavour: a root Binding's Lambda
/// child, a root Lambda itself, or the root Bindings of a root module (the `main` binding counts
/// as an entry point; a hardware module binding is structural and names no lambda). A graph fact
/// Composer's emission reads (`Codata.DeclarationRootLambdas`).
module Clef.Compiler.PSGSaturation.SemanticGraph.Roots

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

let declarationRootLambdas (graph: SemanticGraph) : Map<NodeId, DeclRoot> =
    let lambdaChild (node: SemanticNode) =
        match node.Children with
        | lambdaId :: _ -> Some lambdaId
        | [] -> None
    graph.DeclarationRoots
    |> List.collect (fun (rootId, rootKind) ->
        match Map.tryFind rootId graph.Nodes with
        | Some ({ Kind = SemanticKind.Binding (_, _, _, Some dr) } as node) ->
            lambdaChild node |> Option.map (fun l -> (l, dr)) |> Option.toList
        | Some { Kind = SemanticKind.Lambda _ } -> [ (rootId, rootKind) ]
        | Some { Kind = SemanticKind.ModuleDef (_, memberIds) } ->
            memberIds |> List.choose (fun memberId ->
                match Map.tryFind memberId graph.Nodes with
                | Some { Kind = SemanticKind.Binding (_, _, _, Some DeclRoot.HardwareModule) } -> None
                | Some ({ Kind = SemanticKind.Binding (_, _, _, Some dr) } as m) -> lambdaChild m |> Option.map (fun l -> (l, dr))
                | Some ({ Kind = SemanticKind.Binding (name, _, _, None) } as m) when name = "main" ->
                    lambdaChild m |> Option.map (fun l -> (l, DeclRoot.EntryPoint))
                | _ -> None)
        | _ -> [])
    |> Map.ofList
