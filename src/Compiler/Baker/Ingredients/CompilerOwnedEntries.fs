// SPDX-License-Identifier: MIT
/// Current source incidence for compiler-owned entries. This reader establishes
/// module code residence only. Target conventions belong to the contract recipe.
module Clef.Compiler.Baker.Ingredients.CompilerOwnedEntries

open System.Runtime.CompilerServices
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

type Entry = {
    Lifetime: ProgramImageCodeLifetime
    Symbol: string
    Parameters: (string * NativeType * NodeId) list
    Result: NodeId
}

type Formation = {
    Formation: NodeId
    Entry: Entry
}

let payload ty =
    match applySubst ty with
    | NativeType.TApp(constructor, [signature]) when constructor.NTUKind = Some NTUKind.NTUfnptr ->
        match applySubst signature with NativeType.TFun _ -> Some signature | _ -> None
    | _ -> None

/// A binding retains its exact module membership and physical implementation.
/// Parent metadata alone cannot establish residence in a source module.
let private entryAt (graph: SemanticGraph) (binding: SemanticNode) =
    match binding.Kind, binding.Children, binding.Parent with
    | SemanticKind.Binding(name, false, _, _), [implementation], Some scope
        when not (binding.Metadata.ContainsKey "FidelityExtern.Library" || binding.Metadata.ContainsKey "FidelityExtern.Symbol") ->
        match graph.Nodes.TryFind scope, graph.Nodes.TryFind implementation with
        | Some { Kind = SemanticKind.ModuleDef(moduleName, members) },
          Some ({ Kind = SemanticKind.Lambda(parameters, result, [], _, LambdaContext.RegularClosure); IsReachable = true } as code)
            when (members |> List.filter ((=) binding.Id) |> List.length) = 1 &&
                 not (code.Metadata.ContainsKey "FidelityExtern.Library" || code.Metadata.ContainsKey "FidelityExtern.Symbol") ->
            Some {
                Lifetime = { Module = scope; Binding = binding.Id; Implementation = implementation }
                Symbol = moduleName + "." + name
                Parameters = parameters
                Result = result
            }
        | _ -> None
    | _ -> None

// One local declaration index per immutable source reading. It retains every
// candidate so duplicate bindings of one implementation remain ambiguous.
let private entriesCache = ConditionalWeakTable<SemanticGraph, Map<NodeId, Entry list>>()
let private entries graph =
    entriesCache.GetValue(graph, fun graph ->
        graph.Nodes.Values
        |> Seq.choose (entryAt graph)
        |> Seq.groupBy (fun entry -> entry.Lifetime.Implementation)
        |> Seq.map (fun (implementation, candidates) -> implementation, List.ofSeq candidates)
        |> Map.ofSeq)

let tryImplementation graph implementation =
    entries graph |> Map.tryFind implementation
    |> Option.bind (function [entry] -> Some entry | _ -> None)

let private unannotated (graph: SemanticGraph) start =
    let rec read seen id =
        if Set.contains id seen then None else
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> read (Set.add id seen) inner
        | value -> value
    read Set.empty start

/// Resolve only the actual ofFunction application and immutable source aliases.
/// Field projection has its own aggregate row and cannot manufacture a formation.
let tryFormation (graph: SemanticGraph) occurrence =
    let rec read seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> read seen inner
        | Some { Kind = SemanticKind.VarRef(_, Some binding) } -> read seen binding
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> read seen value
        | Some { Kind = SemanticKind.Application(fn, [argument]); Type = ty } when payload ty |> Option.isSome ->
            match unannotated graph fn, unannotated graph argument with
            | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.FnPtr; Operation = "ofFunction" } },
              Some { Kind = SemanticKind.VarRef(_, Some binding) } ->
                graph.Nodes.TryFind binding |> Option.bind (entryAt graph)
                |> Option.bind (fun entry ->
                    match tryImplementation graph entry.Lifetime.Implementation with
                    | Some current when current = entry -> Some { Formation = id; Entry = entry }
                    | _ -> None)
            | _ -> None
        | _ -> None
    read Set.empty occurrence

let lifetimeNodes (lifetime: ProgramImageCodeLifetime) =
    [lifetime.Module; lifetime.Binding; lifetime.Implementation]

let lifetimeParticipants identity lifetime : Participant list =
    lifetimeNodes lifetime |> List.mapi (fun ordinal node ->
        { Node = node; Role = ParticipantRole.CallableLifetime; Ordinal = ordinal; Group = identity })

let current graph (lifetime: ProgramImageCodeLifetime) =
    tryImplementation graph lifetime.Implementation
    |> Option.exists (fun entry -> entry.Lifetime = lifetime)
