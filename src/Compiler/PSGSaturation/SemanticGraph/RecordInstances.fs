// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Immutable field and identity reads for instantiated record types.
/// Dimensional_Range_Design.md §3.3 and ruling 2: symbolic type identity is preserved,
/// fields are instantiated in CCS, and Placement settles the bytes the witness reads.
module Clef.Compiler.PSGSaturation.SemanticGraph.RecordInstances

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open System.Runtime.CompilerServices

let private parameter = function
    | NativeType.TVar parameter | NativeType.TNum (CarrierRef.CVar parameter, _) -> Some parameter
    | NativeType.TMeasure dimension when dimension.Bases.IsEmpty ->
        match Map.toList dimension.Vars with
        | [variable, 1] -> Some (measureCellOf variable)
        | _ -> None
    | _ -> None

let private definitionIndexes = ConditionalWeakTable<SemanticGraph, Map<NominalTypeIdentity, SemanticNode>>()

/// Exact declarations, indexed once per immutable graph snapshot. Abbreviations carry the
/// abbreviated type on their node and therefore cannot establish its declaration identity.
let definitions (graph: SemanticGraph) =
    definitionIndexes.GetValue(graph, fun graph ->
        graph.Nodes.Values
        |> Seq.choose (fun node ->
            match node.Kind, node.Type with
            | SemanticKind.TypeDef (_, (TypeDefKind.RecordDef _ | TypeDefKind.UnionDef _), _), NativeType.TApp (declared, _)
            | SemanticKind.TypeDef (_, (TypeDefKind.RecordDef _ | TypeDefKind.UnionDef _), _), NativeType.TUnion (declared, _) ->
                Some(NominalTypeIdentity.ofConstructor declared, node)
            | _ -> None)
        |> Map.ofSeq)

/// Lexical indexes can contain a short-name alias. Definition authority is the exact
/// constructor identity carried by the type, independent of which alias was indexed last.
let tryDefinition (identity: NominalTypeIdentity) (graph: SemanticGraph) =
    (definitions graph).TryFind identity

let tryUnionCases (ty: NativeType) (graph: SemanticGraph) =
    match applySubst ty with
    | NativeType.TUnion (_, cases) -> Some (cases |> List.map (fun case -> case.Name, case.Fields))
    | NativeType.TApp (tycon, arguments) ->
        tryDefinition (NominalTypeIdentity.ofConstructor tycon) graph
        |> Option.bind (fun node ->
            match node.Kind, canonicalizeVars node.Type with
            | SemanticKind.TypeDef (_, TypeDefKind.UnionDef cases, _), NativeType.TApp (_, parameters)
                when parameters.Length = arguments.Length ->
                let declared = parameters |> List.choose parameter
                if declared.Length <> parameters.Length then None
                else
                    cases |> List.map (fun (name, fields) ->
                        name, fields |> List.map (fun (field, ty) -> field, instantiate declared arguments (canonicalizeVars ty)))
                    |> Some
            | _ -> None)
    | _ -> None

/// Read a record instance's fields without binding its declaration's type variables.
/// The declaration's TApp records parameter order (including phantom parameters), whereas
/// the order of variables encountered in fields need not. Reuse the type checker's
/// dimension/carrier-aware substitution; placement and witnesses read the same instance.
let tryFields (ty: NativeType) (graph: SemanticGraph) : (string * NativeType) list option =
    match applySubst ty with
    | NativeType.TApp (tycon, args) when TypeLayout.baseLayout tycon.Layout = TypeLayout.Record || tycon.FieldCount > 0 ->
        let definition = tryDefinition (NominalTypeIdentity.ofConstructor tycon) graph
        definition |> Option.map (fun node ->
            match node.Kind, canonicalizeVars node.Type with
            | SemanticKind.TypeDef (_, TypeDefKind.RecordDef fields, _), NativeType.TApp (_, parameters) ->
                let parameter = function
                    | NativeType.TVar p | NativeType.TNum (CarrierRef.CVar p, _) -> p
                    | NativeType.TMeasure dimension when dimension.Bases.IsEmpty ->
                        match Map.toList dimension.Vars with
                        | [variable, 1] -> measureCellOf variable
                        | _ -> failwithf "Record '%s' has a non-parameter measure in its declaration" tycon.Name
                    | _ -> failwithf "Record '%s' has a resolved value in its declaration's parameter list" tycon.Name
                let parameters = parameters |> List.map parameter
                fields |> List.map (fun (name, fieldType) ->
                    name, instantiate parameters args (canonicalizeVars fieldType))
            | _ -> failwith "Record definition changed while reading its instance")
    | _ -> None

/// Exact instance identity, including nominal owner, native kind and generic dimensions.
let layoutKey (ty: NativeType) : TypeIdentity =
    Clef.Compiler.NativeTypedTree.TypeIdentities.ofType ty
