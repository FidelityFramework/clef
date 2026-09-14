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

/// Read a record instance's fields without binding its declaration's type variables.
/// The declaration's TApp records parameter order (including phantom parameters), whereas
/// the order of variables encountered in fields need not. Reuse the type checker's
/// dimension/carrier-aware substitution; placement and witnesses read the same instance.
let tryFields (ty: NativeType) (graph: SemanticGraph) : (string * NativeType) list option =
    match applySubst ty with
    | NativeType.TApp (tycon, args) when TypeLayout.baseLayout tycon.Layout = TypeLayout.Record || tycon.FieldCount > 0 ->
        let matches (node: SemanticNode) =
            match node.Kind, node.Type with
            | SemanticKind.TypeDef (_, TypeDefKind.RecordDef _, _), NativeType.TApp (declared, _) ->
                declared.Name = tycon.Name && declared.Module = tycon.Module
            | _ -> false
        let definition =
            match SemanticGraph.recallType tycon.Name graph |> Option.bind (fun id -> SemanticGraph.tryGetNode id graph) with
            | Some node when matches node -> Some node
            | _ -> graph.Nodes |> Map.values |> Seq.tryFind matches
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

/// Identity for an instantiated record's settled layout. Declaration names remain the
/// keys for non-generic records and declared boundaries. Generic instances retain module,
/// carrier and dimension identity; display rendering alone omits module qualifications.
let layoutKey (ty: NativeType) : string =
    let named (tc: TypeConRef) = sprintf "%A" (tc.Module, tc.Name)
    let dimensionKey (dimension: Dimension) =
        sprintf "%A" (dimension.Bases |> Map.toList |> List.map (fun (b, e) -> b.Module, b.Name, e),
                      dimension.Vars |> Map.toList |> List.map (fun (v, e) -> v.Id, e))
    let tagged tag parts = tag + sprintf "%A" parts
    let rec identity ty =
        match applySubst ty with
        | NativeType.TApp (tc, args) -> tagged ("app" + named tc) (List.map identity args)
        | NativeType.TNum (carrier, dimension) ->
            let carrierKey = match CarrierRef.resolve carrier with CarrierRef.Carrier tc -> named tc | CarrierRef.CVar p -> string p.Id
            tagged "number" [carrierKey; dimensionKey dimension]
        | NativeType.TMeasure dimension -> tagged "measure" [dimensionKey dimension]
        | NativeType.TVar p -> tagged "variable" [string p.Id]
        | NativeType.TFun (domain, range) -> tagged "function" [identity domain; identity range]
        | NativeType.TTuple (elements, isStruct) -> tagged (sprintf "tuple:%b" isStruct) (List.map identity elements)
        | NativeType.TAnon (fields, isStruct) -> tagged (sprintf "record:%b" isStruct) (fields |> List.map (fun (name, ty) -> tagged name [identity ty]))
        | NativeType.TUnion (tc, _) -> tagged "union" [named tc]
        | NativeType.TForall (parameters, body) -> tagged "forall" [sprintf "%A" (parameters |> List.map (fun p -> p.Id)); identity body]
        | NativeType.TByref (element, kind) -> tagged (sprintf "byref:%A" kind) [identity element]
        | NativeType.TNativePtr element -> tagged "pointer" [identity element]
        | NativeType.TLazy element -> tagged "lazy" [identity element]
        | NativeType.TSeq element -> tagged "sequence" [identity element]
        | NativeType.TSeqEnumerator element -> tagged "enumerator" [identity element]
        | NativeType.TList element -> tagged "list" [identity element]
        | NativeType.TMap (key, value) -> tagged "map" [identity key; identity value]
        | NativeType.TSet element -> tagged "set" [identity element]
        | NativeType.TError message -> tagged "error" [message]
    match applySubst ty with
    | NativeType.TApp (tycon, []) -> tycon.Name
    | ty -> identity ty
