// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Source-owned immutable identity snapshots, independent of diagnostic rendering.
module Clef.Compiler.NativeTypedTree.TypeIdentities

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind

let constructor (tycon: TypeConRef) : ConstructorIdentity =
    { Declaration = NominalTypeIdentity.ofConstructor tycon
      Parameters = tycon.ParamKinds
      NativeKind = tycon.NTUKind }

/// Normalize the current source substitution once, then copy identities rather than cells.
/// Unresolved variables retain their representative identity and sort. This operation makes
/// no representation decision and proves neither resolution nor runtime admission.
let rec ofType (ty: NativeType) : TypeIdentity =
    match applySubst ty with
    | NativeType.TApp (tycon, arguments) -> TypeIdentity.Application(constructor tycon, List.map ofType arguments)
    | NativeType.TNum (carrier, dimension) ->
        let carrier =
            match CarrierRef.resolve carrier with
            | CarrierRef.Carrier tycon -> CarrierIdentity.Constructor(constructor tycon)
            | CarrierRef.CVar parameter -> CarrierIdentity.Variable(parameter.Id, parameter.Kind)
        TypeIdentity.Numeric(carrier, dimension)
    | NativeType.TMeasure dimension -> TypeIdentity.Measure dimension
    | NativeType.TVar parameter ->
        let representative, _ = find parameter
        TypeIdentity.Variable(representative.Id, representative.Kind)
    | NativeType.TFun (domain, range) -> TypeIdentity.Function(ofType domain, ofType range)
    | NativeType.TTuple (elements, isStruct) -> TypeIdentity.Tuple(isStruct, List.map ofType elements)
    | NativeType.TAnon (fields, isStruct) -> TypeIdentity.AnonymousRecord(isStruct, fields |> List.map (fun (name, ty) -> name, ofType ty))
    | NativeType.TUnion (tycon, cases) ->
        TypeIdentity.Union(constructor tycon,
            cases |> List.map (fun case -> case.Name, case.Index, case.Fields |> List.map (fun (name, ty) -> name, ofType ty)))
    | NativeType.TForall (parameters, body) -> TypeIdentity.Forall(parameters |> List.map (fun parameter -> parameter.Id, parameter.Kind), ofType body)
    | NativeType.TByref (element, kind) -> TypeIdentity.Byref(kind, ofType element)
    | NativeType.TNativePtr element -> TypeIdentity.NativePointer(ofType element)
    | NativeType.TLazy element -> TypeIdentity.Lazy(ofType element)
    | NativeType.TSeq element -> TypeIdentity.Sequence(ofType element)
    | NativeType.TSeqEnumerator element -> TypeIdentity.Enumerator(ofType element)
    | NativeType.TList element -> TypeIdentity.List(ofType element)
    | NativeType.TMap (key, value) -> TypeIdentity.Map(ofType key, ofType value)
    | NativeType.TSet element -> TypeIdentity.Set(ofType element)
    | NativeType.TError message -> TypeIdentity.Error message
