// SPDX-License-Identifier: MIT
/// Resolve aggregate slots from exact instantiated declarations. This ingredient
/// supplies type/slot identity only; it establishes no origin, residence, native
/// contract or permission to store a function as data.
module Clef.Compiler.Baker.Ingredients.CallableAggregateTypes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Instances = Clef.Compiler.PSGSaturation.SemanticGraph.RecordInstances
module Identity = Clef.Compiler.NativeTypedTree.TypeIdentities
module Builtins = Clef.Compiler.NativeTypedTree.Expressions.Types

[<RequireQualifiedAccess>]
type Shape =
    | Record of declaration: NodeId option * fields: (string * NativeType) list
    | Union of declaration: NodeId option * cases: (string * (string option * NativeType) list) list

type Slot = {
    AggregateType: NativeType
    Declaration: NodeId option
    Path: CallableAggregatePathStep list
    ValueType: NativeType
    Kind: CallableKind
    /// Actual declarations encountered along the nested slot path.
    Declarations: NodeId list
}

let rec callableKind ty =
    match applySubst ty with
    | NativeType.TFun _ -> Some CallableKind.OrdinaryFlatClosure
    | NativeType.TForall(_, body) -> callableKind body
    | ty ->
        match Types.tryGetNTUKind ty with
        | Some NTUKind.NTUfnptr -> Some CallableKind.NativeEntry
        | _ -> None

let shape (graph: SemanticGraph) ty =
    let declaration constructor =
        Instances.tryDefinition (NominalTypeIdentity.ofConstructor constructor) graph
        |> Option.map _.Id
    let sameConstructor left right = Identity.constructor left = Identity.constructor right
    match applySubst ty with
    | NativeType.TTuple(elements, _) ->
        elements |> List.mapi (fun ordinal ty -> $"Item{ordinal + 1}", ty)
        |> fun fields -> Some(Shape.Record(None, fields))
    | NativeType.TAnon(fields, _) -> Some(Shape.Record(None, fields))
    | NativeType.TApp(constructor, [payload])
        when sameConstructor constructor Types.optionTyCon ->
        Some(Shape.Union(declaration constructor, ["None", []; "Some", [None, payload]]))
    | NativeType.TApp(constructor, [payload])
        when sameConstructor constructor Types.voptionTyCon ->
        Some(Shape.Union(declaration constructor, ["ValueNone", []; "ValueSome", [None, payload]]))
    | NativeType.TApp(constructor, [ok; error])
        when sameConstructor constructor Builtins.resultTycon ->
        Some(Shape.Union(declaration constructor, ["Ok", [None, ok]; "Error", [None, error]]))
    | NativeType.TApp(constructor, _) as instance ->
        match declaration constructor with
        | None -> None
        | Some declared ->
            match Instances.tryFields instance graph with
            | Some fields -> Some(Shape.Record(Some declared, fields))
            | None -> Instances.tryUnionCases instance graph |> Option.map (fun cases -> Shape.Union(Some declared, cases))
    | NativeType.TUnion(constructor, cases) ->
        Some(Shape.Union(declaration constructor, cases |> List.map (fun case -> case.Name, case.Fields)))
    | _ -> None

/// Freeze precisely the source declaration used by slot resolution. NativeType
/// cells stay with the checker; the retained fact records their current values.
let declarationFact (graph: SemanticGraph) (identity: NodeId) : Result<CallableAggregateDeclarationFact, string> =
    let definition =
        graph.Nodes.TryFind identity |> Option.bind (fun node ->
            match node.Kind with
            | SemanticKind.TypeDef(_, TypeDefKind.RecordDef fields, _) ->
                Some(node, CallableAggregateDeclarationDefinition.RecordDef(
                    fields |> List.map (fun (name, ty) -> name, Identity.ofType ty)))
            | SemanticKind.TypeDef(_, TypeDefKind.UnionDef cases, _) ->
                Some(node, CallableAggregateDeclarationDefinition.UnionDef(
                    cases |> List.map (fun (name, fields) ->
                        name, fields |> List.map (fun (name, ty) -> name, Identity.ofType ty))))
            | _ -> None)
    match definition with
    | Some(node, definition) ->
        Ok { Identity = identity; DeclaredType = Identity.ofType node.Type; Definition = definition }
    | None -> Error "The callable aggregate declaration is absent or is no longer the exact record/union definition."

/// Preserve declaration occurrences in path order, including repeated uses of
/// the same generic declaration at distinct instantiated steps.
let declarationFacts (graph: SemanticGraph) (identities: NodeId list) =
    let facts = identities |> List.map (declarationFact graph)
    match facts |> List.tryPick (function Error reason -> Some reason | _ -> None) with
    | Some reason -> Error reason
    | None -> Ok(facts |> List.choose (function Ok fact -> Some fact | _ -> None))

/// Enumerate callable leaves of the admitted record/union structure. Recursion
/// through a repeated type is not an inline component path; its link protocol
/// remains with the collection/recursive-value owner.
let slots (graph: SemanticGraph) aggregateType =
    let rootDeclaration =
        match shape graph aggregateType with
        | Some(Shape.Record(declaration, _)) | Some(Shape.Union(declaration, _)) -> declaration
        | None -> None
    let rec visit seen declarations path ty =
        match callableKind ty with
        | Some kind ->
            [{ AggregateType = aggregateType
               Declaration = rootDeclaration
               Path = path; ValueType = ty; Kind = kind
               Declarations = declarations }]
        | None ->
            let identity = Identity.ofType ty
            if Set.contains identity seen then [] else
            let seen = Set.add identity seen
            let retain declaration = declarations @ Option.toList declaration
            match shape graph ty with
            | Some(Shape.Record(declaration, fields)) ->
                fields |> List.mapi (fun ordinal (_, fieldType) ->
                    visit seen (retain declaration) (path @ [CallableAggregatePathStep.RecordField ordinal]) fieldType)
                |> List.concat
            | Some(Shape.Union(declaration, cases)) ->
                cases |> List.mapi (fun caseOrdinal (_, fields) ->
                    fields |> List.mapi (fun payloadOrdinal (_, fieldType) ->
                        visit seen (retain declaration)
                            (path @ [CallableAggregatePathStep.UnionPayload(caseOrdinal, payloadOrdinal)]) fieldType)
                    |> List.concat)
                |> List.concat
            | None -> []
    visit Set.empty [] [] aggregateType
