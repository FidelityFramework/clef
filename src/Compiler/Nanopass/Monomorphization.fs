// SPDX-License-Identifier: MIT

/// Monomorphization of generic (let-polymorphic) top-level functions.
///
/// The type checker generalizes a module-level, non-recursive, non-inline function binding
/// whose inferred type still has free type variables into a `TForall` scheme (Bindings.fs),
/// and every use site instantiates that scheme with fresh type variables (Identity.fs).
/// After constraint solving each use site therefore carries a concrete instance of the
/// function type while the definition's body still mentions the scheme's type parameters.
///
/// Native code has one representation per type, so a generic function is compiled once per
/// distinct instantiation: this pass clones the Binding + Lambda subtree for every distinct
/// type-argument tuple found at its use sites, substitutes the type arguments into every
/// node type (and into the types embedded in patterns and lambda parameters), renames the
/// clone (`name__monoN`), repoints the use sites at their clone, replaces the generic
/// original in its ModuleDef, and drops it from the graph.
///
/// The pass runs on the resolved node map (after substitutions are applied, before
/// reachability and Baker), so cloned bodies are ordinary monomorphic code for every
/// later pass. Instantiations that leave a type argument unresolved are cloned as well;
/// the unresolved variable then surfaces at emission, exactly as before this pass.
module Clef.Compiler.Nanopass.Monomorphization

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

//-------------------------------------------------------------------------
// Type-argument recovery: match a scheme body against an instance
//-------------------------------------------------------------------------

/// Walk `scheme` and `instance` in parallel, recording what each scheme type parameter
/// stands for in the instance. Returns None when the shapes disagree (should not happen
/// after successful type checking).
let private matchTypeArgs (typars: TypeParam list) (scheme: NativeType) (instance: NativeType) : Map<int, NativeType> option =
    let paramIds = typars |> List.map (fun tp -> tp.Id) |> Set.ofList
    let mutable ok = true
    let mutable subst : Map<int, NativeType> = Map.empty
    let rec go (s: NativeType) (i: NativeType) =
        if not ok then () else
        match s with
        | NativeType.TVar tp when Set.contains tp.Id paramIds ->
            // A measure-kinded parameter is neither key material nor substituted at cloning
            // (design note d.3, DTS/DMM §2.3: dimensions never change the emitted instructions,
            // so a measure-only instantiation is one body). Only type-kinded parameters are
            // learned here; later, carrier-kinded ones join them.
            match tp.Kind with
            | TypeParamKind.Measure -> ()
            | _ ->
                match Map.tryFind tp.Id subst with
                | None -> subst <- Map.add tp.Id (applySubst i) subst
                | Some _ -> ()
        | _ ->
            match s, applySubst i with
            | NativeType.TApp (tc1, a1), NativeType.TApp (tc2, a2) when tc1.Name = tc2.Name && List.length a1 = List.length a2 ->
                List.iter2 go a1 a2
            | NativeType.TFun (d1, r1), NativeType.TFun (d2, r2) -> go d1 d2; go r1 r2
            | NativeType.TTuple (e1, _), NativeType.TTuple (e2, _) when List.length e1 = List.length e2 -> List.iter2 go e1 e2
            | NativeType.TByref (e1, _), NativeType.TByref (e2, _) -> go e1 e2
            | NativeType.TNativePtr e1, NativeType.TNativePtr e2 -> go e1 e2
            | NativeType.TList e1, NativeType.TList e2 -> go e1 e2
            | NativeType.TSeq e1, NativeType.TSeq e2 -> go e1 e2
            | NativeType.TLazy e1, NativeType.TLazy e2 -> go e1 e2
            | NativeType.TMap (k1, v1), NativeType.TMap (k2, v2) -> go k1 k2; go v1 v2
            | NativeType.TSet e1, NativeType.TSet e2 -> go e1 e2
            | NativeType.TAnon (f1, _), NativeType.TAnon (f2, _) when List.length f1 = List.length f2 ->
                List.iter2 (fun (_, a) (_, b) -> go a b) f1 f2
            | NativeType.TVar _, _ -> ()          // a non-parameter variable in the scheme: nothing to learn
            | _, NativeType.TVar _ -> ()          // instance still open here: nothing to learn
            | NativeType.TMeasure _, NativeType.TMeasure _ -> ()   // a measure position: nothing to learn (d.3)
            | NativeType.TForall (_, b1), other -> go b1 other
            | _ -> ok <- false
    go scheme instance
    if ok then Some subst else None

//-------------------------------------------------------------------------
// Cloning with NodeId remapping and type substitution
//-------------------------------------------------------------------------

/// Apply `f` to every NativeType embedded in a pattern.
let rec private mapPatternTypes (f: NativeType -> NativeType) (p: Pattern) : Pattern =
    match p with
    | Pattern.Const _ | Pattern.Wildcard | Pattern.Null -> p
    | Pattern.Var (name, ty) -> Pattern.Var (name, f ty)
    | Pattern.Tuple elems -> Pattern.Tuple (elems |> List.map (mapPatternTypes f))
    | Pattern.Union (c, tag, payload, uty) -> Pattern.Union (c, tag, payload |> Option.map (mapPatternTypes f), f uty)
    | Pattern.Record (fields, rty) -> Pattern.Record (fields |> List.map (fun (n, q) -> (n, mapPatternTypes f q)), f rty)
    | Pattern.Array elems -> Pattern.Array (elems |> List.map (mapPatternTypes f))
    | Pattern.Or (a, b) -> Pattern.Or (mapPatternTypes f a, mapPatternTypes f b)
    | Pattern.And (a, b) -> Pattern.And (mapPatternTypes f a, mapPatternTypes f b)
    | Pattern.As (q, name) -> Pattern.As (mapPatternTypes f q, name)
    | Pattern.IsType ty -> Pattern.IsType (f ty)
    | Pattern.Exception (ty, bind) -> Pattern.Exception (f ty, bind)

/// Remap every NodeId embedded in a kind with `r` and every embedded type with `f`.
let private mapKind (r: NodeId -> NodeId) (f: NativeType -> NativeType) (kind: SemanticKind) : SemanticKind =
    let ro (o: NodeId option) = Option.map r o
    match kind with
    | SemanticKind.Binding _ -> kind
    | SemanticKind.Application (fn, args) -> SemanticKind.Application (r fn, List.map r args)
    | SemanticKind.Lambda (ps, body, captures, enclosing, ctx) ->
        let ps' = ps |> List.map (fun (n, ty, id) -> (n, f ty, r id))
        let captures' = captures |> List.map (fun c -> { c with Type = f c.Type; SourceNodeId = ro c.SourceNodeId })
        SemanticKind.Lambda (ps', r body, captures', enclosing, ctx)
    | SemanticKind.Literal _ -> kind
    | SemanticKind.VarRef (name, def) -> SemanticKind.VarRef (name, ro def)
    | SemanticKind.Match (scrutinee, cases) ->
        let cases' = cases |> List.map (fun c ->
            { Pattern = mapPatternTypes f c.Pattern
              PatternBindings = List.map r c.PatternBindings
              Guard = ro c.Guard
              Body = r c.Body })
        SemanticKind.Match (r scrutinee, cases')
    | SemanticKind.CaseElimination (scrutinee, arms) ->
        let arms' = arms |> List.map (fun a ->
            { Pattern = mapPatternTypes f a.Pattern
              Bindings = List.map r a.Bindings
              Guard = ro a.Guard
              Body = r a.Body })
        SemanticKind.CaseElimination (r scrutinee, arms')
    | SemanticKind.Sequential nodes -> SemanticKind.Sequential (List.map r nodes)
    | SemanticKind.WhileLoop (g, b) -> SemanticKind.WhileLoop (r g, r b)
    | SemanticKind.ForLoop (v, s, e, up, b) -> SemanticKind.ForLoop (v, r s, r e, up, r b)
    | SemanticKind.ForEach (v, c, b) -> SemanticKind.ForEach (v, r c, r b)
    | SemanticKind.IfThenElse (g, t, e) -> SemanticKind.IfThenElse (r g, r t, ro e)
    | SemanticKind.TryWith (b, h) -> SemanticKind.TryWith (r b, r h)
    | SemanticKind.TryFinally (b, c) -> SemanticKind.TryFinally (r b, r c)
    | SemanticKind.RecordExpr (fields, copyFrom) -> SemanticKind.RecordExpr (fields |> List.map (fun (n, id) -> (n, r id)), ro copyFrom)
    | SemanticKind.UnionCase (c, i, payload) -> SemanticKind.UnionCase (c, i, ro payload)
    | SemanticKind.DUGetTag (v, ty) -> SemanticKind.DUGetTag (r v, f ty)
    | SemanticKind.DUEliminate (v, i, c, ty) -> SemanticKind.DUEliminate (r v, i, c, f ty)
    | SemanticKind.DUConstruct (c, i, payload, arena) -> SemanticKind.DUConstruct (c, i, ro payload, ro arena)
    | SemanticKind.TupleExpr elems -> SemanticKind.TupleExpr (List.map r elems)
    | SemanticKind.ArrayExpr elems -> SemanticKind.ArrayExpr (List.map r elems)
    | SemanticKind.ListExpr elems -> SemanticKind.ListExpr (List.map r elems)
    | SemanticKind.FieldGet (e, n) -> SemanticKind.FieldGet (r e, n)
    | SemanticKind.FieldSet (e, n, v) -> SemanticKind.FieldSet (r e, n, r v)
    | SemanticKind.IndexGet (e, i) -> SemanticKind.IndexGet (r e, r i)
    | SemanticKind.IndexSet (e, i, v) -> SemanticKind.IndexSet (r e, r i, r v)
    | SemanticKind.NamedIndexedPropertySet (e, n, i, v) -> SemanticKind.NamedIndexedPropertySet (r e, n, r i, r v)
    | SemanticKind.TypeAnnotation (e, ty) -> SemanticKind.TypeAnnotation (r e, f ty)
    | SemanticKind.Upcast (e, ty) -> SemanticKind.Upcast (r e, f ty)
    | SemanticKind.Downcast (e, ty) -> SemanticKind.Downcast (r e, f ty)
    | SemanticKind.TypeTest (e, ty) -> SemanticKind.TypeTest (r e, f ty)
    | SemanticKind.AddressOf (e, b) -> SemanticKind.AddressOf (r e, b)
    | SemanticKind.Deref e -> SemanticKind.Deref (r e)
    | SemanticKind.Set (t, v) -> SemanticKind.Set (r t, r v)
    | SemanticKind.PlatformBinding _ -> kind
    | SemanticKind.Obligation _ -> kind
    | SemanticKind.Intrinsic _ -> kind
    | SemanticKind.TraitCall (m, tys, a) -> SemanticKind.TraitCall (m, List.map f tys, r a)
    | SemanticKind.Quote (e, t) -> SemanticKind.Quote (r e, t)
    | SemanticKind.ObjectExpr (ty, members) -> SemanticKind.ObjectExpr (f ty, List.map r members)
    | SemanticKind.ModuleDef (n, members) -> SemanticKind.ModuleDef (n, List.map r members)
    | SemanticKind.TypeDef (n, k, members) -> SemanticKind.TypeDef (n, k, List.map r members)
    | SemanticKind.MemberDef (n, k, body) -> SemanticKind.MemberDef (n, k, ro body)
    | SemanticKind.InterpolatedString parts ->
        SemanticKind.InterpolatedString (parts |> List.map (function
            | InterpolatedPart.ExprPart id -> InterpolatedPart.ExprPart (r id)
            | other -> other))
    | SemanticKind.PatternBinding _ -> kind
    | SemanticKind.LazyExpr (b, captures) ->
        SemanticKind.LazyExpr (r b, captures |> List.map (fun c -> { c with Type = f c.Type; SourceNodeId = ro c.SourceNodeId }))
    | SemanticKind.LazyForce v -> SemanticKind.LazyForce (r v)
    | SemanticKind.SeqExpr (b, captures) ->
        SemanticKind.SeqExpr (r b, captures |> List.map (fun c -> { c with Type = f c.Type; SourceNodeId = ro c.SourceNodeId }))
    | SemanticKind.Yield v -> SemanticKind.Yield (r v)
    | SemanticKind.YieldBang s -> SemanticKind.YieldBang (r s)
    | SemanticKind.TupleGet (t, i) -> SemanticKind.TupleGet (r t, i)
    | SemanticKind.Error _ -> kind

/// Collect the subtree rooted at `rootId` (children edges), in depth-first order.
let private collectSubtree (nodes: Map<NodeId, SemanticNode>) (rootId: NodeId) : NodeId list =
    let visited = System.Collections.Generic.HashSet<NodeId>()
    let acc = System.Collections.Generic.List<NodeId>()
    let rec walk (id: NodeId) =
        if visited.Add id then
            match Map.tryFind id nodes with
            | Some node ->
                acc.Add id
                for c in node.Children do walk c
            | None -> ()
    walk rootId
    List.ofSeq acc

/// Clone the subtree rooted at `rootId` with fresh NodeIds, substituting `f` into every
/// type, remapping internal references, and re-parenting the clone under `newParent`.
/// Returns the new root id and the cloned nodes.
let private cloneSubtree
    (nodes: Map<NodeId, SemanticNode>)
    (rootId: NodeId)
    (f: NativeType -> NativeType)
    (newParent: NodeId option)
    : NodeId * SemanticNode list =
    let ids = collectSubtree nodes rootId
    let mapping = ids |> List.map (fun id -> (id, NodeId.fresh())) |> Map.ofList
    let remap (id: NodeId) = match Map.tryFind id mapping with Some n -> n | None -> id
    let cloned =
        ids |> List.map (fun id ->
            let node = nodes.[id]
            let parent =
                if id = rootId then newParent
                else node.Parent |> Option.map remap
            { node with
                Id = remap id
                Kind = mapKind remap f node.Kind
                Type = f node.Type
                Children = node.Children |> List.map remap
                Parent = parent })
    (remap rootId, cloned)

//-------------------------------------------------------------------------
// The pass
//-------------------------------------------------------------------------

/// A generic top-level function: its Binding node (with a TForall type) and its Lambda child.
let private isGenericFunctionBinding (nodes: Map<NodeId, SemanticNode>) (node: SemanticNode) : (TypeParam list * NativeType * NodeId) option =
    match node.Kind, node.Type with
    | SemanticKind.Binding (_, _, false, None), NativeType.TForall (typars, body) ->
        match node.Children with
        | [lambdaId] ->
            match Map.tryFind lambdaId nodes with
            | Some { Kind = SemanticKind.Lambda _ } -> Some (typars, body, lambdaId)
            | _ -> None
        | _ -> None
    | _ -> None

/// A printable key for a type-argument tuple (grouping instantiations). Measure-kinded parameters
/// are not key material: two use sites that differ only in dimension share one body (d.3).
let private instanceKey (typars: TypeParam list) (subst: Map<int, NativeType>) : string =
    typars
    |> List.filter (fun tp -> tp.Kind <> TypeParamKind.Measure)
    |> List.map (fun tp ->
        match Map.tryFind tp.Id subst with
        | Some ty -> formatType (applySubst ty)
        | None -> "?")
    |> String.concat ","

/// Run monomorphization over the resolved node map. Returns the updated node map.
let run (nodes: Map<NodeId, SemanticNode>) : Map<NodeId, SemanticNode> =
    let mutable current = nodes
    let mutable progress = true
    let mutable rounds = 0
    // Clones can reference other generic functions at new instantiations, so iterate to a fixpoint.
    while progress && rounds < 8 do
        progress <- false
        rounds <- rounds + 1
        let generics =
            current
            |> Map.toList
            |> List.choose (fun (id, node) ->
                isGenericFunctionBinding current node |> Option.map (fun (tps, body, lambdaId) -> (id, node, tps, body, lambdaId)))
        for (bindingId, bindingNode, rawTypars, rawSchemeBody, lambdaId) in generics do
            // Re-root the scheme: unions since generalization may have moved a parameter's root.
            let typars = rawTypars |> List.map (fun tp -> fst (find tp)) |> List.distinctBy (fun tp -> tp.Id)
            let schemeBody = canonicalizeVars rawSchemeBody
            let bindingName = match bindingNode.Kind with SemanticKind.Binding (n, _, _, _) -> n | _ -> "generic"
            // Use sites: VarRefs whose definition is this binding
            let useSites =
                current
                |> Map.toList
                |> List.choose (fun (id, node) ->
                    match node.Kind with
                    | SemanticKind.VarRef (_, Some def) when def = bindingId -> Some (id, node)
                    | _ -> None)
            if List.isEmpty useSites then
                // No instantiation anywhere: nothing to compile. Remove the generic original so no
                // body with unbound type variables reaches emission.
                progress <- true
                match bindingNode.Parent with
                | Some parentId ->
                    match Map.tryFind parentId current with
                    | Some ({ Kind = SemanticKind.ModuleDef (mname, members) } as parentNode) ->
                        current <- Map.add parentId { parentNode with Kind = SemanticKind.ModuleDef (mname, members |> List.filter ((<>) bindingId)); Children = parentNode.Children |> List.filter ((<>) bindingId) } current
                    | _ -> ()
                | None -> ()
                for id in collectSubtree current bindingId do
                    current <- Map.remove id current
            else
                // Recover the type arguments at every use site. A use site whose type cannot be
                // matched against the scheme leaves this binding as it is (shared-variable
                // behavior) rather than dangling a reference to a deleted node.
                let matched =
                    useSites
                    |> List.map (fun (id, node) ->
                        match matchTypeArgs typars schemeBody (canonicalizeVars node.Type) with
                        | Some subst -> Some (instanceKey typars subst, subst, id)
                        | None -> None)
                let allMatched = matched |> List.forall Option.isSome
                if not allMatched then () else
                progress <- true
                // Group use sites by their type-argument tuple
                let groups =
                    matched
                    |> List.choose id
                    |> List.groupBy (fun (key, _, _) -> key)
                let mutable cloneIds : NodeId list = []
                let mutable redirect : Map<NodeId, NodeId> = Map.empty
                groups |> List.iteri (fun gi (_, members) ->
                    let (_, subst, _) = List.head members
                    // A measure-kinded parameter never appears in `subst` (matchTypeArgs), so it
                    // is carried as itself: the clone keeps the scheme's measure variables.
                    let args = typars |> List.map (fun tp -> match Map.tryFind tp.Id subst with Some ty -> ty | None -> NativeType.TVar tp)
                    let substitute (ty: NativeType) = Clef.Compiler.NativeTypedTree.NativeTypes.instantiate typars args (canonicalizeVars ty)
                    let cloneName = sprintf "%s__mono%d" bindingName (gi + 1)
                    let newBindingId = NodeId.fresh()
                    let (newLambdaId, clonedNodes) = cloneSubtree current lambdaId substitute (Some newBindingId)
                    let newBinding =
                        { bindingNode with
                            Id = newBindingId
                            Kind = SemanticKind.Binding (cloneName, false, false, None)
                            Type = substitute schemeBody
                            Children = [newLambdaId] }
                    for n in clonedNodes do current <- Map.add n.Id n current
                    current <- Map.add newBindingId newBinding current
                    cloneIds <- cloneIds @ [newBindingId]
                    for (_, _, useId) in members do redirect <- Map.add useId newBindingId redirect)
                // Repoint use sites at their clone
                for (useId, useNode) in useSites do
                    match Map.tryFind useId redirect with
                    | Some target ->
                        let name = match useNode.Kind with SemanticKind.VarRef (n, _) -> n | _ -> bindingName
                        current <- Map.add useId { useNode with Kind = SemanticKind.VarRef (name, Some target) } current
                    | None -> ()
                // Replace the generic original in its ModuleDef by the clones, and drop it
                match bindingNode.Parent with
                | Some parentId ->
                    match Map.tryFind parentId current with
                    | Some ({ Kind = SemanticKind.ModuleDef (mname, members) } as parentNode) ->
                        let replaced = members |> List.collect (fun m -> if m = bindingId then cloneIds else [m])
                        let children = parentNode.Children |> List.collect (fun m -> if m = bindingId then cloneIds else [m])
                        current <- Map.add parentId { parentNode with Kind = SemanticKind.ModuleDef (mname, replaced); Children = children } current
                    | _ -> ()
                | None -> ()
                // Drop the generic original and its subtree
                for id in collectSubtree current bindingId do
                    current <- Map.remove id current
    current
