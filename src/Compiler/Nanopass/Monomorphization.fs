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
/// distinct instantiation: this pass clones the Binding + callable subtree for every distinct
/// type-argument tuple found at its use sites, substitutes the type arguments into every
/// node type (and into the types embedded in patterns and lambda parameters), renames the
/// clone (`name__monoN`), repoints the use sites at their clone, replaces the generic
/// original in its ModuleDef, and retires its execution while retaining derivation evidence.
///
/// The pass runs on the resolved node map (after substitutions are applied, before
/// reachability and Baker). A physical clone retains only its residual measure
/// scheme; all exact checker instances and the original scheme remain in the tape.
/// Instantiations that leave a type argument unresolved are cloned as well;
/// the unresolved variable then surfaces at emission, exactly as before this pass.
module Clef.Compiler.Nanopass.Monomorphization

open Clef.Compiler.NativeTypedTree.DimensionAlgebra
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
            // A measure-kinded parameter is not physical key material. Its
            // substitution authority comes from exact checker instances below,
            // never from recovering a dimension by matching this result type.
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
            // A numeric position: the dimension is not key material (d.3). A carrier parameter of
            // the scheme is learned from the instance's carrier (carrier-kinded parameters are key
            // material); two constructors must agree by name; an instance whose carrier is still
            // open teaches nothing.
            | NativeType.TNum (c1, _), NativeType.TNum (c2, _) ->
                match CarrierRef.resolve c1, CarrierRef.resolve c2 with
                | CarrierRef.CVar tp, CarrierRef.Carrier tc when Set.contains tp.Id paramIds ->
                    if not (Map.containsKey tp.Id subst) then
                        subst <- Map.add tp.Id (NativeType.TNum (CarrierRef.Carrier tc, Dimension.one)) subst
                | CarrierRef.Carrier tc1, CarrierRef.Carrier tc2 when tc1.Name = tc2.Name -> ()
                | CarrierRef.CVar _, _ | _, CarrierRef.CVar _ -> ()
                | _ -> ok <- false
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
    | SemanticKind.ContinuationDispatch (selector, cases, otherwise) ->
        SemanticKind.ContinuationDispatch (r selector, cases |> List.map (fun (state, body) -> state, r body), r otherwise)
    | SemanticKind.AggregateStorage source -> SemanticKind.AggregateStorage (r source)
    | SemanticKind.DUInitialize (destination, name, index, payload) -> SemanticKind.DUInitialize (r destination, name, index, Option.map r payload)
    | SemanticKind.FrameRead (frame, slot) -> SemanticKind.FrameRead (r frame, r slot)
    | SemanticKind.FrameBorrow (frame, slot) -> SemanticKind.FrameBorrow (r frame, r slot)
    | SemanticKind.FrameWrite (frame, slot, value) -> SemanticKind.FrameWrite (r frame, r slot, r value)
    | SemanticKind.ContinuationStorage owner -> SemanticKind.ContinuationStorage (r owner)
    | SemanticKind.ContinuationAllocate owner -> SemanticKind.ContinuationAllocate (r owner)
    | SemanticKind.ClosureValue(implementation, environment) -> SemanticKind.ClosureValue(r implementation, r environment)
    | SemanticKind.EnvironmentCreate(owner, initializers) -> SemanticKind.EnvironmentCreate(r owner, initializers |> List.map (fun (slot, value) -> r slot, r value))
    | SemanticKind.EnvironmentAllocate owner -> SemanticKind.EnvironmentAllocate(r owner)
    | SemanticKind.EnvironmentReference value -> SemanticKind.EnvironmentReference(r value)
    | SemanticKind.EnvironmentRead(environment, slot) -> SemanticKind.EnvironmentRead(r environment, r slot)
    | SemanticKind.EnvironmentBorrow(environment, slot) -> SemanticKind.EnvironmentBorrow(r environment, r slot)
    | SemanticKind.EnvironmentWrite(environment, slot, value) -> SemanticKind.EnvironmentWrite(r environment, r slot, r value)
    | SemanticKind.ForLoop (v, s, e, up, b) -> SemanticKind.ForLoop (v, r s, r e, up, r b)
    | SemanticKind.ForEach (v, p, c, b) -> SemanticKind.ForEach (v, r p, r c, r b)
    | SemanticKind.IfThenElse (g, t, e) -> SemanticKind.IfThenElse (r g, r t, ro e)
    | SemanticKind.Require(condition, diagnostic) -> SemanticKind.Require(r condition, diagnostic)
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
    | SemanticKind.EagerExpr v -> SemanticKind.EagerExpr (r v)
    | SemanticKind.LazyValue(thunk, environment) -> SemanticKind.LazyValue(r thunk, r environment)
    | SemanticKind.LazyEnvironment(owner, initializers) -> SemanticKind.LazyEnvironment(r owner, initializers |> List.map (fun (slot, value) -> r slot, r value))
    | SemanticKind.LazyEnvironmentReference value -> SemanticKind.LazyEnvironmentReference(r value)
    | SemanticKind.LazyAllocate owner -> SemanticKind.LazyAllocate(r owner)
    | SemanticKind.LazyRead(environment, slot) -> SemanticKind.LazyRead(r environment, r slot)
    | SemanticKind.LazyBorrow(environment, slot) -> SemanticKind.LazyBorrow(r environment, r slot)
    | SemanticKind.LazyWrite(environment, slot, value) -> SemanticKind.LazyWrite(r environment, r slot, r value)
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
let internal cloneSubtreeWithOrigins
    (nodes: Map<NodeId, SemanticNode>)
    (rootId: NodeId)
    (f: NativeType -> NativeType)
    (newParent: NodeId option)
    : NodeId * SemanticNode list * Map<NodeId, NodeId> =
    let ids = collectSubtree nodes rootId
    let mapping = ids |> List.map (fun id -> (id, NodeId.fresh())) |> Map.ofList
    let remap (id: NodeId) = match Map.tryFind id mapping with Some n -> n | None -> id
    let declaration id =
        match nodes[rootId].Parent, newParent with
        | Some original, Some replacement when id = original -> replacement
        | _ -> remap id
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
                Metadata = node.Metadata |> Map.map (fun key value ->
                    match value with
                    | MetadataValue.Type ty -> MetadataValue.Type(f ty)
                    | MetadataValue.NodeId id when key = SchemeMetadata.Definition || key = SchemeMetadata.ImplementationDeclaration ->
                        MetadataValue.NodeId(declaration id)
                    | _ -> value)
                Children = node.Children |> List.map remap
                Parent = parent })
    (remap rootId, cloned, mapping)

let internal cloneSubtree nodes rootId substitute newParent =
    let root, cloned, _ = cloneSubtreeWithOrigins nodes rootId substitute newParent
    root, cloned

//-------------------------------------------------------------------------
// The pass
//-------------------------------------------------------------------------

/// A generic function declaration or immutable bare library operation alias.
/// Bare operations have no captured evaluation to duplicate; Baker reifies each
/// specialized intrinsic later. Existing function-value references remain values.
/// An immutable alias of a bare operation has no supplied operands or captured
/// evaluation. Keep its own typed occurrence as the specialization frontier:
/// specializing the upstream alias against this still-generic reference would
/// otherwise manufacture an open monotype before the final call supplies types.
let private bareLibraryOperation (nodes: Map<NodeId, SemanticNode>) id =
    let rec operation seen depth id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match Map.tryFind id nodes with
        | Some { Kind = SemanticKind.Intrinsic info } when
            info.Module = IntrinsicModule.Option || info.Module = IntrinsicModule.Result || info.Module = IntrinsicModule.Seq -> Some (info, depth)
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> operation seen depth inner
        | Some { Kind = SemanticKind.VarRef (_, Some definition) } ->
            match Map.tryFind definition nodes with
            | Some { Kind = SemanticKind.Binding (_, false, false, None); Children = [value] } -> operation seen (depth + 1) value
            | _ -> None
        | _ -> None
    operation Set.empty 0 id

let private isBareLibraryOperation nodes id = bareLibraryOperation nodes id |> Option.isSome

let private isGenericFunctionBinding (nodes: Map<NodeId, SemanticNode>) (node: SemanticNode) : (TypeParam list * NativeType * NodeId) option =
    if not node.IsReachable then None else
    match node.Kind, node.Type with
    | SemanticKind.Binding (_, isMutable, false, None), NativeType.TForall (typars, body) ->
        match node.Children with
        | [lambdaId] ->
            match Map.tryFind lambdaId nodes with
            | Some { Kind = SemanticKind.Lambda _ } -> Some (typars, body, lambdaId)
            | _ when not isMutable && isBareLibraryOperation nodes lambdaId -> Some (typars, body, lambdaId)
            | _ -> None
        | _ -> None
    | _ -> None

/// Exact native type identity groups physical instances. Display names are not
/// identities: distinct nominal owners can have the same printed type name.
/// Measure-kinded parameters do not split physical bodies (d.3).
let private instanceKey (typars: TypeParam list) (subst: Map<int, NativeType>) : NativeType option list =
    typars
    |> List.filter (fun tp -> tp.Kind <> TypeParamKind.Measure)
    |> List.map (fun tp -> Map.tryFind tp.Id subst |> Option.map applySubst)

/// Read the exact instance minted by the checker. Dimensions are not recovered
/// by matching a result type: coupled/phantom parameters need their own facts.
let private checkedArguments declaration (parameters: TypeParam list) body (node: SemanticNode) =
    let expected = parameters |> List.indexed |> List.map (fun (ordinal, _) -> SchemeMetadata.argument ordinal) |> Set.ofList
    let recorded = node.Metadata.Keys |> Seq.filter (fun key -> key.StartsWith("Scheme.Argument.", System.StringComparison.Ordinal)) |> Set.ofSeq
    let arguments = parameters |> List.indexed |> List.map (fun (ordinal, _) ->
        match node.Metadata.TryFind (SchemeMetadata.argument ordinal) with
        | Some(MetadataValue.Type ty) -> Some(applySubst ty)
        | _ -> None)
    let declared =
        match node.Metadata.TryFind SchemeMetadata.Definition, node.Metadata.TryFind SchemeMetadata.Declaration with
        | Some(MetadataValue.NodeId id), Some(MetadataValue.Type(NativeType.TForall(actual, signature))) ->
            id = declaration &&
            List.map (fun (p: TypeParam) -> p.Id, p.Kind) actual = List.map (fun (p: TypeParam) -> p.Id, p.Kind) parameters &&
            canonicalizeVars signature = body
        | _ -> false
    if not declared || expected <> recorded || arguments |> List.exists Option.isNone then None else
    let arguments = List.choose id arguments
    let lawfulKinds =
        List.forall2 (fun (parameter: TypeParam) argument ->
            match parameter.Kind, argument with
            | TypeParamKind.Measure, NativeType.TMeasure _ -> true
            | TypeParamKind.Carrier, NativeType.TNum(_, dimension) -> dimension = Dimension.one
            | TypeParamKind.Type, NativeType.TMeasure _ -> false
            | TypeParamKind.Type, _ -> true
            | _ -> false) parameters arguments
    if lawfulKinds && applySubst (instantiate parameters arguments body) = applySubst node.Type then Some arguments else None

let private clearInstanceMetadata (metadata: Map<string, MetadataValue>) =
    metadata |> Map.filter (fun key _ ->
        key <> SchemeMetadata.Definition && key <> SchemeMetadata.Declaration &&
        not (key.StartsWith("Scheme.Argument.", System.StringComparison.Ordinal)))

/// A physical specialization can still be polymorphic in measures. Publish
/// that residual source scheme, rather than retaining already specialized type
/// binders or leaving its measure variables without declaration authority.
let private residualMetadata declaration parameters signature metadata =
    let metadata = clearInstanceMetadata metadata
    if List.isEmpty parameters then metadata
    else metadata.Add(SchemeMetadata.Declaration, MetadataValue.Type(NativeType.TForall(parameters, signature)))
                 .Add(SchemeMetadata.ImplementationDeclaration, MetadataValue.NodeId declaration)

/// Project an exact checked instance onto the binders retained by its shared
/// implementation. An absent/invalid instance cannot mint new authority.
let private projectInstanceMetadata target (parameters: TypeParam list) (residual: TypeParam list) signature actualArguments metadata =
    let cleared = clearInstanceMetadata metadata
    match residual, actualArguments with
    | [], _ -> cleared
    | _, Some actual ->
        let arguments = List.zip parameters actual |> List.map (fun (parameter, value) -> parameter.Id, value) |> Map.ofList
        residual |> List.indexed |> List.fold (fun metadata (ordinal, parameter) ->
            Map.add (SchemeMetadata.argument ordinal) (MetadataValue.Type arguments[parameter.Id]) metadata)
            (cleared.Add(SchemeMetadata.Definition, MetadataValue.NodeId target)
                    .Add(SchemeMetadata.Declaration, MetadataValue.Type(NativeType.TForall(residual, signature))))
    | _, None -> metadata

/// Declaration membership is authoritative before parent navigation edges are linked.
/// Replace module members, and pure local library aliases in their sequence, at the
/// existing position so specialization leaves no references to the removed generic declaration.
let private replaceBindingMembership (bindingId: NodeId) (replacements: NodeId list) (localLibraryAlias: bool) (nodes: Map<NodeId, SemanticNode>) =
    let replace ids = ids |> List.collect (fun id -> if id = bindingId then replacements else [id])
    nodes |> Map.map (fun _ node ->
        match node.Kind with
        | SemanticKind.ModuleDef (name, members) when List.contains bindingId members ->
            { node with Kind = SemanticKind.ModuleDef (name, replace members)
                        Children = replace node.Children }
        | SemanticKind.Sequential expressions when localLibraryAlias && List.contains bindingId expressions ->
            { node with Kind = SemanticKind.Sequential (replace expressions)
                        Children = replace node.Children }
        | _ -> node)

/// Capture once, before any later rewrite or checker substitution can change
/// the printed input/output. These records are not consumed by admission.
let private snapshot (node: SemanticNode) : SpecializationNodeSnapshot =
    { Kind = sprintf "%A" node.Kind; Type = formatType node.Type
      Children = node.Children; Parent = node.Parent }

let private recordDerivation sourceDeclaration cloneDeclaration parameters arguments requests
                             (before: Map<NodeId, SemanticNode>) (mapping: Map<NodeId, NodeId>)
                             (after: Map<NodeId, SemanticNode>) =
    let scheme = formatType (NativeType.TForall(parameters, before[sourceDeclaration].Type |> function NativeType.TForall(_, body) -> body | ty -> ty))
    mapping |> Map.fold (fun ((nodes: Map<NodeId, SemanticNode>), edges) source clone ->
        let trace = {
            SourceDeclaration = sourceDeclaration; SourceNode = source
            CloneDeclaration = cloneDeclaration; CloneNode = clone
            Scheme = scheme; Parameters = parameters |> List.map (fun parameter -> parameter.Id, string parameter.Kind)
            CodeArguments = arguments |> List.map formatType
            Requests = requests; RetiresSource = true
            Input = snapshot before[source]; Output = snapshot after[clone] }
        let node = nodes[clone]
        let node = { node with Metadata = node.Metadata.Add(SchemeMetadata.Specialization, MetadataValue.Specialization trace) }
        let edge = {
            Class = EdgeClass.Provenance; Role = EdgeRole.SchemeSpecialization; Ordinal = 0
            Sources = [sourceDeclaration; source; cloneDeclaration; clone] @ (requests |> List.map fst)
            Target = clone }
        nodes.Add(clone, node), edge :: edges) (after, [])

/// Recursive declarations are specialized together: reserve each requested
/// declaration before visiting its body, then redirect self/peer references
/// through that reservation. No partially rewritten component is installed.
let rec private specializeRecursiveComponents (nodes: Map<NodeId, SemanticNode>) =
    let declarations =
        nodes |> Map.toList |> List.choose (fun (id, node) ->
            match node.Kind, node.Children with
            | SemanticKind.Binding(_, false, true, None), [body] when node.IsReachable ->
                match nodes.TryFind body with
                | Some { Kind = SemanticKind.Lambda _ } -> Some(id, (node, body))
                | _ -> None
            | _ -> None) |> Map.ofList
    let members = declarations.Keys |> Set.ofSeq
    let bodies = declarations |> Map.map (fun _ (_, body) -> collectSubtree nodes body |> Set.ofList)
    let dependencies = bodies |> Map.map (fun _ body ->
        body |> Seq.choose (fun id ->
            match nodes[id].Kind with
            | SemanticKind.VarRef(_, Some target) when members.Contains target -> Some target
            | _ -> None) |> Set.ofSeq)
    let reachable root =
        let rec walk seen id =
            if Set.contains id seen then seen else
            dependencies[id] |> Set.fold walk (Set.add id seen)
        walk Set.empty root
    let closure = members |> Seq.map (fun id -> id, reachable id) |> Map.ofSeq
    let mutable remaining = members
    let mutable current = nodes
    let mutable evidence = []
    while not remaining.IsEmpty do
        let first = Set.minElement remaining
        let group = closure[first] |> Set.filter (fun id -> closure[id].Contains first)
        remaining <- Set.difference remaining group
        let schemes = group |> Seq.map (fun id ->
            let node, _ = declarations[id]
            let parameters, body =
                match node.Type with NativeType.TForall(parameters, body) -> parameters, body | ty -> [], ty
            let parameters = parameters |> List.map (find >> fst) |> List.distinctBy _.Id
            id, (parameters, canonicalizeVars body)) |> Map.ofSeq
        let present = group |> Seq.forall (fun id -> current.ContainsKey id && current.ContainsKey (snd declarations[id]))
        let hasKeyMaterial = schemes.Values |> Seq.exists (fun (parameters, _) -> parameters |> List.exists (fun parameter -> parameter.Kind <> TypeParamKind.Measure))
        if present && hasKeyMaterial then
            let inside = group |> Seq.map (fun id -> bodies[id]) |> Set.unionMany
            let uses = current.Values |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.VarRef(_, Some target) when node.IsReachable && group.Contains target && not (inside.Contains node.Id) -> Some(node, target)
                | _ -> None) |> Seq.toList
            if not uses.IsEmpty then
                let reserved = System.Collections.Generic.Dictionary<NodeId * NativeType option list, NodeId * string>()
                let requests = System.Collections.Generic.Dictionary<NodeId, ResizeArray<NodeId * string>>()
                let pending = System.Collections.Generic.Queue<NodeId * Map<int, NativeType> * NodeId * string>()
                let cloneSchemes = System.Collections.Generic.Dictionary<NodeId, TypeParam list * TypeParam list * NativeType>()
                let itself (parameter: TypeParam) =
                    match parameter.Kind with
                    | TypeParamKind.Type -> NativeType.TVar parameter
                    | TypeParamKind.Carrier -> NativeType.TNum(CarrierRef.CVar parameter, Dimension.one)
                    | TypeParamKind.Measure -> NativeType.TMeasure(Dimension.ofVar (measureVarOf parameter))
                let mutable valid = true
                let request occurrence declaration actual =
                    let parameters, body = schemes[declaration]
                    match matchTypeArgs parameters body (canonicalizeVars actual) with
                    | Some substitution when parameters |> List.forall (fun parameter ->
                        parameter.Kind = TypeParamKind.Measure ||
                        (substitution.TryFind parameter.Id |> Option.exists (hasUnboundVars >> not))) ->
                        let key = declaration, instanceKey parameters substitution
                        let id =
                            match reserved.TryGetValue key with
                            | true, (id, _) -> id
                            | _ ->
                                let original, _ = declarations[declaration]
                                let name = match original.Kind with SemanticKind.Binding(name, _, _, _) -> name | _ -> invalidOp "Recursive declaration required"
                                let id = NodeId.fresh()
                                let symbol = sprintf "%s__rec_mono%d" name (reserved.Count + 1)
                                reserved.Add(key, (id, symbol))
                                requests.Add(id, ResizeArray())
                                let arguments = parameters |> List.map (fun parameter -> substitution.TryFind parameter.Id |> Option.defaultValue (itself parameter))
                                let signature = instantiate parameters arguments body
                                let residual = parameters |> List.filter (fun parameter -> parameter.Kind = TypeParamKind.Measure)
                                cloneSchemes.Add(id, (parameters, residual, signature))
                                pending.Enqueue(declaration, substitution, id, symbol)
                                id
                        requests[id].Add(occurrence, formatType actual)
                        id
                    | _ -> valid <- false; declaration
                let redirects = uses |> List.map (fun (node, target) -> node.Id, request node.Id target node.Type) |> Map.ofList
                let mutable created = Map.empty
                let mutable replacements = Map.empty<NodeId, NodeId list>
                let mutable derivations = []
                while valid && pending.Count > 0 do
                    let originalId, substitution, bindingId, symbol = pending.Dequeue()
                    let original, lambda = declarations[originalId]
                    let parameters, body = schemes[originalId]
                    let ownerIds = parameters |> List.map _.Id |> Set.ofList
                    let arguments = parameters |> List.map (fun parameter ->
                        match substitution.TryFind parameter.Id with
                        | Some value -> value
                        | None -> NativeType.TMeasure(Dimension.ofVar (measureVarOf parameter)))
                    let substitute ty = instantiate parameters arguments (canonicalizeVars ty)
                    let root, cloned, mapping = cloneSubtreeWithOrigins current lambda substitute (Some bindingId)
                    let originalByClone = mapping |> Map.toList |> List.map (fun (original, clone) -> clone, original) |> Map.ofList
                    let peers = cloned |> List.choose (fun node ->
                        match node.Kind with
                        | SemanticKind.VarRef(_, Some target) when group.Contains target ->
                            Some(node.Id, target, request node.Id target node.Type)
                        | _ -> None)
                    let peerGroups = peers |> List.groupBy (fun (_, target, _) -> target)
                    if peerGroups |> List.exists (fun (_, targets) -> targets |> List.map (fun (_, _, clone) -> clone) |> List.distinct |> List.length <> 1) then valid <- false
                    let peerMap = peers |> List.map (fun (_, target, clone) -> target, clone) |> Map.ofList
                    let peerOccurrences = peers |> List.map (fun (occurrence, target, clone) -> occurrence, (target, clone)) |> Map.ofList
                    let remap id = peerMap.TryFind id |> Option.defaultValue id
                    let metadata values = values |> Map.map (fun key value ->
                        match value with
                        | MetadataValue.NodeId id when key = SchemeMetadata.Definition || key = SchemeMetadata.ImplementationDeclaration -> MetadataValue.NodeId(remap id)
                        | _ -> value)
                    for node in cloned do
                        let mutable projected = metadata node.Metadata
                        if node.Id = root then
                            let _, residual, signature = cloneSchemes[bindingId]
                            projected <- residualMetadata bindingId residual signature projected
                        match peerOccurrences.TryFind node.Id with
                        | Some(target, clone) when cloneSchemes.ContainsKey clone ->
                            let targetParameters, targetBody = schemes[target]
                            let originalUse = current[originalByClone[node.Id]]
                            let checkedInstance = checkedArguments target targetParameters targetBody originalUse
                            // Inferred recursion is checked monomorphically before group
                            // generalization. Only exact same-component shared cells can
                            // supply the identity instance when no scheme use was minted.
                            let shared =
                                let hasInstance = originalUse.Metadata |> Map.exists (fun key _ ->
                                    key = SchemeMetadata.Definition || key = SchemeMetadata.Declaration ||
                                    key.StartsWith("Scheme.Argument.", System.StringComparison.Ordinal))
                                let present = Set.union (freeTypeVars originalUse.Type) (freeMeasureVars originalUse.Type |> List.map _.Id |> Set.ofList)
                                let targetIds = targetParameters |> List.map _.Id |> Set.ofList
                                match originalUse.Kind with
                                | SemanticKind.VarRef(_, Some actual) when actual = target && not hasInstance &&
                                    Set.isSubset targetIds ownerIds && Set.isSubset targetIds present &&
                                    canonicalizeVars originalUse.Type = targetBody ->
                                    Some(targetParameters |> List.map itself)
                                | _ -> None
                            let actual = checkedInstance |> Option.orElse shared |> Option.map (List.map (substitute >> applySubst))
                            let targetParameters, residual, signature = cloneSchemes[clone]
                            let actual = actual |> Option.filter (fun arguments ->
                                applySubst (instantiate targetParameters arguments signature) = applySubst node.Type)
                            projected <- projectInstanceMetadata clone targetParameters residual signature actual projected
                        | _ -> ()
                        created <- created.Add(node.Id, { node with Kind = mapKind remap id node.Kind; Metadata = projected })
                    let _, residual, signature = cloneSchemes[bindingId]
                    let binding =
                        { original with Id = bindingId; Kind = SemanticKind.Binding(symbol, false, true, None)
                                        Type = substitute body; Children = [root]
                                        Metadata = residualMetadata bindingId residual signature original.Metadata }
                    created <- created.Add(bindingId, binding)
                    derivations <- (originalId, bindingId, parameters, arguments, mapping.Add(originalId, bindingId)) :: derivations
                    replacements <- replacements.Add(originalId, (replacements.TryFind originalId |> Option.defaultValue []) @ [bindingId])
                if valid then
                    for original, clone, parameters, arguments, mapping in derivations do
                        let updated, edges = recordDerivation original clone parameters arguments (requests[clone] |> Seq.distinct |> Seq.toList) current mapping created
                        created <- updated
                        evidence <- edges @ evidence
                    let retired = Set.union group inside
                    // Flattened source applications outside the executable
                    // subtree can still cite these original identities. Keep
                    // the source graph closed while retiring its execution.
                    current <- current |> Map.map (fun id node ->
                        if retired.Contains id then
                            { node with IsReachable = false; Metadata = node.Metadata.Add(SchemeMetadata.HistoricalOnly, MetadataValue.Bool true) }
                        else node)
                    for KeyValue(id, node) in created do current <- current.Add(id, node)
                    for node, original in uses do
                        let target = redirects[node.Id]
                        let parameters, body = schemes[original]
                        let _, residual, signature = cloneSchemes[target]
                        let actual = checkedArguments original parameters body node
                        let metadata = projectInstanceMetadata target parameters residual signature actual node.Metadata
                        let name = match node.Kind with SemanticKind.VarRef(name, _) -> name | _ -> invalidOp "Recursive use required"
                        current <- current.Add(node.Id, { node with Kind = SemanticKind.VarRef(name, Some target); Metadata = metadata })
                    for original in group do
                        current <- replaceBindingMembership original (replacements.TryFind original |> Option.defaultValue []) true current
    if obj.ReferenceEquals(nodes, current) then current, evidence
    else
        let result, subsequent = specializeRecursiveComponents current
        result, evidence @ subsequent

type Result = { Nodes: Map<NodeId, SemanticNode>; Derivations: Hyperedge list }

/// Run specialization and retain its applied derivations for initial F.
let runWithEvidence (nodes: Map<NodeId, SemanticNode>) : Result =
    // Preserve the checked binders and their actual implementation ownership.
    // Measures do not split native bodies, but their occurrence substitutions
    // remain source facts; erasing TForall must not erase that authority.
    let mutable current = nodes
    for KeyValue(id, node) in nodes do
        match node.Kind, node.Type with
        | SemanticKind.Binding(_, false, _, _), (NativeType.TForall(parameters, body) as scheme) ->
            match applySubst body with
            | NativeType.TFun _ ->
                let metadata = node.Metadata.Add(SchemeMetadata.Declaration, MetadataValue.Type scheme)
                let ty = if parameters |> List.forall (fun parameter -> parameter.Kind = TypeParamKind.Measure) then body else node.Type
                current <- current.Add(id, { node with Type = ty; Metadata = metadata })
                match node.Children with
                | [value] ->
                    match current.TryFind value with
                    | Some ({ Kind = SemanticKind.Lambda _ } as implementation) ->
                        let metadata = implementation.Metadata
                                           .Add(SchemeMetadata.Declaration, MetadataValue.Type scheme)
                                           .Add(SchemeMetadata.ImplementationDeclaration, MetadataValue.NodeId id)
                        current <- current.Add(value, { implementation with Metadata = metadata })
                    | _ -> ()
                | _ -> ()
            | _ -> ()
        | _ -> ()
    let recursiveNodes, recursiveEvidence = specializeRecursiveComponents current
    current <- recursiveNodes
    let mutable evidence = recursiveEvidence
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
            // Instantiate the final alias first. Its retirement removes generic
            // forwarding references before upstream declarations discover uses.
            |> List.sortByDescending (fun (_, _, _, _, value) ->
                bareLibraryOperation current value |> Option.map snd |> Option.defaultValue 0)
        for (bindingId, bindingNode, rawTypars, rawSchemeBody, lambdaId) in generics do
            // Re-root the scheme: unions since generalization may have moved a parameter's root.
            let typars = rawTypars |> List.map (fun tp -> fst (find tp)) |> List.distinctBy (fun tp -> tp.Id)
            let schemeBody = canonicalizeVars rawSchemeBody
            let bindingName = match bindingNode.Kind with SemanticKind.Binding (n, _, _, _) -> n | _ -> "generic"
            // A scheme with no key material (only measure-kinded parameters) is one body (d.3):
            // the binding keeps its name and its monotype body (whose measure variables stay, as
            // any monotype's do), and its use sites keep pointing at it; nothing is cloned or renamed.
            let hasKeyMaterial = typars |> List.exists (fun tp -> tp.Kind <> TypeParamKind.Measure)
            if not hasKeyMaterial then
                current <- Map.add bindingId { bindingNode with Type = schemeBody } current
            else
                // Use sites: VarRefs whose definition is this binding
                let useSites =
                    current
                    |> Map.toList
                    |> List.choose (fun (id, node) ->
                        match node.Kind with
                        | SemanticKind.VarRef (_, Some def) when node.IsReachable && def = bindingId -> Some (id, node)
                        | _ -> None)
                if List.isEmpty useSites then
                    // No live instantiation: retire execution without erasing
                    // earlier derivation participants or source navigation.
                    progress <- true
                    current <- replaceBindingMembership bindingId [] true current
                    let retained = evidence |> List.collect (fun edge -> edge.Target :: edge.Sources) |> Set.ofList
                    for id in collectSubtree current bindingId do
                        if retained.Contains id then
                            current <- current.Add(id, { current[id] with IsReachable = false; Metadata = current[id].Metadata.Add(SchemeMetadata.HistoricalOnly, MetadataValue.Bool true) })
                        else current <- current.Remove id
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
                    let mutable instanceMetadata : Map<NodeId, Map<string, MetadataValue>> = Map.empty
                    groups |> List.iteri (fun gi (_, members) ->
                        let (_, subst, _) = List.head members
                        let checkedInstances = members |> List.map (fun (_, _, id) ->
                            id, checkedArguments bindingId typars schemeBody current[id])
                        // Code grouping remains measure-independent. A uniform
                        // checked measure can specialize this existing group;
                        // a differing/unknown request retains its measure binder.
                        // The complete request set is retained in the tape below.
                        let uniformMeasures =
                            typars |> List.indexed |> List.choose (fun (ordinal, parameter) ->
                                if parameter.Kind <> TypeParamKind.Measure then None else
                                let values = checkedInstances |> List.map (fun (_, values) -> values |> Option.map (List.item ordinal))
                                if List.exists Option.isNone values then None else
                                match values |> List.choose id |> List.distinct with
                                | [NativeType.TMeasure dimension as argument] when dimension.Vars.IsEmpty -> Some(parameter.Id, argument)
                                | _ -> None) |> Map.ofList
                        let itself (tp: TypeParam) =
                            match tp.Kind with
                            | TypeParamKind.Carrier -> NativeType.TNum (CarrierRef.CVar tp, Dimension.one)
                            | TypeParamKind.Measure -> NativeType.TMeasure (Dimension.ofVar (measureVarOf tp))
                            | TypeParamKind.Type -> NativeType.TVar tp
                        let args = typars |> List.map (fun tp ->
                            match Map.tryFind tp.Id subst |> Option.orElseWith (fun () -> uniformMeasures.TryFind tp.Id) with
                            | Some ty -> ty
                            | None -> itself tp)
                        let substitute (ty: NativeType) = Clef.Compiler.NativeTypedTree.NativeTypes.instantiate typars args (canonicalizeVars ty)
                        let residual = typars |> List.filter (fun tp -> tp.Kind = TypeParamKind.Measure && not (uniformMeasures.ContainsKey tp.Id))
                        let signature = substitute schemeBody
                        let cloneName = sprintf "%s__mono%d" bindingName (gi + 1)
                        let newBindingId = NodeId.fresh()
                        let before = current
                        let (newLambdaId, clonedNodes, mapping) = cloneSubtreeWithOrigins current lambdaId substitute (Some newBindingId)
                        let newBinding =
                            { bindingNode with
                                Id = newBindingId
                                Kind = SemanticKind.Binding (cloneName, false, false, None)
                                Type = signature
                                Children = [newLambdaId]
                                Metadata = residualMetadata newBindingId residual signature bindingNode.Metadata }
                        for n in clonedNodes do
                            let node =
                                if n.Id = newLambdaId then
                                    { n with Metadata = residualMetadata newBindingId residual signature n.Metadata }
                                else n
                            current <- Map.add node.Id node current
                        current <- Map.add newBindingId newBinding current
                        let requests = members |> List.map (fun (_, _, useId) -> useId, formatType before[useId].Type)
                        let updated, edges = recordDerivation bindingId newBindingId typars args requests before (mapping.Add(bindingId, newBindingId)) current
                        current <- updated
                        evidence <- edges @ evidence
                        cloneIds <- cloneIds @ [newBindingId]
                        for (useId, actualArguments) in checkedInstances do
                            redirect <- Map.add useId newBindingId redirect
                            // Only a checker-issued instance can authorize the
                            // residual scheme's use at this exact occurrence.
                            let metadata = projectInstanceMetadata newBindingId typars residual signature actualArguments current[useId].Metadata
                            instanceMetadata <- instanceMetadata.Add(useId, metadata))
                    // Repoint use sites at their clone
                    for (useId, useNode) in useSites do
                        match Map.tryFind useId redirect with
                        | Some target ->
                            let name = match useNode.Kind with SemanticKind.VarRef (n, _) -> n | _ -> bindingName
                            current <- Map.add useId
                                { useNode with Kind = SemanticKind.VarRef (name, Some target)
                                               Metadata = instanceMetadata[useId] } current
                        | None -> ()
                    // Replace execution membership; keep source participants.
                    current <- replaceBindingMembership bindingId cloneIds true current
                    // Retired source is evidence, never an executable root.
                    for id in collectSubtree current bindingId do
                        current <- current.Add(id, { current[id] with IsReachable = false; Metadata = current[id].Metadata.Add(SchemeMetadata.HistoricalOnly, MetadataValue.Bool true) })
    { Nodes = current; Derivations = evidence }

/// Compatibility for callers that only need the executable node rewrite.
let run nodes = (runWithEvidence nodes).Nodes
