// SPDX-License-Identifier: MIT
/// Check non-null foreign values while CCS still owns resolved source types.
/// Zero bytes can denote an absent Option, but never a CHandle or native entry.
module Clef.Compiler.PSGSaturation.SemanticGraph.BoundaryValues

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

/// Built-in unions have canonical constructor identities and source-declared
/// cases, even when they do not contribute a user TypeDef node to this graph.
let private unionCases graph ty =
    let same left right =
        Clef.Compiler.NativeTypedTree.TypeIdentities.constructor left =
            Clef.Compiler.NativeTypedTree.TypeIdentities.constructor right
    match applySubst ty with
    | NativeType.TApp(tc, [payload]) when same tc Clef.Compiler.NativeTypedTree.Expressions.Types.optionTycon ->
        Some ["None", []; "Some", [None, payload]]
    | NativeType.TApp(tc, [payload]) when same tc Clef.Compiler.NativeTypedTree.Expressions.Types.voptionTycon ->
        Some ["ValueNone", []; "ValueSome", [None, payload]]
    | NativeType.TApp(tc, [ok; error]) when same tc Clef.Compiler.NativeTypedTree.Expressions.Types.resultTycon ->
        Some ["Ok", [None, ok]; "Error", [None, error]]
    | _ -> RecordInstances.tryUnionCases ty graph

/// A concrete instance cannot hide an invalid native signature behind a type
/// abbreviation or a generic aggregate. Unresolved declaration parameters remain
/// symbolic until a consumer establishes their instance.
let typeDiagnostics (graph: SemanticGraph) : Diagnostic list =
    let rec invalidSignature seen ty =
        let ty = applySubst ty
        let key = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType ty
        if Set.contains key seen then false else
        let seen = Set.add key seen
        let any = List.exists (invalidSignature seen)
        match ty with
        | NativeType.TApp(tc, [signature]) when tc = Types.fnPtrTyCon ->
            match applySubst signature with
            | NativeType.TFun _ -> invalidSignature seen signature
            | NativeType.TVar _ | NativeType.TError _ -> false
            | _ -> true
        | NativeType.TFun(domain, result) -> any [domain; result]
        | NativeType.TForall(_, body) -> invalidSignature seen body
        | NativeType.TTuple(fields, _) -> any fields
        | NativeType.TByref(inner, _) | NativeType.TNativePtr inner | NativeType.TLazy inner -> invalidSignature seen inner
        | NativeType.TApp(_, arguments) ->
            any arguments ||
            (RecordInstances.tryFields ty graph |> Option.exists (List.exists (snd >> invalidSignature seen))) ||
            (unionCases graph ty |> Option.exists (List.exists (snd >> List.exists (snd >> invalidSignature seen))))
        | NativeType.TUnion(_, cases) ->
            cases |> List.exists (fun case -> case.Fields |> List.exists (snd >> invalidSignature seen))
        | _ -> false
    graph.Nodes.Values |> Seq.choose (fun node ->
        if not (invalidSignature Set.empty node.Type) then None else
        Some { Severity = NativeDiagnosticSeverity.Error; Code = "CCS8096"
               Message = "FnPtr requires a function signature; this concrete source instance supplies a non-function payload."
               Range = node.Range; RelatedNodes = [node.Id]; Reachability = ReachabilityContext.Unknown })
    |> Seq.distinctBy _.Range |> Seq.toList

let diagnostics (graph: SemanticGraph) : Diagnostic list =
    let rec containsNonNull seen ty =
        let ty = applySubst ty
        let key = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType ty
        if Set.contains key seen then false else
        let seen = Set.add key seen
        match ty with
        | NativeType.TApp(tc, _) when tc = Types.cHandleTyCon || tc = Types.fnPtrTyCon -> true
        // The zero representation selects None; its dormant payload is absent.
        | NativeType.TApp(tc, _) when
            Clef.Compiler.NativeTypedTree.TypeIdentities.constructor tc = Clef.Compiler.NativeTypedTree.TypeIdentities.constructor Clef.Compiler.NativeTypedTree.Expressions.Types.optionTycon ||
            Clef.Compiler.NativeTypedTree.TypeIdentities.constructor tc = Clef.Compiler.NativeTypedTree.TypeIdentities.constructor Clef.Compiler.NativeTypedTree.Expressions.Types.voptionTycon -> false
        | NativeType.TTuple(fields, _) -> fields |> List.exists (containsNonNull seen)
        | NativeType.TFun(_, result) | NativeType.TForall(_, result) -> containsNonNull seen result
        | NativeType.TApp _ ->
            let fields =
                RecordInstances.tryFields ty graph
                |> Option.map (List.map snd)
                |> Option.orElseWith (fun () ->
                    unionCases graph ty
                    |> Option.bind List.tryHead |> Option.map (snd >> List.map snd))
            fields |> Option.exists (List.exists (containsNonNull seen))
        | NativeType.TUnion(_, cases) ->
            cases |> List.tryHead |> Option.exists (fun first -> first.Fields |> List.exists (snd >> containsNonNull seen))
        | _ -> false
    let rec resultType = function
        | NativeType.TForall(_, body) | NativeType.TFun(_, body) -> resultType body
        | ty -> ty
    // A polymorphic intrinsic keeps its declaration scheme on the value node.
    // Its consumer supplies the concrete instance, including when the factory
    // travels through aliases, aggregates or higher-order arguments.
    let rec inspect seen expected id =
        if Set.contains id seen then [] else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some ({ Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.NativeDefault; Operation = "zeroed" } } as node) ->
            if containsNonNull Set.empty (resultType expected) then [node] else []
        | Some ({ Kind = SemanticKind.Binding _ } as binding) ->
            if Clef.Compiler.Baker.Recipes.BoundaryDeclarations.isExternal binding then []
            else binding.Children |> List.collect (inspect seen expected)
        | Some { Kind = SemanticKind.VarRef(_, Some value) | SemanticKind.TypeAnnotation(value, _)
                       | SemanticKind.EagerExpr value } -> inspect seen expected value
        | Some { Kind = SemanticKind.Sequential values } ->
            values |> List.tryLast |> Option.map (inspect seen expected) |> Option.defaultValue []
        | Some { Kind = SemanticKind.IfThenElse(_, yes, no) } ->
            (yes :: Option.toList no) |> List.collect (inspect seen expected)
        | Some { Kind = SemanticKind.RecordExpr(fields, _) } ->
            let types = RecordInstances.tryFields expected graph |> Option.defaultValue [] |> Map.ofList
            fields |> List.collect (fun (name, value) ->
                types.TryFind name |> Option.map (fun ty -> inspect seen ty value) |> Option.defaultValue [])
        | Some { Kind = SemanticKind.TupleExpr values } ->
            match applySubst expected with
            | NativeType.TTuple(types, _) when types.Length = values.Length ->
                List.zip types values |> List.collect (fun (ty, value) -> inspect seen ty value)
            | _ -> []
        | Some { Kind = SemanticKind.UnionCase(name, tag, Some payload)
                       | SemanticKind.DUConstruct(name, tag, Some payload, _) } ->
            unionCases graph expected
            |> Option.bind (List.tryItem tag)
            |> Option.filter (fun (declaredName, _) -> declaredName = name)
            |> Option.map (fun (_, fields) ->
                match fields |> List.map snd with
                | [ty] -> inspect seen ty payload
                | types -> inspect seen (NativeType.TTuple(types, false)) payload)
            |> Option.defaultValue []
        | Some ({ Kind = SemanticKind.Application(callee, _) } as node) ->
            match Clef.Compiler.Baker.Recipes.BoundaryDeclarations.target graph callee with
            | Some ({ Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.NativeDefault; Operation = "zeroed" } }, _)
                when containsNonNull Set.empty (resultType expected) -> [node]
            | _ -> []
        | _ -> []
    let rec argumentTypes ty values =
        match applySubst ty, values with
        | NativeType.TForall(_, body), _ -> argumentTypes body values
        | NativeType.TFun(domain, result), value :: rest -> (domain, value) :: argumentTypes result rest
        | _ -> []
    graph.Nodes.Values
    |> Seq.collect (fun node ->
        if not node.IsReachable then [] else
        let own = inspect Set.empty node.Type node.Id
        let arguments =
            match node.Kind with
            | SemanticKind.Application(callee, values) ->
                graph.Nodes.TryFind callee
                |> Option.map (fun target -> argumentTypes target.Type values |> List.collect (fun (ty, value) -> inspect Set.empty ty value))
                |> Option.defaultValue []
            | _ -> []
        own @ arguments)
    |> Seq.map (fun node ->
        { Severity = NativeDiagnosticSeverity.Error
          Code = "CCS8010"
          Message = "NativeDefault.zeroed cannot construct a non-null CHandle or FnPtr, including a record or tuple containing one. Obtain the value from a declared foreign boundary or FnPtr.ofFunction; use None for absence."
          Range = node.Range; RelatedNodes = [node.Id]
          Reachability = ReachabilityContext.Reachable })
    |> Seq.distinctBy _.Range
    |> Seq.toList
