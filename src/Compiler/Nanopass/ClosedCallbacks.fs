// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// A declared closed callback adapter is specialized while the typed graph
/// still carries source identities. The result is an ordinary module function
/// and listener construction, validated by the existing native entry reader.
module Clef.Compiler.Nanopass.ClosedCallbacks

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
open Clef.Compiler.PSGSaturation.SemanticGraph.MappedBindings
open Clef.Compiler.PSGSaturation.SemanticGraph.Reachability
open Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

type private Declaration = {
    Site: SemanticNode
    Factory: SemanticNode
    Adapter: SemanticNode
    Field: string
    RecordType: NativeType
    PointerType: NativeType
    EntryType: NativeType
    HandlerType: NativeType
}

let private sameType left right = formatType (applySubst left) = formatType (applySubst right)

let expand (graph: SemanticGraph) : SemanticGraph * Diagnostic list =
    let mutable diagnostics = []
    let error (site: SemanticNode) message =
        diagnostics <- {
            Severity = NativeDiagnosticSeverity.Error
            Code = Clef.Compiler.NativeTypedTree.Expressions.Types.DiagnosticCodes.CCS8096_ClosedCallbackDeclaration
            Message = message
            Range = site.Range
            RelatedNodes = [site.Id]
            Reachability = ReachabilityContext.Reachable
        } :: diagnostics
    let moduleLevel (node: SemanticNode) =
        match node.Parent |> Option.bind (fun parent -> SemanticGraph.tryGetNode parent graph) with
        | Some { Kind = SemanticKind.ModuleDef _ } -> true
        | _ -> false
    let closedDeclaration (node: SemanticNode) =
        match node.Kind, node.Children with
        | SemanticKind.Binding (_, false, _, _), [body] when moduleLevel node ->
            match graph.Nodes[body].Kind with
            | SemanticKind.Lambda (_, _, [], _, _) -> true
            | _ -> false
        | _ -> false
    let rec unannotated id =
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> unannotated inner
        | node -> node
    let zeroedPlaceholder id =
        match unannotated id with
        | Some { Kind = SemanticKind.Application (callee, [argument]) } ->
            match unannotated callee, unannotated argument with
            | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.NativeDefault; Operation = "zeroed" } },
              Some { Kind = SemanticKind.Literal NativeLiteral.Unit } -> true
            | _ -> false
        | _ -> false
    let bindings = graph.Nodes.Values |> Seq.filter (fun node ->
        match node.Kind with SemanticKind.Binding _ -> true | _ -> false) |> Seq.toList
    let moduleBindings = bindings |> List.filter moduleLevel
    let qualified name = bindings |> List.filter (fun node -> qualifiedBindingName graph node = name)
    let mutable declarations = []
    for binding in bindings do
        match List.tryLast binding.Children |> Option.bind (recordOf graph) with
        | Some (site, _) when typeName site = Some "ClosedCallbackDescriptor" && not (moduleLevel binding) ->
            error site "A ClosedCallbackDescriptor must be a module-level declaration."
        | Some (site, fields) when typeName site = Some "ClosedCallbackDescriptor" ->
            let text name = field name fields |> Option.bind (stringOf graph)
            match text "Binding", text "Adapter", text "Record", text "Field" with
            | Some factoryName, Some adapterName, Some recordName, Some fieldName ->
                match qualified factoryName, qualified adapterName with
                | [factory], [adapter] when closedDeclaration factory && closedDeclaration adapter ->
                    match lambdaOfBinding graph factory.Id, lambdaOfBinding graph adapter.Id, applySubst factory.Type with
                    | Some ([_], factoryBody), Some ((_, handlerType, handlerParameter) :: _, adapterBody), NativeType.TFun (factoryHandler, (NativeType.TApp (tc, _) as recordType)) when zeroedPlaceholder factoryBody ->
                        let recordMatches = tc.Name = recordName || (not (recordName.Contains('.')) && (tc.Name.Split('.') |> Array.last) = recordName)
                        let recordFields = SemanticGraph.tryGetRecordFields tc.Name graph
                        match recordFields, applySubst adapter.Type, applySubst factoryHandler with
                        | Some [(actualField, (NativeType.TApp (pointer, [entryType]) as pointerType))], NativeType.TFun (_, adapterEntry), NativeType.TFun _
                            when recordMatches && actualField = fieldName && pointer.NTUKind = Some NTUKind.NTUfnptr
                                 && sameType factoryHandler handlerType && sameType entryType adapterEntry ->
                            let matchingRecords =
                                graph.Nodes.Values |> Seq.choose (fun node ->
                                    match node.Kind with
                                    | SemanticKind.TypeDef (name, TypeDefKind.RecordDef _, _)
                                        when name = recordName || (not (recordName.Contains('.')) && (name.Split('.') |> Array.last) = recordName) -> Some name
                                    | _ -> None) |> Seq.toList
                            let nativeDeclaration = matchingRecords.Length = 1 && (moduleBindings |> List.exists (fun candidate ->
                                match List.tryLast candidate.Children |> Option.bind (recordOf graph) with
                                | Some (descriptor, fields) when typeName descriptor = Some "CallbackDescriptor" ->
                                    field "Record" fields |> Option.bind (stringOf graph) = Some recordName
                                    && field "Field" fields |> Option.bind (stringOf graph) = Some fieldName
                                | _ -> false))
                            let rec capturesHandler seen id =
                                if Set.contains id seen then false else
                                let node = graph.Nodes[id]
                                let nestedCapture =
                                    match node.Kind with
                                    | SemanticKind.Lambda (_, _, captures, _, _) ->
                                        captures |> List.exists (fun capture -> capture.SourceNodeId = Some handlerParameter)
                                    | _ -> false
                                nestedCapture || (node.Children |> List.exists (capturesHandler (Set.add id seen)))
                            if capturesHandler Set.empty adapterBody then
                                error site "A closed callback adapter cannot capture its handler in a nested closure."
                            elif nativeDeclaration then
                                declarations <- { Site = site; Factory = factory; Adapter = adapter; Field = fieldName
                                                  RecordType = recordType; PointerType = pointerType; EntryType = entryType
                                                  HandlerType = handlerType } :: declarations
                            else error site "A closed callback adapter requires the native listener field's CallbackDescriptor."
                        | _ -> error site "A closed callback factory must return a one-field native listener; its adapter takes the handler followed by that field's complete native entry signature."
                    | _ -> error site "A closed callback factory takes one function and its body must be exactly NativeDefault.zeroed (); its adapter is a module function with that handler first."
                | _ -> error site "A closed callback declaration must name unique fully qualified immutable module functions without captures."
            | _ -> error site "A ClosedCallbackDescriptor requires literal Binding, Adapter, Record and Field names."
        | _ -> ()

    let duplicateFactories = declarations |> List.groupBy (fun declaration -> declaration.Factory.Id) |> List.filter (fun (_, values) -> values.Length > 1)
    let duplicates = duplicateFactories |> List.map fst |> Set.ofList
    for _, values in duplicateFactories do
        for declaration in values do error declaration.Site "A closed callback factory has more than one declaration."
    let declarations = declarations |> List.filter (fun declaration -> not (duplicates.Contains declaration.Factory.Id))
    let reachable = computeReachable graph (graph.DeclarationRoots |> List.map fst)
    let rec namedModule seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> namedModule seen inner
        | Some { Kind = SemanticKind.VarRef (_, Some target) } -> namedModule seen target
        | Some ({ Kind = SemanticKind.Binding (_, false, _, _); Children = [body] } as binding) ->
            match binding.Parent |> Option.bind (fun parent -> SemanticGraph.tryGetNode parent graph), SemanticGraph.tryGetNode body graph with
            | Some { Kind = SemanticKind.ModuleDef _ }, Some { Kind = SemanticKind.Lambda (_, _, [], _, _) } -> Some binding
            | _, Some { Kind = SemanticKind.VarRef _ | SemanticKind.TypeAnnotation _ } -> namedModule seen body
            | _ -> None
        | _ -> None
    let rec factoryOf id =
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> factoryOf inner
        | Some { Kind = SemanticKind.VarRef (_, Some target) } -> declarations |> List.tryFind (fun declaration -> declaration.Factory.Id = target)
        | _ -> None

    let mutable nodes = graph.Nodes
    let mutable entries = Map.empty<NodeId * NodeId, NodeId>
    for site in graph.Nodes.Values do
        match site.Kind with
        | SemanticKind.Application (callee, [handler]) when reachable.Contains site.Id ->
            match factoryOf callee with
            | Some declaration ->
                match namedModule Set.empty handler with
                | Some target when sameType target.Type declaration.HandlerType ->
                    let key = declaration.Factory.Id, target.Id
                    let entryBinding =
                        match entries.TryFind key with
                        | Some id -> id
                        | None ->
                            let adapterLambda = List.exactlyOne declaration.Adapter.Children
                            let entryId = NodeId.fresh()
                            let lambdaId, cloned = Monomorphization.cloneSubtree nodes adapterLambda id (Some entryId)
                            for node in cloned do nodes <- nodes.Add(node.Id, markBaker "ClosedCallback" (NodeId.value site.Id) { node with IsReachable = true })
                            let clonedLambda = nodes[lambdaId]
                            let allParameters, result =
                                let rec parameters current =
                                    match nodes[current].Kind with
                                    | SemanticKind.Lambda (arguments, body, _, _, _) ->
                                        match nodes[body].Kind with
                                        | SemanticKind.Lambda _ -> let rest, result = parameters body in arguments @ rest, result
                                        | _ -> arguments, body
                                    | _ -> [], current
                                parameters lambdaId
                            let _, _, handlerParameter = List.head allParameters
                            let nativeParameters = List.tail allParameters
                            let entryName = sprintf "__closed_callback_%d_%d" (NodeId.value declaration.Factory.Id) (NodeId.value target.Id)
                            let targetName = qualifiedBindingName graph target
                            for node in cloned do
                                match node.Kind with
                                | SemanticKind.VarRef (_, Some definition) when definition = handlerParameter ->
                                    nodes <- nodes.Add(node.Id, { nodes[node.Id] with Kind = SemanticKind.VarRef (targetName, Some target.Id); Type = target.Type })
                                | _ -> ()
                            let captures, enclosing, context =
                                match clonedLambda.Kind with
                                | SemanticKind.Lambda (_, _, captures, enclosing, context) -> captures, enclosing, context
                                | _ -> failwith "A closed adapter's lambda disappeared while cloning."
                            let specializedLambda =
                                { nodes[lambdaId] with
                                    Kind = SemanticKind.Lambda (nativeParameters, result, captures, enclosing, context)
                                    Type = declaration.EntryType
                                    Children = (nativeParameters |> List.map (fun (_, _, id) -> id)) @ [result] }
                            nodes <- nodes.Add(lambdaId, specializedLambda)
                            for child in nodes[lambdaId].Children do nodes <- nodes.Add(child, { nodes[child] with Parent = Some lambdaId })
                            let entry =
                                { declaration.Adapter with
                                    Id = entryId; Kind = SemanticKind.Binding (entryName, false, false, None)
                                    Type = declaration.EntryType; Children = [lambdaId]; IsReachable = true
                                    Metadata = Map.empty }
                            nodes <- nodes.Add(entryId, markBaker "ClosedCallback" (NodeId.value site.Id) entry)
                            match entry.Parent |> Option.bind (fun parent -> nodes.TryFind parent) with
                            | Some ({ Kind = SemanticKind.ModuleDef (name, members) } as owner) ->
                                nodes <- nodes.Add(owner.Id, { owner with Kind = SemanticKind.ModuleDef (name, members @ [entryId]); Children = owner.Children @ [entryId] })
                            | _ -> error declaration.Site "A closed callback adapter must be a module-level function."
                            entries <- entries.Add(key, entryId)
                            entryId
                    let entryName = match nodes[entryBinding].Kind with SemanticKind.Binding (name, _, _, _) -> name | _ -> ""
                    let referenceId, intrinsicId, addressId = NodeId.fresh(), NodeId.fresh(), NodeId.fresh()
                    let reference = { site with Id = referenceId; Kind = SemanticKind.VarRef (entryName, Some entryBinding); Type = declaration.EntryType; Children = []; Parent = Some addressId; Metadata = Map.empty }
                    let intrinsicInfo =
                        { Module = IntrinsicModule.FnPtr; Operation = "ofFunction"
                          Category = IntrinsicCategory.Pure; FullName = "FnPtr.ofFunction" }
                    let intrinsic =
                        { reference with Id = intrinsicId; Kind = SemanticKind.Intrinsic intrinsicInfo
                                         Type = NativeType.TFun (declaration.EntryType, declaration.PointerType) }
                    let address = { site with Id = addressId; Kind = SemanticKind.Application (intrinsicId, [referenceId]); Type = declaration.PointerType
                                              Children = [intrinsicId; referenceId]; Parent = Some site.Id; Metadata = Map.empty }
                    for node in [reference; intrinsic; address] do nodes <- nodes.Add(node.Id, markBaker "ClosedCallback" (NodeId.value site.Id) node)
                    nodes <- nodes.Add(site.Id, { site with Kind = SemanticKind.RecordExpr ([declaration.Field, addressId], None); Type = declaration.RecordType; Children = [addressId] })
                | _ -> error site "A closed callback adapter requires a named module handler without captures; use an inline binding wrapper so its target is known here."
            | None -> ()
        | _ -> ()
    let expanded =
        { graph with Nodes = nodes; Types = SemanticGraph.mkTypesIndex nodes; ModuleClassifications = SemanticGraph.mkModuleClassifications nodes }
    let remaining = computeReachable expanded (expanded.DeclarationRoots |> List.map fst)
    let factories = declarations |> List.map (fun declaration -> declaration.Factory.Id) |> Set.ofList
    for node in expanded.Nodes.Values do
        match node.Kind with
        | SemanticKind.VarRef (_, Some target) when remaining.Contains node.Id && factories.Contains target ->
            error node "A closed callback factory must be applied directly to a known closed module handler; it cannot escape as a function value."
        | _ -> ()
    expanded, List.rev diagnostics
