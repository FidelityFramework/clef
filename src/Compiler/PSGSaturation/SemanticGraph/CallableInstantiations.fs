// SPDX-License-Identifier: MIT
/// Checker-owned scheme instances survive shared code and immutable value flow.
/// This reader composes the arguments actually minted during checking. It does
/// not solve new dimensional equations, mutate unification state, or replay a
/// callable's initializer to obtain another environment.
module Clef.Compiler.PSGSaturation.SemanticGraph.CallableInstantiations

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

type Template = {
    Declaration: NodeId
    Implementation: NodeId
    Parameters: TypeParam list
    Signature: NativeType
}

type Evidence = {
    Occurrence: NodeId
    Template: Template
    Arguments: NativeType list
    InstanceType: NativeType
    Participants: Set<NodeId>
    ValuePath: Set<NodeId>
}

let private publicType = SchemeInstances.publicType
let private scheme = SchemeInstances.scheme
let private measureParameters = SchemeInstances.measureParameters

/// Implementation ownership is a source declaration relationship, independent
/// of a generated symbol's spelling and of any environment instance address.
let private templateWith implementationOf (graph: SemanticGraph) implementation signature =
    match graph.Nodes.TryFind implementation with
    | Some ({ Kind = SemanticKind.Lambda(parameters, result, _, _, _) } as code)
        when graph.Nodes.TryFind result |> Option.exists (fun body ->
            applySubst code.Type = applySubst (List.foldBack (fun (_, ty, _) tail -> NativeType.TFun(ty, tail)) parameters body.Type)) ->
        match code.Metadata.TryFind SchemeMetadata.ImplementationDeclaration, scheme code with
        | Some(MetadataValue.NodeId declaration), Some(parameters, body) when measureParameters parameters ->
            match graph.Nodes.TryFind declaration with
            | Some ({ Kind = SemanticKind.Binding(_, false, _, _) } as source)
                when scheme source = Some(parameters, body) &&
                     applySubst body = applySubst signature && publicType source = applySubst body &&
                     implementationOf declaration = Some implementation ->
                Some { Declaration = declaration; Implementation = implementation; Parameters = parameters; Signature = body }
            | _ -> None
        | _ -> None
    | _ -> None

let template graph implementation signature =
    templateWith (ClosureEnvironments.tryImplementation graph) graph implementation signature

/// Build once per immutable reading: closed ingress, source reference origins
/// and complete formal/result calls are shared by every instance query.
let readerWith (graph: SemanticGraph) (resolution: CallableOrigins.Resolution) (ingress: CallableIngress.Reading) =
    let checkedInstance = SchemeInstances.reader graph
    let capturedValue = ClosureEnvironments.tryCapturedValue graph
    let implementationOf = ClosureEnvironments.tryImplementation graph
    let templates = System.Collections.Generic.Dictionary<NodeId, Template option>()
    let declared implementation signature =
        let cached =
            match templates.TryGetValue implementation with
            | true, value -> value
            | _ ->
                // Cache declaration authority, not a caller's proposed view.
                // A rejected request must not poison later lawful queries.
                let value = graph.Nodes.TryFind implementation |> Option.bind (fun code ->
                    templateWith implementationOf graph implementation (publicType code))
                templates.Add(implementation, value)
                value
        cached |> Option.filter (fun value -> applySubst value.Signature = applySubst signature)
    let sourceType id = graph.Nodes.TryFind id |> Option.map publicType
    fun implementation signature occurrence ->
        match declared implementation signature, graph.Nodes.TryFind occurrence,
              (CallableIngress.tryEvidence ingress occurrence |> Option.orElseWith (fun () -> CallableIngress.tryRetainedEvidence ingress occurrence)) with
        | Some declared, Some occurrenceNode, Some ingressEvidence ->
            let instanceType = publicType occurrenceNode
            let rec walk pending transform participants id =
                if Set.contains id pending then None else
                let pending = Set.add id pending
                let participants = Set.add id participants
                match graph.Nodes.TryFind id with
                | Some node when applySubst (transform (publicType node)) = instanceType ->
                    let next = walk pending transform participants
                    let all values =
                        let proofs = values |> List.map next
                        if proofs.IsEmpty || List.exists Option.isNone proofs then None else
                        let proofs = List.choose (fun proof -> proof) proofs
                        let firstArguments, _ = List.head proofs
                        if proofs |> List.exists (fun (arguments, _) -> arguments <> firstArguments) then None
                        else Some(firstArguments, proofs |> List.map snd |> Set.unionMany)
                    match node.Kind, node.Children with
                    | SemanticKind.Lambda _, _ when id = implementation ->
                        let values = declared.Parameters |> List.map (fun parameter ->
                            NativeType.TMeasure(Clef.Compiler.NativeTypedTree.DimensionAlgebra.Dimension.ofVar (measureVarOf parameter))
                            |> transform |> applySubst)
                        if applySubst (instantiate declared.Parameters values declared.Signature) = instanceType then
                            Some(values, Set.add declared.Declaration participants)
                        else None
                    | SemanticKind.ClosureValue(code, _), _ when code = implementation ->
                        // The physical lambda has a real leading environment
                        // formal; its public signature is the source front's.
                        walk pending transform participants code
                    | SemanticKind.VarRef(_, Some target), _ ->
                        match checkedInstance id with
                        | Some instance ->
                            walk pending (instantiate instance.Parameters instance.Arguments >> transform)
                                (Set.union participants instance.Participants) instance.Declaration
                        | None when not (node.Metadata.ContainsKey SchemeMetadata.Definition) &&
                                    not (node.Metadata.ContainsKey SchemeMetadata.Declaration) &&
                                    sourceType target = Some(publicType node) -> next target
                        | _ -> None
                    | SemanticKind.Binding(_, false, _, _), [value]
                    | SemanticKind.TypeAnnotation(value, _), _ when sourceType value = Some(publicType node) -> next value
                    | SemanticKind.EagerExpr value, _ when ExplicitDemand.operand graph id = Some value && sourceType value = Some(publicType node) -> next value
                    | SemanticKind.Sequential values, _ when node.Children = values ->
                        List.tryLast values |> Option.bind next
                    | SemanticKind.FrameRead(_, slot), _ ->
                        match CallableIngress.tryEvidence ingress id with
                        | Some access when access.Participants.Contains slot && sourceType slot = Some(publicType node) ->
                            walk pending transform participants slot
                        | _ -> None
                    | SemanticKind.EnvironmentRead(environment, slot), _ ->
                        capturedValue environment slot |> Option.bind next
                    | SemanticKind.PatternBinding _, _ ->
                        resolution.ParameterInputs.TryFind id |> Option.map (List.map snd) |> Option.bind all
                    | SemanticKind.Application _, _ ->
                        resolution.Calls.TryFind id |> Option.bind (fun call ->
                            if call.Complete && not call.Unknown then call.Targets |> List.map _.Body |> all else None)
                    | SemanticKind.IfThenElse(_, yes, Some no), _ -> all [yes; no]
                    | _ -> None
                | _ -> None
            walk Set.empty (fun ty -> ty) Set.empty occurrence
            |> Option.map (fun (arguments, participants) ->
                { Occurrence = occurrence; Template = declared; Arguments = arguments
                  InstanceType = instanceType; ValuePath = participants
                  Participants = Set.union ingressEvidence.Participants (Set.add implementation participants) })
        | _ -> None

let reader graph =
    let resolution = CallableOrigins.resolve graph
    readerWith graph resolution (CallableIngress.analyzeWith graph resolution)

/// A shared physical signature may retain only its declared measure binders.
/// This does not license arbitrary free variables at data occurrences: the
/// participant must be an actual typed formal or the exact body result.
let allowsSignatureData (graph: SemanticGraph) (carrier: CallableCarrier) participant =
    match graph.Nodes.TryFind carrier.Implementation, graph.Nodes.TryFind participant with
    | Some ({ Kind = SemanticKind.Lambda(parameters, body, [], _, _); Type = physical } as code), Some node
        when parameters = carrier.Parameters && body = carrier.Result ->
        let signature = publicType code
        match template graph code.Id signature with
        | Some declared ->
            let rec result parameters ty =
                match parameters, applySubst ty with
                | [], ty -> Some ty
                | (_, expected, _) :: rest, NativeType.TFun(actual, tail) when applySubst expected = applySubst actual -> result rest tail
                | _ -> None
            let expected =
                parameters |> List.tryPick (fun (_, ty, id) -> if id = participant then Some ty else None)
                |> Option.orElseWith (fun () -> if body = participant then result parameters physical else None)
            let quantified = declared.Parameters |> List.map (measureVarOf >> fun variable -> variable.Id) |> Set.ofList
            expected = Some(applySubst node.Type) && not (hasUnboundVars node.Type) &&
            (freeMeasureVars node.Type |> List.forall (fun variable -> quantified.Contains variable.Id))
        | None -> false
    | _ -> false

type CallInstance = {
    Site: NodeId
    Implementation: NodeId
    Callable: Evidence
    Parameters: (string * NativeType * NodeId) list
    Arguments: NodeId list
    Result: NodeId
    SignatureData: Set<NodeId>
    Participants: Set<NodeId>
}

/// A physical direct call can still carry a quantified shared code signature.
/// Its concrete source instance comes from the actual callee/environment path,
/// including a fully validated continuation access, never from code identity.
let callReader (graph: SemanticGraph) =
    let resolution = CallableOrigins.resolve graph
    let ingress = CallableIngress.analyzeWith graph resolution
    let instance = readerWith graph resolution ingress
    let known = ClosureEnvironments.knownCallables graph
    let implementationOf = ClosureEnvironments.tryImplementation graph
    let invocations = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.EnvironmentInvocation) |> List.groupBy _.Target |> Map.ofList
    let originals = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.ContinuationValue) |> List.groupBy _.Target |> Map.ofList
    let rec invocationOrigin seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match invocations.TryFind id with
        | Some [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = callable :: implementation :: environment :: arguments }] ->
            match graph.Nodes.TryFind id, graph.Nodes.TryFind environment with
            | Some { Kind = SemanticKind.Application(callee, actual); Children = children },
              Some { Kind = SemanticKind.EnvironmentReference value; Children = [child] }
                when value = callable && child = callable && actual = environment :: arguments && children = callee :: actual &&
                     implementationOf callee = Some implementation ->
                Some(callable, implementation, environment, Set.ofList (id :: callee :: callable :: implementation :: environment :: arguments))
            | _ -> None
        | Some _ -> None
        | None ->
            match originals.TryFind id with
            | Some [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [original] }] ->
                CallableIngress.tryCorrespondence ingress original id |> Option.bind (fun participants ->
                    invocationOrigin seen original |> Option.map (fun (callable, implementation, environment, prior) ->
                        callable, implementation, environment, Set.union prior participants))
            | _ -> None
    let rec environmentCallable seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some node when applySubst node.Type = ClosureEnvironments.environmentType ->
            let add = Option.map (fun (callable, participants) -> callable, Set.add id participants)
            match node.Kind, node.Children with
            | SemanticKind.EnvironmentReference callable, [child] when child = callable -> Some(callable, Set.ofList [id; callable])
            | SemanticKind.VarRef(_, Some source), _
            | SemanticKind.TypeAnnotation(source, _), _
            | SemanticKind.Binding(_, false, _, _), [source] -> environmentCallable seen source |> add
            | SemanticKind.FrameRead _, _ ->
                CallableIngress.tryAccess ingress id |> Option.bind (fun access ->
                    environmentCallable seen access.Source |> Option.map (fun (callable, participants) ->
                        callable, Set.union participants access.Participants)) |> add
            | _ -> None
        | _ -> None
    fun site implementation ->
        match graph.Nodes.TryFind site, graph.Nodes.TryFind implementation, resolution.Calls.TryFind site with
        | Some ({ Kind = SemanticKind.Application(callee, arguments); IsReachable = true } as call),
          Some ({ Kind = SemanticKind.Lambda(parameters, body, [], _, LambdaContext.RegularClosure) } as code),
          Some invocation when invocation.Complete && not invocation.Unknown && call.Children = callee :: arguments ->
            match invocation.Targets, graph.Nodes.TryFind body with
            | [target], Some result when target.Lambda = implementation && target.Parameters = parameters &&
                                        target.Arguments = arguments && parameters.Length = arguments.Length &&
                                        applySubst code.Type = applySubst (List.foldBack (fun (_, ty, _) tail -> NativeType.TFun(ty, tail)) parameters result.Type) ->
                let signature = publicType code
                let environmentRows = graph.Edges |> List.filter (fun edge ->
                    edge.Role = EdgeRole.EnvironmentFormal && List.tryLast edge.Sources = Some implementation)
                let origin =
                    match environmentRows, parameters, arguments with
                    | [], _, _ -> Some(callee, parameters, Set.empty)
                    | [{ Class = EdgeClass.Provenance; Ordinal = 0; Sources = [owner; actual]; Target = formal }],
                      (_, ty, first) :: remaining, environment :: _
                        when actual = implementation && first = formal && applySubst ty = ClosureEnvironments.environmentType ->
                        environmentCallable Set.empty environment |> Option.bind (fun (callable, participants) ->
                            match known.TryFind callable, invocationOrigin Set.empty site with
                            | Some value, Some(original, target, _, origins)
                                when value.Implementation = implementation && value.EnvironmentOwner = owner &&
                                     target = implementation && original = callable ->
                                Some(callable, remaining, Set.unionMany [participants; origins; Set.ofList [owner; formal]])
                            | _ -> None)
                    | _ -> None
                origin |> Option.bind (fun (callable, visible, participants) ->
                    let logical = List.foldBack (fun (_, ty, _) result -> NativeType.TFun(ty, result)) visible result.Type
                    if applySubst logical <> signature then None else
                    instance implementation signature callable |> Option.bind (fun proof ->
                        let substitute = instantiate proof.Template.Parameters proof.Arguments >> applySubst
                        let parametersAgree =
                            List.zip parameters arguments |> List.forall (fun ((_, declared, formal), argument) ->
                                match graph.Nodes.TryFind formal, graph.Nodes.TryFind argument with
                                | Some { Kind = SemanticKind.PatternBinding _; Type = actual }, Some value ->
                                    applySubst actual = applySubst declared && substitute declared = applySubst value.Type
                                | _ -> false)
                        if not parametersAgree || substitute result.Type <> applySubst call.Type then None else
                        let quantified = proof.Template.Parameters |> List.map (measureVarOf >> fun variable -> variable.Id) |> Set.ofList
                        let data = body :: (parameters |> List.map (fun (_, _, formal) -> formal))
                        let valid = data |> List.forall (fun id ->
                            let ty = graph.Nodes[id].Type
                            not (hasUnboundVars ty) && (freeMeasureVars ty |> List.forall (fun variable -> quantified.Contains variable.Id)))
                        if not valid then None else
                        Some { Site = site; Implementation = implementation; Callable = proof; Parameters = parameters
                               Arguments = arguments; Result = body; SignatureData = Set.ofList data
                               Participants = Set.unionMany [proof.Participants; participants; Set.ofList (site :: callee :: implementation :: (data @ arguments))] }))
            | _ -> None
        | _ -> None

/// Validate an exact immutable transport step without changing either value.
/// The caller still checks actual implementation/environment and SSA identity.
let canTransport graph source destination =
    let read = reader graph
    match graph.Nodes.TryFind source, graph.Nodes.TryFind destination,
          ClosureEnvironments.tryImplementation graph source, ClosureEnvironments.tryImplementation graph destination with
    | Some _, Some _, Some implementation, Some actual when actual = implementation ->
        match graph.Nodes[implementation].Metadata.TryFind ClosureMetadata.SourceSignature with
        | Some(MetadataValue.Type signature) ->
            match read implementation signature source, read implementation signature destination with
            | Some left, Some right -> left.Template = right.Template && right.ValuePath.Contains source
            | _ -> false
        | _ -> false
    | _ -> false
