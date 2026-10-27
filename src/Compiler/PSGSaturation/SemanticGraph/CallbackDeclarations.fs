/// Generated callback descriptors bind listener fields to the actual native
/// entry supplied by the program. ABI ranges are declarations, never inferred
/// from one event value or from the machine's register width.
module Clef.Compiler.PSGSaturation.SemanticGraph.CallbackDeclarations

open System.Runtime.CompilerServices
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

type Callback = {
    Lambda: NodeId
    Address: NodeId
    Record: string
    Field: string
    Function: DeclaredFunction
    ReturnsVoid: bool
}

/// This is a declared receiving association, not code lifetime or a foreign call trace.
type ReceivingCallback = {
    Call: NodeId
    Operand: NodeId
    Lambda: NodeId
    Declaration: NodeId
    Address: NodeId
    Transport: NodeId list
    Invocation: DeclaredCallbackInvocation
    Signature: DeclaredEntrySignature
}

/// Source selection only; an absent arm has no manufactured receiving entry.
type OptionalReceivingCallback = {
    Call: NodeId
    Operand: NodeId
    Construction: NodeId
    CaseOrdinal: int
    Payload: NodeId option
    Transport: NodeId list
    Invocation: DeclaredCallbackInvocation
    Receiving: ReceivingCallback option
}

type Reading = {
    Callbacks: Callback list
    Receiving: ReceivingCallback list
    OptionalReceiving: OptionalReceivingCallback list
    NumericBoundaries: Map<NodeId, DeclaredParameter>
    Findings: DeclarationFinding list
}

let private shortName (name: string) = name.Split('.') |> Array.last
let private named (wanted: string) (actual: string) = wanted = actual || (not (wanted.Contains('.')) && wanted = shortName actual)
let private caseName graph id =
    caseOf graph id |> Option.map (fun (_, name, _) -> name)

let private readUncached (aggregateOrigins: Lazy<CallableOrigins.Resolution>) (graph: SemanticGraph) : Reading =
    let mutable callbacks = []
    let mutable findings = []
    let finding (node: SemanticNode) defect message =
        findings <- { Node = node.Id; Range = node.Range; Defect = defect; Message = message } :: findings
    let pointerDeclared typeId =
        match typeId |> Option.bind (caseOf graph) with
        | Some (node, "Pointer", Some bitsId) ->
            match int64Of graph bitsId, graph.Platform |> Option.bind (fun p -> Map.tryFind "Pointer" p.Dimensions) with
            | Some bits, Some expected when bits <> int64 expected ->
                finding node DeclarationDefect.Invalid "A native callback pointer declaration must match the platform's Pointer dimension."
                false
            | Some bits, Some _ when bits > 0L -> true
            | Some _, None ->
                finding node DeclarationDefect.Invalid
                    (sprintf "PSG settlement (PlatformResolution) did not settle the platform's Pointer dimension for native callback pointer declaration %d: the declared width cannot be validated against an absent platform fact." (NodeId.value node.Id))
                false
            | _ -> false
        | _ -> false
    let rec unannotated id =
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> unannotated inner
        | other -> other
    let target id =
        match unannotated id with
        | Some { Kind = SemanticKind.VarRef (_, Some bindingId) } ->
            match SemanticGraph.tryGetNode bindingId graph with
            | Some ({ Kind = SemanticKind.Binding (name, _, _, _); Children = [body]; Parent = Some parent } as binding) ->
                match SemanticGraph.tryGetNode parent graph, unannotated body with
                | Some { Kind = SemanticKind.ModuleDef _ }, Some ({ Kind = SemanticKind.Lambda (_, _, [], _, _) } as lambda) -> Some(binding, name, lambda)
                | _ -> None
            | _ -> None
        | _ -> None
    let constructions =
        graph.Nodes.Values
        |> Seq.filter (fun n -> n.IsReachable)
        |> Seq.choose (fun node ->
            match node.Kind, node.Type with
            | SemanticKind.RecordExpr (fields, _), NativeType.TApp (tc, _) -> Some(tc.Name, fields)
            | _ -> None)
        |> Seq.toList
    for binding in graph.Nodes.Values do
        let moduleLevel =
            match binding.Parent |> Option.bind (fun p -> SemanticGraph.tryGetNode p graph) with
            | Some { Kind = SemanticKind.ModuleDef _ } -> true
            | _ -> false
        match binding.Kind, List.tryLast binding.Children with
        | SemanticKind.Binding _, Some body when moduleLevel ->
            match recordOf graph body with
            | Some (descriptor, fields) when typeName descriptor = Some "CallbackDescriptor" ->
                match field "Record" fields |> Option.bind (stringOf graph),
                      field "Field" fields |> Option.bind (stringOf graph),
                      field "Signature" fields |> Option.bind (recordOf graph) with
                | Some recordName, Some fieldName, Some (signature, signatureFields) ->
                    let records =
                        graph.Nodes.Values
                        |> Seq.choose (fun node ->
                            match node.Kind with
                            | SemanticKind.TypeDef (name, TypeDefKind.RecordDef fields, _) when named recordName name -> Some(name, fields)
                            | _ -> None)
                        |> Seq.toList
                    match records with
                    | [(actualName, recordFields)] ->
                        match List.tryFind (fun (name, _) -> name = fieldName) recordFields with
                        | Some (_, NativeType.TApp (tc, [_])) when tc.NTUKind = Some NTUKind.NTUfnptr ->
                            let returnsVoid = field "ReturnType" signatureFields |> Option.bind (caseName graph) = Some "Void"
                            if field "CallingConvention" signatureFields |> Option.bind (caseName graph) <> Some "CDecl" then
                                finding signature DeclarationDefect.Invalid "Native callback declarations currently require CDecl."
                            for name, values in constructions do
                                if name = actualName then
                                    match field fieldName values |> Option.bind (valueOf graph) with
                                    | Some ({ Kind = SemanticKind.Application (fn, [argument]) } as address) ->
                                        match valueOf graph fn, target argument with
                                        | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.FnPtr; Operation = "ofFunction" } }, Some (entry, entryName, lambda) ->
                                            let declared, more = readFunctionForBinding graph entry entryName signature signatureFields
                                            findings <- List.rev more @ findings
                                            match declared, lambda.Kind with
                                            | Some declared, SemanticKind.Lambda (parameters, body, _, _, _) ->
                                                let parameterTypes =
                                                    match field "Parameters" signatureFields |> Option.bind (valueOf graph) with
                                                    | Some { Kind = SemanticKind.ArrayExpr ids } ->
                                                        ids |> List.map (fun id -> recordOf graph id |> Option.bind (fun (_, fields) -> field "Type" fields))
                                                    | _ -> []
                                                for index, (_, ty, paramId) in List.indexed parameters do
                                                    let parameter = declared.Parameters |> List.tryFind (fun (id, _) -> id = paramId) |> Option.bind snd
                                                    match parameter, Types.tryGetNTUKind ty with
                                                    | Some _, _ -> () // The common descriptor reader validates scalar/source agreement.
                                                    | None, Some NTUKind.NTUunit when parameters.Length = 1 && returnsVoid &&
                                                                                   declared.Parameters.IsEmpty &&
                                                                                   (graph.Nodes.TryFind paramId |> Option.exists (fun node -> Types.tryGetNTUKind node.Type = Some NTUKind.NTUunit)) &&
                                                                                   (field "Parameters" signatureFields |> Option.bind (valueOf graph)
                                                                                    |> Option.exists (fun node -> match node.Kind with SemanticKind.ArrayExpr [] -> true | _ -> false)) -> ()
                                                    | None, Some NTUKind.NTUptr | None, Some NTUKind.NTUfnptr ->
                                                        if not (pointerDeclared (List.tryItem index parameterTypes |> Option.flatten)) then
                                                            finding address DeclarationDefect.Invalid "An opaque callback parameter requires a matching Pointer declaration."
                                                    | _ -> finding address DeclarationDefect.Invalid "A native callback parameter needs a matching scalar declaration or an opaque handle representation."
                                                match SemanticGraph.tryGetNode body graph with
                                                | None ->
                                                    finding address DeclarationDefect.Malformed
                                                        (sprintf "PSG settlement (CallbackDeclarations) did not settle the result node %d of native callback lambda %d: the body is absent from the graph." (NodeId.value body) (NodeId.value lambda.Id))
                                                | Some sourceResult ->
                                                let resultKind = Types.tryGetNTUKind sourceResult.Type
                                                let sourceVoid = resultKind = Some NTUKind.NTUunit
                                                if returnsVoid <> sourceVoid then
                                                    finding address DeclarationDefect.Invalid "A callback's Void result must agree with its Clef unit result."
                                                if not returnsVoid then
                                                    match declared.Return, resultKind with
                                                    | Some _, _ when Types.isIntegerType sourceResult.Type || resultKind = Some NTUKind.NTUbool -> ()
                                                    | None, Some NTUKind.NTUptr | None, Some NTUKind.NTUfnptr ->
                                                        if not (pointerDeclared (field "ReturnType" signatureFields)) then
                                                            finding address DeclarationDefect.Invalid "An opaque callback result requires a matching Pointer declaration."
                                                    | _ -> finding address DeclarationDefect.Invalid "A native callback result needs a matching scalar declaration or an opaque handle representation."
                                                if not (List.isEmpty declared.References && List.isEmpty declared.PointerReferences && List.isEmpty declared.RecordReferences) then
                                                    finding address DeclarationDefect.Invalid "Native callback parameters cannot use caller-owned reference-array projection."
                                                callbacks <- { Lambda = lambda.Id; Address = address.Id; Record = actualName; Field = fieldName
                                                               Function = declared; ReturnsVoid = returnsVoid } :: callbacks
                                            | _ -> ()
                                        | _ -> finding address DeclarationDefect.Invalid "A declared listener callback must be FnPtr.ofFunction of a named module function without captures."
                                    | Some value -> finding value DeclarationDefect.Invalid "A declared listener callback requires an explicit FnPtr.ofFunction entry."
                                    | None -> () // Copy/update constructions can leave an existing callback field intact.
                        | _ -> finding descriptor DeclarationDefect.Invalid (sprintf "Callback field '%s.%s' must have a typed FnPtr signature." recordName fieldName)
                    | [] -> finding descriptor DeclarationDefect.Invalid (sprintf "Callback record '%s' is not declared." recordName)
                    | _ -> finding descriptor DeclarationDefect.Ambiguous (sprintf "Callback record '%s' is ambiguous; qualify its name." recordName)
                | _ -> finding descriptor DeclarationDefect.Malformed "A CallbackDescriptor requires literal Record/Field names and a FunctionDescriptor Signature."
            | _ -> ()
        | _ -> ()
    let descriptors = readDescriptors graph
    let mutable receiving = []
    let mutable optionalReceiving = []

    // A completed ordinary call may identify the source constructor for
    // declaration discovery. Only the later aggregate recipe authors its
    // distinct result instance and current dependency account.
    let optionalValue actual =
        valuePath graph actual |> Option.bind (fun (node, path) ->
            match node.Kind with
            | SemanticKind.Application(callee, [argument]) ->
                let origins = aggregateOrigins.Value
                match origins.Calls.TryFind node.Id, origins.Aggregates.TryFind node.Id with
                | Some { Complete=true; Unknown=false; Targets=[called] }, Some aggregate
                    when aggregate.UnknownOrigins.IsEmpty && aggregate.AbsentOrigins.IsEmpty ->
                    match called.Parameters, aggregate.Alternatives,
                          graph.Nodes.TryFind called.Lambda, graph.Nodes.TryFind callee with
                    | [(_, parameterType, formal)], [formation],
                      Some { Kind=SemanticKind.Lambda([(_, _, heldFormal)],body,[],_,_) },
                      Some { Kind=SemanticKind.VarRef(_,Some binding) }
                        when formal=heldFormal && body=called.Body && called.Arguments=[argument] &&
                             Types.tryGetNTUKind parameterType=Some NTUKind.NTUunit &&
                             (graph.Nodes.TryFind argument |> Option.exists(fun actual->Types.tryGetNTUKind actual.Type=Some NTUKind.NTUunit)) &&
                             (graph.Nodes.TryFind binding |> Option.exists(fun definition->
                                 match definition.Kind,definition.Children with
                                 | SemanticKind.Binding(_,false,false,_),[implementation] -> implementation=called.Lambda
                                 | _ -> false)) ->
                        let returned =
                            body=formation.Construction ||
                            (graph.Nodes.TryFind body |> Option.exists(fun returned->
                                match returned.Kind,returned.Children with
                                | SemanticKind.TypeAnnotation(value,ty),[child] ->
                                    value=formation.Construction && child=value &&
                                    Clef.Compiler.NativeTypedTree.TypeIdentities.ofType ty=aggregate.AggregateType
                                | _ -> false))
                        graph.Nodes.TryFind formation.Construction |> Option.filter(fun construction->
                            returned && (optionalEntrySignature construction.Type |> Option.isSome))
                        |> Option.map(fun construction->
                            construction,List.distinct(path @ [callee;binding;argument;called.Lambda;formal;body;construction.Id]))
                    | _ -> None
                | _ -> None
            | _ -> Some(node,path))

    for call in graph.Nodes.Values do
        match call.Kind with
        | SemanticKind.Application(callee, actuals) when call.IsReachable ->
            match target callee with
            | Some(receiver, _, _) ->
                for invocation in descriptors.CallbackInvocations do
                    if
                        invocation.Declaration.Binding = receiver.Id
                        && actuals.Length = invocation.Declaration.Formals.Length
                    then
                        let actual = actuals[invocation.Parameter]
                        let optional = optionalEntrySignature graph.Nodes[invocation.Formal].Type |> Option.isSome
                        let selections =
                            if not optional then [None] else
                            match optionalValue actual with
                            | Some(construction, path) when optionalEntrySignature construction.Type |> Option.isSome ->
                                let immutable = path |> List.forall (fun id ->
                                    match graph.Nodes[id].Kind with SemanticKind.Binding(_, true, _, _) -> false | _ -> true)
                                let candidates =
                                    match construction.Kind, construction.Children with
                                    | SemanticKind.IfThenElse(condition, whenTrue, Some whenFalse), [c; t; f]
                                        when c = condition && t = whenTrue && f = whenFalse && whenTrue <> whenFalse &&
                                             (graph.Nodes.TryFind condition |> Option.exists (fun predicate ->
                                                 match predicate.Kind, predicate.Children with
                                                 | SemanticKind.VarRef(_, Some formal), [] when Types.tryGetNTUKind predicate.Type = Some NTUKind.NTUbool ->
                                                     graph.Nodes.Values |> Seq.exists (fun owner ->
                                                         match owner.Kind with
                                                         | SemanticKind.Lambda(parameters, _, _, _, _) -> parameters |> List.exists (fun (_, _, id) -> id = formal)
                                                         | _ -> false)
                                                 | _ -> false)) ->
                                        match aggregateOrigins.Value.Aggregates.TryFind actual with
                                        | Some reading when reading.UnknownOrigins.IsEmpty && reading.AbsentOrigins.IsEmpty &&
                                            reading.Alternatives.Length = 2 &&
                                            (reading.Alternatives |> List.map _.Construction |> Set.ofList) = Set.ofList [whenTrue; whenFalse] &&
                                            reading.Dependencies.TryFind construction.Id = Some [condition; whenTrue; whenFalse] ->
                                            match graph.Nodes.TryFind whenTrue, graph.Nodes.TryFind whenFalse with
                                            | Some left, Some right ->
                                                [left, List.distinct (path @ [construction.Id; whenTrue])
                                                 right, List.distinct (path @ [construction.Id; whenFalse])]
                                            | _ -> []
                                        | _ -> []
                                    | _ -> [construction, path]
                                let selected = candidates |> List.choose (fun (candidate, candidatePath) ->
                                    let shape = Clef.Compiler.Baker.Ingredients.CallableAggregateTypes.shape graph candidate.Type
                                    match candidate.Kind, shape with
                                    | (SemanticKind.UnionCase(name, ordinal, payload) | SemanticKind.DUConstruct(name, ordinal, payload, _)),
                                      Some(Clef.Compiler.Baker.Ingredients.CallableAggregateTypes.Shape.Union(_, cases)) when immutable ->
                                        match List.tryItem ordinal cases, payload with
                                        | Some(expectedName, fields), None when expectedName = name && fields.IsEmpty ->
                                            Some { Call=call.Id; Operand=actual; Construction=candidate.Id; CaseOrdinal=ordinal
                                                   Payload=None; Transport=candidatePath; Invocation=invocation; Receiving=None }
                                        | Some(expectedName, [_, payloadType]), Some payload when expectedName = name &&
                                            Clef.Compiler.NativeTypedTree.TypeIdentities.ofType graph.Nodes[payload].Type = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType payloadType ->
                                            Some { Call=call.Id; Operand=actual; Construction=candidate.Id; CaseOrdinal=ordinal
                                                   Payload=Some payload; Transport=candidatePath; Invocation=invocation; Receiving=None }
                                        | _ -> None
                                    | _ -> None)
                                if not candidates.IsEmpty && selected.Length = candidates.Length then selected |> List.map Some
                                else
                                    finding call DeclarationDefect.Invalid "The optional callback requires a literal nominal Option constructor and immutable aliases."
                                    []
                            | _ -> finding call DeclarationDefect.Invalid "The optional callback requires a literal nominal Option constructor and immutable aliases."; []

                        for selection in selections do
                            let source =
                                (if optional then selection |> Option.bind _.Payload else Some actual)
                                |> Option.bind (valuePath graph)
                                |> Option.bind (fun (node, path) ->
                                    match node.Kind with
                                    | SemanticKind.FieldGet _ ->
                                        let origins = aggregateOrigins.Value
                                        Clef.Compiler.Baker.Ingredients.CallableAggregateProjections.read origins node.Id
                                        |> Option.bind (fun projection ->
                                            match projection.Path, projection.Inputs, origins.Aggregates.TryFind projection.Aggregate with
                                            | [CallableAggregatePathStep.RecordField _], [input], Some aggregate when
                                                aggregate.AbsentOrigins.IsEmpty && aggregate.UnknownOrigins.IsEmpty &&
                                                aggregate.Alternatives.Length = 1 &&
                                                (aggregate.Alternatives.Head.Slots |> List.filter (fun slot -> slot.Path = projection.Path)
                                                 |> function [slot] -> not slot.Absent && slot.UnknownOrigins.IsEmpty | _ -> false) ->
                                                valuePath graph input |> Option.map (fun (address, inputPath) ->
                                                    // The aggregate account retains dependency premises. Code
                                                    // transport retains the actual projection and stored value path.
                                                    address, (path @ inputPath @ [projection.Aggregate] @
                                                              (aggregate.Alternatives |> List.map _.Construction) |> List.distinct))
                                            | _ -> None)
                                    | _ -> Some(node, path))
                            match source with
                            | Some({
                                       Kind = SemanticKind.Application(fn, [ argument ])
                                   } as address,
                                   path) ->
                                match valueOf graph fn, target argument with
                                | Some {
                                           Kind = SemanticKind.Intrinsic {
                                                                             Module = IntrinsicModule.FnPtr
                                                                             Operation = "ofFunction"
                                                                         }
                                       },
                                  Some(entry, _, lambda) ->
                                    let immutable =
                                        path
                                        |> List.forall (fun id ->
                                            match graph.Nodes.TryFind id |> Option.map _.Kind with
                                            | Some(SemanticKind.Binding(_, true, _, _)) -> false
                                            | _ -> true)

                                    match recordOf graph invocation.SignatureNode with
                                    | Some(signatureNode, signatureFields) when immutable ->
                                        let signature, more =
                                            readEntrySignatureForBinding graph entry signatureNode signatureFields

                                        findings <- List.rev more @ findings

                                        match signature with
                                        | Some signature when
                                            more.IsEmpty
                                            && signature.Body.IsSome
                                            && (signature.Parameters |> List.forall (snd >> Option.isSome))
                                            ->
                                            let evidence =
                                                {
                                                    Call = call.Id
                                                    Operand = actual
                                                    Lambda = lambda.Id
                                                    Declaration = entry.Id
                                                    Address = address.Id
                                                    Transport = path
                                                    Invocation = invocation
                                                    Signature = signature
                                                }
                                            match selection with
                                            | Some selected -> optionalReceiving <- { selected with Receiving=Some evidence; Transport=List.distinct(selected.Transport @ path) } :: optionalReceiving
                                            | None -> receiving <- evidence :: receiving
                                        | _ ->
                                            finding
                                                address
                                                DeclarationDefect.Invalid
                                                "The receiving entry needs its complete declared scalar signature and source body."
                                    | _ ->
                                        finding
                                            address
                                            DeclarationDefect.Invalid
                                            "The receiving entry signature or immutable source transport is absent."
                                | _ ->
                                    finding
                                        address
                                        DeclarationDefect.Invalid
                                        "The receiving entry must be FnPtr.ofFunction of a closed named module function."
                            | _ when optional ->
                                match selection with
                                | Some selected when selected.Payload.IsNone -> optionalReceiving <- selected :: optionalReceiving
                                | Some _ -> finding call DeclarationDefect.Invalid "The optional Some callback requires its exact closed FnPtr.ofFunction payload."
                                | None -> ()
                            | _ ->
                                finding
                                    call
                                    DeclarationDefect.Invalid
                                    "The receiving entry needs current FnPtr.ofFunction transport or one immutable record projection with an exact source supplier."
            | _ -> ()
        | _ -> ()

    let receiving =
        List.rev receiving
        |> List.distinctBy (fun entry -> entry.Call, entry.Address, entry.Invocation.Quote)
    let optionalReceiving = List.rev optionalReceiving
    let allReceiving = receiving @ (optionalReceiving |> List.choose _.Receiving)

    let signatureKey (signature: DeclaredEntrySignature) =
        signature.Parameters
        |> List.map (snd >> Option.map (fun parameter -> parameter.Bits, parameter.Range)),
        signature.Return |> Option.map (fun result -> result.Bits, result.Range)

    for lambda, entries in allReceiving |> List.groupBy _.Lambda do
        if
            entries
            |> List.map (fun entry -> signatureKey entry.Signature)
            |> List.distinct
            |> List.length
            <> 1
        then
            finding
                graph.Nodes[lambda]
                DeclarationDefect.Ambiguous
                "One receiving callback implementation has incompatible native entry signatures."

    let key callback =
        callback.ReturnsVoid,
        callback.Function.Parameters |> List.map (fun (_, d) -> d |> Option.map (fun p -> p.Bits, p.Range)),
        callback.Function.Return |> Option.map (fun p -> p.Bits, p.Range)
    for _, instances in callbacks |> List.groupBy (fun c -> c.Lambda) do
        if instances |> List.map key |> List.distinct |> List.length > 1 then
            let node = SemanticGraph.getNode instances.Head.Lambda graph
            finding node DeclarationDefect.Ambiguous "One native callback entry is assigned incompatible declared signatures."
    let callbacks = List.rev callbacks |> List.distinctBy (fun c -> c.Address, c.Function.Node)
    let numeric =
        callbacks
        |> List.collect (fun c ->
            let parameters = c.Function.Parameters |> List.choose (fun (id, d) -> d |> Option.map (fun d -> id, d))
            match c.Function.Body, c.Function.Return with
            | Some body, Some result -> (body, result) :: parameters
            | _ -> parameters)
        |> Map.ofList
    let numeric =
        allReceiving |> List.fold (fun numeric entry ->
            let formals = entry.Signature.Parameters |> List.choose (fun (id, declared) -> declared |> Option.map (fun declared -> id, declared))
            let result =
                match entry.Signature.Body, entry.Signature.Return with
                | Some body, Some declared -> [body, declared]
                | _ -> []
            (formals @ result) |> List.fold (fun numeric (id, declared) -> Map.add id declared numeric) numeric) numeric
    { Callbacks = callbacks
      Receiving = receiving
      OptionalReceiving = optionalReceiving
      NumericBoundaries = numeric
      Findings = List.rev findings }

// Width readers run for many nodes of the same immutable graph. Retain the
// structural declaration reading once per graph without retaining old graphs.
let private cache = ConditionalWeakTable<SemanticGraph, Reading>()
let read graph = cache.GetValue(graph, fun graph -> readUncached (lazy (CallableOrigins.resolve graph)) graph)

/// A producing recipe already holds the completed origin reading. Reuse it;
/// declaration discovery must not start another callable fixed point.
let readWithOrigins origins graph = readUncached (lazy origins) graph

/// Present payloads retain their optional selection owner while supplying the
/// same declared incoming domain as an ordinary closed receiving entry.
let presentReceiving graph =
    let reading = read graph
    reading.Receiving @ (reading.OptionalReceiving |> List.choose _.Receiving)

let forLambda graph lambda = (read graph).Callbacks |> List.tryFind (fun c -> c.Lambda = lambda)

/// Follow a pointer value's declared listener provenance through ordinary
/// aliases. A field retains its ABI even when its record is passed as a value.
let forPointer (graph: SemanticGraph) pointer =
    let callbacks = (read graph).Callbacks
    let rec find seen id =
        if Set.contains id seen then None
        else
            let seen = Set.add id seen
            match callbacks |> List.tryFind (fun c -> c.Address = id) with
            | Some callback -> Some callback
            | None ->
                match SemanticGraph.tryGetNode id graph with
                | Some { Kind = SemanticKind.VarRef (_, Some source) }
                | Some { Kind = SemanticKind.TypeAnnotation (source, _) } -> find seen source
                | Some { Kind = SemanticKind.Binding _; Children = children } -> List.tryLast children |> Option.bind (find seen)
                | Some { Kind = SemanticKind.Application (fn, [argument]) } ->
                    match valueOf graph fn, valueOf graph argument with
                    | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.FnPtr; Operation = "ofFunction" } },
                      Some { Kind = SemanticKind.Lambda _; Id = lambda } ->
                        callbacks |> List.tryFind (fun c -> c.Lambda = lambda)
                    | _ -> None
                | Some { Kind = SemanticKind.FieldGet (record, fieldName) } ->
                    match SemanticGraph.tryGetNode record graph with
                    | Some { Type = NativeType.TApp (tc, _) } -> callbacks |> List.tryFind (fun c -> c.Record = tc.Name && c.Field = fieldName)
                    | _ -> None
                | _ -> None
    find Set.empty pointer

/// A scalar result crossing a declared native entry keeps that entry's ABI at
/// the indirect call. Ordinary binding/use meets may then select another width.
let invocationResult (graph: SemanticGraph) nodeId =
    match SemanticGraph.tryGetNode nodeId graph with
    | Some { Kind = SemanticKind.Application (fn, pointer :: _) } ->
        match valueOf graph fn with
        | Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.FnPtr; Operation = "invoke" } } ->
            forPointer graph pointer |> Option.bind (fun c -> c.Function.Return)
        | _ -> None
    | _ -> None

let numericBoundary (graph: SemanticGraph) nodeId : DeclaredParameter option =
    let declarations = (read graph).NumericBoundaries
    let rec find visited id =
        if Set.contains id visited then None
        else
            match Map.tryFind id declarations with
            | Some declaration -> Some declaration
            | None ->
                match SemanticGraph.tryGetNode id graph with
                | Some { Kind = SemanticKind.VarRef (_, Some source) }
                | Some { Kind = SemanticKind.TypeAnnotation (source, _) } -> find (Set.add id visited) source
                | _ -> invocationResult graph id
    find Set.empty nodeId
