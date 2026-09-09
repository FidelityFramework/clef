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

type Reading = {
    Callbacks: Callback list
    NumericBoundaries: Map<NodeId, DeclaredParameter>
    Findings: DeclarationFinding list
}

let private shortName (name: string) = name.Split('.') |> Array.last
let private named (wanted: string) (actual: string) = wanted = actual || (not (wanted.Contains('.')) && wanted = shortName actual)
let private caseName graph id =
    caseOf graph id |> Option.map (fun (_, name, _) -> name)

let private readUncached (graph: SemanticGraph) : Reading =
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
            | Some bits, _ when bits > 0L -> true
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
                                                    | None, Some NTUKind.NTUptr | None, Some NTUKind.NTUfnptr ->
                                                        if not (pointerDeclared (List.tryItem index parameterTypes |> Option.flatten)) then
                                                            finding address DeclarationDefect.Invalid "An opaque callback parameter requires a matching Pointer declaration."
                                                    | _ -> finding address DeclarationDefect.Invalid "A native callback parameter needs a matching scalar declaration or an opaque handle representation."
                                                let sourceResult = SemanticGraph.getNode body graph
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
    { Callbacks = callbacks
      NumericBoundaries = numeric
      Findings = List.rev findings }

// Width readers run for many nodes of the same immutable graph. Retain the
// structural declaration reading once per graph without retaining old graphs.
let private cache = ConditionalWeakTable<SemanticGraph, Reading>()
let read graph = cache.GetValue(graph, fun graph -> readUncached graph)
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
