/// Scoped native mappings are declarations over real foreign bindings. The
/// opaque pointer returned by C becomes a borrowed view only at this boundary.
module Clef.Compiler.PSGSaturation.SemanticGraph.MappedBindings

open System.Runtime.CompilerServices
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

type MappedValue = Input of string | Output of string

type DeclaredMapping = {
    Node: NodeId
    Binding: NodeId
    BindingName: string
    Parameters: (string * NativeType * NodeId) list
    CallbackParameter: NodeId
    AcquireBinding: NodeId
    Acquire: DeclaredFunction
    AcquireParameters: (string * NativeType * NodeId) list
    ReleaseBinding: NodeId
    Release: DeclaredFunction
    ReleaseParameters: (string * NativeType * NodeId) list
    Layout: string
    Owner: MappedValue
    RowStride: MappedValue
    RowCount: MappedValue
    RowWidth: MappedValue
    ReleaseArguments: MappedValue list
    FailureStatus: int
}

type Reading = { Mappings: DeclaredMapping list; Findings: DeclarationFinding list }

/// Bindings in different modules cannot satisfy each other's declaration.
let qualifiedBindingName (graph: SemanticGraph) (binding: SemanticNode) =
    let combine (prefix: string) (name: string) =
        if prefix = "" || name.StartsWith(prefix + ".", System.StringComparison.Ordinal) then name
        else prefix + "." + name
    let rec prefix seen parent =
        match parent with
        | Some id when not (Set.contains id seen) ->
            match SemanticGraph.tryGetNode id graph with
            | Some node ->
                let outer = prefix (Set.add id seen) node.Parent
                match node.Kind with SemanticKind.ModuleDef(name, _) -> combine outer name | _ -> outer
            | None -> ""
        | _ -> ""
    match binding.Kind with
    | SemanticKind.Binding(name, _, _, _) -> combine (prefix Set.empty binding.Parent) name
    | _ -> ""

let private readUncached (graph: SemanticGraph) =
    let descriptors = readDescriptors graph
    let mutable mappings = []
    let mutable findings = []
    let findBinding name =
        graph.Nodes.Values
        |> Seq.filter (fun node -> qualifiedBindingName graph node = name)
        |> Seq.toList
        |> function [one] -> Some one | _ -> None
    let functionOf (binding: SemanticNode) =
        lambdaOfBinding graph binding.Id |> Option.bind (fun (parameters, body) ->
            descriptors.Functions |> List.tryPick (fun descriptor ->
                if descriptor.Body = Some body then Some(parameters, descriptor) else None))
    let value node =
        match caseOf graph node with
        | Some (_, "Input", Some payload) -> stringOf graph payload |> Option.map Input
        | Some (_, "Output", Some payload) -> stringOf graph payload |> Option.map Output
        | _ -> None
    for binding in graph.Nodes.Values do
        match binding.Kind, List.tryLast binding.Children with
        | SemanticKind.Binding _, Some body ->
            match recordOf graph body with
            | Some (declaration, fields) when typeName declaration = Some "MappedReturnDescriptor" ->
                let fail message =
                    findings <- { Node = declaration.Id; Range = declaration.Range; Defect = DeclarationDefect.Invalid; Message = message } :: findings
                let text name = field name fields |> Option.bind (stringOf graph)
                let select name = field name fields |> Option.bind value
                let releaseArguments =
                    field "ReleaseArguments" fields |> Option.bind (valueOf graph) |> Option.bind (fun node ->
                        match node.Kind with
                        | SemanticKind.ArrayExpr elements | SemanticKind.ListExpr elements ->
                            let values = List.choose value elements
                            if values.Length = elements.Length then Some values else None
                        | _ -> None)
                let native name = text name |> Option.bind findBinding |> Option.bind (fun b -> functionOf b |> Option.map (fun (p,d) -> b,p,d))
                match text "Binding" |> Option.bind findBinding, native "Acquire", native "Release", text "Layout", text "CallbackParameter",
                      select "Owner", select "RowStride", select "RowCount", select "RowWidth", releaseArguments,
                      field "FailureStatus" fields |> Option.bind (int64Of graph) with
                | Some wrapper, Some(acquire, acquireParameters, acquireDescriptor), Some(release, releaseParameters, releaseDescriptor), Some layout, Some callback,
                  Some owner, Some stride, Some rows, Some width, Some releaseArgs, Some failure when failure < 0L && failure >= int64 System.Int32.MinValue ->
                    match lambdaOfBinding graph wrapper.Id with
                    | Some (parameters, _) ->
                        let references =
                            (acquireDescriptor.References |> List.map fst) @ (acquireDescriptor.PointerReferences |> List.map fst)
                            |> Set.ofList
                        let sourceParameter name = parameters |> List.tryFind (fun (n,_,_) -> n = name)
                        let nativeParameter name = acquireParameters |> List.tryFind (fun (n,_,_) -> n = name)
                        let validValue = function
                            | Input name -> name <> callback && (sourceParameter name).IsSome &&
                                            (nativeParameter name |> Option.exists (fun (_,_,native) -> not (Set.contains native references)))
                            | Output name -> nativeParameter name |> Option.exists (fun (_,_,id) -> Set.contains id references)
                        let implicitInputs = acquireParameters |> List.filter (fun (_,_,id) -> not (Set.contains id references))
                        let actualInputs = parameters |> List.filter (fun (n,_,_) -> n <> callback)
                        let callbackParameter = sourceParameter callback
                        let sameNames = List.map (fun(n,_,_)->n) implicitInputs = List.map (fun(n,_,_)->n) actualInputs
                        let nativePointerReturn =
                            field "ReturnType" (recordOf graph acquireDescriptor.Node |> Option.map snd |> Option.defaultValue [])
                            |> Option.bind (caseOf graph) |> Option.exists (fun (_,name,_) -> name = "Pointer")
                        let sameType a b = formatType (applySubst a) = formatType (applySubst b)
                        let sameInputTypes = implicitInputs.Length = actualInputs.Length &&
                                             List.forall2 (fun (_,a,_) (_,b,_) -> sameType a b) implicitInputs actualInputs
                        let selectedType = function
                            | Input name -> nativeParameter name |> Option.map (fun (_,ty,_) -> ty)
                            | Output name -> nativeParameter name |> Option.bind (fun (_,ty,_) ->
                                match applySubst ty with
                                | NativeType.TApp(tc, [elem]) when tc.Name = "array" || tc.Name = "Array" -> Some elem
                                | _ -> None)
                        let scalarInput = function
                            | Input name -> nativeParameter name |> Option.exists (fun (_,_,id) ->
                                acquireDescriptor.Parameters |> List.exists (fun (p,d) -> p = id && (d |> Option.exists (fun d -> ValueRange.isNonNegative d.Range))))
                            | _ -> false
                        let scalarOutput = function
                            | Output name -> nativeParameter name |> Option.exists (fun (_,_,id) ->
                                acquireDescriptor.References |> List.exists (fun (p,d) -> p = id && ValueRange.isNonNegative d.Range))
                            | _ -> false
                        let ownerIsHandle = match owner with Input _ -> selectedType owner |> Option.exists (fun ty -> Types.tryGetNTUKind ty = Some NTUKind.NTUptr) | _ -> false
                        let releaseCompatible = releaseArgs.Length = releaseParameters.Length &&
                                                List.forall2 (fun selector (_,ty,_) -> selectedType selector |> Option.exists (sameType ty)) releaseArgs releaseParameters
                        let releaseIsVoid =
                            field "ReturnType" (recordOf graph releaseDescriptor.Node |> Option.map snd |> Option.defaultValue [])
                            |> Option.bind (caseOf graph) |> Option.exists (fun (_,name,_) -> name = "Void")
                        if callbackParameter.IsNone || not sameNames || not nativePointerReturn
                           || not sameInputTypes || not ownerIsHandle || not (scalarOutput stride)
                           || not (scalarInput rows && scalarInput width) || not releaseCompatible || not releaseIsVoid
                           || not (List.forall validValue (owner :: stride :: rows :: width :: releaseArgs)) then
                            fail "A mapped return requires matching native inputs, an opaque owner, unsigned scalar row extents, a scalar stride output, a pointer result, one callback, and type-compatible void release arguments in native order."
                        elif acquireDescriptor.RecordReferences <> [] then
                            fail "Mapped acquisition record references require an explicit output projection."
                        else
                            let _,_,callbackId = callbackParameter.Value
                            mappings <- { Node = declaration.Id; Binding = wrapper.Id; BindingName = qualifiedBindingName graph wrapper
                                          Parameters = parameters; CallbackParameter = callbackId
                                          AcquireBinding = acquire.Id; Acquire = acquireDescriptor; AcquireParameters = acquireParameters
                                          ReleaseBinding = release.Id; Release = releaseDescriptor; ReleaseParameters = releaseParameters
                                          Layout = layout; Owner = owner; RowStride = stride; RowCount = rows; RowWidth = width
                                          ReleaseArguments = releaseArgs; FailureStatus = int failure } :: mappings
                    | None -> fail "The mapped wrapper must be a declared function."
                | _ -> fail "A mapped return must name unique qualified bindings, a layout, callback, input/output selectors, and a negative failure status."
            | _ -> ()
        | _ -> ()
    let duplicates = mappings |> List.groupBy (fun m -> m.Binding) |> List.filter (fun (_,xs) -> xs.Length > 1)
    let duplicateBindings = duplicates |> List.map fst |> Set.ofList
    for _, duplicates in duplicates do
        for mapping in duplicates do
            let node = graph.Nodes.[mapping.Node]
            findings <- { Node = node.Id; Range = node.Range; Defect = DeclarationDefect.Invalid; Message = "A scoped mapped binding has more than one mapped-return declaration." } :: findings
    { Mappings = List.rev mappings |> List.filter (fun m -> not (Set.contains m.Binding duplicateBindings)); Findings = List.rev findings }

let private cache = ConditionalWeakTable<SemanticGraph, Reading>()
let read graph = cache.GetValue(graph, fun graph -> readUncached graph)

let tryFindCall (graph: SemanticGraph) (funcId: NodeId) =
    let rec binding seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.TypeAnnotation(inner, _) } -> binding seen inner
        | Some { Kind = SemanticKind.Application(inner, _) } -> binding seen inner
        | Some { Kind = SemanticKind.VarRef(_, Some target) } -> Some target
        | Some { Kind = SemanticKind.Binding _ } -> Some id
        | _ -> None
    binding Set.empty funcId |> Option.bind (fun id -> (read graph).Mappings |> List.tryFind (fun m -> m.Binding = id))

/// The scoped callback and adapter report status through the declared Register
/// carrier. The zeroed source placeholder is never evidence that status is zero.
let numericBoundary (graph: SemanticGraph) (nodeId: NodeId) : DeclaredParameter option =
    let mapped =
        match SemanticGraph.tryGetNode nodeId graph with
        | Some { Kind = SemanticKind.Application(funcId, _); Type = ty } when Types.isIntegerType ty -> tryFindCall graph funcId
        | _ -> (read graph).Mappings |> List.tryFind (fun m ->
            lambdaOfBinding graph m.Binding |> Option.exists (fun (_, body) -> body = nodeId))
    mapped |> Option.bind (fun mapping ->
        graph.Platform |> Option.bind (fun platform ->
            PlatformContext.tryWidth platform (WidthDimension.name WidthDimension.Register) |> Result.toOption)
        |> Option.map (fun bits -> { Node = nodeId; Name = mapping.BindingName; Bits = bits; Range = ValueRange.twosComplement bits }))
