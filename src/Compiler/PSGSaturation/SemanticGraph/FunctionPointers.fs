/// Resolve native function entries before the witness boundary. No symbol-string
/// lookup, closure erasure, or callback signature inference belongs in Alex.
module Clef.Compiler.PSGSaturation.SemanticGraph.FunctionPointers

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

let rec private resolved = function
    | NativeType.TVar tv ->
        match tv.Parent with TypeParamState.Bound ty -> resolved ty | _ -> NativeType.TVar tv
    | ty -> ty

let rec private signature ty =
    match resolved ty with
    | NativeType.TFun (arg, rest) -> let args, result = signature rest in arg :: args, result
    | result -> [], result

/// The native void boundary has a separate entry, so taking a C address never
/// changes the logical unit result of ordinary calls to the source function.
let nativeEntrySymbol (lambda: NodeId) = sprintf "__clef_callback_%d" (NodeId.value lambda)

let settle (graph: SemanticGraph) : Map<NodeId, FunctionPointerPlan> * Diagnostic list =
    let mutable plans = Map.empty
    let mutable errors = []
    let error (site: SemanticNode) message =
        errors <- { Severity = NativeDiagnosticSeverity.Error; Code = "CCS8096"
                    Message = message; Range = site.Range; RelatedNodes = [site.Id]
                    Reachability = ReachabilityContext.Reachable } :: errors
    let rec node id =
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> node inner
        | other -> other
    for KeyValue(_, site) in graph.Nodes do
        if site.IsReachable then
            match site.Kind with
            | SemanticKind.Application (fn, args) ->
                match node fn with
                | Some { Kind = SemanticKind.Intrinsic info } when info.Module = IntrinsicModule.FnPtr ->
                    match info.Operation, args with
                    | "ofFunction", [value] ->
                        match node value with
                        | Some { Kind = SemanticKind.VarRef (_, Some bindingId) } ->
                            match node bindingId with
                            | Some { Kind = SemanticKind.Binding (name, _, _, _); Children = [body]; Parent = Some parent } ->
                                match node parent, node body with
                                | Some { Kind = SemanticKind.ModuleDef (moduleName, _) },
                                  Some ({ Kind = SemanticKind.Lambda (_, _, [], _, _) } as lambda) when lambda.Id = body ->
                                    let symbol =
                                        match CallbackDeclarations.forLambda graph lambda.Id with
                                        | Some callback when callback.ReturnsVoid -> nativeEntrySymbol lambda.Id
                                        | _ -> moduleName + "." + name
                                    plans <- Map.add site.Id (FunctionPointerPlan.Address (symbol, lambda.Id)) plans
                                | Some { Kind = SemanticKind.ModuleDef _ }, Some { Kind = SemanticKind.Lambda (_, _, [], _, _) } ->
                                    error site "FnPtr.ofFunction currently requires a module function declared with parameters; whole-function expression annotations are not supported by native declaration emission."
                                | _ -> error site "FnPtr.ofFunction requires a named module function without captured state; pass the environment explicitly."
                            | _ -> error site "FnPtr.ofFunction requires a named module function."
                        | _ -> error site "FnPtr.ofFunction requires a resolved named function; a closure cannot be converted to a native callback."
                    | "invoke", pointer :: arguments ->
                        match node pointer |> Option.map (fun p -> resolved p.Type) with
                        | Some (NativeType.TApp (tc, [functionType])) when tc.NTUKind = Some NTUKind.NTUfnptr ->
                            let parameters, result = signature functionType
                            if parameters.Length = arguments.Length && not parameters.IsEmpty then
                                plans <- Map.add site.Id (FunctionPointerPlan.Invoke (pointer, arguments, parameters, result)) plans
                            else error site "FnPtr.invoke requires all arguments of a resolved callback signature."
                        | _ -> error site "FnPtr.invoke requires a typed function pointer."
                    | _ -> error site "This native function-pointer operation is not supported; use FnPtr.ofFunction and a fully applied FnPtr.invoke."
                | _ -> ()
            | _ -> ()
    plans, List.rev errors
