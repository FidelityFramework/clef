// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// PlatformBindings: how every platform call site resolves, and the pin facts of a hardware
/// design, read from the description and the graph and carried as `Codata.Bindings` and
/// `Codata.Pins`. A `Sys` intrinsic resolves to a libc call under the libc runtime and to a
/// syscall under the freestanding one; an application of a `[<FidelityExtern>]` binding resolves
/// to the library and symbol its metadata names. The witnesses read the resolution and decide
/// nothing.
module Clef.Compiler.PSGSaturation.SemanticGraph.PlatformBindings

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core

//-------------------------------------------------------------------------
// Call sites
//-------------------------------------------------------------------------

/// The runtime the description declares: libc (console), or direct syscalls (freestanding, bare).
/// A description declaring none is freestanding exactly when the project's startup is (the
/// project checker settles that from its output kind).
let runtimeMode (context: PlatformContext option) : RuntimeMode =
    match context with
    | None -> RuntimeMode.Console
    | Some ctx ->
        match ctx.RuntimeModel with
        | Some RuntimeModel.Freestanding | Some RuntimeModel.Bare -> RuntimeMode.Freestanding
        | Some RuntimeModel.Libc | Some RuntimeModel.ROCm | Some RuntimeModel.XDNA -> RuntimeMode.Console
        | None -> if ctx.FreestandingStartup.IsSome then RuntimeMode.Freestanding else RuntimeMode.Console

let private isPlatformIntrinsic (info: IntrinsicInfo) : bool =
    match info.Module, info.Operation with
    | IntrinsicModule.Sys, _ -> true
    | IntrinsicModule.DateTime, ("now" | "utcNow") -> true
    | _ -> false

let private resolveIntrinsic (mode: RuntimeMode) (info: IntrinsicInfo) : ResolvedBinding option =
    match info.Module, info.Operation with
    | IntrinsicModule.Sys, ("write" | "read" | "exit" as op) ->
        match mode with
        | RuntimeMode.Freestanding -> Some (ResolvedBinding.Syscall op)
        | RuntimeMode.Console -> Some (ResolvedBinding.LibcCall op)
    | _ -> None

/// The `[<FidelityExtern>]` binding an application's function resolves to, through an
/// annotation and a reference: its library and symbol.
let private externOf (graph: SemanticGraph) (funcId: NodeId) : (string * string) option =
    let rec toBinding (id: NodeId) =
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> toBinding inner
        | Some { Kind = SemanticKind.VarRef (_, Some defId) } -> SemanticGraph.tryGetNode defId graph
        | Some ({ Kind = SemanticKind.Binding _ } as b) -> Some b
        | _ -> None
    toBinding funcId |> Option.bind (fun binding ->
        match Map.tryFind "FidelityExtern.Library" binding.Metadata, Map.tryFind "FidelityExtern.Symbol" binding.Metadata with
        | Some (MetadataValue.String library), Some (MetadataValue.String symbol) -> Some (library, symbol)
        | _ -> None)

let private intrinsicOf (graph: SemanticGraph) (funcId: NodeId) : IntrinsicInfo option =
    match SemanticGraph.tryGetNode funcId graph with
    | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } ->
        match SemanticGraph.tryGetNode inner graph with
        | Some { Kind = SemanticKind.Intrinsic info } when isPlatformIntrinsic info -> Some info
        | _ -> None
    | Some { Kind = SemanticKind.Intrinsic info } when isPlatformIntrinsic info -> Some info
    | _ -> None

/// Resolve every platform call site of the graph.
let resolve (context: PlatformContext option) (graph: SemanticGraph) : PlatformBindings =
    let mode = runtimeMode context
    let bindings =
        graph.Nodes
        |> Map.toSeq
        |> Seq.choose (fun (nodeId, node) ->
            match node.Kind with
            | SemanticKind.Application (funcId, _) ->
                match intrinsicOf graph funcId with
                | Some info ->
                    resolveIntrinsic mode info
                    |> Option.map (fun resolved -> nodeId, ({ Node = nodeId; EntryPoint = sprintf "%s.%s" (string info.Module) info.Operation; Resolved = resolved } : BindingResolution))
                | None ->
                    externOf graph funcId
                    |> Option.map (fun (library, symbol) -> nodeId, ({ Node = nodeId; EntryPoint = symbol; Resolved = ResolvedBinding.ExternCall (library, symbol) } : BindingResolution))
            | _ -> None)
        |> Map.ofSeq
    // statically linked libraries only: a dynamic extern is loaded at run time
    let externLibraries =
        bindings
        |> Map.toSeq
        |> Seq.choose (fun (_, b) ->
            match b.Resolved with
            | ResolvedBinding.LibcCall _ -> Some "c"
            | ResolvedBinding.ExternCall (library, _) when library = "c" -> Some library
            | _ -> None)
        |> Set.ofSeq
    { RuntimeMode = mode; Bindings = bindings; ExternLibraries = externLibraries }

//-------------------------------------------------------------------------
// Pins (the hardware design's endpoints joined with its [<Pin>] attributes)
//-------------------------------------------------------------------------

let rec private stringOf (graph: SemanticGraph) (id: NodeId) : string option =
    match SemanticGraph.tryGetNode id graph with
    | Some { Kind = SemanticKind.Literal (NativeLiteral.String s) } -> Some s
    | Some { Kind = SemanticKind.VarRef (_, Some bindingId) } ->
        match SemanticGraph.tryGetNode bindingId graph with
        | Some { Children = [ valueId ] } -> stringOf graph valueId
        | _ -> None
    | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> stringOf graph inner
    | Some { Kind = SemanticKind.Application (_, [ argId ]) } -> stringOf graph argId
    | _ -> None

let rec private int64Of (graph: SemanticGraph) (id: NodeId) : int64 option =
    match SemanticGraph.tryGetNode id graph with
    | Some { Kind = SemanticKind.Literal (NativeLiteral.Int (v, _)) } -> Some v
    | Some { Kind = SemanticKind.VarRef (_, Some bindingId) } ->
        match SemanticGraph.tryGetNode bindingId graph with
        | Some { Children = [ valueId ] } -> int64Of graph valueId
        | _ -> None
    | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> int64Of graph inner
    | _ -> None

let private shortName (ty: NativeType) : string option =
    match ty with
    | NativeType.TApp (tycon, _) ->
        match tycon.Name.LastIndexOf '.' with
        | -1 -> Some tycon.Name
        | i -> Some (tycon.Name.Substring (i + 1))
    | _ -> None

let rec private recordFields (graph: SemanticGraph) (id: NodeId) : (string * NodeId) list option =
    match SemanticGraph.tryGetNode id graph with
    | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> recordFields graph inner
    | Some { Kind = SemanticKind.RecordExpr (fields, _) } -> Some fields
    | _ -> None

let private field (name: string) (fields: (string * NodeId) list) : NodeId option =
    fields |> List.tryFind (fun (n, _) -> n = name) |> Option.map snd

/// A pin's logical name as a port identifier.
let private portName (name: string) = name.Replace("[", "_").Replace("]", "")

let private pinOf (graph: SemanticGraph) (fields: (string * NodeId) list) : PinConstraint option =
    match field "LogicalName" fields |> Option.bind (stringOf graph), field "PackagePin" fields |> Option.bind (stringOf graph) with
    | Some ln, Some pp ->
        Some ({ PortName = portName ln
                PackagePin = pp
                IOStandard = field "Standard" fields |> Option.bind (stringOf graph) |> Option.defaultValue "LVCMOS33"
                Direction = field "Direction" fields |> Option.bind (stringOf graph) |> Option.defaultValue "InOut" } : PinConstraint)
    | _ -> None

let private clockOf (graph: SemanticGraph) (fields: (string * NodeId) list) : ClockConstraint option =
    match field "Name" fields |> Option.bind (stringOf graph), field "PackagePin" fields |> Option.bind (stringOf graph), field "FrequencyHz" fields |> Option.bind (int64Of graph) with
    | Some n, Some pp, Some freq ->
        Some ({ PortName = portName n
                PackagePin = pp
                IOStandard = field "Standard" fields |> Option.bind (stringOf graph) |> Option.defaultValue "LVCMOS33"
                FrequencyHz = freq } : ClockConstraint)
    | _ -> None

let private resetOf (graph: SemanticGraph) (fields: (string * NodeId) list) : ResetConstraint option =
    match field "Name" fields |> Option.bind (stringOf graph), field "Kind" fields |> Option.bind (stringOf graph) with
    | Some n, Some k ->
        let text name fallback = field name fields |> Option.bind (stringOf graph) |> Option.defaultValue fallback
        Some ({ PortName = portName n
                IsExternal = (k = "External")
                PackagePin = text "PackagePin" "NONE"
                IOStandard = text "Standard" "LVCMOS33"
                ActiveHigh = (text "ActiveLevel" "High" = "High") } : ResetConstraint)
    | _ -> None

let private devicePartOf (graph: SemanticGraph) (fields: (string * NodeId) list) : string option =
    match field "Device" fields |> Option.bind (stringOf graph), field "Package" fields |> Option.bind (stringOf graph), field "SpeedGrade" fields |> Option.bind (stringOf graph) with
    | Some d, Some p, Some sg -> Some (sprintf "%s%s%s" (d.ToLowerInvariant()) (p.ToLowerInvariant()) sg)
    | _ -> None

/// The pin mapping of the graph's hardware design: None where no type carries a `[<Pin>]`
/// attribute, or the description declares no clock or device.
let pins (graph: SemanticGraph) : PinMapping option =
    let attrs =
        let rec ofType (acc: Map<string, string list>) (ty: NativeType) =
            match ty with
            | NativeType.TApp (tycon, args) ->
                let acc = tycon.FieldPinAttributes |> Map.fold (fun acc k v -> Map.add k (v |> List.map portName) acc) acc
                args |> List.fold ofType acc
            | NativeType.TTuple (types, _) -> types |> List.fold ofType acc
            | _ -> acc
        graph.Nodes |> Map.fold (fun acc _ node -> ofType acc node.Type) Map.empty
    if Map.isEmpty attrs then None
    else
        let bindings =
            graph.Nodes
            |> Map.toList
            |> List.choose (fun (_, node) ->
                match node.Kind, node.Children with
                | SemanticKind.Binding _, [ childId ] -> shortName node.Type |> Option.bind (fun n -> recordFields graph childId |> Option.map (fun f -> n, f))
                | _ -> None)
        let ofShape name read = bindings |> List.choose (fun (n, fields) -> if n = name then read graph fields else None)
        let pinsByName = ofShape "PinEndpoint" pinOf |> List.map (fun p -> p.PortName, p) |> Map.ofList
        let designPins = attrs |> Map.toList |> List.collect (fun (_, names) -> names |> List.choose (fun n -> Map.tryFind n pinsByName))
        match ofShape "ClockEndpoint" clockOf, ofShape "PlatformDescriptor" devicePartOf with
        | clock :: _, device :: _ ->
            Some { Pins = designPins
                   Clock = clock
                   Reset = ofShape "ResetEndpoint" resetOf |> List.tryHead
                   DevicePart = device
                   FieldPinAttrs = attrs }
        | _ -> None
