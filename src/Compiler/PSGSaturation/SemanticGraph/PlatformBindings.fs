// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Independent hardware pin facts. Call and runtime identity belong exclusively
/// to Baker's boundary declaration and call relations.
module Clef.Compiler.PSGSaturation.SemanticGraph.PlatformBindings

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core

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

/// A required string field of a pin-inventory record. The description declares every
/// electrical fact; none is supplied here in its place.
let private requiredText (graph: SemanticGraph) (shape: string) (fields: (string * NodeId) list) (name: string) : string =
    match field name fields |> Option.bind (stringOf graph) with
    | Some value -> value
    | None ->
        let subject = field "LogicalName" fields |> Option.orElse (field "Name" fields) |> Option.bind (stringOf graph) |> Option.defaultValue "<unnamed>"
        failwithf "PSG settlement (PlatformBindings) did not settle the %s of the %s '%s': the platform description's field is absent or not a string value" name shape subject

/// A closed-vocabulary field: a value outside the vocabulary is the description's defect.
let private oneOf (shape: string) (subject: string) (name: string) (vocabulary: string list) (value: string) : string =
    if List.contains value vocabulary then value
    else failwithf "PSG settlement (PlatformBindings) did not settle the %s of the %s '%s': '%s' is not one of %s" name shape subject value (String.concat ", " vocabulary)

let private pinOf (graph: SemanticGraph) (fields: (string * NodeId) list) : PinConstraint option =
    let text = requiredText graph "PinEndpoint" fields
    Some ({ PortName = portName (text "LogicalName")
            PackagePin = text "PackagePin"
            IOStandard = text "Standard"
            Direction = text "Direction" |> oneOf "PinEndpoint" (text "LogicalName") "Direction" ["Input"; "Output"; "InOut"] } : PinConstraint)

let private clockOf (graph: SemanticGraph) (fields: (string * NodeId) list) : ClockConstraint option =
    let text = requiredText graph "ClockEndpoint" fields
    match field "FrequencyHz" fields |> Option.bind (int64Of graph) with
    | Some freq ->
        Some ({ PortName = portName (text "Name")
                PackagePin = text "PackagePin"
                IOStandard = text "Standard"
                FrequencyHz = freq } : ClockConstraint)
    | None -> failwithf "PSG settlement (PlatformBindings) did not settle the FrequencyHz of the ClockEndpoint '%s': the platform description's field is absent or not an integer literal" (text "Name")

let private resetOf (graph: SemanticGraph) (fields: (string * NodeId) list) : ResetConstraint option =
    let text = requiredText graph "ResetEndpoint" fields
    let closed name vocabulary = text name |> oneOf "ResetEndpoint" (text "Name") name vocabulary
    Some ({ PortName = portName (text "Name")
            IsExternal = (closed "Kind" ["External"; "Internal"] = "External")
            PackagePin = text "PackagePin"
            IOStandard = text "Standard"
            ActiveHigh = (closed "ActiveLevel" ["High"; "Low"] = "High") } : ResetConstraint)

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
                | SemanticKind.Binding _, [ childId ] when PlatformResolution.isSelectedPlatformDeclaration graph node ->
                    shortName node.Type |> Option.bind (fun n -> recordFields graph childId |> Option.map (fun f -> n, f))
                | _ -> None)
        let ofShape name read = bindings |> List.choose (fun (n, fields) -> if n = name then read graph fields else None)
        let pinsByName = ofShape "PinEndpoint" pinOf |> List.map (fun p -> p.PortName, p) |> Map.ofList
        let clocks = ofShape "ClockEndpoint" clockOf
        let resets = ofShape "ResetEndpoint" resetOf
        // Clock and reset ports are declared by their own endpoints, not the pin inventory.
        let endpointPorts = Set.ofList ((clocks |> List.map _.PortName) @ (resets |> List.map _.PortName))
        let designPins =
            attrs |> Map.toList |> List.collect (fun (_, names) ->
                names |> List.choose (fun n ->
                    match Map.tryFind n pinsByName with
                    | Some pin -> Some pin
                    | None when endpointPorts.Contains n -> None
                    | None -> failwithf "PSG settlement (PlatformBindings) did not settle the pin '%s' that a [<Pin>] attribute names: the selected platform declares no PinEndpoint, ClockEndpoint or ResetEndpoint of that name" n))
        match clocks, ofShape "PlatformDescriptor" devicePartOf with
        | clock :: _, device :: _ ->
            Some { Pins = designPins
                   Clock = clock
                   Reset = resets |> List.tryHead
                   DevicePart = device
                   FieldPinAttrs = attrs }
        | [], _ ->
            failwithf "PSG settlement (PlatformBindings) did not settle the clock of the hardware design whose fields name pins [%s]: the selected platform declares no ClockEndpoint" (attrs |> Map.toList |> List.collect snd |> String.concat ", ")
        | _, [] ->
            failwith "PSG settlement (PlatformBindings) did not settle the device part of the hardware design: no selected PlatformDescriptor declares literal Device, Package and SpeedGrade"
