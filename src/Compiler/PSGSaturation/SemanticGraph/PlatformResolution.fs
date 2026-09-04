// SPDX-License-Identifier: MIT

/// Platform Resolution: the cross-compiled platform description, read out of
/// the graph it was compiled into.
///
/// `Fidelity.Platform/<target>/Description.clef` declares the target's memory
/// spaces, buffer schemas, surfaces and transports in BAREWire's vocabulary
/// (BAREWire docs/11), as plain module-level record values. It compiles WITH
/// the program, so those declarations are RecordExpr nodes in this graph. This
/// module finds them structurally -- by type name and field name, following a
/// reference to the binding it names -- exactly as Composer's
/// PlatformPinResolution reads FPGA pins (Fidelity.Platform
/// docs/CANONICAL_PLATFORM_SPEC.md, "The mechanism constraint").
///
/// The declarations are read whether or not they are reachable: nothing in the
/// program references `rodata` by name, so reachability marks it dead, and that
/// is correct -- a declaration is cited through F, never emitted (PHG paper
/// 2.4). Resolution is a pure projection of the graph.
module Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core

//-------------------------------------------------------------------------
// The declared platform, as the compiler reads it
//-------------------------------------------------------------------------

/// A declared memory space: the node that declares it and the facts an
/// obligation cites. Mirrors BAREWire.Platform.MemorySpace; only the fields the
/// compiler's obligations need are carried.
type DeclaredSpace = {
    Node: NodeId
    Name: string
    Kind: string
    Capacity: int64
    Alignment: int
    Access: string
}

/// A declared buffer schema. Mirrors BAREWire.Platform.BufferSchema.
type DeclaredBuffer = {
    Node: NodeId
    Name: string
    Capacity: int64
    Space: string
    Framing: string
    TrimDelimiter: bool
}

/// The platform description: its root node, its id (the prefix of every
/// declaration citation, `<id>:<name>`), and its spaces and buffers.
type DeclaredPlatform = {
    Node: NodeId
    Id: string
    Spaces: DeclaredSpace list
    Buffers: DeclaredBuffer list
}

//-------------------------------------------------------------------------
// Value following
//-------------------------------------------------------------------------

/// Follow a node to the value it denotes: through a TypeAnnotation, through a
/// VarRef to its binding's value, and through a conversion application
/// (`int64 X`) to its operand. Stops at the first node that is none of those.
let rec private valueOf (graph: SemanticGraph) (id: NodeId) : SemanticNode option =
    match SemanticGraph.tryGetNode id graph with
    | None -> None
    | Some node ->
        match node.Kind with
        | SemanticKind.TypeAnnotation (inner, _) -> valueOf graph inner
        | SemanticKind.VarRef (_, Some bindingId) ->
            match SemanticGraph.tryGetNode bindingId graph with
            | Some ({ Children = [ valueId ] } : SemanticNode) -> valueOf graph valueId
            | _ -> None
        | SemanticKind.Application (funcId, [ arg ]) ->
            match valueOf graph funcId with
            | Some ({ Kind = SemanticKind.Intrinsic { Category = IntrinsicCategory.Conversion } } : SemanticNode) -> valueOf graph arg
            | _ -> Some node
        | _ -> Some node

let private stringOf (graph: SemanticGraph) (id: NodeId) : string option =
    match valueOf graph id with
    | Some ({ Kind = SemanticKind.Literal (NativeLiteral.String s) } : SemanticNode) -> Some s
    | _ -> None

let private int64Of (graph: SemanticGraph) (id: NodeId) : int64 option =
    match valueOf graph id with
    | Some ({ Kind = SemanticKind.Literal (NativeLiteral.Int (v, _)) } : SemanticNode) -> Some v
    | Some ({ Kind = SemanticKind.Literal (NativeLiteral.UInt (v, _)) } : SemanticNode) -> Some (int64 v)
    | _ -> None

let private boolOf (graph: SemanticGraph) (id: NodeId) : bool option =
    match valueOf graph id with
    | Some ({ Kind = SemanticKind.Literal (NativeLiteral.Bool b) } : SemanticNode) -> Some b
    | _ -> None

/// The fields of a record value, with the declaring node.
let private recordOf (graph: SemanticGraph) (id: NodeId) : (SemanticNode * (string * NodeId) list) option =
    match valueOf graph id with
    | Some (({ Kind = SemanticKind.RecordExpr (fields, _) } : SemanticNode) as node) -> Some (node, fields)
    | _ -> None

let private elementsOf (graph: SemanticGraph) (id: NodeId) : NodeId list =
    match valueOf graph id with
    | Some ({ Kind = SemanticKind.ArrayExpr elements } : SemanticNode) -> elements
    | Some ({ Kind = SemanticKind.ListExpr elements } : SemanticNode) -> elements
    | _ -> []

let private field (name: string) (fields: (string * NodeId) list) : NodeId option =
    fields |> List.tryFind (fun (n, _) -> n = name) |> Option.map snd

/// The last segment of a node's type-constructor name: `Platform.MemorySpace`
/// -> `MemorySpace`.
let private typeName (node: SemanticNode) : string option =
    match node.Type with
    | NativeType.TApp (tycon, _) ->
        let name = tycon.Name
        match name.LastIndexOf '.' with
        | -1 -> Some name
        | i -> Some (name.Substring(i + 1))
    | _ -> None

//-------------------------------------------------------------------------
// Reading the declarations
//-------------------------------------------------------------------------

let private readSpace (graph: SemanticGraph) (id: NodeId) : DeclaredSpace option =
    match recordOf graph id with
    | Some (node, fields) when typeName node = Some "MemorySpace" ->
        let str n = field n fields |> Option.bind (stringOf graph)
        let i64 n = field n fields |> Option.bind (int64Of graph)
        match str "Name", str "Kind", i64 "Capacity", i64 "Alignment", str "Access" with
        | Some name, Some kind, Some capacity, Some align, Some access ->
            Some { Node = node.Id; Name = name; Kind = kind; Capacity = capacity; Alignment = int align; Access = access }
        | _ -> None
    | _ -> None

let private readBuffer (graph: SemanticGraph) (id: NodeId) : DeclaredBuffer option =
    match recordOf graph id with
    | Some (node, fields) when typeName node = Some "BufferSchema" ->
        let str n = field n fields |> Option.bind (stringOf graph)
        let i64 n = field n fields |> Option.bind (int64Of graph)
        let bl n = field n fields |> Option.bind (boolOf graph)
        match str "Name", i64 "Capacity", str "Space", str "Framing", bl "TrimDelimiter" with
        | Some name, Some capacity, Some space, Some framing, Some trim ->
            Some { Node = node.Id; Name = name; Capacity = capacity; Space = space; Framing = framing; TrimDelimiter = trim }
        | _ -> None
    | _ -> None

/// Find the platform description compiled into this graph and read it.
/// None when no `PlatformDescription` value is present (a program compiled
/// without a described platform), or when the root is malformed.
let resolve (graph: SemanticGraph) : DeclaredPlatform option =
    graph.Nodes
    |> Map.toSeq
    |> Seq.map snd
    |> Seq.tryPick (fun node ->
        match node.Kind with
        | SemanticKind.RecordExpr (fields, _) when typeName node = Some "PlatformDescription" ->
            match field "Id" fields |> Option.bind (stringOf graph) with
            | Some id ->
                let spaces = field "Spaces" fields |> Option.map (elementsOf graph) |> Option.defaultValue [] |> List.choose (readSpace graph)
                let buffers = field "Buffers" fields |> Option.map (elementsOf graph) |> Option.defaultValue [] |> List.choose (readBuffer graph)
                Some { Node = node.Id; Id = id; Spaces = spaces; Buffers = buffers }
            | None -> None
        | _ -> None)

/// A declared space by name.
let spaceNamed (name: string) (platform: DeclaredPlatform) : DeclaredSpace option =
    platform.Spaces |> List.tryFind (fun s -> s.Name = name)

/// A declared buffer by name.
let bufferNamed (name: string) (platform: DeclaredPlatform) : DeclaredBuffer option =
    platform.Buffers |> List.tryFind (fun b -> b.Name = name)

/// The citation an obligation carries for a declaration: `<id>:<name>`, the
/// form BAREWire's own Platform/Obligations.fs uses.
let cite (platform: DeclaredPlatform) (declaration: string) : string =
    platform.Id + ":" + declaration
