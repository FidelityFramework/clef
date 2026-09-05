// SPDX-License-Identifier: MIT

/// Platform Resolution: the cross-compiled platform description, read out of
/// the graph it was compiled into.
///
/// `Fidelity.Platform/<target>/Description.clef` declares the target's memory
/// spaces, buffer schemas, surfaces and transports in BAREWire's vocabulary
/// (BAREWire docs/11), as typed record values, and its core's width dimensions
/// and numeric representations (plan D8) in the same value's `Core`. A
/// Contracts leaf (`Platform.clef`, `PlatformDescriptor`) declares the same
/// core in the Contracts vocabulary. Both compile WITH the program, so those
/// declarations are RecordExpr nodes in this graph, whether the developer wrote
/// the record plainly or inside a quotation (`<@ { ... } @>`, the spec's form,
/// platform-bindings.md "Platform Descriptor"): a quotation is a phase-distinct
/// structure whose typed record the reader follows into and never evaluates.
/// This module finds the declaration structurally -- by type name and field
/// name, following a reference to the binding it names -- exactly as
/// Composer's PlatformPinResolution reads FPGA pins (Fidelity.Platform
/// docs/CANONICAL_PLATFORM_SPEC.md, "The mechanism constraint"). It is the one
/// reader of the declaration.
///
/// The declarations are read whether or not they are reachable: nothing in the
/// program references `rodata` by name, so reachability marks it dead, and that
/// is correct -- a declaration is cited through F, never emitted (PHG paper
/// 2.4). Resolution is a pure projection of the graph.
///
/// A defect in the declaration is a finding at the declaring node, never a
/// silent omission: an element the reader cannot read (CCS8206), an element
/// outside its vocabulary (CCS8207), a second description of one form
/// (CCS8208). What can be read is read; the findings travel beside it so that
/// PlatformDeclaration reports them before any program site is checked and no
/// site is blamed for a defect of the description.
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

/// A declared width dimension: the node that declares it, its name and its
/// bits. Mirrors BAREWire.Platform.WidthDeclaration and the Contracts twin.
type DeclaredWidth = {
    Node: NodeId
    Name: string
    Bits: int
}

/// A declared numeric representation: the node that declares it and the
/// representation as the context carries it. Mirrors
/// BAREWire.Platform.Representation and the Contracts twin.
type DeclaredRepresentation = {
    Node: NodeId
    Representation: NumericRepresentation
}

/// The declared core: the width dimensions and the numeric representations
/// (plan D8). Mirrors the `Widths` and `Representations` of
/// BAREWire.Platform.TargetCore; the identity fields are not carried here.
type DeclaredCore = {
    Node: NodeId
    Widths: DeclaredWidth list
    Representations: DeclaredRepresentation list
}

/// The platform description: its root node, its id (the prefix of every
/// declaration citation, `<id>:<name>`), its core when it declares one, and
/// its spaces and buffers.
type DeclaredPlatform = {
    Node: NodeId
    Id: string
    Core: DeclaredCore option
    Spaces: DeclaredSpace list
    Buffers: DeclaredBuffer list
}

//-------------------------------------------------------------------------
// Defects of the declaration itself
//-------------------------------------------------------------------------

/// What is wrong with a declaration, at the node that declares it.
[<RequireQualifiedAccess>]
type DeclarationDefect =
    /// The reader cannot read the element: a field that is not a literal, an
    /// element that is not the record its list is declared over, a `Core` that
    /// is neither `Some core` nor `None`. CCS8206.
    | Malformed
    /// The element reads but says what the vocabulary does not admit: a tag
    /// outside its closed set, a width of no bits, a name declared twice, a
    /// Register width disagreeing with the word size. CCS8207.
    | Invalid
    /// A second description of one form in the graph; the first in node order
    /// is the one read. CCS8208.
    | Ambiguous

/// One defect, located at the declaring node.
type DeclarationFinding = {
    Node: NodeId
    Range: SourceRange
    Defect: DeclarationDefect
    Message: string
}

/// The declaration as read, with every defect found on the way. `Platform` is
/// what could be read; a defect never empties it, it is reported beside it.
type Reading = {
    Platform: DeclaredPlatform option
    Findings: DeclarationFinding list
}

//-------------------------------------------------------------------------
// Value following
//-------------------------------------------------------------------------

/// Follow a node to the value it denotes: through a TypeAnnotation, through a
/// quotation to the expression it quotes, through a VarRef to its binding's
/// value, and through a conversion application (`int64 X`) to its operand.
/// Stops at the first node that is none of those.
let rec private valueOf (graph: SemanticGraph) (id: NodeId) : SemanticNode option =
    match SemanticGraph.tryGetNode id graph with
    | None -> None
    | Some node ->
        match node.Kind with
        | SemanticKind.TypeAnnotation (inner, _) -> valueOf graph inner
        | SemanticKind.Quote (inner, _) -> valueOf graph inner
        | SemanticKind.VarRef (_, Some bindingId) ->
            match SemanticGraph.tryGetNode bindingId graph with
            | Some ({ Children = [ valueId ] } : SemanticNode) -> valueOf graph valueId
            | _ -> None
        | SemanticKind.Application (funcId, [ arg ]) ->
            match valueOf graph funcId with
            | Some ({ Kind = SemanticKind.Intrinsic { Category = IntrinsicCategory.Conversion } } : SemanticNode) -> valueOf graph arg
            | _ -> Some node
        | _ -> Some node

/// The node a finding about `id` is located at: the value it denotes, else the
/// referencing node itself.
let private siteOf (graph: SemanticGraph) (id: NodeId) : SemanticNode option =
    match valueOf graph id with
    | Some node -> Some node
    | None -> SemanticGraph.tryGetNode id graph

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

/// The elements of an array or list literal; None when the value is neither.
let private elementsOf (graph: SemanticGraph) (id: NodeId) : NodeId list option =
    match valueOf graph id with
    | Some ({ Kind = SemanticKind.ArrayExpr elements } : SemanticNode) -> Some elements
    | Some ({ Kind = SemanticKind.ListExpr elements } : SemanticNode) -> Some elements
    | _ -> None

/// An option value as declared: `Some x` yields `Some (Some x's node)`, `None`
/// yields `Some None`, anything else `None`. A case is a UnionCase node until
/// Baker saturation and the DUConstruct it is decomposed into after it; the
/// declaration is read from the saturated graph, so both are followed.
let private optionOf (graph: SemanticGraph) (id: NodeId) : NodeId option option =
    match valueOf graph id with
    | Some ({ Kind = SemanticKind.UnionCase ("Some", _, Some payload) } : SemanticNode)
    | Some ({ Kind = SemanticKind.DUConstruct ("Some", _, Some payload, _) } : SemanticNode) -> Some (Some payload)
    | Some ({ Kind = SemanticKind.UnionCase ("None", _, _) } : SemanticNode)
    | Some ({ Kind = SemanticKind.DUConstruct ("None", _, _, _) } : SemanticNode) -> Some None
    | _ -> None

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
// Findings
//-------------------------------------------------------------------------

let private noRange : SourceRange =
    { File = ""; Start = { Line = 0; Column = 0 }; End = { Line = 0; Column = 0 } }

let private findingAt (node: SemanticNode) (defect: DeclarationDefect) (message: string) : DeclarationFinding =
    { Node = node.Id; Range = node.Range; Defect = defect; Message = message }

/// A finding about the element `id` refers to, located at the value it denotes
/// or, failing that, at the reference; an id the graph does not hold is
/// reported without a range rather than not at all.
let private findingOn (graph: SemanticGraph) (id: NodeId) (defect: DeclarationDefect) (message: string) : DeclarationFinding =
    match siteOf graph id with
    | Some node -> findingAt node defect message
    | None -> { Node = id; Range = noRange; Defect = defect; Message = message }

/// Read every element of a declared list: the elements that read, and a
/// finding for each that does not. A field the record does not carry (the
/// Contracts form declares no `Spaces`) is an empty list; a field carried but
/// not a list literal is one finding at the field's value.
let private readList
    (graph: SemanticGraph)
    (fields: (string * NodeId) list)
    (name: string)
    (read: NodeId -> Result<'element, DeclarationFinding>)
    : 'element list * DeclarationFinding list =
    match field name fields with
    | None -> [], []
    | Some listId ->
        match elementsOf graph listId with
        | None -> [], [ findingOn graph listId DeclarationDefect.Malformed (sprintf "%s is not an array or list literal" name) ]
        | Some elements ->
            elements
            |> List.fold (fun (ok, bad) element ->
                match read element with
                | Ok e -> e :: ok, bad
                | Error f -> ok, f :: bad) ([], [])
            |> fun (ok, bad) -> List.rev ok, List.rev bad

/// The elements whose name a previous element already declared, each a finding
/// at the later declaration.
let private duplicates (what: string) (nameOf: 'element -> string) (nodeOf: 'element -> NodeId) (graph: SemanticGraph) (elements: 'element list) : DeclarationFinding list =
    elements
    |> List.fold (fun (seen: Set<string>, out) element ->
        let name = nameOf element
        if Set.contains name seen then
            seen, findingOn graph (nodeOf element) DeclarationDefect.Invalid (sprintf "the %s '%s' is declared twice" what name) :: out
        else Set.add name seen, out) (Set.empty, [])
    |> snd
    |> List.rev

//-------------------------------------------------------------------------
// Reading the declarations
//-------------------------------------------------------------------------

let private readSpace (graph: SemanticGraph) (id: NodeId) : Result<DeclaredSpace, DeclarationFinding> =
    match recordOf graph id with
    | Some (node, fields) when typeName node = Some "MemorySpace" ->
        let str n = field n fields |> Option.bind (stringOf graph)
        let i64 n = field n fields |> Option.bind (int64Of graph)
        match str "Name", str "Kind", i64 "Capacity", i64 "Alignment", str "Access" with
        | Some name, Some kind, Some capacity, Some align, Some access ->
            Ok { Node = node.Id; Name = name; Kind = kind; Capacity = capacity; Alignment = int align; Access = access }
        | _ -> Error (findingAt node DeclarationDefect.Malformed "a MemorySpace's Name, Kind and Access must be string literals and its Capacity and Alignment integer literals")
    | _ -> Error (findingOn graph id DeclarationDefect.Malformed "an element of Spaces is not a MemorySpace record")

let private readBuffer (graph: SemanticGraph) (id: NodeId) : Result<DeclaredBuffer, DeclarationFinding> =
    match recordOf graph id with
    | Some (node, fields) when typeName node = Some "BufferSchema" ->
        let str n = field n fields |> Option.bind (stringOf graph)
        let i64 n = field n fields |> Option.bind (int64Of graph)
        let bl n = field n fields |> Option.bind (boolOf graph)
        match str "Name", i64 "Capacity", str "Space", str "Framing", bl "TrimDelimiter" with
        | Some name, Some capacity, Some space, Some framing, Some trim ->
            Ok { Node = node.Id; Name = name; Capacity = capacity; Space = space; Framing = framing; TrimDelimiter = trim }
        | _ -> Error (findingAt node DeclarationDefect.Malformed "a BufferSchema's Name, Space and Framing must be string literals, its Capacity an integer literal and its TrimDelimiter a boolean literal")
    | _ -> Error (findingOn graph id DeclarationDefect.Malformed "an element of Buffers is not a BufferSchema record")

let private readWidth (graph: SemanticGraph) (id: NodeId) : Result<DeclaredWidth, DeclarationFinding> =
    match recordOf graph id with
    | Some (node, fields) when typeName node = Some "WidthDeclaration" ->
        match field "Name" fields |> Option.bind (stringOf graph), field "Bits" fields |> Option.bind (int64Of graph) with
        | Some name, Some bits when bits > 0L -> Ok { Node = node.Id; Name = name; Bits = int bits }
        | Some name, Some bits -> Error (findingAt node DeclarationDefect.Invalid (sprintf "the width dimension '%s' declares %d bits; a width is a positive number of bits" name bits))
        | _ -> Error (findingAt node DeclarationDefect.Malformed "a WidthDeclaration's Name must be a string literal and its Bits an integer literal")
    | _ -> Error (findingOn graph id DeclarationDefect.Malformed "an element of Widths is not a WidthDeclaration record")

let private readRepresentation (graph: SemanticGraph) (id: NodeId) : Result<DeclaredRepresentation, DeclarationFinding> =
    match recordOf graph id with
    | Some (node, fields) when typeName node = Some "Representation" ->
        let str n = field n fields |> Option.bind (stringOf graph)
        let i64 n = field n fields |> Option.bind (int64Of graph)
        match str "Name", str "Capability", str "Family", i64 "Bits", str "MinMagnitude", str "MaxMagnitude", str "Boundary" with
        | Some name, Some capability, Some family, Some bits, Some minMagnitude, Some maxMagnitude, Some boundary ->
            let representation =
                { Name = name; Capability = capability; Family = family; Bits = int bits
                  MinMagnitude = minMagnitude; MaxMagnitude = maxMagnitude; Boundary = boundary }
            match NumericRepresentation.problems representation with
            | [] -> Ok { Node = node.Id; Representation = representation }
            | problems -> Error (findingAt node DeclarationDefect.Invalid (sprintf "the representation '%s': %s" name (String.concat "; " problems)))
        | _ -> Error (findingAt node DeclarationDefect.Malformed "a Representation's Name, Capability, Family, MinMagnitude, MaxMagnitude and Boundary must be string literals and its Bits an integer literal")
    | _ -> Error (findingOn graph id DeclarationDefect.Malformed "an element of Representations is not a Representation record")

/// The core, read through `Core = Some core`: its widths and representations,
/// with every finding about them. `None` when the description declares no core
/// (`Core = None`: an FPGA) or the core cannot be read, the latter a finding.
let private readCore (graph: SemanticGraph) (id: NodeId) : DeclaredCore option * DeclarationFinding list =
    match optionOf graph id with
    | Some None -> None, []
    | None -> None, [ findingOn graph id DeclarationDefect.Malformed "Core must be `Some core` or `None`" ]
    | Some (Some coreId) ->
        match recordOf graph coreId with
        | Some (node, fields) when typeName node = Some "TargetCore" ->
            let widths, widthFindings = readList graph fields "Widths" (readWidth graph)
            let representations, representationFindings = readList graph fields "Representations" (readRepresentation graph)
            let duplicateWidths = duplicates "width dimension" (fun w -> w.Name) (fun w -> w.Node) graph widths
            let duplicateRepresentations = duplicates "representation" (fun r -> r.Representation.Name) (fun r -> r.Node) graph representations
            // The word size and a declared Register width state one fact; they must agree
            // (BAREWire Check.run refuses the same disagreement for a description it runs on).
            let wordSizeFindings =
                match field "WordSizeBits" fields |> Option.bind (int64Of graph), widths |> List.tryFind (fun w -> w.Name = "Register") with
                | Some wordSize, Some register when int64 register.Bits <> wordSize ->
                    [ findingAt node DeclarationDefect.Invalid (sprintf "the declared Register width %d disagrees with WordSizeBits %d" register.Bits wordSize) ]
                | _ -> []
            Some { Node = node.Id; Widths = widths; Representations = representations },
            widthFindings @ representationFindings @ duplicateWidths @ duplicateRepresentations @ wordSizeFindings
        | _ -> None, [ findingOn graph coreId DeclarationDefect.Malformed "Core's payload is not a TargetCore record" ]

/// The two record types a description is declared as: BAREWire's
/// `PlatformDescription` (a CPU or FPGA `Description.clef`) and the Contracts
/// `PlatformDescriptor` (an MCU, GPU or NPU `Platform.clef`). Both carry `Id`
/// and `Core`; only the first carries spaces and buffers.
let private isDescriptionType (node: SemanticNode) : bool =
    match typeName node with
    | Some "PlatformDescription" | Some "PlatformDescriptor" -> true
    | _ -> false

let private readPlatform (graph: SemanticGraph) (node: SemanticNode) (fields: (string * NodeId) list) : DeclaredPlatform option * DeclarationFinding list =
    match field "Id" fields |> Option.bind (stringOf graph) with
    | None -> None, [ findingAt node DeclarationDefect.Malformed "a platform description's Id must be a string literal" ]
    | Some id ->
        let spaces, spaceFindings = readList graph fields "Spaces" (readSpace graph)
        let buffers, bufferFindings = readList graph fields "Buffers" (readBuffer graph)
        let core, coreFindings =
            match field "Core" fields with
            | Some coreId -> readCore graph coreId
            | None -> None, []
        Some { Node = node.Id; Id = id; Core = core; Spaces = spaces; Buffers = buffers },
        spaceFindings @ bufferFindings @ coreFindings

/// The sources the platform binding compiles are the ones that declare the
/// platform; a description value anywhere else in the program is ordinary data
/// (BAREWire's RoundTrip sample builds one to run `Check.run` on). When the
/// graph carries a context naming the binding's project file, only a
/// declaration in a file under that project's directory is a candidate;
/// without one, every description is.
let private declaredByBinding (graph: SemanticGraph) : SemanticNode -> bool =
    let normalise (path: string) = (System.IO.Path.GetFullPath path).Replace('\\', '/')
    match graph.Platform |> Option.bind (fun ctx -> ctx.PlatformLibraryPath) with
    | None -> fun _ -> true
    | Some path ->
        let full = normalise path
        let directory =
            if System.IO.Directory.Exists full then full
            else
                match System.IO.Path.GetDirectoryName full with
                | null -> full
                | parent -> parent
        let root = directory.TrimEnd('/') + "/"
        fun node -> node.Range.File <> "" && (normalise node.Range.File).StartsWith root

/// Find the platform description compiled into this graph and read it, with
/// every finding about it. No description at all (a program compiled without a
/// described platform) is `Platform = None` and no finding. When a graph
/// carries both forms for one board (the Arty leaf declares its pins in the
/// Contracts form and its spaces in BAREWire's), the BAREWire description is
/// the one read, being the one with spaces and buffers; a second description
/// of the form read, from the binding's own sources, is a finding at its
/// declaration and is not read.
let read (graph: SemanticGraph) : Reading =
    let isDeclaration = declaredByBinding graph
    let candidates =
        graph.Nodes
        |> Map.toList
        |> List.choose (fun (_, node) ->
            match node.Kind with
            | SemanticKind.RecordExpr (fields, _) when isDescriptionType node && isDeclaration node -> Some (node, fields)
            | _ -> None)
    let ofForm name = candidates |> List.filter (fun (node, _) -> typeName node = Some name)
    let chosen, others =
        match ofForm "PlatformDescription", ofForm "PlatformDescriptor" with
        | first :: rest, _ -> Some first, rest
        | [], first :: rest -> Some first, rest
        | [], [] -> None, []
    let ambiguous =
        others
        |> List.map (fun (node, _) ->
            findingAt node DeclarationDefect.Ambiguous "a second platform description of the same form; the first in node order is the one read")
    match chosen with
    | None -> { Platform = None; Findings = [] }
    | Some (node, fields) ->
        let platform, findings = readPlatform graph node fields
        { Platform = platform; Findings = findings @ ambiguous }

/// The declaration alone, for readers that cite it: what `read` could read.
/// The findings are reported once, by PlatformDeclaration at saturation.
let resolve (graph: SemanticGraph) : DeclaredPlatform option =
    (read graph).Platform

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
