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
    Granularity: int
    Growth: string
    Base: int64 option
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

/// A declared return bound of an endpoint (Dimensional_Range_Design.md, ruling
/// 2 of CS-12): read from a Contract whose `AtMost` names a parameter, with its
/// `Floor`; the endpoint's return lies in `[Floor, hi(AtMost)]`. Mirrors the
/// two fields of BAREWire.Platform.Contract.
type DeclaredReturn = {
    Node: NodeId
    Endpoint: string
    Floor: bigint
    AtMost: string
}

/// The platform description: its root node, its id (the prefix of every
/// declaration citation, `<id>:<name>`), its core when it declares one, its
/// spaces and buffers, and the return bounds its endpoint contracts declare.
type DeclaredPlatform = {
    Node: NodeId
    Id: string
    Core: DeclaredCore option
    Spaces: DeclaredSpace list
    Buffers: DeclaredBuffer list
    Returns: DeclaredReturn list
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
let rec valueOf (graph: SemanticGraph) (id: NodeId) : SemanticNode option =
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

let stringOf (graph: SemanticGraph) (id: NodeId) : string option =
    match valueOf graph id with
    | Some ({ Kind = SemanticKind.Literal (NativeLiteral.String s) } : SemanticNode) -> Some s
    | _ -> None

/// An integer as declared: a literal, or the negation of one (`-4095L`, a floor).
let rec int64Of (graph: SemanticGraph) (id: NodeId) : int64 option =
    match valueOf graph id with
    | Some ({ Kind = SemanticKind.Literal (NativeLiteral.Int (v, _)) } : SemanticNode) -> Some v
    | Some ({ Kind = SemanticKind.Literal (NativeLiteral.UInt (v, _)) } : SemanticNode) -> Some (int64 v)
    | Some ({ Kind = SemanticKind.Application (funcId, [ arg ]) } : SemanticNode) ->
        match valueOf graph funcId with
        | Some ({ Kind = SemanticKind.Intrinsic { Operation = "op_UnaryNegation" } } : SemanticNode) -> int64Of graph arg |> Option.map (fun v -> -v)
        | _ -> None
    | _ -> None

let private boolOf (graph: SemanticGraph) (id: NodeId) : bool option =
    match valueOf graph id with
    | Some ({ Kind = SemanticKind.Literal (NativeLiteral.Bool b) } : SemanticNode) -> Some b
    | _ -> None

/// The fields of a record value, with the declaring node.
let recordOf (graph: SemanticGraph) (id: NodeId) : (SemanticNode * (string * NodeId) list) option =
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

let field (name: string) (fields: (string * NodeId) list) : NodeId option =
    fields |> List.tryFind (fun (n, _) -> n = name) |> Option.map snd

/// The last segment of a node's type-constructor name: `Platform.MemorySpace`
/// -> `MemorySpace`.
let typeName (node: SemanticNode) : string option =
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
        let baseValue =
            field "Base" fields |> Option.bind (optionOf graph) |> Option.bind (function
                | None -> Some None
                | Some value -> int64Of graph value |> Option.map Some)
        match str "Name", str "Kind", i64 "Capacity", i64 "Alignment", i64 "Granularity", str "Growth", str "Access", baseValue with
        | Some name, Some kind, Some capacity, Some align, Some granularity, Some growth, Some access, Some baseValue
            when align >= 0L && align <= int64 System.Int32.MaxValue && granularity >= 0L && granularity <= int64 System.Int32.MaxValue ->
            Ok { Node = node.Id; Name = name; Kind = kind; Capacity = capacity; Alignment = int align
                 Granularity = int granularity; Growth = growth; Base = baseValue; Access = access }
        | _ -> Error (findingAt node DeclarationDefect.Malformed "a MemorySpace requires literal Name, Kind, Growth and Access, integer Capacity, bounded Alignment and Granularity, and Base = None or Some integer")
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

/// The return bounds the description's surfaces declare: every Contract of every Endpoint of
/// every BoundarySurface whose `AtMost` names a parameter, with its `Floor`. A Contract that
/// carries no `AtMost` (the Contracts form declares none) or an empty one declares no bound.
let private readReturns (graph: SemanticGraph) (fields: (string * NodeId) list) : DeclaredReturn list * DeclarationFinding list =
    let readContract (endpoint: string) (id: NodeId) : Result<DeclaredReturn option, DeclarationFinding> =
        match recordOf graph id with
        | Some (node, cf) when typeName node = Some "Contract" ->
            match field "AtMost" cf with
            | None -> Ok None
            | Some atMostId ->
                match stringOf graph atMostId with
                | Some "" -> Ok None
                | Some atMost ->
                    match field "Floor" cf |> Option.bind (int64Of graph) with
                    | Some floor -> Ok (Some { Node = node.Id; Endpoint = endpoint; Floor = bigint floor; AtMost = atMost })
                    | None -> Error (findingAt node DeclarationDefect.Malformed "a Contract that names an AtMost parameter must declare its Floor as an integer literal")
                | None -> Error (findingAt node DeclarationDefect.Malformed "a Contract's AtMost must be a string literal")
        | _ -> Error (findingOn graph id DeclarationDefect.Malformed "an element of Contracts is not a Contract record")
    let readEndpoint (id: NodeId) : Result<DeclaredReturn list * DeclarationFinding list, DeclarationFinding> =
        match recordOf graph id with
        | Some (node, ef) when typeName node = Some "Endpoint" ->
            match field "Name" ef |> Option.bind (stringOf graph) with
            | Some name ->
                let bounds, findings = readList graph ef "Contracts" (readContract name)
                Ok (List.choose (fun b -> b) bounds, findings)
            | None -> Error (findingAt node DeclarationDefect.Malformed "an Endpoint's Name must be a string literal")
        | _ -> Error (findingOn graph id DeclarationDefect.Malformed "an element of Endpoints is not an Endpoint record")
    let readSurface (id: NodeId) : Result<DeclaredReturn list * DeclarationFinding list, DeclarationFinding> =
        match recordOf graph id with
        | Some (node, sf) when typeName node = Some "BoundarySurface" ->
            let endpoints, findings = readList graph sf "Endpoints" readEndpoint
            Ok (endpoints |> List.collect fst, findings @ (endpoints |> List.collect snd))
        | _ -> Error (findingOn graph id DeclarationDefect.Malformed "an element of Surfaces is not a BoundarySurface record")
    let surfaces, findings = readList graph fields "Surfaces" readSurface
    let returns = surfaces |> List.collect fst
    returns, findings @ (surfaces |> List.collect snd) @ duplicates "return bound" (fun r -> r.Endpoint) (fun r -> r.Node) graph returns

let private readPlatform (graph: SemanticGraph) (node: SemanticNode) (fields: (string * NodeId) list) : DeclaredPlatform option * DeclarationFinding list =
    match field "Id" fields |> Option.bind (stringOf graph) with
    | None -> None, [ findingAt node DeclarationDefect.Malformed "a platform description's Id must be a string literal" ]
    | Some id ->
        let spaces, spaceFindings = readList graph fields "Spaces" (readSpace graph)
        let buffers, bufferFindings = readList graph fields "Buffers" (readBuffer graph)
        let returns, returnFindings = readReturns graph fields
        let core, coreFindings =
            match field "Core" fields with
            | Some coreId -> readCore graph coreId
            | None -> None, []
        Some { Node = node.Id; Id = id; Core = core; Spaces = spaces; Buffers = buffers; Returns = returns },
        spaceFindings @ bufferFindings @ returnFindings @ coreFindings

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

//-------------------------------------------------------------------------
// The declared boundaries (Dimensional_Range_Design.md §4.1, ruling 1 of CS-12): one reader
// for the wire-schema field, the MMIO register's descriptor, and the C ABI parameter
//-------------------------------------------------------------------------

/// One integer field a layout descriptor declares (BAREWire `FieldDescriptor`): the field's
/// name, its declared representation (`Repr`, `"u16"`), the bits that representation has and
/// the exact range a value of it holds. A field whose representation is not an integer (a
/// real, a pointer) is not carried: nothing integer crosses there.
type DeclaredField = {
    Node: NodeId
    Name: string
    Repr: string
    Bits: int
    Range: ValueRange
}

/// Measured physical fields are retained independently of integer range facts.
type DeclaredPhysicalField = { Node: NodeId; Name: string; Repr: string; Offset: int; Count: int }

/// A layout descriptor (a `StructDescriptor` or a `PeripheralDescriptor`): the node that
/// declares it, its declared name, the record type of this graph it describes when exactly one
/// record type bears that name (its fields are then seeded from `Fields`), and its integer
/// fields. A descriptor naming no record type of the graph describes a C struct or a register
/// block with no Clef record, and seeds nothing.
type DeclaredLayout = {
    Node: NodeId
    Name: string
    RecordType: string option
    Fields: DeclaredField list
    PhysicalFields: DeclaredPhysicalField list
    Size: int option
    Alignment: int option
}

/// One parameter or the return of a binding descriptor (BAREWire `ParameterInfo`, `TypeRef`)
/// that carries an integer or a boolean: its name, its declared bits and the exact range.
type DeclaredParameter = {
    Node: NodeId
    Name: string
    Bits: int
    Range: ValueRange
}

/// A pointer cell carries an opaque nullable handle, never a source numeric range.
type DeclaredPointerReference = {
    Node: NodeId
    Name: string
    Bits: int
}

/// A binding descriptor (`Expr<FunctionDescriptor>`, the quotation a generator emits beside an
/// extern; platform-bindings.md "Layer 2"): the node that declares it, the C name, and, when
/// the extern it describes sits beside it (`<name>Descriptor` beside `<name>`, in one module),
/// the extern's parameter nodes paired with their declared ranges (None for a parameter that is
/// not an integer or a boolean on the C side: a pointer, a real, a named type) and the extern's
/// body node with the declared return. An extern with no descriptor beside it is not described
/// here and keeps the CPU leg's rule for its parameters.
type DeclaredFunction = {
    Node: NodeId
    CName: string
    Parameters: (NodeId * DeclaredParameter option) list
    /// A reference parameter exposes exactly one declared scalar in a bounded array.
    References: (NodeId * DeclaredParameter) list
    PointerReferences: (NodeId * DeclaredPointerReference) list
    RecordReferences: (NodeId * bool) list // parameter, explicitly read-only
    Body: NodeId option
    Return: DeclaredParameter option
}

/// Every boundary declaration in the graph, with every defect found reading them.
type Descriptors = {
    Layouts: DeclaredLayout list
    Functions: DeclaredFunction list
    Findings: DeclarationFinding list
}

/// The exact range and bits a BAREWire `Repr` tag declares for an integer or boolean field:
/// None for a representation that carries no integer (`f32`, `f64`, `pointer`), Error for a tag
/// outside the vocabulary.
let private rangeOfRepr (repr: string) : Result<(int * ValueRange) option, string> =
    match repr with
    | "u8" -> Ok (Some (8, ValueRange.unsignedOf 8))
    | "u16" -> Ok (Some (16, ValueRange.unsignedOf 16))
    | "u32" -> Ok (Some (32, ValueRange.unsignedOf 32))
    | "u64" -> Ok (Some (64, ValueRange.unsignedOf 64))
    | "i8" -> Ok (Some (8, ValueRange.twosComplement 8))
    | "i16" -> Ok (Some (16, ValueRange.twosComplement 16))
    | "i32" -> Ok (Some (32, ValueRange.twosComplement 32))
    | "i64" -> Ok (Some (64, ValueRange.twosComplement 64))
    | "bool" -> Ok (Some (1, ValueRange.boolean))
    | "f32" | "f64" | "pointer" -> Ok None
    | other -> Error (sprintf "'%s' is not a representation the BAREWire vocabulary names" other)

/// A union case as declared: its name and its payload node, through a `UnionCase` (before
/// Baker saturation) or the `DUConstruct` it becomes.
let caseOf (graph: SemanticGraph) (id: NodeId) : (SemanticNode * string * NodeId option) option =
    match valueOf graph id with
    | Some (({ Kind = SemanticKind.UnionCase (name, _, payload) } : SemanticNode) as node)
    | Some (({ Kind = SemanticKind.DUConstruct (name, _, payload, _) } : SemanticNode) as node) -> Some (node, name, payload)
    | _ -> None

/// The two elements of a pair payload (`Integer (Signed, 32)`).
let private pairOf (graph: SemanticGraph) (id: NodeId) : (NodeId * NodeId) option =
    match valueOf graph id with
    | Some ({ Kind = SemanticKind.TupleExpr [ a; b ] } : SemanticNode) -> Some (a, b)
    | Some ({ Children = [ a; b ] } : SemanticNode) -> Some (a, b)
    | _ -> None

/// A `TypeRef` as declared: the bits and range of an integer or boolean reference, None for a
/// reference that carries no integer (`Float`, `Pointer`, `Void`, `Named`), a finding for a
/// case the vocabulary does not name, a payload the reader cannot read, or a width of no bits.
let private readTypeRef (graph: SemanticGraph) (id: NodeId) : Result<(int * ValueRange) option, DeclarationFinding> =
    match caseOf graph id with
    | Some (node, "Integer", Some payload) ->
        match pairOf graph payload with
        | Some (signId, bitsId) ->
            match caseOf graph signId, int64Of graph bitsId with
            | Some (_, "Signed", _), Some bits when bits > 0L -> Ok (Some (int bits, ValueRange.twosComplement (int bits)))
            | Some (_, "Unsigned", _), Some bits when bits > 0L -> Ok (Some (int bits, ValueRange.unsignedOf (int bits)))
            | Some (_, ("Signed" | "Unsigned"), _), Some bits -> Error (findingAt node DeclarationDefect.Invalid (sprintf "an Integer of %d bits; a width is a positive number of bits" bits))
            | _ -> Error (findingAt node DeclarationDefect.Malformed "an Integer's payload must be a Signedness case and an integer literal")
        | None -> Error (findingAt node DeclarationDefect.Malformed "an Integer's payload must be a pair (Signed | Unsigned, bits)")
    | Some (node, (("Float" | "Pointer") as case), Some payload) ->
        match int64Of graph payload with
        | Some bits when bits > 0L -> Ok None
        | Some bits -> Error (findingAt node DeclarationDefect.Invalid (sprintf "a %s of %d bits; a width is a positive number of bits" case bits))
        | None -> Error (findingAt node DeclarationDefect.Malformed (sprintf "a %s's bits must be an integer literal" case))
    | Some (_, "Bool", _) -> Ok (Some (1, ValueRange.boolean))
    | Some (_, ("Void" | "Named"), _) -> Ok None
    | Some (node, other, _) -> Error (findingAt node DeclarationDefect.Invalid (sprintf "'%s' is not a TypeRef case the BAREWire vocabulary names" other))
    | None -> Error (findingOn graph id DeclarationDefect.Malformed "a Type must be a TypeRef case (Integer, Float, Pointer, Bool, Void, Named)")

/// One `ParameterInfo` as declared.
let private readParameter (graph: SemanticGraph) (id: NodeId) : Result<(string * DeclaredParameter option * bool * DeclaredPointerReference option * string option * bool), DeclarationFinding> =
    match recordOf graph id with
    | Some (node, fields) when typeName node = Some "ParameterInfo" ->
        match field "Name" fields |> Option.bind (stringOf graph), field "Type" fields with
        | Some name, Some typeId ->
            readTypeRef graph typeId
            |> Result.map (Option.map (fun (bits, range) -> { Node = node.Id; Name = name; Bits = bits; Range = range }))
            |> Result.map (fun declared ->
                let passing = field "PassBy" fields |> Option.bind (caseOf graph)
                let readOnly = passing |> Option.exists (fun (_, name, _) -> name = "ReadOnlyReference")
                let byReference = readOnly || (passing |> Option.exists (fun (_, name, _) -> name = "Reference"))
                let pointer =
                    match caseOf graph typeId with
                    | Some (_, "Pointer", Some bits) ->
                        int64Of graph bits |> Option.map (fun bits -> { Node = node.Id; Name = name; Bits = int bits } : DeclaredPointerReference)
                    | _ -> None
                let named =
                    match caseOf graph typeId with
                    | Some (_, "Named", Some name) -> stringOf graph name
                    | _ -> None
                name, declared, byReference, pointer, named, readOnly)
        | _ -> Error (findingAt node DeclarationDefect.Malformed "a ParameterInfo's Name must be a string literal and it must declare a Type")
    | _ -> Error (findingOn graph id DeclarationDefect.Malformed "an element of Parameters is not a ParameterInfo record")

/// One `FieldDescriptor` as declared, when it carries an integer.
let private readField (graph: SemanticGraph) (id: NodeId) : Result<DeclaredField option, DeclarationFinding> =
    match recordOf graph id with
    | Some (node, fields) when typeName node = Some "FieldDescriptor" ->
        match field "Name" fields |> Option.bind (stringOf graph), field "Repr" fields |> Option.bind (stringOf graph) with
        | Some name, Some repr ->
            match rangeOfRepr repr with
            | Ok (Some (bits, range)) -> Ok (Some { Node = node.Id; Name = name; Repr = repr; Bits = bits; Range = range })
            | Ok None -> Ok None
            | Error message -> Error (findingAt node DeclarationDefect.Invalid (sprintf "the field '%s': %s" name message))
        | _ -> Error (findingAt node DeclarationDefect.Malformed "a FieldDescriptor's Name and Repr must be string literals")
    | _ -> Error (findingOn graph id DeclarationDefect.Malformed "an element of Fields is not a FieldDescriptor record")

/// The bit fields of a field descriptor, each checked: a bare integer width of at least one bit
/// at a non-negative position.
let private bitFieldFindings (graph: SemanticGraph) (fieldId: NodeId) : DeclarationFinding list =
    match recordOf graph fieldId with
    | Some (_, fields) ->
        let read (id: NodeId) : Result<unit, DeclarationFinding> =
            match recordOf graph id with
            | Some (node, bf) when typeName node = Some "BitFieldDescriptor" ->
                match field "Position" bf |> Option.bind (int64Of graph), field "Width" bf |> Option.bind (int64Of graph) with
                | Some position, Some width when position >= 0L && width >= 1L -> Ok ()
                | Some position, Some width -> Error (findingAt node DeclarationDefect.Invalid (sprintf "a bit field at position %d of width %d; a bit field is at least one bit at a non-negative position" position width))
                | _ -> Error (findingAt node DeclarationDefect.Malformed "a BitFieldDescriptor's Position and Width must be integer literals")
            | _ -> Error (findingOn graph id DeclarationDefect.Malformed "an element of BitFields is not a BitFieldDescriptor record")
        snd (readList graph fields "BitFields" read)
    | None -> []

/// The last segment of a qualified type name.
let private shortName (name: string) : string =
    match name.LastIndexOf '.' with
    | -1 -> name
    | i -> name.Substring(i + 1)

/// The record types of the graph a descriptor's name denotes: the one whose qualified name is
/// the name, or those whose last segment is.
let private recordTypesNamed (graph: SemanticGraph) (name: string) : string list =
    let types = graph.Types.Value |> Map.toList |> List.map fst
                |> List.filter (fun name -> SemanticGraph.tryGetRecordFields name graph |> Option.isSome)
    match types |> List.filter (fun t -> t = name) with
    | [ exact ] -> [ exact ]
    | _ -> types |> List.filter (fun t -> shortName t = name)

/// A layout descriptor (`StructDescriptor` or `PeripheralDescriptor`) at its declaring node,
/// with its integer fields and the record type it seeds. A field the descriptor declares that
/// the record it names does not carry, or carries at a type that is not an integer or a
/// boolean, is a finding at the field.
let private readLayout (graph: SemanticGraph) (node: SemanticNode) (fields: (string * NodeId) list) : DeclaredLayout option * DeclarationFinding list =
    match field "Name" fields |> Option.bind (stringOf graph) with
    | None -> None, [ findingAt node DeclarationDefect.Malformed "a descriptor's Name must be a string literal" ]
    | Some name ->
        let layoutFields, layoutFindings =
            match field "Layout" fields |> Option.bind (recordOf graph) with
            | Some (layoutNode, layoutFields) when typeName layoutNode = Some "PeripheralLayout" ->
                let declared, findings = readList graph layoutFields "Fields" (readField graph)
                let bitFindings =
                    match field "Fields" layoutFields |> Option.bind (elementsOf graph) with
                    | Some elements -> elements |> List.collect (bitFieldFindings graph)
                    | None -> []
                List.choose id declared, findings @ bitFindings
            | _ -> [], [ findingAt node DeclarationDefect.Malformed "a descriptor's Layout must be a PeripheralLayout record" ]
        let recordType, typeFindings =
            match recordTypesNamed graph name with
            | [] -> None, []
            | [ one ] ->
                let recordFields = SemanticGraph.tryGetRecordFields one graph |> Option.defaultValue []
                let absent =
                    layoutFields
                    |> List.filter (fun f ->
                        match recordFields |> List.tryFind (fun (n, _) -> n = f.Name) with
                        | Some (_, ty) -> not (Types.isIntegerType ty || Types.tryGetNTUKind ty = Some NTUKind.NTUbool)
                        | None -> true)
                    |> List.map (fun f -> findingAt (SemanticGraph.tryGetNode f.Node graph |> Option.defaultValue node) DeclarationDefect.Invalid (sprintf "the field '%s' is declared '%s' but the record '%s' carries no integer or boolean field of that name" f.Name f.Repr one))
                Some one, absent
            | many -> None, [ findingAt node DeclarationDefect.Ambiguous (sprintf "the descriptor '%s' names more than one record type of the program (%s); qualify the name" name (String.concat ", " many)) ]
        let physical, size, alignment =
            match field "Layout" fields |> Option.bind (recordOf graph) with
            | Some (_, body) ->
                let physical =
                    field "Fields" body |> Option.bind (elementsOf graph) |> Option.defaultValue []
                    |> List.choose (fun id ->
                        match recordOf graph id with
                        | Some (f, ff) ->
                            match field "Name" ff |> Option.bind (stringOf graph), field "Repr" ff |> Option.bind (stringOf graph), field "Offset" ff |> Option.bind (int64Of graph), field "Count" ff |> Option.bind (int64Of graph) with
                            | Some name, Some repr, Some offset, Some count -> Some { Node = f.Id; Name = name; Repr = repr; Offset = int offset; Count = int count }
                            | _ -> None
                        | None -> None)
                physical, (field "Size" body |> Option.bind (int64Of graph) |> Option.map int), (field "Alignment" body |> Option.bind (int64Of graph) |> Option.map int)
            | None -> [], None, None
        Some { Node = node.Id; Name = name; RecordType = recordType; Fields = layoutFields; PhysicalFields = physical; Size = size; Alignment = alignment }, layoutFindings @ typeFindings

/// The lambda a binding's value is, through an annotation.
let lambdaOfBinding (graph: SemanticGraph) (bindingId: NodeId) : ((string * NativeType * NodeId) list * NodeId) option =
    let rec ofValue (id: NodeId) (depth: int) =
        if depth > 4 then None
        else
            match SemanticGraph.tryGetNode id graph with
            | Some { Kind = SemanticKind.Lambda (parameters, body, _, _, _) } -> Some (parameters, body)
            | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> ofValue inner (depth + 1)
            | _ -> None
    match SemanticGraph.tryGetNode bindingId graph with
    | Some { Kind = SemanticKind.Lambda _ } -> ofValue bindingId 0
    | Some { Children = children } when not (List.isEmpty children) -> ofValue (List.last children) 0
    | _ -> None

/// The extern `<name>` beside the descriptor `<name>Descriptor`: a binding of that name with
/// the same parent carrying `FidelityExtern.Library`.
let private externBeside (graph: SemanticGraph) (descriptor: SemanticNode) (bindingName: string) : SemanticNode option =
    if not (bindingName.EndsWith "Descriptor") then None
    else
        let name = bindingName.Substring(0, bindingName.Length - "Descriptor".Length)
        graph.Nodes
        |> Map.toList
        |> List.tryPick (fun (_, node) ->
            match node.Kind with
            | SemanticKind.Binding (n, _, _, _) when n = name && node.Parent = descriptor.Parent && Map.containsKey "FidelityExtern.Library" node.Metadata -> Some node
            | _ -> None)

/// A binding descriptor at its declaring node, paired with the extern beside it.
let readFunctionForBinding (graph: SemanticGraph) (binding: SemanticNode) (_bindingName: string) (node: SemanticNode) (fields: (string * NodeId) list) : DeclaredFunction option * DeclarationFinding list =
    match field "CName" fields |> Option.bind (stringOf graph), field "ReturnType" fields with
    | Some cname, Some returnId ->
        let parameters, parameterFindings = readList graph fields "Parameters" (readParameter graph)
        let returned, returnFindings =
            match readTypeRef graph returnId with
            | Ok (Some (bits, range)) -> Some { Node = returnId; Name = "ReturnType"; Bits = bits; Range = range }, []
            | Ok None -> None, []
            | Error f -> None, [ f ]
        let pairs, references, pointerReferences, recordReferences, body, externFindings =
            match lambdaOfBinding graph binding.Id with
            | None -> [], [], [], [], None, []
            | Some (lambdaParameters, body) ->
                let lambdaParameters =
                    match parameters, lambdaParameters with
                    | [], [(_, ty, _)] when Types.tryGetNTUKind ty = Some NTUKind.NTUunit -> []
                    | _ -> lambdaParameters
                if List.length lambdaParameters <> List.length parameters then
                    [], [], [], [], None, [ findingAt node DeclarationDefect.Invalid (sprintf "the descriptor of '%s' declares %d parameters; the binding takes %d" cname parameters.Length lambdaParameters.Length) ]
                else
                    let rows =
                        List.zip lambdaParameters parameters
                        |> List.map (fun ((_, ty, paramId), (declaredName, declared, byReference, pointer, named, readOnly)) ->
                            let ranged ty = Types.isIntegerType ty || Types.tryGetNTUKind ty = Some NTUKind.NTUbool
                            let element =
                                match ty with
                                | NativeType.TApp (tc, [elem]) when tc.Name = "array" || tc.Name = "Array" -> Some elem
                                | _ -> None
                            let nullableHandle ty =
                                match ty with
                                | NativeType.TApp (tc, [inner]) when tc.Name = "option" -> Types.tryGetNTUKind inner = Some NTUKind.NTUptr
                                | _ -> false
                            let invalid message = (paramId, None), None, None, None, Some (findingAt node DeclarationDefect.Invalid message)
                            match declared, byReference, pointer, named, element with
                            | Some d, true, _, _, Some elem when ranged elem -> (paramId, None), Some (paramId, d), None, None, None
                            | Some _, true, _, _, _ -> invalid (sprintf "the reference parameter '%s' of '%s' requires a bounded scalar array" declaredName cname)
                            | _, true, Some d, _, Some elem when nullableHandle elem -> (paramId, None), None, Some (paramId, d), None, None
                            | _, true, Some _, _, _ -> invalid (sprintf "the pointer reference '%s' of '%s' requires a bounded option<CHandle<_>> array" declaredName cname)
                            | _, true, _, Some name, _ ->
                                let declaredTypes = recordTypesNamed graph name
                                let actual = match ty with NativeType.TApp (tc, _) -> Some tc.Name | _ -> None
                                if actual |> Option.exists (fun actual -> declaredTypes |> List.exists (fun name -> name = actual || shortName name = shortName actual)) then
                                    (paramId, None), None, None, Some (paramId, readOnly), None
                                else invalid (sprintf "the reference '%s' of '%s' requires the declared record '%s'" declaredName cname name)
                            | Some d, false, _, _, _ when not (ranged ty) -> invalid (sprintf "the parameter '%s' of '%s' is declared an integer of %d bits, but the binding's parameter is not an integer" declaredName cname d.Bits)
                            | _ -> (paramId, (if ranged ty then declared else None)), None, None, None, None)
                    rows |> List.map (fun (p, _, _, _, _) -> p),
                    rows |> List.choose (fun (_, r, _, _, _) -> r),
                    rows |> List.choose (fun (_, _, p, _, _) -> p),
                    rows |> List.choose (fun (_, _, _, r, _) -> r),
                    Some body, rows |> List.choose (fun (_, _, _, _, f) -> f)
        Some { Node = node.Id; CName = cname; Parameters = pairs; References = references; PointerReferences = pointerReferences; RecordReferences = recordReferences; Body = body; Return = returned },
        parameterFindings @ returnFindings @ externFindings
    | _ -> None, [ findingAt node DeclarationDefect.Malformed "a FunctionDescriptor's CName must be a string literal and it must declare a ReturnType" ]

/// Resolve the generated extern beside its descriptor, then use the same reader as callbacks.
let private readFunction graph binding bindingName node fields =
    let target = externBeside graph binding bindingName |> Option.defaultValue binding
    readFunctionForBinding graph target bindingName node fields

/// Every boundary declaration in the graph: a module-level binding whose value, through an
/// annotation or a quotation, is a `StructDescriptor`, a `PeripheralDescriptor` or a
/// `FunctionDescriptor` record. Read whether or not reachable (a declaration never is). A
/// descriptor built by a function is a value, not a declaration, and is not read.
let readDescriptors (graph: SemanticGraph) : Descriptors =
    let isModuleLevel (node: SemanticNode) =
        match node.Parent |> Option.bind (fun p -> SemanticGraph.tryGetNode p graph) with
        | Some { Kind = SemanticKind.ModuleDef _ } -> true
        | _ -> false
    graph.Nodes
    |> Map.toList
    |> List.fold (fun (layouts, functions, findings) (_, node) ->
        match node.Kind with
        | SemanticKind.Binding (name, _, _, _) when isModuleLevel node && not (List.isEmpty node.Children) ->
            match recordOf graph (List.last node.Children) with
            | Some (record, fields) ->
                match typeName record with
                | Some "StructDescriptor" | Some "PeripheralDescriptor" ->
                    let layout, more = readLayout graph record fields
                    (Option.toList layout @ layouts, functions, findings @ more)
                | Some "FunctionDescriptor" ->
                    let f, more = readFunction graph node name record fields
                    (layouts, Option.toList f @ functions, findings @ more)
                | _ -> (layouts, functions, findings)
            | None -> (layouts, functions, findings)
        | _ -> (layouts, functions, findings)) ([], [], [])
    |> fun (layouts, functions, findings) -> { Layouts = List.rev layouts; Functions = List.rev functions; Findings = findings }

/// The bounded scalar references a call passes, paired with its actual arrays.
/// The descriptor supplies the element ABI; the lowering must retain an extent
/// check before projecting the first element's address across the foreign call.
let referenceArguments (graph: SemanticGraph) (funcId: NodeId) (args: NodeId list) =
    let rec binding id =
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> binding inner
        | Some { Kind = SemanticKind.VarRef (_, Some id) } -> Some id
        | _ -> None
    match binding funcId |> Option.bind (lambdaOfBinding graph) with
    | Some (parameters, _) when parameters.Length = args.Length ->
        let declared = (readDescriptors graph).Functions |> List.collect (fun f -> f.References) |> Map.ofList
        List.zip parameters args
        |> List.choose (fun ((_, _, parameter), arg) -> Map.tryFind parameter declared |> Option.map (fun d -> arg, d))
    | _ -> []

/// Scalar arrays retain their interior representation. A native projection may
/// omit copy-back only when the parameter declaration explicitly permits reads.
let readOnlyScalarReferenceArguments graph funcId args =
    referenceArguments graph funcId args
    |> List.choose (fun (id, declared) ->
        match recordOf graph declared.Node with
        | Some (_, fields) ->
            match field "PassBy" fields |> Option.bind (caseOf graph) with
            | Some (_, "ReadOnlyReference", _) -> Some id
            | _ -> None
        | None -> None)
    |> Set.ofList

/// Non-numeric reference contracts remain separate from scalar range propagation.
let private actualReferences (graph: SemanticGraph) (funcId: NodeId) (args: NodeId list) (select: DeclaredFunction -> (NodeId * 'T) list) =
    let rec binding id =
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> binding inner
        | Some { Kind = SemanticKind.VarRef (_, Some id) } -> Some id
        | _ -> None
    match binding funcId |> Option.bind (lambdaOfBinding graph) with
    | Some (parameters, _) when parameters.Length = args.Length ->
        let declared = (readDescriptors graph).Functions |> List.collect select |> Map.ofList
        List.zip parameters args |> List.choose (fun ((_, _, parameter), arg) -> Map.tryFind parameter declared |> Option.map (fun d -> arg, d))
    | _ -> []

let pointerReferenceArguments graph funcId args = actualReferences graph funcId args (fun f -> f.PointerReferences)
let recordReferenceArguments graph funcId args = actualReferences graph funcId args (fun f -> f.RecordReferences) |> List.map fst |> Set.ofList

/// The result ABI declared beside the actual foreign callee. A call's locally
/// refined range does not change the width returned by the native library.
let returnOfCall (graph: SemanticGraph) (funcId: NodeId) =
    let rec binding id =
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> binding inner
        | Some { Kind = SemanticKind.VarRef (_, Some id) } -> Some id
        | _ -> None
    binding funcId
    |> Option.bind (lambdaOfBinding graph)
    |> Option.bind (fun (_, body) ->
        (readDescriptors graph).Functions
        |> List.tryPick (fun f -> if f.Body = Some body then f.Return else None))

/// The target declares which C ABI its foreign aggregate calls use.
let cAbiOfGraph (graph: SemanticGraph) =
    graph.Nodes |> Map.toSeq |> Seq.choose (fun (_, node) ->
        match node.Kind with
        | SemanticKind.Binding _ ->
            node.Children |> List.tryLast |> Option.bind (recordOf graph)
            |> Option.bind (fun (record, fields) ->
                if typeName record <> Some "CAbiDescriptor" then None
                else
                    match field "Name" fields |> Option.bind (stringOf graph), field "PointerBits" fields |> Option.bind (int64Of graph), field "ScalarAggregateRegisterBytes" fields |> Option.bind (int64Of graph) with
                    | Some name, Some bits, Some registerBytes -> Some (name, int bits, int registerBytes)
                    | _ -> None)
        | _ -> None) |> Seq.distinct |> Seq.toList

/// Only these parameters allow a temporary native record projection without write-back.
let readOnlyRecordReferenceArguments graph funcId args =
    actualReferences graph funcId args (fun f -> f.RecordReferences)
    |> List.choose (fun (id, readOnly) -> if readOnly then Some id else None) |> Set.ofList
