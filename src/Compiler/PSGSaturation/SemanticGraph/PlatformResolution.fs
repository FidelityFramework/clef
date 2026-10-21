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

/// A role reference and the unique memory-space declaration it resolves to.
type DeclaredProgramSpace = {
    Reference: NodeId
    Space: DeclaredSpace
}

/// The selected descriptor's explicit program-lifetime authority. Absence is
/// unavailable, including older Contracts records that declare no spaces.
type DeclaredProgramLifetime = {
    Node: NodeId
    Immutable: DeclaredProgramSpace
    Mutable: DeclaredProgramSpace option
}

/// The physical-layout projection shared by device-access checking and image
/// layout. Availability/version/map metadata are outside this projection.
let memorySpace (s: DeclaredSpace) : BAREWire.Platform.MemorySpace = {
    Name = s.Name; Kind = s.Kind; Base = s.Base; Capacity = s.Capacity
    Alignment = s.Alignment; Granularity = s.Granularity; Growth = s.Growth; Access = s.Access
    Notes = ""; MapKind = ""; Since = ""; Until = ""
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
    Arch: string
    Os: string
    Runtime: string
    Triple: string
    CpuModel: string
    Widths: DeclaredWidth list
    Representations: DeclaredRepresentation list
}

/// Transport the resolved source runtime vocabulary; project claims never
/// replace this declaration and remain available for consistency checking.
let runtimeModel (core: DeclaredCore) : RuntimeModel option =
    match core.Runtime with
    | "libc" -> Some RuntimeModel.Libc
    | "freestanding" -> Some RuntimeModel.Freestanding
    | "bare" -> Some RuntimeModel.Bare
    | "rocm" -> Some RuntimeModel.ROCm
    | "xdna" -> Some RuntimeModel.XDNA
    | _ -> None

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
    ProgramLifetime: DeclaredProgramLifetime option
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
let valuePath (graph: SemanticGraph) (id: NodeId) : (SemanticNode * NodeId list) option =
    let rec follow seen path id =
        // A cyclic declaration has no settled literal value. Keep its graph
        // intact for the owning declaration/dependency diagnostic.
        if Set.contains id seen then None else
        let seen = Set.add id seen
        let path = path @ [id]
        match SemanticGraph.tryGetNode id graph with
        | None -> None
        | Some node ->
            match node.Kind with
            | SemanticKind.TypeAnnotation (inner, _) -> follow seen path inner
            | SemanticKind.Quote (inner, _) -> follow seen path inner
            | SemanticKind.VarRef (_, Some bindingId) ->
                match SemanticGraph.tryGetNode bindingId graph with
                | Some ({ Children = [ valueId ] } : SemanticNode) -> follow seen (path @ [bindingId]) valueId
                | _ -> None
            | SemanticKind.Application (funcId, [ arg ]) ->
                match follow seen path funcId with
                | Some (({ Kind = SemanticKind.Intrinsic { Category = IntrinsicCategory.Conversion } } : SemanticNode), functionPath) -> follow seen functionPath arg
                | _ -> Some (node, path)
            | _ -> Some (node, path)
    follow Set.empty [] id

/// The existing value API projects the same owner, which also retains quote incidence.
let valueOf (graph: SemanticGraph) (id: NodeId) : SemanticNode option =
    valuePath graph id |> Option.map fst

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

/// An integer as declared: a literal, or its unary negation, within signed64.
let int64Of (graph: SemanticGraph) (id: NodeId) : int64 option =
    let rec exact id =
        match valueOf graph id with
        | Some ({ Kind = SemanticKind.Literal (NativeLiteral.Int (v, _)) } : SemanticNode) -> Some (bigint v)
        | Some ({ Kind = SemanticKind.Literal (NativeLiteral.UInt (v, _)) } : SemanticNode) -> Some (bigint v)
        | Some ({ Kind = SemanticKind.Application (funcId, [ arg ]) } : SemanticNode) ->
            match valueOf graph funcId with
            | Some ({ Kind = SemanticKind.Intrinsic { Operation = "op_UnaryNegation" } } : SemanticNode) -> exact arg |> Option.map (~-)
            | _ -> None
        | _ -> None
    exact id |> Option.bind (fun value ->
        if value < bigint System.Int64.MinValue || value > bigint System.Int64.MaxValue then None
        else Some (int64 value))

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
let elementsOf (graph: SemanticGraph) (id: NodeId) : NodeId list option =
    match valueOf graph id with
    | Some ({ Kind = SemanticKind.ArrayExpr elements } : SemanticNode) -> Some elements
    | Some ({ Kind = SemanticKind.ListExpr elements } : SemanticNode) -> Some elements
    | _ -> None

/// An option value as declared: `Some x` yields `Some (Some x's node)`, `None`
/// yields `Some None`, anything else `None`. A case is a UnionCase node until
/// Baker saturation and the DUConstruct it is decomposed into after it; the
/// declaration is read from the saturated graph, so both are followed.
let optionOf (graph: SemanticGraph) (id: NodeId) : NodeId option option =
    match valueOf graph id with
    | Some ({ Kind = SemanticKind.UnionCase ("Some", _, Some payload) } : SemanticNode)
    | Some ({ Kind = SemanticKind.DUConstruct ("Some", _, Some payload, _) } : SemanticNode) -> Some (Some payload)
    | Some ({ Kind = SemanticKind.UnionCase ("None", _, _) } : SemanticNode)
    | Some ({ Kind = SemanticKind.DUConstruct ("None", _, _, _) } : SemanticNode) -> Some None
    | _ -> None

/// The ordinary nominal Option carrier, never a union recognised by case names.
let optionalEntrySignature ty =
    match Clef.Compiler.NativeTypedTree.UnionFind.applySubst ty with
    | NativeType.TApp(option, [payload]) when
        Clef.Compiler.NativeTypedTree.TypeIdentities.constructor option =
            Clef.Compiler.NativeTypedTree.TypeIdentities.constructor Types.optionTyCon ->
        match Clef.Compiler.NativeTypedTree.UnionFind.applySubst payload with
        | NativeType.TApp(entry, [signature]) when entry.NTUKind = Some NTUKind.NTUfnptr ->
            match Clef.Compiler.NativeTypedTree.UnionFind.applySubst signature with NativeType.TFun _ -> Some signature | _ -> None
        | _ -> None
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
                match field "WordSizeBits" fields with
                | None -> []
                | Some wordSizeId ->
                    match int64Of graph wordSizeId, widths |> List.tryFind (fun w -> w.Name = "Register") with
                    | None, _ ->
                        [ findingOn graph wordSizeId DeclarationDefect.Malformed "a TargetCore's WordSizeBits must be an exact signed 64-bit integer declaration" ]
                    | Some wordSize, Some register when int64 register.Bits <> wordSize ->
                        [ findingAt node DeclarationDefect.Invalid (sprintf "the declared Register width %d disagrees with WordSizeBits %d" register.Bits wordSize) ]
                    | _ -> []
            let text name = field name fields |> Option.bind (stringOf graph) |> Option.defaultValue ""
            let optionalText name = field name fields |> Option.bind (optionOf graph) |> Option.flatten |> Option.bind (stringOf graph) |> Option.defaultValue ""
            let triple = if text "Triple" <> "" then text "Triple" else optionalText "TripleOverride"
            let cpu = if text "CpuModel" <> "" then text "CpuModel" else optionalText "CpuModel"
            // An identity field the core does not carry is undeclared (""); one it
            // carries must read as a string literal or `Some`/`None` of one, never
            // collapse to the undeclared spelling.
            let identityFindings =
                [ "Arch"; "Os"; "Runtime"; "Triple"; "CpuModel"; "TripleOverride" ]
                |> List.choose (fun name ->
                    field name fields |> Option.bind (fun id ->
                        let readable =
                            (stringOf graph id).IsSome ||
                            (match optionOf graph id with
                             | Some None -> true
                             | Some (Some payload) -> (stringOf graph payload).IsSome
                             | None -> false)
                        if readable then None
                        else Some (findingOn graph id DeclarationDefect.Malformed (sprintf "TargetCore.%s must be a string literal, or Some/None of one" name))))
            Some { Node = node.Id; Arch = text "Arch"; Os = text "Os"; Runtime = text "Runtime"; Triple = triple; CpuModel = cpu; Widths = widths; Representations = representations },
            widthFindings @ representationFindings @ duplicateWidths @ duplicateRepresentations @ wordSizeFindings @ identityFindings
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

let private readProgramLifetime (graph: SemanticGraph) (fields: (string * NodeId) list) (spaces: DeclaredSpace list)
    : DeclaredProgramLifetime option * DeclarationFinding list =
    let reference role immutable id =
        match stringOf graph id with
        | None -> Result.Error (findingOn graph id DeclarationDefect.Malformed (sprintf "ProgramLifetime.%s must be a string literal" role))
        | Some "" -> Result.Error (findingOn graph id DeclarationDefect.Invalid (sprintf "ProgramLifetime.%s must name a declared memory space" role))
        | Some name ->
            match spaces |> List.filter (fun space -> space.Name = name) with
            | [] -> Result.Error (findingOn graph id DeclarationDefect.Invalid (sprintf "ProgramLifetime.%s names undeclared memory space '%s'" role name))
            | [space] ->
                let permitted =
                    if immutable then space.Access = BAREWire.Platform.Access.ReadOnly || space.Access = BAREWire.Platform.Access.ReadExecute
                    else space.Access = BAREWire.Platform.Access.ReadWrite
                if permitted then Result.Ok { Reference = id; Space = space }
                else Result.Error (findingOn graph id DeclarationDefect.Invalid (sprintf "ProgramLifetime.%s is incompatible with the declared access of memory space '%s'" role name))
            | _ -> Result.Error (findingOn graph id DeclarationDefect.Ambiguous (sprintf "ProgramLifetime.%s names ambiguous memory space '%s'" role name))
    match field "ProgramLifetime" fields with
    | None -> None, []
    | Some id ->
        match optionOf graph id with
        | Some None -> None, []
        | None -> None, [findingOn graph id DeclarationDefect.Malformed "ProgramLifetime must be Some literal designation or None"]
        | Some (Some payload) ->
            match recordOf graph payload with
            | None -> None, [findingOn graph payload DeclarationDefect.Malformed "ProgramLifetime must contain a literal designation record"]
            | Some (node, roles) ->
                let immutable =
                    match field "Immutable" roles with
                    | Some id -> reference "Immutable" true id
                    | None -> Result.Error (findingAt node DeclarationDefect.Malformed "ProgramLifetime requires an Immutable space name")
                let mutableSpace =
                    match field "Mutable" roles with
                    | None -> Result.Error (findingAt node DeclarationDefect.Malformed "ProgramLifetime requires a Mutable option")
                    | Some id ->
                        match optionOf graph id with
                        | Some None -> Result.Ok None
                        | Some (Some name) -> reference "Mutable" false name |> Result.map Some
                        | None -> Result.Error (findingOn graph id DeclarationDefect.Malformed "ProgramLifetime.Mutable must be Some space name or None")
                match immutable, mutableSpace with
                | Result.Ok immutable, Result.Ok mutableSpace -> Some { Node = node.Id; Immutable = immutable; Mutable = mutableSpace }, []
                | _ ->
                    None, [match immutable with Result.Error error -> yield error | _ -> ()
                           match mutableSpace with Result.Error error -> yield error | _ -> ()]

let private readPlatform (graph: SemanticGraph) (node: SemanticNode) (fields: (string * NodeId) list) : DeclaredPlatform option * DeclarationFinding list =
    match field "Id" fields |> Option.bind (stringOf graph) with
    | None -> None, [ findingAt node DeclarationDefect.Malformed "a platform description's Id must be a string literal" ]
    | Some id ->
        let spaces, spaceFindings = readList graph fields "Spaces" (readSpace graph)
        let programLifetime, programFindings = readProgramLifetime graph fields spaces
        let buffers, bufferFindings = readList graph fields "Buffers" (readBuffer graph)
        let returns, returnFindings = readReturns graph fields
        let core, coreFindings =
            match field "Core" fields with
            | Some coreId -> readCore graph coreId
            | None -> None, []
        Some { Node = node.Id; Id = id; Core = core; Spaces = spaces; ProgramLifetime = programLifetime; Buffers = buffers; Returns = returns },
        spaceFindings @ duplicates "memory space" (fun (space: DeclaredSpace) -> space.Name) (fun space -> space.Node) graph spaces
        @ programFindings @ bufferFindings @ returnFindings @ coreFindings

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
let private readLegacy (graph: SemanticGraph) : Reading =
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

let private combineQualifiedName (prefix: string) (name: string) =
    if prefix = "" || name = prefix || name.StartsWith(prefix + ".", System.StringComparison.Ordinal) then name
    else prefix + "." + name

let private declaredPrefix (graph: SemanticGraph) id =
    graph.Modules
    |> Map.toList
    |> List.tryPick (fun (path, nodes) ->
        if List.contains id nodes then Some (String.concat "." path) else None)

/// Canonical source module identity. Namespace prefixes have no ModuleDef wrapper.
let qualifiedModuleName (graph: SemanticGraph) id : string option =
    let rec modulePrefix seen id =
        if Set.contains id seen then None else
        match SemanticGraph.tryGetNode id graph with
        | Some node ->
            match node.Kind with
            | SemanticKind.ModuleDef(name, _) ->
                let prefix =
                    match node.Parent with
                    | Some parent -> modulePrefix (Set.add id seen) parent
                    | None -> declaredPrefix graph id
                prefix |> Option.map (fun prefix -> combineQualifiedName prefix name)
            | _ -> None
        | None -> None
    modulePrefix Set.empty id

/// Canonical module-level export identity, using the same module-name owner.
let qualifiedExportName (graph: SemanticGraph) (binding: SemanticNode) : string option =
    match binding.Kind with
    | SemanticKind.Binding(name, _, _, _) ->
        let prefix =
            match binding.Parent with
            | Some parent -> qualifiedModuleName graph parent
            | None -> declaredPrefix graph binding.Id
        prefix |> Option.map (fun prefix -> combineQualifiedName prefix name)
    | _ -> None

/// Select a static export without executing calls or taking a mutable
/// initializer as its value. Quoted exports and immutable aliases preserve
/// the original record identity used by memory-space and MMIO checks.
let private explicitRecord (graph: SemanticGraph) (accept: SemanticNode -> bool) (binding: SemanticNode) =
    let rec follow seen id =
        if Set.contains id seen then None else
        let seen = Set.add id seen
        match SemanticGraph.tryGetNode id graph with
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] }
        | Some { Kind = SemanticKind.TypeAnnotation(value, _) }
        | Some { Kind = SemanticKind.Quote(value, _) } -> follow seen value
        | Some { Kind = SemanticKind.VarRef(_, Some value) } -> follow seen value
        | Some node ->
            match node.Kind with
            | SemanticKind.RecordExpr(fields, _) when accept node -> Some(node, fields)
            | _ -> None
        | None -> None
    follow Set.empty binding.Id

let private explicitDescription graph binding = explicitRecord graph isDescriptionType binding

/// Selection is constrained by the selected package's dependency closure,
/// independently of the larger compilation's application and catalogue inputs.
let private inSelectedSources (graph: SemanticGraph) (node: SemanticNode) =
    node.Range.File <> "" &&
    (graph.Platform |> Option.exists (fun ctx ->
        let path = (System.IO.Path.GetFullPath node.Range.File).Replace('\\', '/')
        Set.contains path ctx.PlatformSourcePaths))

/// A root inside the closure must not obtain its core, spaces or aliased value
/// from an unrelated dependency that happened to be loaded first. Preserve
/// the references; report the undeclared package dependency at its use site.
let private explicitSourceCensus (graph: SemanticGraph) (root: SemanticNode) =
    let rec visit seen id =
        if Set.contains id seen then seen, [] else
        let seen = Set.add id seen
        match SemanticGraph.tryGetNode id graph with
        | None -> seen, []
        | Some node ->
            let refs, findings =
                match node.Kind with
                | SemanticKind.VarRef(_, Some bindingId) ->
                    match SemanticGraph.tryGetNode bindingId graph with
                    | Some ({ Kind = SemanticKind.Binding _ } as binding) when not (inSelectedSources graph binding) ->
                        [], [findingAt node DeclarationDefect.Malformed
                            "the explicit description references a binding outside the selected platform's source dependency closure"]
                    | _ -> [bindingId], []
                | _ -> [], []
            (node.Children @ refs)
            |> List.fold (fun (seen, findings) child ->
                let seen, nested = visit seen child
                seen, findings @ nested) (seen, findings)
    visit Set.empty root.Id

let private explicitSourceFindings graph root = explicitSourceCensus graph root |> snd

/// Auxiliary platform declarations (for example C ABI and pin inventory) use
/// the same source provenance as an explicit root. Legacy unbound graphs keep
/// their existing structural discovery behavior.
let isSelectedPlatformDeclaration (graph: SemanticGraph) (node: SemanticNode) =
    match graph.Platform |> Option.bind (fun ctx -> ctx.PlatformDescription) with
    | None -> true
    | Some _ -> inSelectedSources graph node && List.isEmpty (explicitSourceFindings graph node)

let private explicitCoreFindings (ctx: PlatformContext) (graph: SemanticGraph) (platform: DeclaredPlatform option) =
    match platform |> Option.bind (fun p -> p.Core) with
    | None -> [] // FPGA descriptions legitimately have no instruction core.
    | Some core ->
        let runtime = function
            | RuntimeModel.Libc -> "libc"
            | RuntimeModel.Freestanding | RuntimeModel.Bare -> "freestanding"
            | RuntimeModel.ROCm -> "rocm"
            | RuntimeModel.XDNA -> "xdna"
        let normalizeRuntime = function "bare" -> "freestanding" | name -> name
        let metadataFindings =
            [ "arch", ctx.PlatformArchitecture, core.Arch
              "os", ctx.PlatformOS, core.Os
              "runtime_model", ctx.RuntimeModel |> Option.map runtime, normalizeRuntime core.Runtime ]
            |> List.choose (fun (key, claim, actual) ->
                match claim with
                | Some expected when expected <> actual ->
                    Some (findingOn graph core.Node DeclarationDefect.Invalid
                        (sprintf "selected [platform] %s '%s' disagrees with the explicit description's core '%s'" key expected actual))
                | _ -> None)
        // Compatibility for the instruction/OS spellings implemented by the
        // current explicit targets. This is not LLVM's general triple parser
        // or alias canonicalizer; extending the target vocabulary requires
        // extending these checks alongside that target's backend support.
        let tripleFindings =
            if System.String.IsNullOrWhiteSpace core.Triple then [] else
            let parts = core.Triple.Split '-'
            let architecture = parts.[0]
            let expectedArchitecture =
                match core.Arch with
                | "x86_64" -> Some "x86_64"
                | "arm_cortex_m33" -> Some "thumbv8m.main"
                | "arm_cortex_m7" -> Some "thumbv7em"
                | _ -> None
            let architectureFindings =
                match expectedArchitecture with
                | Some expected when architecture <> expected ->
                    [findingOn graph core.Node DeclarationDefect.Invalid
                        (sprintf "target triple architecture '%s' disagrees with core Arch '%s'; the supported triple spelling uses '%s'" architecture core.Arch expected)]
                | _ -> []
            let os =
                match Array.toList parts with
                // The existing ARM embedded triple omits the vendor component.
                | ["thumbv8m.main"; "none"; "eabi"] -> "none"
                | ["thumbv7em"; "none"; "eabihf"] -> "none"
                | _ when parts.Length >= 3 -> parts.[2]
                | _ -> ""
            let osFindings =
                match expectedArchitecture, core.Os with
                | Some _, ("linux" | "none") when os <> core.Os ->
                    [findingOn graph core.Node DeclarationDefect.Invalid
                        (sprintf "target triple OS '%s' disagrees with core Os '%s'; current targets support explicit Linux/none OS components and declared Cortex-M embedded triples" os core.Os)]
                | _ -> []
            architectureFindings @ osFindings
        metadataFindings @ tripleFindings

/// An explicit export is authoritative even when its declaration belongs to
/// a sibling dependency. Unselected catalogue records are ordinary data.
/// Legacy leaves retain the directory-scoped, BAREWire-preferred reader.
let read (graph: SemanticGraph) : Reading =
    match graph.Platform |> Option.bind (fun ctx -> ctx.PlatformDescription) with
    | None -> readLegacy graph
    | Some name ->
        let candidates =
            graph.Nodes.Values
            |> Seq.filter (fun node -> inSelectedSources graph node && qualifiedExportName graph node = Some name)
            |> Seq.toList
        match candidates with
        | [] ->
            let path = graph.Platform |> Option.bind (fun ctx -> ctx.PlatformLibraryPath) |> Option.defaultValue ""
            { Platform = None
              Findings = [{ Node = NodeId 0; Range = { noRange with File = path }; Defect = DeclarationDefect.Malformed
                            Message = sprintf "explicit description export '%s' was not found in the selected platform's source dependency closure" name }] }
        | [binding] ->
            match explicitSourceFindings graph binding with
            | _ :: _ as findings -> { Platform = None; Findings = findings }
            | [] ->
            match explicitDescription graph binding with
            | None ->
                { Platform = None
                  Findings = [findingAt binding DeclarationDefect.Malformed
                    (sprintf "explicit description export '%s' must be an immutable PlatformDescription or PlatformDescriptor declaration (plain, quoted, or an immutable alias)" name)] }
            | Some(node, fields) ->
                let platform, findings = readPlatform graph node fields
                let consistency = graph.Platform |> Option.map (fun ctx -> explicitCoreFindings ctx graph platform) |> Option.defaultValue []
                { Platform = platform; Findings = findings @ consistency }
        | bindings ->
            { Platform = None
              Findings = bindings |> List.map (fun binding ->
                  findingAt binding DeclarationDefect.Ambiguous
                      (sprintf "explicit description export '%s' is ambiguous: %d bindings have that qualified name" name bindings.Length)) }

/// The declaration alone, for readers that cite it: what `read` could read.
/// The findings are reported once, by PlatformDeclaration at saturation.
let resolve (graph: SemanticGraph) : DeclaredPlatform option =
    (read graph).Platform

/// A stated process-link assumption, selected independently of the platform
/// description. The declaration and all of its literal premises stay visible.
type DeclaredProcessLink =
    {
        Node: NodeId
        Binding: NodeId
        Selector: string
        Contract: BAREWire.Platform.ProcessLinkContract
        Participants: Set<NodeId>
    }

/// The platform reader is the only owner of the selected loading export. An
/// unselected catalogue contract supplies no authority to an imported entry.
let readLoading (graph: SemanticGraph) : Result<DeclaredProcessLink option, DeclarationFinding list> =
    match graph.Platform |> Option.bind (fun context -> context.PlatformLoading) with
    | None -> Ok None
    | Some selector ->
        let candidates =
            graph.Nodes.Values
            |> Seq.filter (fun node -> inSelectedSources graph node && qualifiedExportName graph node = Some selector)
            |> Seq.toList

        match candidates with
        | [] ->
            let path =
                graph.Platform
                |> Option.bind (fun context -> context.PlatformLibraryPath)
                |> Option.defaultValue ""

            Error
                [
                    {
                        Node = NodeId 0
                        Range = { noRange with File = path }
                        Defect = DeclarationDefect.Malformed
                        Message = $"explicit loading export '{selector}' was not found in the selected platform's source dependency closure"
                    }
                ]
        | [ binding ] ->
            let participants, findings = explicitSourceCensus graph binding

            match findings with
            | _ :: _ -> Error findings
            | [] ->
                match explicitRecord graph (fun node -> typeName node = Some "ProcessLinkContract") binding with
                | None ->
                    Error
                        [
                            findingAt
                                binding
                                DeclarationDefect.Malformed
                                $"explicit loading export '{selector}' must be an immutable ProcessLinkContract declaration (plain, quoted, or an immutable alias)"
                        ]
                | Some(node, fields) ->
                    let text name =
                        match fields |> List.filter (fun (field, _) -> field = name) with
                        | [ (_, id) ] ->
                            match valuePath graph id with
                            | Some({
                                       Kind = SemanticKind.Literal(NativeLiteral.String value)
                                   },
                                   path) when
                                not (System.String.IsNullOrWhiteSpace value)
                                && (path
                                    |> List.forall (fun id ->
                                        graph.Nodes.TryFind id
                                        |> Option.exists (fun premise ->
                                            match premise.Kind with
                                            | SemanticKind.Binding(_, true, _, _) -> false
                                            | _ -> true)))
                                ->
                                Ok value
                            | _ -> Error name
                        | _ -> Error name

                    let names =
                        [
                            "Identity"
                            "Version"
                            "Source"
                            "Library"
                            "Runtime"
                            "Os"
                            "Arch"
                            "LoadAt"
                            "LiveUntil"
                            "Unloading"
                            "ExportedLibrary"
                        ]

                    let values = names |> List.map (fun name -> name, text name)

                    let malformed =
                        values
                        |> List.choose (fun (_, value) ->
                            match value with
                            | Error name -> Some name
                            | Ok _ -> None)

                    if not malformed.IsEmpty then
                        let fields = System.String.Join(", ", malformed)

                        Error
                            [
                                findingAt
                                    node
                                    DeclarationDefect.Malformed
                                    $"the selected loading contract requires unique immutable nonempty string fields: {fields}"
                            ]
                    else
                        let values =
                            values
                            |> List.choose (fun (name, value) -> value |> Result.toOption |> Option.map (fun value -> name, value))
                            |> Map.ofList

                        let contract: BAREWire.Platform.ProcessLinkContract =
                            {
                                Identity = values["Identity"]
                                Version = values["Version"]
                                Source = values["Source"]
                                Library = values["Library"]
                                Runtime = values["Runtime"]
                                Os = values["Os"]
                                Arch = values["Arch"]
                                LoadAt = values["LoadAt"]
                                LiveUntil = values["LiveUntil"]
                                Unloading = values["Unloading"]
                                ExportedLibrary = values["ExportedLibrary"]
                            }

                        let platform = read graph

                        let expected =
                            contract.Runtime = "libc"
                            && contract.Os = "linux"
                            && contract.Arch = "x86_64"

                        let policy =
                            contract.LoadAt = "ProcessStartup"
                            && contract.LiveUntil = "ProcessTermination"
                            && contract.Unloading = "Forbidden"
                            && contract.ExportedLibrary = "Forbidden"

                        let target =
                            platform.Platform
                            |> Option.bind _.Core
                            |> Option.exists (fun core ->
                                core.Runtime = contract.Runtime
                                && core.Os = contract.Os
                                && core.Arch = contract.Arch)

                        if not platform.Findings.IsEmpty then
                            Error platform.Findings
                        elif not expected || not policy then
                            Error
                                [
                                    findingAt
                                        node
                                        DeclarationDefect.Invalid
                                        "the loading contract must declare its library under Linux AMD64 libc at process startup until process termination, with unloading and exported-library authority forbidden"
                                ]
                        elif not target then
                            Error
                                [
                                    findingAt
                                        node
                                        DeclarationDefect.Invalid
                                        "the loading contract disagrees with the selected source platform's core runtime, OS or architecture"
                                ]
                        else
                            Ok(
                                Some
                                    {
                                        Node = node.Id
                                        Binding = binding.Id
                                        Selector = selector
                                        Contract = contract
                                        Participants = Set.add node.Id participants
                                    }
                            )
        | bindings ->
            Error(
                bindings
                |> List.map (fun binding ->
                    findingAt
                        binding
                        DeclarationDefect.Ambiguous
                        $"explicit loading export '{selector}' is ambiguous: {bindings.Length} bindings have that qualified name")
            )

/// A declared space by name.
let spaceNamed (name: string) (platform: DeclaredPlatform) : DeclaredSpace option =
    platform.Spaces |> List.tryFind (fun s -> s.Name = name)

/// The explicitly designated immutable image space, never inferred by spelling.
let immutableProgramSpace (platform: DeclaredPlatform) : DeclaredSpace option =
    platform.ProgramLifetime |> Option.map (fun roles -> roles.Immutable.Space)

/// The finite premises of immutable program residence: selected descriptor,
/// designation record, its name reference, and the resolved space declaration.
let immutableProgramAuthority (platform: DeclaredPlatform) : NodeId list =
    platform.ProgramLifetime
    |> Option.map (fun roles -> [platform.Node; roles.Node; roles.Immutable.Reference; roles.Immutable.Space.Node] |> List.distinct)
    |> Option.defaultValue []

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
    RecordType: NominalTypeIdentity option
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
/// Native entry signatures have no external symbol name. Parameter ordinals and
/// source result identity are read by the same owner as FunctionDescriptor.
type DeclaredEntrySignature = {
    Node: NodeId
    Parameters: (NodeId * DeclaredParameter option) list
    References: (NodeId * DeclaredParameter) list
    PointerReferences: (NodeId * DeclaredPointerReference) list
    RecordReferences: (NodeId * bool) list
    Body: NodeId option
    Return: DeclaredParameter option
}

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

/// A source-quoted behavioral hypothesis and its exact boundary declaration.
/// SourcePath preserves quotation/alias occurrence; Node is the actual record.
type DeclaredResultRange = {
    Node: NodeId
    DescriptorBinding: NodeId
    SourcePath: NodeId list
    Declaration: BoundaryDeclaration
    Hypothesis: ForeignResultHypothesis
    AbiDescriptor: NodeId
    Participants: NodeId list
}

/// A receiving quote selects a current native receiver and its original formal.
/// It supplies no callback arguments, invocation count, or code lifetime.
type DeclaredCallbackInvocation = {
    Node: NodeId
    DescriptorBinding: NodeId
    Quote: NodeId
    SourcePath: NodeId list
    Declaration: BoundaryDeclaration
    AbiDescriptor: NodeId
    Parameter: int
    Formal: NodeId
    ScopeBinding: NodeId
    Scope: NodeId
    SignatureNode: NodeId
    Contract: BAREWire.Descriptors.CallbackInvocationContract
    Participants: NodeId list
}

/// Exact source resource declaration only. This grants no acquisition,
/// nullable-word conversion, cleanup, alias retirement or execution authority.
type DeclaredCallbackAbsence = {
    Node: NodeId
    DescriptorBinding: NodeId
    Quote: NodeId
    SourcePath: NodeId list
    Invocation: DeclaredCallbackInvocation
    Contract: BAREWire.Descriptors.CallbackAbsenceContract
    Inputs: (CallbackAbsenceInputRole * NodeId list) list
}

type DeclaredResource = {
    Node: NodeId
    Quote: NodeId
    DescriptorBinding: NodeId
    SourcePath: NodeId list
    Acquisition: BoundaryDeclaration
    AcquisitionDescriptor: NodeId
    AcquisitionDescriptorBinding: NodeId
    Release: BoundaryDeclaration
    ReleaseDescriptor: NodeId
    ReleaseDescriptorBinding: NodeId
    ReleaseFormal: NodeId
    PointerBits: int
    AcquisitionType: TypeIdentity
    ResultType: TypeIdentity
    HandleType: TypeIdentity
    Contract: BAREWire.Descriptors.ResourceDescriptor
    Participants: NodeId list
}

/// Every boundary declaration in the graph, with every defect found reading them.
type DeclaredWritableBuffer = {
    Node: NodeId
    Quote: NodeId
    DescriptorBinding: NodeId
    SourcePath: NodeId list
    Declaration: BoundaryDeclaration
    AbiDescriptor: NodeId
    AbiDescriptorBinding: NodeId
    Parameter: int
    CountParameter: int
    BufferFormal: NodeId
    CountFormal: NodeId
    Contract: BAREWire.Descriptors.WritableBufferDescriptor
    Participants: NodeId list
}

type Descriptors = {
    Layouts: DeclaredLayout list
    Functions: DeclaredFunction list
    ResultRanges: DeclaredResultRange list
    CallbackInvocations: DeclaredCallbackInvocation list
    CallbackAbsences: DeclaredCallbackAbsence list
    Resources: DeclaredResource list
    WritableBuffers: DeclaredWritableBuffer list
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

type DeclaredSyscall = { Node: NodeId; Surface: NodeId; Number: bigint }

/// Capability is an endpoint in the selected description, never a runtime default.
let syscall (graph: SemanticGraph) (platform: DeclaredPlatform) name =
    let endpoints =
        recordOf graph platform.Node |> Option.toList |> List.collect (fun (_, fields) ->
            field "Surfaces" fields |> Option.bind (elementsOf graph) |> Option.defaultValue []
            |> List.collect (fun surface ->
                recordOf graph surface |> Option.toList |> List.collect (fun (owner, fields) ->
                    field "Endpoints" fields |> Option.bind (elementsOf graph) |> Option.defaultValue []
                    |> List.choose (fun endpoint ->
                        recordOf graph endpoint |> Option.bind (fun (node, fields) ->
                            if field "Name" fields |> Option.bind (stringOf graph) = Some name then Some(owner.Id, node, fields) else None)))))
    match endpoints with
    | [surface, node, fields] ->
        match field "Location" fields |> Option.bind (stringOf graph), field "Address" fields |> Option.bind (stringOf graph) with
        | Some location, Some address when location = BAREWire.Platform.EndpointKind.SyscallNumber ->
            match System.Numerics.BigInteger.TryParse address with
            | true, number when number >= 0I -> Some { Node = node.Id; Surface = surface; Number = number }
            | _ -> None
        | _ -> None
    | _ -> None

/// The two elements of a pair payload (`Integer (Signed, 32)`).
let private pairOf (graph: SemanticGraph) (id: NodeId) : (NodeId * NodeId) option =
    match valueOf graph id with
    | Some ({ Kind = SemanticKind.TupleExpr [ a; b ] } : SemanticNode) -> Some (a, b)
    | _ -> None

/// A `TypeRef` as declared: the bits and range of an integer or boolean reference, None for a
/// reference that carries no integer (`Float`, `Pointer`, `Void`, `Named`), a finding for a
/// case the vocabulary does not name, a payload the reader cannot read, or a width of no bits.
[<RequireQualifiedAccess>]
type DeclaredTypeRef =
    | Scalar of BoundaryScalar
    | Void
    | Float of int
    | Pointer of int
    | Named of string
    | Entry of string

let scalarRange = function
    | BoundaryScalar.Boolean -> 1, ValueRange.boolean
    | BoundaryScalar.Integer(bits, true) -> bits, ValueRange.twosComplement bits
    | BoundaryScalar.Integer(bits, false) -> bits, ValueRange.unsignedOf bits
    | BoundaryScalar.Entry _ -> invalidOp "An entry declaration has no scalar integer range."
    | BoundaryScalar.ResourceHandle _ -> invalidOp "An opaque resource handle has no scalar integer range."
    | BoundaryScalar.WritableBytes _ -> invalidOp "A writable byte buffer has no scalar integer range."

let private numericType = function
    | DeclaredTypeRef.Scalar scalar -> Some (scalarRange scalar)
    | _ -> None

/// The one typed TypeRef reader used by range and physical boundary settlement.
let readTypeRef (graph: SemanticGraph) (id: NodeId) : Result<DeclaredTypeRef, DeclarationFinding> =
    match caseOf graph id with
    | Some (node, "Integer", Some payload) ->
        match pairOf graph payload with
        | Some (signId, bitsId) ->
            match caseOf graph signId, int64Of graph bitsId with
            | Some (_, "Signed", None), Some bits when bits > 0L && bits <= int64 System.Int32.MaxValue -> Ok (DeclaredTypeRef.Scalar (BoundaryScalar.Integer(int bits, true)))
            | Some (_, "Unsigned", None), Some bits when bits > 0L && bits <= int64 System.Int32.MaxValue -> Ok (DeclaredTypeRef.Scalar (BoundaryScalar.Integer(int bits, false)))
            | Some (_, ("Signed" | "Unsigned"), None), Some bits -> Error (findingAt node DeclarationDefect.Invalid (sprintf "an Integer of %d bits; a width must be positive and representable by the declaration reader" bits))
            | _ -> Error (findingAt node DeclarationDefect.Malformed "an Integer's payload must be a Signedness case and an integer literal")
        | None -> Error (findingAt node DeclarationDefect.Malformed "an Integer's payload must be a pair (Signed | Unsigned, bits)")
    | Some (node, (("Float" | "Pointer") as case), Some payload) ->
        match int64Of graph payload with
        | Some bits when bits > 0L && bits <= int64 System.Int32.MaxValue -> Ok (if case = "Float" then DeclaredTypeRef.Float (int bits) else DeclaredTypeRef.Pointer (int bits))
        | Some bits -> Error (findingAt node DeclarationDefect.Invalid (sprintf "a %s of %d bits; a width is a positive number of bits" case bits))
        | None -> Error (findingAt node DeclarationDefect.Malformed (sprintf "a %s's bits must be an integer literal" case))
    | Some (_, "Bool", None) -> Ok (DeclaredTypeRef.Scalar BoundaryScalar.Boolean)
    | Some (_, "Void", None) -> Ok DeclaredTypeRef.Void
    | Some (_, "Named", Some payload) when (stringOf graph payload).IsSome -> Ok (DeclaredTypeRef.Named (stringOf graph payload |> Option.get))
    | Some (node, "Named", _) -> Error (findingAt node DeclarationDefect.Malformed "a Named TypeRef's payload must be a string literal naming the record")
    | Some (_, "Entry", Some payload) when (stringOf graph payload |> Option.exists (System.String.IsNullOrWhiteSpace >> not)) ->
        Ok (DeclaredTypeRef.Entry (stringOf graph payload |> Option.get))
    | Some (node, "Entry", _) -> Error (findingAt node DeclarationDefect.Malformed "an Entry TypeRef's payload must be a non-empty qualified callback invocation contract binding")
    | Some (node, other, _) -> Error (findingAt node DeclarationDefect.Invalid (sprintf "'%s' is not a TypeRef case the BAREWire vocabulary names" other))
    | None -> Error (findingOn graph id DeclarationDefect.Malformed "a Type must be a TypeRef case (Integer, Float, Pointer, Bool, Void, Named, Entry)")

/// One `ParameterInfo` as declared.
let private readParameter (graph: SemanticGraph) (id: NodeId) : Result<(string * DeclaredParameter option * bool * DeclaredPointerReference option * string option * bool), DeclarationFinding> =
    match recordOf graph id with
    | Some (node, fields) when typeName node = Some "ParameterInfo" ->
        match field "Name" fields |> Option.bind (stringOf graph), field "Type" fields with
        | Some name, Some typeId ->
            // PassBy is a closed vocabulary; a present value outside it is not "by value".
            let passBy =
                match field "PassBy" fields with
                | None -> Ok None
                | Some id ->
                    match caseOf graph id with
                    | Some (_, ("Value" | "Reference" | "ReadOnlyReference"), _) as passing -> Ok passing
                    | _ -> Error (findingOn graph id DeclarationDefect.Invalid (sprintf "the PassBy of parameter '%s' must be Value, Reference or ReadOnlyReference" name))
            match passBy with
            | Error finding -> Error finding
            | Ok passing ->
            readTypeRef graph typeId
            |> Result.map numericType
            |> Result.map (Option.map (fun (bits, range) -> { Node = node.Id; Name = name; Bits = bits; Range = range }))
            |> Result.map (fun declared ->
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
let private recordTypesNamed (graph: SemanticGraph) (name: string) : NominalTypeIdentity list =
    let types =
        RecordInstances.definitions graph
        |> Map.toList
        |> List.choose (fun (identity, node) ->
            match node.Kind with
            | SemanticKind.TypeDef (_, TypeDefKind.RecordDef _, _) -> Some identity
            | _ -> None)
    let exact = types |> List.filter (fun identity -> NominalTypeIdentity.display identity = name || identity.Name = name)
    if not exact.IsEmpty then exact
    else types |> List.filter (fun identity -> shortName identity.Name = name)

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
                let recordFields =
                    RecordInstances.tryDefinition one graph
                    |> Option.bind (fun definition -> RecordInstances.tryFields definition.Type graph)
                    |> Option.defaultValue []
                let absent =
                    layoutFields
                    |> List.filter (fun f ->
                        match recordFields |> List.tryFind (fun (n, _) -> n = f.Name) with
                        | Some (_, ty) -> not (Types.isIntegerType ty || Types.tryGetNTUKind ty = Some NTUKind.NTUbool)
                        | None -> true)
                    |> List.map (fun f -> findingAt (SemanticGraph.tryGetNode f.Node graph |> Option.defaultValue node) DeclarationDefect.Invalid (sprintf "the field '%s' is declared '%s' but the record '%s' carries no integer or boolean field of that name" f.Name f.Repr (NominalTypeIdentity.display one)))
                Some one, absent
            | many -> None, [ findingAt node DeclarationDefect.Ambiguous (sprintf "the descriptor '%s' names more than one record type of the program (%s); qualify the name" name (many |> List.map NominalTypeIdentity.display |> String.concat ", ")) ]
        let physical, size, alignment, physicalFindings =
            match field "Layout" fields |> Option.bind (recordOf graph) with
            | Some (_, body) ->
                // Name/Repr defects and non-record elements are readField's findings; a
                // field that reads there must also carry its measured Offset and Count.
                let rows =
                    field "Fields" body |> Option.bind (elementsOf graph) |> Option.defaultValue []
                    |> List.choose (fun id ->
                        match recordOf graph id with
                        | Some (f, ff) ->
                            match field "Name" ff |> Option.bind (stringOf graph), field "Repr" ff |> Option.bind (stringOf graph), field "Offset" ff |> Option.bind (int64Of graph), field "Count" ff |> Option.bind (int64Of graph) with
                            | Some name, Some repr, Some offset, Some count -> Some (Ok { Node = f.Id; Name = name; Repr = repr; Offset = int offset; Count = int count })
                            | Some name, Some _, _, _ ->
                                Some (Error (findingAt f DeclarationDefect.Malformed (sprintf "the field '%s' must declare its Offset and Count as integer literals" name)))
                            | _ -> None
                        | None -> None)
                // Size and Alignment the body carries must read; an absent one is undeclared.
                let measure name =
                    match field name body with
                    | None -> None, []
                    | Some id ->
                        match int64Of graph id with
                        | Some value -> Some (int value), []
                        | None -> None, [ findingOn graph id DeclarationDefect.Malformed (sprintf "a descriptor Layout's %s must be an integer literal" name) ]
                let size, sizeFindings = measure "Size"
                let alignment, alignmentFindings = measure "Alignment"
                (rows |> List.choose (function Ok row -> Some row | Error _ -> None)), size, alignment,
                (rows |> List.choose (function Error finding -> Some finding | Ok _ -> None)) @ sizeFindings @ alignmentFindings
            | None -> [], None, None, []
        Some { Node = node.Id; Name = name; RecordType = recordType; Fields = layoutFields; PhysicalFields = physical; Size = size; Alignment = alignment }, layoutFindings @ typeFindings @ physicalFindings

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
let private externBesideWithSuffix (suffix: string) (graph: SemanticGraph) (descriptor: SemanticNode) (bindingName: string) : SemanticNode option =
    if not (bindingName.EndsWith suffix) then None
    else
        let name = bindingName.Substring(0, bindingName.Length - suffix.Length)
        graph.Nodes
        |> Map.toList
        |> List.tryPick (fun (_, node) ->
            match node.Kind with
            | SemanticKind.Binding (n, _, _, _) when n = name && node.Parent = descriptor.Parent && Map.containsKey "FidelityExtern.Library" node.Metadata -> Some node
            | _ -> None)

let private externBeside graph descriptor bindingName =
    externBesideWithSuffix "Descriptor" graph descriptor bindingName

/// One parameter/result reader for named imports and symbol-free native entries.
let private readSignatureForBinding
    (graph: SemanticGraph)
    (binding: SemanticNode)
    (cname: string)
    (node: SemanticNode)
    (fields: (string * NodeId) list)
    : DeclaredEntrySignature option * DeclarationFinding list =
    match field "ReturnType" fields with
    | Some returnId ->
        let parameters, parameterFindings =
            readList graph fields "Parameters" (readParameter graph)

        let returned, returnFindings =
            match readTypeRef graph returnId |> Result.map numericType with
            | Ok(Some(bits, range)) ->
                Some
                    {
                        Node = returnId
                        Name = "ReturnType"
                        Bits = bits
                        Range = range
                    },
                []
            | Ok None -> None, []
            | Error f -> None, [ f ]

        let pairs, references, pointerReferences, recordReferences, body, externFindings =
            match lambdaOfBinding graph binding.Id with
            | None -> [], [], [], [], None, []
            | Some(lambdaParameters, body) ->
                let lambdaParameters =
                    match parameters, lambdaParameters with
                    | [], [ (_, ty, _) ] when Types.tryGetNTUKind ty = Some NTUKind.NTUunit -> []
                    | _ -> lambdaParameters

                if List.length lambdaParameters <> List.length parameters then
                    [],
                    [],
                    [],
                    [],
                    None,
                    [
                        findingAt
                            node
                            DeclarationDefect.Invalid
                            (sprintf
                                "the descriptor of '%s' declares %d parameters; the binding takes %d"
                                cname
                                parameters.Length
                                lambdaParameters.Length)
                    ]
                else
                    let rows =
                        List.zip lambdaParameters parameters
                        |> List.map (fun ((_, ty, paramId), (declaredName, declared, byReference, pointer, named, readOnly)) ->
                            let ranged ty =
                                Types.isIntegerType ty || Types.tryGetNTUKind ty = Some NTUKind.NTUbool

                            let element =
                                match ty with
                                | NativeType.TApp(tc, [ elem ]) when tc.Name = "array" || tc.Name = "Array" -> Some elem
                                | _ -> None

                            let nullableHandle ty =
                                match ty with
                                | NativeType.TApp(tc, [ inner ]) when tc.Name = "option" -> Types.tryGetNTUKind inner = Some NTUKind.NTUptr
                                | _ -> false

                            let invalid message =
                                (paramId, None), None, None, None, Some(findingAt node DeclarationDefect.Invalid message)

                            match declared, byReference, pointer, named, element with
                            | Some d, true, _, _, Some elem when ranged elem -> (paramId, None), Some(paramId, d), None, None, None
                            | Some _, true, _, _, _ ->
                                invalid (sprintf "the reference parameter '%s' of '%s' requires a bounded scalar array" declaredName cname)
                            | _, true, Some d, _, Some elem when nullableHandle elem -> (paramId, None), None, Some(paramId, d), None, None
                            | _, true, Some _, _, _ ->
                                invalid (
                                    sprintf
                                        "the pointer reference '%s' of '%s' requires a bounded option<CHandle<_>> array"
                                        declaredName
                                        cname
                                )
                            | _, true, _, Some name, _ ->
                                let declaredTypes = recordTypesNamed graph name

                                let actual =
                                    match ty with
                                    | NativeType.TApp(tc, _) -> Some(NominalTypeIdentity.ofConstructor tc)
                                    | _ -> None

                                if actual |> Option.exists (fun actual -> declaredTypes = [ actual ]) then
                                    (paramId, None), None, None, Some(paramId, readOnly), None
                                else
                                    invalid (
                                        sprintf "the reference '%s' of '%s' requires the declared record '%s'" declaredName cname name
                                    )
                            | Some d, false, _, _, _ when not (ranged ty) ->
                                invalid (
                                    sprintf
                                        "the parameter '%s' of '%s' is declared an integer of %d bits, but the binding's parameter is not an integer"
                                        declaredName
                                        cname
                                        d.Bits
                                )
                            | _ -> (paramId, (if ranged ty then declared else None)), None, None, None, None)

                    rows |> List.map (fun (p, _, _, _, _) -> p),
                    rows |> List.choose (fun (_, r, _, _, _) -> r),
                    rows |> List.choose (fun (_, _, p, _, _) -> p),
                    rows |> List.choose (fun (_, _, _, r, _) -> r),
                    Some body,
                    rows |> List.choose (fun (_, _, _, _, f) -> f)

        Some
            {
                Node = node.Id
                Parameters = pairs
                References = references
                PointerReferences = pointerReferences
                RecordReferences = recordReferences
                Body = body
                Return = returned
            },
        parameterFindings @ returnFindings @ externFindings
    | _ ->
        None,
        [
            findingAt node DeclarationDefect.Malformed "a native signature must declare a ReturnType"
        ]

/// A binding descriptor retains its declared external symbol separately from ABI.
let readFunctionForBinding graph binding (_bindingName: string) node fields : DeclaredFunction option * DeclarationFinding list =
    match field "CName" fields |> Option.bind (stringOf graph), field "ReturnType" fields with
    | Some cname, Some _ ->
        let signature, findings = readSignatureForBinding graph binding cname node fields

        signature
        |> Option.map (fun signature ->
            {
                Node = signature.Node
                CName = cname
                Parameters = signature.Parameters
                References = signature.References
                PointerReferences = signature.PointerReferences
                RecordReferences = signature.RecordReferences
                Body = signature.Body
                Return = signature.Return
            }),
        findings
    | _ ->
        None,
        [
            findingAt
                node
                DeclarationDefect.Malformed
                "a FunctionDescriptor's CName must be a string literal and it must declare a ReturnType"
        ]

/// A receiving entry's ABI has no CName; its declaration remains the source binding.
let readEntrySignatureForBinding graph binding node fields : DeclaredEntrySignature option * DeclarationFinding list =
    if typeName node = Some "EntrySignature" then
        let name = qualifiedExportName graph binding |> Option.defaultValue "native entry"
        readSignatureForBinding graph binding name node fields
    else
        None,
        [
            findingAt node DeclarationDefect.Malformed "a callback invocation Signature must be an EntrySignature record"
        ]

/// Resolve the generated extern beside its descriptor, then use the same reader as callbacks.
let private readFunction graph binding bindingName node fields =
    let target = externBeside graph binding bindingName |> Option.defaultValue binding
    target.Id, readFunctionForBinding graph target bindingName node fields

/// Every boundary declaration in the graph: a module-level binding whose value, through an
/// annotation or a quotation, is a `StructDescriptor`, a `PeripheralDescriptor` or a
/// `FunctionDescriptor` record. Read whether or not reachable (a declaration never is). A
/// descriptor built by a function is a value, not a declaration, and is not read.
let readDescriptors (graph: SemanticGraph) : Descriptors =
    let isModuleLevel (node: SemanticNode) =
        match node.Parent |> Option.bind (fun p -> SemanticGraph.tryGetNode p graph) with
        | Some { Kind = SemanticKind.ModuleDef _ } -> true
        | _ -> false
    // Keep the existing single source census. Resolve result contracts from the
    // retained declaration/ABI inventories, never by C symbol or beside-name.
    let absenceDeclarations = ResizeArray<SemanticNode * SemanticNode * (string * NodeId) list * NodeId list>()
    let exactAbsence (node: SemanticNode) =
        match Clef.Compiler.NativeTypedTree.UnionFind.applySubst node.Type with
        | NativeType.TApp(constructor, []) ->
            let identity = NominalTypeIdentity.ofConstructor constructor
            identity.Module = ["BAREWire";"Descriptors"] &&
            identity.Name = "Descriptors.CallbackAbsenceContract" &&
            (RecordInstances.definitions graph |> Map.tryFind identity |> Option.exists(fun definition ->
                match definition.Kind with SemanticKind.TypeDef(_, TypeDefKind.RecordDef _, _) -> true | _ -> false))
        | _ -> false
    let layouts, functionDeclarations, resultDeclarations, invocationDeclarations, resourceDeclarations, writableDeclarations, externs, findings =
        graph.Nodes
        |> Map.toList
        |> List.fold (fun (layouts, functions, ranges, invocations, resources, writable, externs, findings) (_, node) ->
            let externs =
                if node.Metadata.ContainsKey "FidelityExtern.Library" || node.Metadata.ContainsKey "FidelityExtern.Symbol" then
                    qualifiedExportName graph node |> Option.map (fun name -> (name, node.Id) :: externs) |> Option.defaultValue externs
                else externs
            match node.Kind with
            | SemanticKind.Binding (name, _, _, _) when isModuleLevel node && not (List.isEmpty node.Children) ->
                match valuePath graph (List.last node.Children) with
                | Some (({ Kind = SemanticKind.RecordExpr(fields, _) } as record), path) ->
                    if exactAbsence record then absenceDeclarations.Add(node, record, fields, path)
                    match typeName record with
                    | Some "StructDescriptor" | Some "PeripheralDescriptor" ->
                        let layout, more = readLayout graph record fields
                        (Option.toList layout @ layouts, functions, ranges, invocations, resources, writable, externs, findings @ more)
                    | Some "FunctionDescriptor" ->
                        let target, (f, more) = readFunction graph node name record fields
                        (layouts, (f |> Option.map (fun f -> target, f, node.Id) |> Option.toList) @ functions, ranges, invocations, resources, writable, externs, findings @ more)
                    | Some "ResultRangeDescriptor" ->
                        (layouts, functions, (node, record, fields, path) :: ranges, invocations, resources, writable, externs, findings)
                    | Some "ResourceDescriptor" ->
                        (layouts, functions, ranges, invocations, (node, record, fields, path) :: resources, writable, externs, findings)
                    | Some "WritableBufferDescriptor" ->
                        (layouts, functions, ranges, invocations, resources, (node, record, fields, path) :: writable, externs, findings)
                    | Some "CallbackInvocationContract" ->
                        (layouts, functions, ranges, (node, record, fields, path) :: invocations, resources, writable, externs, findings)
                    | _ -> (layouts, functions, ranges, invocations, resources, writable, externs, findings)
                | Some (value, _) when exactAbsence value ->
                    (layouts, functions, ranges, invocations, resources, writable, externs, findings @ [findingAt value DeclarationDefect.Malformed "A CallbackAbsenceContract must retain its exact immutable quoted record."])
                | Some (value, _) when typeName value = Some "ResultRangeDescriptor" || typeName value = Some "WritableBufferDescriptor" ->
                    let name=typeName value |> Option.defaultValue "ResultRangeDescriptor"
                    (layouts, functions, ranges, invocations, resources, writable, externs, findings @ [findingAt value DeclarationDefect.Malformed ($"a {name} must retain its quoted record declaration")])
                | _ ->
                    let declared =
                        match node.Type with
                        | NativeType.TApp(_, [inner]) -> List.contains (typeName { node with Type = inner }) [Some "ResultRangeDescriptor";Some "WritableBufferDescriptor"]
                        | _ -> List.contains (typeName node) [Some "ResultRangeDescriptor";Some "WritableBufferDescriptor"]
                    let name=match node.Type with NativeType.TApp(_, [inner]) -> typeName {node with Type=inner} | _ -> typeName node
                    let descriptorName=name |> Option.defaultValue "ResultRangeDescriptor"
                    let more = if declared then [findingAt node DeclarationDefect.Malformed ($"a {descriptorName} must retain its quoted record declaration")] else []
                    (layouts, functions, ranges, invocations, resources, writable, externs, findings @ more)
            | _ -> (layouts, functions, ranges, invocations, resources, writable, externs, findings)) ([], [], [], [], [], [], [], [])
    // Preserve the exact descriptor binding already visited by this census.
    // This private incidence is not reconstructed from symbols or source names.
    let functions = functionDeclarations |> List.map (fun (target, abi, _) -> target, abi)
    let descriptorBinding target descriptor =
        functionDeclarations
        |> List.choose (fun (current, abi, binding) -> if current = target && abi.Node = descriptor then Some binding else None)
        |> function [binding] -> Some binding | _ -> None
    let readResult (binding: SemanticNode, node: SemanticNode, fields, path) : Result<DeclaredResultRange, DeclarationFinding> =
        let malformed reason = Error (findingAt node DeclarationDefect.Malformed ("a ResultRangeDescriptor " + reason))
        let invalid reason = Error (findingAt node DeclarationDefect.Invalid ("a ResultRangeDescriptor " + reason))
        let immutablePath ids = ids |> List.forall (fun id ->
            match graph.Nodes.TryFind id |> Option.map _.Kind with
            | Some (SemanticKind.Binding(_, true, _, _)) -> false
            | _ -> true)
        let quotes = path |> List.choose (fun id ->
            match graph.Nodes.TryFind id |> Option.map _.Kind with Some (SemanticKind.Quote _) -> Some id | _ -> None)
        let name = field "Binding" fields |> Option.bind (stringOf graph)
        let role = field "Role" fields |> Option.bind (caseOf graph)
        match quotes, name, role, field "Hypothesis" fields |> Option.bind (recordOf graph) with
        | [quote], Some name, Some (_, "ReturnValue", None), Some (hypothesisNode, hypothesisFields)
            when immutablePath (binding.Id :: path) && typeName hypothesisNode = Some "ExternalExecutionHypothesis" ->
            let text key = field key hypothesisFields |> Option.bind (stringOf graph) |> Option.filter (System.String.IsNullOrWhiteSpace >> not)
            match text "Identity", text "Version", text "Source" with
            | Some identity, Some version, Some source ->
                match externs |> List.filter (fun (candidate, _) -> candidate = name) with
                | [_, target] ->
                    let rows = graph.Edges |> List.choose (fun edge ->
                        match edge.Class, edge.Role with
                        | EdgeClass.Boundary, EdgeRole.BoundaryDeclaration declaration when edge.Target = target && declaration.Binding = target -> Some(edge, declaration)
                        | _ -> None)
                    match rows, functions |> List.filter (fun (binding, _) -> binding = target) with
                    | [edge, declaration], [_, abi] when edge.Sources = declaration.Path @ declaration.Formals @ [declaration.Body] &&
                                                       (edge.Sources |> List.forall graph.Nodes.ContainsKey) ->
                        match graph.Nodes.TryFind declaration.Implementation |> Option.map _.Kind, recordOf graph abi.Node with
                        | Some (SemanticKind.Lambda(formals, body, captures, _, _)), Some (_, abiFields)
                            when captures.IsEmpty && body = declaration.Body && (formals |> List.map (fun (_, _, id) -> id)) = declaration.Formals ->
                            let parameters = field "Parameters" abiFields |> Option.bind (elementsOf graph)
                            let returned = field "ReturnType" abiFields |> Option.map (readTypeRef graph)
                            match parameters, returned with
                            | Some parameters, Some (Ok (DeclaredTypeRef.Scalar (BoundaryScalar.Integer _))) when abi.Body = Some body && abi.Parameters.Length = parameters.Length &&
                                   (graph.Nodes.TryFind body |> Option.exists (fun body -> Types.isIntegerType body.Type)) ->
                                let endpoint key =
                                    match field key fields |> Option.bind (caseOf graph) with
                                    | Some (_, "Constant", Some payload) ->
                                        match int64Of graph payload with
                                        | Some value when value >= int64 System.Int32.MinValue && value <= int64 System.Int32.MaxValue -> Ok (ForeignResultBound.Constant (bigint value))
                                        | _ -> malformed (key + " Constant requires a literal int value")
                                    | Some (_, "Argument", Some payload) ->
                                        match int64Of graph payload with
                                        | Some ordinal when ordinal >= 0L && ordinal < int64 parameters.Length ->
                                            let index = int ordinal
                                            match recordOf graph parameters[index] with
                                            | Some (_, parameterFields) ->
                                                match field "PassBy" parameterFields |> Option.bind (caseOf graph), field "Type" parameterFields |> Option.map (readTypeRef graph), List.tryItem index abi.Parameters with
                                                | Some (_, "Value", None), Some (Ok (DeclaredTypeRef.Scalar (BoundaryScalar.Integer _))), Some (_, Some _) when List.tryItem index formals |> Option.exists (fun (_, ty, _) -> Types.isIntegerType ty) -> Ok (ForeignResultBound.Argument index)
                                                | _ -> invalid (sprintf "%s Argument %d requires a native scalar integer Value parameter" key index)
                                            | _ -> malformed (key + " Argument requires a ParameterInfo record")
                                        | _ -> invalid (key + " Argument is outside the exact native arity")
                                    | _ -> malformed (key + " must be Constant int or Argument int")
                                match endpoint "Lower", endpoint "Upper" with
                                | Ok lower, Ok upper ->
                                    let participantFields = (fields @ hypothesisFields) |> List.map snd
                                    let endpoints = ["Lower"; "Upper"] |> List.collect (fun key ->
                                        field key fields |> Option.bind (caseOf graph) |> Option.map (fun (_, _, payload) -> Option.toList payload) |> Option.defaultValue [])
                                    let paths = participantFields @ endpoints |> List.collect (fun id -> valuePath graph id |> Option.map snd |> Option.defaultValue [id])
                                    let abiParameterFields = parameters |> List.collect (fun id -> recordOf graph id |> Option.map (snd >> List.map snd) |> Option.defaultValue [id])
                                    let abiTypes = (field "ReturnType" abiFields |> Option.toList) @ (parameters |> List.choose (fun id -> recordOf graph id |> Option.bind (snd >> field "Type")))
                                    let abiPayloads = abiTypes |> List.collect (fun id ->
                                        caseOf graph id |> Option.bind (fun (_, _, payload) -> payload) |> Option.map (fun payload ->
                                            payload :: (pairOf graph payload |> Option.map (fun (sign, bits) -> [sign; bits]) |> Option.defaultValue [])) |> Option.defaultValue [])
                                    let abiPaths = (abiFields |> List.map snd) @ abiParameterFields @ abiTypes @ abiPayloads |> List.collect (fun id -> valuePath graph id |> Option.map snd |> Option.defaultValue [id])
                                    if not (immutablePath (paths @ abiPaths)) then invalid "requires immutable literal hypothesis inputs" else
                                    match lower, upper with
                                    | ForeignResultBound.Constant lo, ForeignResultBound.Constant hi when lo > hi -> invalid "constant bounds are contradictory"
                                    | _ -> Ok {
                                        Node = node.Id; DescriptorBinding = binding.Id; SourcePath = path; Declaration = declaration
                                        Hypothesis = { Quote = quote; Declaration = target; Identity = identity; Version = version; Source = source; Lower = lower; Upper = upper }
                                        AbiDescriptor = abi.Node
                                        Participants = binding.Id :: path @ [hypothesisNode.Id] @ paths @ edge.Sources @ [abi.Node] @ parameters @ abiPaths }
                                | Error finding, _ | _, Error finding -> Error finding
                            | _ -> invalid "requires an exact-arity scalar integer native return ABI descriptor"
                        | _ -> invalid "requires its existing capture-free boundary declaration identity row"
                    | _ -> invalid "requires exactly one boundary declaration row and paired native ABI descriptor"
                | [] -> invalid (sprintf "Binding '%s' names no fully qualified extern declaration" name)
                | _ -> invalid (sprintf "Binding '%s' is ambiguous" name)
            | _ -> malformed "requires nonempty literal hypothesis Identity, Version and Source"
        | _ -> malformed "requires one immutable quotation, literal Binding, ReturnValue role and ExternalExecutionHypothesis record"
    let readInvocation (binding: SemanticNode, node: SemanticNode, fields, path) : Result<DeclaredCallbackInvocation, DeclarationFinding> =
        let invalid message =
            Error(findingAt node DeclarationDefect.Invalid ("A CallbackInvocationContract " + message))

        let text key fields =
            field key fields
            |> Option.bind (stringOf graph)
            |> Option.filter (System.String.IsNullOrWhiteSpace >> not)

        let quoted path =
            path
            |> List.choose (fun id ->
                match graph.Nodes.TryFind id |> Option.map _.Kind with
                | Some(SemanticKind.Quote _) -> Some id
                | _ -> None)

        let immutable ids =
            ids
            |> List.forall (fun id ->
                match graph.Nodes.TryFind id |> Option.map _.Kind with
                | Some(SemanticKind.Binding(_, true, _, _)) -> false
                | _ -> true)

        let integer =
            function
                | DeclaredTypeRef.Scalar(BoundaryScalar.Integer(bits, signed)) ->
                    Ok(
                        BAREWire.Descriptors.TypeRef.Integer(
                            (if signed then
                                 BAREWire.Descriptors.Signedness.Signed
                             else
                                 BAREWire.Descriptors.Signedness.Unsigned),
                            bits
                        )
                    )
                | _ -> invalid "requires scalar integer entry parameters and result in this closed C profile."

        let signature (signature: SemanticNode) signatureFields =
            match
                field "CallingConvention" signatureFields |> Option.bind (caseOf graph),
                field "Parameters" signatureFields |> Option.bind (elementsOf graph),
                field "ReturnType" signatureFields
            with
            | Some(_, "CDecl", None), Some parameters, Some returned when typeName signature = Some "EntrySignature" ->
                let declared =
                    parameters
                    |> List.map (fun id ->
                        match recordOf graph id with
                        | Some(parameter, parameterFields) when typeName parameter = Some "ParameterInfo" ->
                            match
                                text "Name" parameterFields,
                                field "PassBy" parameterFields |> Option.bind (caseOf graph),
                                field "Type" parameterFields
                            with
                            | Some name, Some(_, "Value", None), Some typeId ->
                                readTypeRef graph typeId
                                |> Result.bind integer
                                |> Result.map (fun ty ->
                                    {
                                        Name = name
                                        Type = ty
                                        PassBy = BAREWire.Descriptors.PassBy.Value
                                    }
                                    : BAREWire.Descriptors.ParameterInfo)
                            | _ -> invalid "requires entry ParameterInfo Name, integer Type and explicit PassBy.Value."
                        | _ -> invalid "requires entry ParameterInfo records.")

                let parameters =
                    List.foldBack
                        (fun item result -> Result.bind (fun value -> Result.map (fun tail -> value :: tail) result) item)
                        declared
                        (Ok [])

                parameters
                |> Result.bind (fun parameters ->
                    readTypeRef graph returned
                    |> Result.bind (function
                        | DeclaredTypeRef.Void -> Ok BAREWire.Descriptors.TypeRef.Void
                        | result -> integer result)
                    |> Result.map (fun returned ->
                        {
                            Parameters = Array.ofList parameters
                            ReturnType = returned
                            CallingConvention = BAREWire.Descriptors.CallConv.CDecl
                        }
                        : BAREWire.Descriptors.EntrySignature))
            | _ -> invalid "requires a quoted EntrySignature with complete CDecl scalar parameters and result."

        match
            quoted path,
            text "Binding" fields,
            field "Parameter" fields |> Option.bind (int64Of graph),
            text "Scope" fields,
            field "Signature" fields |> Option.bind (recordOf graph),
            field "Hypothesis" fields |> Option.bind (recordOf graph)
        with
        | [ quote ], Some name, Some ordinal, Some scopeName, Some(signatureNode, signatureFields), Some(hypothesisNode, hypothesisFields) when
            immutable (binding.Id :: path)
            && typeName hypothesisNode = Some "ExternalExecutionHypothesis"
            ->
            match text "Identity" hypothesisFields, text "Version" hypothesisFields, text "Source" hypothesisFields with
            | Some identity, Some version, Some source ->
                match externs |> List.filter (fun (candidate, _) -> candidate = name) with
                | [ _, receiver ] ->
                    let rows =
                        graph.Edges
                        |> List.choose (fun edge ->
                            match edge.Class, edge.Role with
                            | EdgeClass.Boundary, EdgeRole.BoundaryDeclaration declaration when
                                edge.Target = receiver && declaration.Binding = receiver
                                ->
                                Some(edge, declaration)
                            | _ -> None)

                    match rows, functions |> List.filter (fun (target, _) -> target = receiver) with
                    | [ edge, declaration ], [ _, abi ] when
                        edge.Sources = declaration.Path @ declaration.Formals @ [ declaration.Body ]
                        && (edge.Sources |> List.forall graph.Nodes.ContainsKey)
                        && ordinal >= 0L
                        && ordinal < int64 declaration.Formals.Length
                        ->
                        let ordinal = int ordinal
                        let formal = declaration.Formals[ordinal]
                        let ownName = qualifiedExportName graph binding

                        let declaredEntry =
                            recordOf graph abi.Node
                            |> Option.bind (fun (_, fields) -> field "Parameters" fields |> Option.bind (elementsOf graph))
                            |> Option.bind (List.tryItem ordinal)
                            |> Option.bind (recordOf graph)
                            |> Option.bind (fun (_, fields) -> field "Type" fields)
                            |> Option.map (readTypeRef graph)

                        match declaredEntry, graph.Nodes.TryFind formal with
                        | Some(Ok(DeclaredTypeRef.Entry selected)), Some formalNode when
                            Some selected = ownName
                            && (Types.tryGetNTUKind formalNode.Type = Some NTUKind.NTUfnptr ||
                                (optionalEntrySignature formalNode.Type |> Option.isSome))
                            ->
                            let scopes =
                                graph.Nodes.Values
                                |> Seq.filter (fun candidate -> qualifiedExportName graph candidate = Some scopeName)
                                |> Seq.toList

                            match scopes with
                            | [ scopeBinding ] ->
                                match List.tryLast scopeBinding.Children |> Option.bind (valuePath graph) with
                                | Some(scopeNode, _) when typeName scopeNode = Some "ProcessExitCallbackDescriptor" && (optionalEntrySignature formalNode.Type |> Option.isSome) ->
                                    invalid "Optional native entries require a during-call activation; process-exit optional callbacks are not admitted."
                                | Some(scopeNode, scopePath) when
                                    (typeName scopeNode = Some "ScopedCallbackDescriptor" || typeName scopeNode = Some "ProcessExitCallbackDescriptor")
                                    && immutable (scopeBinding.Id :: scopePath)
                                    ->
                                    match quoted scopePath with
                                    | [ scopeQuote ] ->
                                        signature signatureNode signatureFields
                                        |> Result.bind (fun signature ->
                                            let contract: BAREWire.Descriptors.CallbackInvocationContract =
                                                {
                                                    Binding = name
                                                    Parameter = ordinal
                                                    Signature = signature
                                                    Hypothesis =
                                                        {
                                                            Identity = identity
                                                            Version = version
                                                            Source = source
                                                        }
                                                    Scope = scopeName
                                                }

                                            let inputs = (fields @ hypothesisFields @ signatureFields) |> List.map snd

                                            let paths =
                                                inputs
                                                |> List.collect (fun id ->
                                                    valuePath graph id |> Option.map snd |> Option.defaultValue [ id ])

                                            if not (immutable paths) then
                                                invalid "requires immutable literal signature and hypothesis inputs."
                                            else
                                                Ok
                                                    {
                                                        Node = node.Id
                                                        DescriptorBinding = binding.Id
                                                        Quote = quote
                                                        SourcePath = path
                                                        Declaration = declaration
                                                        AbiDescriptor = abi.Node
                                                        Parameter = ordinal
                                                        Formal = formal
                                                        ScopeBinding = scopeBinding.Id
                                                        Scope = scopeQuote
                                                        SignatureNode = signatureNode.Id
                                                        Contract = contract
                                                        Participants =
                                                                binding.Id :: path
                                                                @ edge.Sources
                                                                @ [
                                                                    abi.Node
                                                                    formal
                                                                    scopeBinding.Id
                                                                    scopeNode.Id
                                                                    signatureNode.Id
                                                                    hypothesisNode.Id
                                                                ]
                                                                @ scopePath
                                                                @ paths
                                                    })
                                    | _ -> invalid "Scope requires one current immutable quoted ScopedCallbackDescriptor."
                                | _ -> invalid "Scope must select an immutable quoted ScopedCallbackDescriptor binding."
                            | _ -> invalid "Scope names a missing or ambiguous fully qualified scoped declaration."
                        | _ -> invalid "must be selected by TypeRef.Entry at the exact receiver's original nonnullable FnPtr formal."
                    | _ -> invalid "requires one current receiving declaration/ABI and an ordinal within its unchanged native arity."
                | _ -> invalid "Binding names a missing or ambiguous fully qualified extern declaration."
            | _ -> invalid "requires nonempty literal external hypothesis Identity, Version and Source."
        | _ -> invalid "requires one immutable quote, exact Binding/Parameter/Signature/Hypothesis and Scope."

    let readResource (binding: SemanticNode, node: SemanticNode, fields, path) : Result<DeclaredResource, DeclarationFinding> =
        let invalid reason = Error (findingAt node DeclarationDefect.Invalid ("A ResourceDescriptor " + reason))
        let immutable ids = ids |> List.forall (fun id ->
            match graph.Nodes.TryFind id |> Option.map _.Kind with
            | Some (SemanticKind.Binding(_, true, _, _)) -> false
            | _ -> true)
        let declaration target =
            let rows = graph.Edges |> List.choose (fun edge ->
                match edge.Class, edge.Role with
                | EdgeClass.Boundary, EdgeRole.BoundaryDeclaration value when value.Binding = target && edge.Target = target -> Some(edge,value)
                | _ -> None)
            match rows, functions |> List.filter (fun (id,_) -> id = target) with
            | [edge,value], [_,abi] when edge.Sources = value.Path @ value.Formals @ [value.Body] && abi.Body = Some value.Body -> Some(value,abi)
            | _ -> None
        let pointerType id = readTypeRef graph id |> function Ok (DeclaredTypeRef.Pointer bits) -> Some bits | _ -> None
        let rawPointerReturn (abi: DeclaredFunction) = recordOf graph abi.Node |> Option.bind (fun (_,fields) -> field "ReturnType" fields |> Option.bind pointerType)
        let cdecl (abi: DeclaredFunction) = recordOf graph abi.Node |> Option.exists (fun (_,fields) -> field "CallingConvention" fields |> Option.bind (caseOf graph) |> Option.exists (fun (_,name,payload) -> name="CDecl" && payload.IsNone))
        let quotes = path |> List.filter (fun id -> match graph.Nodes.TryFind id |> Option.map _.Kind with Some (SemanticKind.Quote _) -> true | _ -> false)
        let companion =
            match binding.Kind with
            | SemanticKind.Binding(name, false, _, _) -> externBesideWithSuffix "ResourceDescriptor" graph binding name
            | _ -> None
        match quotes, companion, field "Resource" fields |> Option.bind (caseOf graph), field "Hypothesis" fields |> Option.bind (recordOf graph) with
        | [quote], Some acquisition, Some (_, "OwnedNullableReturn", Some releaseId), Some (hypothesisNode,hypothesisFields)
            when immutable (binding.Id :: path) && typeName hypothesisNode = Some "ExternalExecutionHypothesis" ->
            let text key = field key hypothesisFields |> Option.bind (stringOf graph) |> Option.filter (System.String.IsNullOrWhiteSpace >> not)
            match recordOf graph releaseId, text "Identity", text "Version", text "Source", declaration acquisition.Id with
            | Some (releaseNode,releaseFields), Some identity, Some version, Some source, Some(acquired,acquireAbi)
                when typeName releaseNode = Some "ResourceRelease" ->
                let releaseName = field "Binding" releaseFields |> Option.bind (stringOf graph)
                let ordinal = field "Parameter" releaseFields |> Option.bind (int64Of graph)
                match releaseName, ordinal with
                | Some name, Some 0L ->
                    match externs |> List.filter (fun (candidate,_) -> candidate = name) with
                    | [_,releasedId] ->
                        match declaration releasedId, lambdaOfBinding graph acquisition.Id, lambdaOfBinding graph releasedId with
                        | Some(released,releaseAbi), Some(_,acquireBody), Some([_,handleTy,formal],releaseBody) ->
                            let returnType = graph.Nodes.TryFind acquireBody |> Option.map _.Type
                            let handle =
                                returnType |> Option.bind (fun ty ->
                                    match Clef.Compiler.NativeTypedTree.UnionFind.applySubst ty with
                                    | NativeType.TApp(tc,[inner]) when tc.Name = "option" ->
                                        match Clef.Compiler.NativeTypedTree.UnionFind.applySubst inner with
                                        | NativeType.TApp(_,[_]) when Types.tryGetNTUKind inner = Some NTUKind.NTUptr -> Some inner
                                        | _ -> None
                                    | _ -> None)
                            let releaseSignature = recordOf graph releaseAbi.Node |> Option.bind (fun (_,fields) ->
                                match field "ReturnType" fields |> Option.map (readTypeRef graph), field "Parameters" fields |> Option.bind (elementsOf graph) with
                                | Some (Ok DeclaredTypeRef.Void), Some [parameter] ->
                                    recordOf graph parameter |> Option.bind (fun (_,fields) ->
                                        match field "PassBy" fields |> Option.bind (caseOf graph), field "Type" fields |> Option.bind pointerType with
                                        | Some(_,"Value",None), Some bits -> Some bits
                                        | _ -> None)
                                | _ -> None)
                            match handle, returnType, rawPointerReturn acquireAbi, releaseSignature, descriptorBinding acquisition.Id acquireAbi.Node, descriptorBinding releasedId releaseAbi.Node with
                            | Some handle, Some resultTy, Some bits, Some releaseBits, Some acquisitionDescriptorBinding, Some releaseDescriptorBinding
                                when bits > 0 && bits = releaseBits && cdecl acquireAbi && cdecl releaseAbi && released.Formals = [formal] && released.Body = releaseBody && acquired.Body = acquireBody &&
                                     Clef.Compiler.NativeTypedTree.TypeIdentities.ofType handle = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType handleTy &&
                                     acquireAbi.References.IsEmpty && acquireAbi.PointerReferences.IsEmpty && acquireAbi.RecordReferences.IsEmpty &&
                                     releaseAbi.References.IsEmpty && releaseAbi.PointerReferences.IsEmpty && releaseAbi.RecordReferences.IsEmpty ->
                                let inputs = (fields @ releaseFields @ hypothesisFields) |> List.map snd
                                let paths = inputs |> List.collect (fun id -> valuePath graph id |> Option.map snd |> Option.defaultValue [id])
                                if not (immutable paths) then invalid "requires immutable resource and hypothesis inputs." else
                                let contract: BAREWire.Descriptors.ResourceDescriptor =
                                    { Resource = BAREWire.Descriptors.ResourceProtocol.OwnedNullableReturn { Binding = name; Parameter = 0 }
                                      Hypothesis = { Identity = identity; Version = version; Source = source } }
                                Ok { Node = node.Id; Quote = quote; DescriptorBinding = binding.Id; SourcePath = path
                                     Acquisition = acquired; AcquisitionDescriptor = acquireAbi.Node; AcquisitionDescriptorBinding = acquisitionDescriptorBinding
                                     Release = released; ReleaseDescriptor = releaseAbi.Node; ReleaseDescriptorBinding = releaseDescriptorBinding
                                     ReleaseFormal = formal; PointerBits = bits; AcquisitionType = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType acquisition.Type
                                     ResultType = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType resultTy; HandleType = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType handle
                                     Contract = contract; Participants = binding.Id :: path @ paths @ [releaseNode.Id;hypothesisNode.Id;acquireAbi.Node;releaseAbi.Node]
                                                                        @ acquired.Path @ acquired.Formals @ [acquired.Body] @ released.Path @ [formal;released.Body] }
                            | _ -> invalid "requires matching nullable CHandle return and unary nonnullable same-handle raw-Void release with identical declared pointer widths."
                        | _ -> invalid "requires exact acquisition/release declaration bodies and one release formal."
                    | _ -> invalid "Release.Binding must name one exact fully qualified external declaration."
                | _ -> invalid "OwnedNullableReturn requires release native Parameter zero."
            | _ -> invalid "requires one exact sibling acquisition, ResourceRelease and nonempty versioned hypothesis."
        | _ -> invalid "requires one immutable sibling quotation and OwnedNullableReturn declaration."

    let readWritable (binding: SemanticNode, node: SemanticNode, fields, path) : Result<DeclaredWritableBuffer, DeclarationFinding> =
        let invalid reason = Error (findingAt node DeclarationDefect.Invalid ("A WritableBufferDescriptor " + reason))
        let text name fields = field name fields |> Option.bind (stringOf graph) |> Option.filter (System.String.IsNullOrWhiteSpace >> not)
        let immutable ids = ids |> List.forall (fun id ->
            match graph.Nodes.TryFind id |> Option.map _.Kind with
            | Some (SemanticKind.Binding(_, true, _, _)) -> false
            | _ -> true)
        let quotes = path |> List.filter (fun id -> graph.Nodes.TryFind id |> Option.exists (fun value -> match value.Kind with SemanticKind.Quote _ -> true | _ -> false))
        match quotes, text "Binding" fields, field "Parameter" fields |> Option.bind (int64Of graph),
              field "CountParameter" fields |> Option.bind (int64Of graph), field "Hypothesis" fields |> Option.bind (recordOf graph) with
        | [quote], Some name, Some parameter, Some countParameter, Some(hypothesis, hypothesisFields)
            when immutable (binding.Id::path) && typeName hypothesis=Some "ExternalExecutionHypothesis" ->
            match text "Identity" hypothesisFields, text "Version" hypothesisFields, text "Source" hypothesisFields,
                  externs |> List.filter (fun (candidate,_) -> candidate=name) with
            | Some identity, Some version, Some source, [_,target] ->
                let declarations = graph.Edges |> List.choose (fun edge ->
                    match edge.Class,edge.Role with
                    | EdgeClass.Boundary,EdgeRole.BoundaryDeclaration declaration when edge.Target=target && declaration.Binding=target -> Some(edge,declaration)
                    | _ -> None)
                match declarations, functions |> List.filter (fun (id,_) -> id=target) with
                | [edge,declaration],[_,abi] when edge.Sources=declaration.Path@declaration.Formals@[declaration.Body] && abi.Body=Some declaration.Body ->
                    match descriptorBinding target abi.Node, recordOf graph abi.Node with
                    | Some abiBinding,Some(_,abiFields) when parameter>=0L && countParameter>=0L && parameter<>countParameter &&
                                                           parameter<int64 declaration.Formals.Length && countParameter<int64 declaration.Formals.Length &&
                                                           (abi.Parameters |> List.map fst) = declaration.Formals ->
                        let parameter,countParameter=int parameter,int countParameter
                        let bufferFormal,countFormal=declaration.Formals[parameter],declaration.Formals[countParameter]
                        let parameters=field "Parameters" abiFields |> Option.bind (elementsOf graph)
                        let parameterFields ordinal=parameters |> Option.bind(List.tryItem ordinal) |> Option.bind(recordOf graph) |> Option.map snd
                        let byteReference = parameterFields parameter |> Option.exists(fun fields ->
                            (field "Type" fields |> Option.map(readTypeRef graph))=Some(Ok(DeclaredTypeRef.Scalar(BoundaryScalar.Integer(8,false)))) &&
                            (field "PassBy" fields |> Option.bind(caseOf graph) |> Option.map(fun(_,name,payload)->name,payload))=Some("Reference",None))
                        let scalarCount=parameterFields countParameter |> Option.exists(fun fields ->
                            (field "PassBy" fields |> Option.bind(caseOf graph) |> Option.map(fun(_,name,payload)->name,payload))=Some("Value",None) &&
                            (field "Type" fields |> Option.map(readTypeRef graph) |> Option.exists(function Ok(DeclaredTypeRef.Scalar(BoundaryScalar.Integer _)) -> true | _ -> false)))
                        let arrayElement=graph.Nodes.TryFind bufferFormal |> Option.exists(fun formal ->
                            match formal.Type with NativeType.TApp(tc,[element]) when tc.Name="array" || tc.Name="Array" -> Types.isIntegerType element | _ -> false)
                        let reference=abi.References |> List.exists(fun(formal,element)->formal=bufferFormal && element.Bits=8 && element.Range=ValueRange.unsignedOf 8)
                        if graph.Nodes.TryFind target |> Option.bind(fun node ->
                            match node.Metadata.TryFind "FidelityExtern.Symbol" with Some(MetadataValue.String symbol)->Some symbol | _->None) <> Some abi.CName then
                            invalid "FunctionDescriptor.CName differs from the exact external declaration symbol."
                        elif not(byteReference && arrayElement && reference) then invalid "requires an explicit unsigned-8 Reference element contract and its exact integer-array formal."
                        elif not scalarCount then invalid "CountParameter requires its exact by-value integer formal."
                        else
                            let paths=(fields@hypothesisFields) |> List.collect(fun(_,id)->valuePath graph id |> Option.map snd |> Option.defaultValue [id])
                            if not(immutable paths) then invalid "requires immutable descriptor and hypothesis inputs." else
                            Ok {Node=node.Id;Quote=quote;DescriptorBinding=binding.Id;SourcePath=path;Declaration=declaration
                                AbiDescriptor=abi.Node;AbiDescriptorBinding=abiBinding;Parameter=parameter;CountParameter=countParameter
                                BufferFormal=bufferFormal;CountFormal=countFormal
                                Contract={Binding=name;Parameter=parameter;CountParameter=countParameter;Hypothesis={Identity=identity;Version=version;Source=source}}
                                Participants=binding.Id::path@paths@edge.Sources@[abi.Node;abiBinding;hypothesis.Id]}
                    | _ -> invalid "requires distinct in-range native buffer/count ordinals and the complete unchanged FunctionDescriptor/formal vector."
                | _ -> invalid "requires the exact current source extern declaration and FunctionDescriptor."
            | _ -> invalid "Binding must select one exact qualified extern with a nonempty versioned hypothesis."
        | _ -> invalid "requires one immutable quotation with exact Binding, Parameter, CountParameter and Hypothesis."

    let results = List.rev resultDeclarations |> List.map readResult
    let ranges = results |> List.choose (function Ok range -> Some range | _ -> None)
    let duplicateFindings = duplicates "result contract" (fun (range: DeclaredResultRange) -> string range.Declaration.Binding) _.Node graph ranges
    let invocationResults = List.rev invocationDeclarations |> List.map readInvocation
    let invocations = invocationResults |> List.choose (function Ok invocation -> Some invocation | _ -> None)
    let invocationDuplicates = duplicates "callback invocation contract" (fun (invocation:DeclaredCallbackInvocation) -> string invocation.Declaration.Binding + ":" + string invocation.Parameter) _.Node graph invocations
    let absenceResults =
        absenceDeclarations |> Seq.toList |> List.map (fun (binding,node,fields,path) ->
            let invalid reason = Error(findingAt node DeclarationDefect.Invalid ("A CallbackAbsenceContract " + reason))
            let quotes = path |> List.filter(fun id -> match graph.Nodes[id].Kind with SemanticKind.Quote _ -> true | _ -> false)
            let text fields name = field name fields |> Option.bind(stringOf graph) |> Option.filter(System.String.IsNullOrWhiteSpace >> not)
            match quotes, text fields "Binding", field "Parameter" fields |> Option.bind(int64Of graph), field "Hypothesis" fields |> Option.bind(recordOf graph) with
            | [quote], Some receiver, Some ordinal, Some(_,hypothesisFields) ->
                let matches = invocations |> List.filter(fun invocation -> invocation.Contract.Binding=receiver && int64 invocation.Parameter=ordinal)
                match matches, text hypothesisFields "Identity", text hypothesisFields "Version", text hypothesisFields "Source" with
                | [invocation], Some identity, Some version, Some source ->
                    let inputs = [CallbackAbsenceInputRole.Binding,field "Binding" fields; CallbackAbsenceInputRole.Parameter,field "Parameter" fields
                                  CallbackAbsenceInputRole.Hypothesis,field "Hypothesis" fields
                                  CallbackAbsenceInputRole.HypothesisIdentity,field "Identity" hypothesisFields
                                  CallbackAbsenceInputRole.HypothesisVersion,field "Version" hypothesisFields
                                  CallbackAbsenceInputRole.HypothesisSource,field "Source" hypothesisFields]
                                 |> List.map(fun(role,id)->role,id |> Option.bind(valuePath graph) |> Option.map snd |> Option.defaultValue [])
                    let immutable = binding.Id::path @ (inputs |> List.collect snd) |> List.forall(fun id ->
                        match graph.Nodes[id].Kind with SemanticKind.Binding(_,true,_,_)->false | _->true)
                    if not immutable || (inputs |> List.exists(snd >> List.isEmpty)) then invalid "requires complete immutable quoted content paths."
                    elif identity=invocation.Contract.Hypothesis.Identity then invalid "requires an absence hypothesis identity distinct from activation."
                    elif optionalEntrySignature graph.Nodes[invocation.Formal].Type |> Option.isNone then invalid "conflicts with the receiving nonnull entry formal or contract."
                    elif recordOf graph invocation.Scope |> Option.exists(fun(scope,_)->typeName scope=Some "ProcessExitCallbackDescriptor") then invalid "requires a during-call receiving invocation."
                    else Ok {Node=node.Id;DescriptorBinding=binding.Id;Quote=quote;SourcePath=path;Invocation=invocation
                             Contract={Binding=receiver;Parameter=int ordinal;Hypothesis={Identity=identity;Version=version;Source=source}};Inputs=inputs}
                | _ -> invalid "requires one exact current receiving invocation and an independent nonempty versioned hypothesis."
            | _ -> invalid "requires one immutable quote and exact Binding, Parameter and Hypothesis fields.")
    let absences = absenceResults |> List.choose(function Ok row->Some row | _->None)
    let absenceDuplicates = duplicates "callback absence contract" (fun (row:DeclaredCallbackAbsence)->string row.Invocation.Declaration.Binding+":"+string row.Contract.Parameter) _.Node graph absences
    let resourceResults = List.rev resourceDeclarations |> List.map readResource
    let resources = resourceResults |> List.choose (function Ok value -> Some value | _ -> None)
    let resourceDuplicates = duplicates "resource contract" (fun resource -> string resource.Acquisition.Binding) _.Node graph resources
    let writableResults = List.rev writableDeclarations |> List.map readWritable
    let writable = writableResults |> List.choose (function Ok value -> Some value | _ -> None)
    let writableDuplicates = duplicates "writable buffer contract" (fun (value:DeclaredWritableBuffer) -> string value.Declaration.Binding+":"+string value.Parameter) _.Node graph writable
    { Layouts = List.rev layouts; Functions = List.rev functions |> List.map snd; ResultRanges = ranges
      CallbackInvocations = invocations; CallbackAbsences = absences; Resources = resources; WritableBuffers = writable
      Findings = findings @ (results |> List.choose (function Error finding -> Some finding | _ -> None)) @ duplicateFindings
                 @ (invocationResults |> List.choose (function Error finding -> Some finding | _ -> None)) @ invocationDuplicates
                 @ (absenceResults |> List.choose(function Error finding->Some finding | _->None)) @ absenceDuplicates
                 @ (resourceResults |> List.choose (function Error finding -> Some finding | _ -> None)) @ resourceDuplicates
                 @ (writableResults |> List.choose (function Error finding -> Some finding | _ -> None)) @ writableDuplicates }

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

/// Exact call-bounded writable hypotheses at their original native ordinals.
/// This grants neither a byte format nor a count/bounds proof.
let writableReferenceArguments (graph:SemanticGraph) funcId (args:NodeId list) =
    let rec binding seen id =
        if Set.contains id seen then None else
        match graph.Nodes.TryFind id with
        | Some {Kind=SemanticKind.TypeAnnotation(inner,_);Children=[child]} when child=inner -> binding (Set.add id seen) inner
        | Some {Kind=SemanticKind.VarRef(_,Some declaration)} -> Some declaration
        | _ -> None
    let descriptors=readDescriptors graph
    match binding Set.empty funcId with
    | Some declaration when descriptors.Findings.IsEmpty ->
        descriptors.WritableBuffers |> List.choose(fun row ->
            if row.Declaration.Binding=declaration && row.Declaration.Formals.Length=args.Length then
                args |> List.tryItem row.Parameter |> Option.map(fun actual->actual,row)
            else None)
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
let cAbiOfGraph (graph: SemanticGraph) : Result<(string * int * int) list, string> =
    let integer descriptor fields name =
        match field name fields |> Option.bind (int64Of graph) with
        | Some value when value >= int64 System.Int32.MinValue && value <= int64 System.Int32.MaxValue -> Ok (int value)
        | _ -> Error (sprintf "CAbiDescriptor '%s' %s must be an exact signed 32-bit integer declaration." descriptor name)
    graph.Nodes |> Map.toList |> List.fold (fun state (_, node) ->
        state |> Result.bind (fun declarations ->
            let selected =
                match node.Kind with
                | SemanticKind.Binding(name, _, _, _) when isSelectedPlatformDeclaration graph node ->
                    node.Children |> List.tryLast |> Option.bind (recordOf graph)
                    |> Option.map (fun (record, fields) -> name, record, fields)
                | _ -> None
            match selected with
            | Some (descriptor, record, fields) when typeName record = Some "CAbiDescriptor" ->
                match field "Name" fields |> Option.bind (stringOf graph) with
                | None -> Error (sprintf "CAbiDescriptor '%s' Name must be a string declaration." descriptor)
                | Some name ->
                    integer descriptor fields "PointerBits" |> Result.bind (fun bits ->
                        integer descriptor fields "ScalarAggregateRegisterBytes" |> Result.map (fun registerBytes ->
                            (name, bits, registerBytes) :: declarations))
            | _ -> Ok declarations)) (Ok [])
    |> Result.map (List.rev >> List.distinct)

/// Only these parameters allow a temporary native record projection without write-back.
let readOnlyRecordReferenceArguments graph funcId args =
    actualReferences graph funcId args (fun f -> f.RecordReferences)
    |> List.choose (fun (id, readOnly) -> if readOnly then Some id else None) |> Set.ofList
