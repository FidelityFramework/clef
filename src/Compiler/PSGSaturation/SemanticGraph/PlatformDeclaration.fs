// SPDX-License-Identifier: MIT

/// Platform Declaration at saturation: the one place the declared platform
/// fills the `PlatformContext`, and the check of every sealed site against it.
///
/// The description compiled into the graph (PlatformResolution, the one reader)
/// declares the core's width dimensions by name and the numeric representations
/// it offers (plan D8; ntu-dimensional-architecture.md §7.1; numeric-selection.md
/// §7, §9 item 6). Once the graph is complete, `fill` copies those declarations
/// into `PlatformContext.Dimensions` and `Representations`; nothing else writes
/// them, and no project-file key or path string ever did after CS-7b (plan L-13).
///
/// `check` reports first what is wrong with the declaration itself, at the node
/// that declares it: an element the reader cannot read is CCS8206, an element
/// outside its vocabulary CCS8207, a second description of one form CCS8208.
/// Then it reads the context back at every reachable site whose type carries a
/// numeric carrier: a carrier sealed to a width dimension the description does
/// not declare is CCS8203 at that site; a carrier whose representation the
/// description does not offer, absent or declared unavailable, is CCS8204 at
/// that site. Each undeclared name is reported once, at the first site in node
/// order that needs it. The description is read; no number is supplied here,
/// and Composer reads the same context (plan D1).
module Clef.Compiler.PSGSaturation.SemanticGraph.PlatformDeclaration

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.Expressions.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
module PlatformResolution = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

//-------------------------------------------------------------------------
// Filling the context from the declaration
//-------------------------------------------------------------------------

/// The context with `Dimensions` and `Representations` read from the core the
/// description declares. A description with no core, or no description at all,
/// leaves both empty: every site that needs one is then reported by `check`.
/// What could be read of a defective declaration is filled; the defect itself
/// is reported by `check` at the declaration, before any site.
let fill (context: PlatformContext option) (graph: SemanticGraph) : PlatformContext option =
    context
    |> Option.map (fun ctx ->
        match (PlatformResolution.read graph).Platform with
        | Some { Core = Some core } ->
            { ctx with
                Dimensions = core.Widths |> List.map (fun w -> w.Name, w.Bits) |> Map.ofList
                Representations = core.Representations |> List.map (fun r -> r.Representation.Name, r.Representation) |> Map.ofList }
        | _ -> { ctx with Dimensions = Map.empty; Representations = Map.empty })

//-------------------------------------------------------------------------
// The sites: every numeric carrier a reachable node's type carries
//-------------------------------------------------------------------------

/// The numeric carriers a type carries, in the order they appear. Every case of
/// `NativeType` is named so that a new case is a compile-time question here,
/// not a site passed over.
let rec private carriersOf (ty: NativeType) : TypeConRef list =
    match ty with
    | NativeType.TNum (carrier, _) ->
        match CarrierRef.tryConstructor carrier with
        | Some tc -> [ tc ]
        | None -> []
    | NativeType.TForall (_, body) -> carriersOf body
    | NativeType.TApp (_, args) -> args |> List.collect carriersOf
    | NativeType.TTuple (elements, _) -> elements |> List.collect carriersOf
    | NativeType.TFun (domain, range) -> carriersOf domain @ carriersOf range
    | NativeType.TAnon (fields, _) -> fields |> List.collect (snd >> carriersOf)
    | NativeType.TUnion (_, cases) -> cases |> List.collect (fun c -> c.Fields |> List.collect (snd >> carriersOf))
    | NativeType.TByref (element, _) -> carriersOf element
    | NativeType.TNativePtr element
    | NativeType.TLazy element
    | NativeType.TSeq element
    | NativeType.TSeqEnumerator element
    | NativeType.TList element
    | NativeType.TSet element -> carriersOf element
    | NativeType.TMap (key, value) -> carriersOf key @ carriersOf value
    | NativeType.TVar _ | NativeType.TMeasure _ | NativeType.TError _ -> []

/// The width dimension a carrier is sealed to, when its width is platform-resolved.
let private dimensionOf (carrier: TypeConRef) : WidthDimension option =
    match carrier.NTUKind with
    | Some (NTUKind.NTUint (NTUWidth.Resolved dim))
    | Some (NTUKind.NTUuint (NTUWidth.Resolved dim))
    | Some (NTUKind.NTUfloat (NTUWidth.Resolved dim))
    | Some (NTUKind.NTUposit (NTUWidth.Resolved dim, _)) -> Some dim
    | _ -> None

//-------------------------------------------------------------------------
// The check
//-------------------------------------------------------------------------

/// What one carrier at one site asks of the declaration, and the answer.
[<RequireQualifiedAccess>]
type private Finding =
    /// The dimension named is not declared: CCS8203.
    | UndeclaredWidth of name: string
    /// The representation described is not offered: CCS8204, with its message.
    | UnofferedRepresentation of message: string

let private findingsOf (ctx: PlatformContext) (carrier: TypeConRef) : Finding list =
    let width =
        dimensionOf carrier
        |> Option.map WidthDimension.name
        |> Option.bind (fun name ->
            match PlatformContext.tryWidth ctx name with
            | Result.Ok _ -> None
            | Result.Error _ -> Some (Finding.UndeclaredWidth name))
    let representation =
        match width with
        | Some _ -> None   // the width is the finding; the representation cannot be named without it
        | None ->
            match PlatformContext.tryRepresentationOfSeal ctx (Types.representationOfCarrier carrier) with
            | Result.Ok _ -> None
            | Result.Error (SealFailure.UndeclaredWidth _) -> None   // reported above by the carrier's own width
            | Result.Error (SealFailure.NotOffered message) -> Some (Finding.UnofferedRepresentation message)
    List.choose id [ width; representation ]

let private siteDiagnostic (ctx: PlatformContext) (node: SemanticNode) (finding: Finding) : Diagnostic =
    let code, message =
        match finding with
        | Finding.UndeclaredWidth name -> DiagnosticCodes.CCS8203_UndeclaredWidthDimension, PlatformContext.undeclaredWidthMessage ctx name
        | Finding.UnofferedRepresentation message -> DiagnosticCodes.CCS8204_RepresentationNotOffered, message
    { Severity = NativeDiagnosticSeverity.Error
      Code = code
      Message = message
      Range = node.Range
      RelatedNodes = [ node.Id ]
      Reachability = ReachabilityContext.Reachable }

/// A defect of the declaration, at its declaring node. The description is
/// compiled with the program, so the node has its range in Description.clef or
/// Platform.clef; the declaration is never reachable, and is not asked to be.
let private declarationDiagnostic (ctx: PlatformContext) (finding: PlatformResolution.DeclarationFinding) : Diagnostic =
    let code =
        match finding.Defect with
        | PlatformResolution.DeclarationDefect.Malformed -> DiagnosticCodes.CCS8206_MalformedPlatformDeclaration
        | PlatformResolution.DeclarationDefect.Invalid -> DiagnosticCodes.CCS8207_InvalidPlatformDeclaration
        | PlatformResolution.DeclarationDefect.Ambiguous -> DiagnosticCodes.CCS8208_AmbiguousPlatformDescription
    { Severity = NativeDiagnosticSeverity.Error
      Code = code
      Message = sprintf "The platform description of '%s': %s" ctx.PlatformId finding.Message
      Range = finding.Range
      RelatedNodes = [ finding.Node ]
      Reachability = ReachabilityContext.Unknown }

/// Every defect of the declaration, then every reachable site whose
/// declaration is missing, each undeclared name at its first site in node
/// order. Empty when there is no platform context (a library), when every
/// element and site is declared, or, for the sites, on fabric: an FPGA has no
/// core to describe (`Core = None`), and there a width is the analysed range's,
/// never a dimension's (ntu-dimensional-architecture.md §7.1: interior widths
/// come from the range and need no dimension; plan D1: "or a range is supplied
/// as the FPGA binding does"), so no site on that substrate asks the
/// description for one. A defective declaration is reported on every substrate.
let check (context: PlatformContext option) (graph: SemanticGraph) : Diagnostic list =
    match context with
    | None -> []
    | Some ctx ->
        let declaration =
            (PlatformResolution.read graph).Findings
            |> List.map (declarationDiagnostic ctx)
        let sites =
            if PlatformContext.substrateKind ctx = SubstrateKind.FPGA then []
            else
                let reachable =
                    graph.Nodes
                    |> Map.toList
                    |> List.map snd
                    |> List.filter (fun node -> node.IsReachable)
                let (_, diagnostics) =
                    reachable
                    |> List.fold (fun (reported: Set<Finding>, acc: Diagnostic list) node ->
                        carriersOf node.Type
                        |> List.collect (findingsOf ctx)
                        |> List.fold (fun (seen, out) finding ->
                            if Set.contains finding seen then (seen, out)
                            else (Set.add finding seen, siteDiagnostic ctx node finding :: out)) (reported, acc)) (Set.empty, [])
                List.rev diagnostics
        declaration @ sites
