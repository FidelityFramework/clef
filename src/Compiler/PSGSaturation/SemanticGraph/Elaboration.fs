/// Enrichment - API for marking compiler-synthesized PSG nodes
///
/// "Enrichment" is the parent concept encompassing:
///   - Elaboration (PLT term): Fleshing out intrinsic semantics
///   - Saturation (Fidelity term): Filling PSG "to the brim" before lowering
///
/// Two categories of enrichment:
///   1. Intrinsic elaboration: Synthesized to implement intrinsic semantics
///      - Example: Hidden syscall in Console.write
///   2. Baker saturation: Decomposition of language features to primitives
///      - HOF decomposition: List.map → recursion
///      - Seq expressions: seq { } → state machine nodes
///      - Lazy expressions: lazy x → thunk structure
///
/// NOTE: Coeffect Analysis is SEPARATE. It computes metadata about existing
/// structure (SSA assignment, mutability, yield states) - it does NOT create
/// new PSG nodes. See: docs/Coeffect_Analysis_Architecture.md
///
/// A for-loop is structurally identical whether from source or enrichment.
/// The ONLY distinction is the presence of enrichment metadata.
module FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Elaboration

open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types

//-------------------------------------------------------------------------
// Enrichment Kinds
//-------------------------------------------------------------------------

/// Standard enrichment kind values
[<RequireQualifiedAccess>]
module ElaborationKind =
    /// Elaborated to implement an intrinsic's semantics
    /// Example: Hidden syscall in Console.write implementation
    [<Literal>]
    let Intrinsic = "Intrinsic"

    /// Saturated during Baker decomposition (HOFs, language features to primitives)
    /// Examples:
    ///   - Recursion generated from List.map
    ///   - State machine nodes from seq expressions
    ///   - Thunk structure from lazy expressions
    [<Literal>]
    let Baker = "Baker"

//-------------------------------------------------------------------------
// Enrichment ID Generation
//-------------------------------------------------------------------------

/// Thread-safe enrichment ID counter
let private nextEnrichmentId = ref 0

/// Generate a fresh enrichment ID to link related nodes
let freshId () : int =
    System.Threading.Interlocked.Increment(nextEnrichmentId)

//-------------------------------------------------------------------------
// Marking API
//-------------------------------------------------------------------------

/// Mark a node as enriched (compiler-synthesized, not from source)
///
/// Parameters:
///   kind - ElaborationKind value ("Intrinsic" or "Baker")
///   forConstruct - What triggered enrichment ("List.map", "Console.write", etc.)
///   id - Enrichment ID linking related nodes (use freshId())
///   node - The SemanticNode to mark
///
/// Returns: Node with enrichment metadata added
let mark (kind: string) (forConstruct: string) (id: int) (node: SemanticNode) : SemanticNode =
    { node with
        Metadata =
            node.Metadata
            |> Map.add ElaborationMetadata.Kind (MetadataValue.String kind)
            |> Map.add ElaborationMetadata.For (MetadataValue.String forConstruct)
            |> Map.add ElaborationMetadata.Id (MetadataValue.Int id) }

/// Mark a node as Baker elaboration (convenience for HOF decomposition)
let markBaker (forConstruct: string) (id: int) (node: SemanticNode) : SemanticNode =
    mark ElaborationKind.Baker forConstruct id node

/// Mark a node as Intrinsic elaboration (convenience for intrinsic implementation)
let markIntrinsic (forConstruct: string) (id: int) (node: SemanticNode) : SemanticNode =
    mark ElaborationKind.Intrinsic forConstruct id node

//-------------------------------------------------------------------------
// Query API
//-------------------------------------------------------------------------

/// Check if a node is enriched (vs source-based)
let isEnriched (node: SemanticNode) : bool =
    Map.containsKey ElaborationMetadata.Kind node.Metadata

/// Alias for backward compatibility
let isElaborated = isEnriched

/// Check if a node is source-based (not enriched)
let isSourceBased (node: SemanticNode) : bool =
    not (isEnriched node)

/// Get enrichment kind if present
let tryGetKind (node: SemanticNode) : string option =
    match Map.tryFind ElaborationMetadata.Kind node.Metadata with
    | Some (MetadataValue.String kind) -> Some kind
    | _ -> None

/// Get the construct that triggered enrichment
let tryGetFor (node: SemanticNode) : string option =
    match Map.tryFind ElaborationMetadata.For node.Metadata with
    | Some (MetadataValue.String forConstruct) -> Some forConstruct
    | _ -> None

/// Get enrichment ID if present
let tryGetId (node: SemanticNode) : int option =
    match Map.tryFind ElaborationMetadata.Id node.Metadata with
    | Some (MetadataValue.Int id) -> Some id
    | _ -> None

/// Complete enrichment info record
type EnrichmentInfo = {
    Kind: string
    For: string
    Id: int
}

/// Alias for backward compatibility
type ElaborationInfo = EnrichmentInfo

/// Get complete enrichment info if node is enriched
let tryGetInfo (node: SemanticNode) : EnrichmentInfo option =
    match tryGetKind node, tryGetFor node, tryGetId node with
    | Some kind, Some forConstruct, Some id ->
        Some { Kind = kind; For = forConstruct; Id = id }
    | _ -> None
