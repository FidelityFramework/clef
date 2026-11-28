// SPDX-License-Identifier: MIT
// Zone A observation seam (clef #204, the clef half of Composer #192).
//
// The core reports what it settled; it does not measure itself. The wall clock,
// the environment variable and the console write that used to sit in the driver
// are gone. This module reads nothing from the host, writes nowhere, holds no
// clock, no thread state and no reflection. A port is a value the caller
// supplies, so the adapter on the host edge (Composer, a test harness, or
// nothing) decides what an observation means. No compiler result depends on an
// observation being delivered, and CLR exception containment belongs at the
// Zone B host adapter edge (`ProjectChecker.containObservationPort`).
module Clef.Compiler.ObservationPort

open Clef.Compiler.PSGSaturation.SemanticGraph.Types

/// Every owner whose settled projection the driver publishes.
[<RequireQualifiedAccess>]
type ProjectionOwner =
    | PlatformReading
    | PlatformDescriptors
    | Numeric
    | Memory
    | Spatial
    | Boundary
    | WitnessSegmentation

/// What the driver did, in the compiler's own vocabulary. Rows are the settled
/// records that owner published, counted from the graph facts already produced.
[<RequireQualifiedAccess>]
type CompilerObservation =
    | Phase of string
    | Pass of string
    | ProjectionComputed of ProjectionOwner * int
    | RootCensus of hardwareModules: int * kernelModules: int

/// A pure sink. Wrapping it around I/O is the adapter's business, not the core's.
type ObservationPort =
    { Emit: CompilerObservation -> unit }

let noopObservationPort: ObservationPort = { Emit = fun _ -> () }

let observationPort (emit: CompilerObservation -> unit) : ObservationPort = { Emit = emit }

/// Pure Zone A observation delivery. Host adapters in Zone B wrap their port
/// with exception containment so host failures never unwind into the compiler core.
let emitObservation (port: ObservationPort) (observation: CompilerObservation) : unit =
    port.Emit observation

/// Lazy optional delivery: when no observer is attached (`None`), the payload
/// thunk is never evaluated so ordinary compilation incurs zero scanning or allocation.
let emitOptional (port: ObservationPort option) (build: unit -> CompilerObservation) : unit =
    match port with
    | None -> ()
    | Some active -> active.Emit (build ())

let private edgeCount (graph: SemanticGraph) (owns: EdgeRole -> bool) : int =
    graph.Edges |> List.fold (fun count edge -> if owns edge.Role then count + 1 else count) 0

let numericRows (graph: SemanticGraph) : int =
    edgeCount graph (function
        | EdgeRole.NumericDomain _
        | EdgeRole.NumericCarrier _
        | EdgeRole.NumericProof _
        | EdgeRole.NumericOperation _
        | EdgeRole.NumericOperationProof _
        | EdgeRole.NumericIndexTransport _ -> true
        | _ -> false)

let memoryRows (graph: SemanticGraph) : int =
    edgeCount graph (function
        | EdgeRole.MemoryDomain _
        | EdgeRole.MemoryOperation _
        | EdgeRole.MemoryArrayCopy _
        | EdgeRole.ArrayAllocationConstruction _
        | EdgeRole.ArrayCopyConstruction _
        | EdgeRole.MemoryProof _
        | EdgeRole.MemoryAccessGuard -> true
        | _ -> false)

let spatialRows (graph: SemanticGraph) : int =
    edgeCount graph (function
        | EdgeRole.SpatialModuleDomain _
        | EdgeRole.HardwareModule _
        | EdgeRole.KernelModule _
        | EdgeRole.KernelIngress _
        | EdgeRole.SpatialProof _ -> true
        | _ -> false)

let boundaryRows (graph: SemanticGraph) : int =
    edgeCount graph (function
        | EdgeRole.BoundaryDeclaration _
        | EdgeRole.BoundaryDomain _
        | EdgeRole.BoundaryResourceDeclaration _
        | EdgeRole.BoundaryWritableBufferDeclaration _
        | EdgeRole.BoundaryWritableBufferUse _
        | EdgeRole.BoundaryReadOnlyBufferDeclaration _
        | EdgeRole.BoundaryReadOnlyBufferUse _
        | EdgeRole.BoundaryBorrowedResultViewDeclaration _
        | EdgeRole.BoundaryBorrowedResultViewUse _
        | EdgeRole.BoundaryBufferAbsence _
        | EdgeRole.BoundaryCountedEntryArray _
        | EdgeRole.BoundaryResourceAccess _
        | EdgeRole.BoundaryImport _
        | EdgeRole.BoundaryCall _
        | EdgeRole.BoundaryOperand _
        | EdgeRole.BoundaryAdaptation _
        | EdgeRole.BoundaryCoverage _
        | EdgeRole.BoundaryProof _ -> true
        | _ -> false)

let witnessSegmentationRows (segmentation: WitnessSegmentation) : int =
    List.length segmentation.Regions

/// Declared hardware and kernel module roots in the settled graph.
let rootCensus (graph: SemanticGraph) : int * int =
    let tally (hardware, kernels) (_, root) =
        match root with
        | DeclRoot.HardwareModule -> (hardware + 1, kernels)
        | DeclRoot.KernelModule -> (hardware, kernels + 1)
        | _ -> (hardware, kernels)
    List.fold tally (0, 0) graph.DeclarationRoots

/// A platform description and the spaces and buffers it declares.
let platformDescriptorRows (platform: Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution.DeclaredPlatform option) : int =
    match platform with
    | None -> 0
    | Some platform ->
        1 + List.length platform.Spaces + List.length platform.Buffers
