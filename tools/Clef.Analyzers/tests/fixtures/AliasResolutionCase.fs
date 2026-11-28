// Negative control, exact reason: CLF001 resolves module aliases and catches
// all PlatformResolution.read* whole-graph readers (clef #165 #12565, wiki §3.3).
module ClefAnalyzerAliasResolutionCase

module PlatformResolution =
    let read (graph : int list) : int list = graph
    let readSharedBufferRegions (graph : int list) : int list = graph
    let resolve (graph : int list) : int option = graph |> List.tryHead

module Platform = PlatformResolution

let elaborate (graph : int list) : int list =
    Platform.read graph

let elaborateBuffers (graph : int list) : int list =
    PlatformResolution.readSharedBufferRegions graph
