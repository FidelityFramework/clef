// Negative control, exact reason: AXC010 covers process-wide concurrent mutable
// state and FSharp.Core Monitor `lock` as ambient state (clef #165-B).
module ClefAnalyzerConcurrentCase

open System.Collections.Concurrent

let sharedCounts : ConcurrentDictionary<int, int> = ConcurrentDictionary<int, int>()

let bump (key : int) : bool = sharedCounts.TryAdd(key, 1)

let lockedBump (gate : string) : int = lock gate (fun () -> 1)
