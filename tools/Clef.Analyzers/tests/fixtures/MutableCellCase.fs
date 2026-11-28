// Negative control, exact reason: ambient mutable state and legacy mutable BCL
// collections (AXC010 / AXC011).
module ClefAnalyzerMutableCellCase

open System.Collections.Generic

let mutable cacheSeed : int = 0
let cache : Dictionary<int, int> = Dictionary<int, int>()

let touchCache (key : int) : int =
    let mutable total = 0
    for value in cache.Values do
        total <- total + value
    snd (cache.TryGetValue(key))
