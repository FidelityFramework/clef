// Negative control, exact reason: AXC010 catches System.Lazy.IsValueCreated
// state branching (ADL ZONE-A-ANALYZER-BOUNDARY).
module ClefAnalyzerLazyStateCase

let checkLazy (cell : System.Lazy<int>) : bool =
    cell.IsValueCreated
