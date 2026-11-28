// Negative control, exact reason: the untyped obj/box escape hatch (AXC001).
module ClefAnalyzerBoxCase

let widened (value : int) : obj = box value
