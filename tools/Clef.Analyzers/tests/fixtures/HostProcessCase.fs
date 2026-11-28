// Negative control, exact reason: host, process and timing primitives.
module ClefAnalyzerHostProcessCase

let runHost () : int = System.Environment.ExitCode
let nowTicks () : int64 = System.DateTime.Now.Ticks
