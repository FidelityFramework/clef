// Negative control, exact reason: CLF002.  The console-writing Printf family
// comes from FSharp.Core, so it never reaches the BCL classifyMember path and
// has to be dispatched explicitly (clef #165-B blocker 7).
module ClefAnalyzerConsoleOutputCase

let reportLine (text : string) : unit = printfn "%s" text

let reportErrorLine (text : string) : unit = eprintfn "%s" text
