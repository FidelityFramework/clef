// Negative control, exact reason: CLF002 console writes.  System.Console is the
// stdout/stderr channel, so it is host I/O rather than a process primitive
// (clef #165-B blocker 7); the entity is refused through the typed symbol use,
// not through a text match.
module ClefAnalyzerConsoleWriteCase

let logLine (text : string) : unit = System.Console.WriteLine(text)

let logErrorLine (text : string) : unit = System.Console.Error.WriteLine(text)
