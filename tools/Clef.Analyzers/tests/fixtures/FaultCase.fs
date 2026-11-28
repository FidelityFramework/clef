// Fault-injection probe: the two constructs the Increment A line-token guard
// cannot classify - a process-wide weak cache and CLR reflection on a value.
// The typed analyzer must refuse both (AXC010 / AXC009).
module ClefAnalyzerFaultCase

open System.Runtime.CompilerServices
open Microsoft.FSharp.Reflection

let weakCache : ConditionalWeakTable<string, obj> = ConditionalWeakTable<string, obj>()

let reflectFields (value : obj) : obj array = FSharpValue.GetTupleFields value
