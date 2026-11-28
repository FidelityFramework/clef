// Negative control, exact reason: CLR reflection, constant-folded (incl.
// dynamic width `%*A`) and runtime PrintfFormat values, and %O/%T format
// specifiers in Zone A (AXC009).
module ClefAnalyzerReflectionCase

open Microsoft.FSharp.Reflection

let fieldsOf (value : obj) : obj array =
    FSharpValue.GetTupleFields value

[<Literal>]
let private Percent = "%"

[<Literal>]
let private FoldedFormat = Percent + "A"

[<Literal>]
let private FoldedWidthFormat = Percent + "*A"

let foldedReflective (x : int) : string =
    sprintf FoldedFormat x

let foldedDynamicWidth (x : int) : string =
    sprintf FoldedWidthFormat 4 x

let runtimeReflective (x : int) : string =
    let fmt = Printf.StringFormat<int -> string>("%" + "A")
    sprintf fmt x

let formatObject (x : int) : string =
    sprintf "%O" x

let rawFormatT : string = "%T"
