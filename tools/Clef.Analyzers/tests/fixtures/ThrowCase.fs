// Negative control, exact reason: CLR throw, including implicit throws
// (failwith, failwithf, nullArgCheck, Option.get, List.head -> AXC008).
module ClefAnalyzerThrowCase

let boom () : int = failwith "unreachable branch"

let boomFormatted (code : int) : int = failwithf "unexpected code %d" code

let firstOf (values : int list) : int = List.head values

let forced (maybe : int option) : int = Option.get maybe

let checkedArg (x : string | null) : string = nullArgCheck "x" x
