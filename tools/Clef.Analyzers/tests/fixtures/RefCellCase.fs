// Negative control, exact reason: AXC010 module-level ref cells and closures
// that capture them (clef #165-B), plus AXC011 function-local ref cells and
// ref-typed record fields mutated via `:=` / `incr` / `!`.
module ClefAnalyzerRefCellCase

let counter = ref 0
let nestedCell = ref (ref 1)
let cellPair = (ref 1, ref 2)

let bump () : int =
    counter := !counter + 1
    !counter

let closure =
    let inner = ref 5
    fun () -> inner := !inner + 1; !inner

type SharedBox = { Items : int list ref }

let appendShared (box : SharedBox) (x : int) : unit =
    box.Items := x :: !box.Items

let localBump () : int =
    let r = ref 0
    incr r
    !r
