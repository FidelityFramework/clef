// Negative control, exact reason: CLF003 normalize-invocation ratchet inside
// NativeService.fs / NativeTypedTree/NormalizeCase.fs (recovery wiki section 3.3).
module Clef.Compiler.NativeTypedTree.NormalizeControl

let normalize (rows : list<int>) : list<int> = rows |> List.sort

let prepare (rows : list<int>) : list<int> = normalize rows
