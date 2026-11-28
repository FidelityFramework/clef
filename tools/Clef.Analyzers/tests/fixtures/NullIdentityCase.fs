// Negative control, exact reason: null (including inside single-$ interpolated
// string holes, after `(* (*) *)`, and after `(* '"' *)`), isNull, and
// reference-identity escapes (AXC004).
module ClefAnalyzerNullIdentityCase

let missingValue : obj = null

let sameObject (a : obj) (b : obj) : bool =
    System.Object.ReferenceEquals (a, b)

let interpolatedNull () : string =
    $"""value { (null : string) }"""

(* (*) *)
let afterOperatorComment : string = null

(* '"' *)
let afterQuoteCharComment : string = null

let checkIsNull (value : string) : bool =
    isNull value

let refHasher () =
    HashIdentity.Reference<obj>
