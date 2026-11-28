// Negative control, exact reason: active compiling inline-MSIL blocks (AXC007),
// including unspaced and legally spaced forms (`( # ... # )`), the exact #12645
// generic inline-IL CLR throw with `'T`, and `ldnull` (clef #165 #12645 Lens 2 B1).
module ClefAnalyzerInlineIlFault

let inline addIl (x : int) (y : int) : int = (# "add" x y : int #)

let inline throwGeneric (e : exn) : 'T = (# "throw" e : 'T #)

let inline throwSpaced (e : exn) : 'T = ( # "throw" e : 'T # )

let inline nullSpaced () : string = ( # "ldnull" : string # )

let boundary : string = "the literal sequence (# appears in ordinary text"
