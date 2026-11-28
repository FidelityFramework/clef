// Positive control for AXC007 (clef #165-B blocker 8).  The previous fixture
// recorded inline MSIL only inside a string literal; a string that *looks* like
// an inline-IL block is not inline IL.  This file is plain Zone A algebra with
// no MSIL block at all, so the analyzer must report nothing here.
module ClefAnalyzerInlineIlCase

type Word = { Units : list<int> }

let unitCount (word : Word) : int = List.length word.Units

let halve (word : Word) : Word = { Units = word.Units |> List.map (fun unit -> unit / 2) }

let total (words : list<Word>) : int = words |> List.sumBy unitCount

// The string literal below contains the two-character sequence that opens an
// inline-MSIL block.  It is data, not IL: the AXC007 scan must not fire on it
// (clef #165-B blocker 8).
let literalWithParenHash : string = "a token that looks like (# but is only text"
let alsoVerbatim : string = """inline-IL-ish marker: (# "push 1" #) inside a verbatim string"""
let charLiteral : char = '('
