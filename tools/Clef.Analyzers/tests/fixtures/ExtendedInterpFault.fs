// Negative control, exact reason: extended interpolated string literal ($$"""...""")
// where FSharpLineTokenizer and fsc disagree on short closing brace runs
// (clef #165 #12645, Lens 1 B1).
module ClefAnalyzerExtendedInterpFault

let render (x : int) : string =
    $$"""{{x}}}"""
