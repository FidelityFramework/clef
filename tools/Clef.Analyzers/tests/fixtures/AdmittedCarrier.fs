// Positive control: the only BCL member the ANALYZER-POLICY Option A allowlist
// admits - 'T[].Length.  The analyzer must report nothing for this file.
module ClefAnalyzerAdmittedCarrier

let itemCount (values : string array) : int = values.Length
