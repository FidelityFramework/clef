// Negative control, exact reason: direct BCL members on primitive carriers.
// Array length is admitted by the Option A allowlist, so it must not be
// reported; Trim is not.
module ClefAnalyzerStringMemberCase

let trimmed (text : string) : string = text.Trim()

let items (values : string array) : int = values.Length
