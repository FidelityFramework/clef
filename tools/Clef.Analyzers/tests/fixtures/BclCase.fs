// Negative control, exact reason: a .NET base class library dependency outside
// the admitted set (AXC002, ANALYZER-POLICY Option A default-refuse).
module ClefAnalyzerBclCase

open System.Text

let build (parts : string list) : string =
    let builder = StringBuilder()
    for part in parts do
        builder.Append part |> ignore
    builder.ToString()
