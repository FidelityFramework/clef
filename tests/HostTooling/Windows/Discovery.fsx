#load "../../../src/Compiler/Utilities/HostTools.Linux.fs"
#load "../../../src/Compiler/Utilities/HostTools.fs"

open System
open System.IO
module Host = Clef.Compiler.Utilities.HostTools

if not (OperatingSystem.IsWindows()) then failwith "Run on Windows."
let root = Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__,"../../../artifacts/scratch/windows-solver-" + Guid.NewGuid().ToString("N")))
try
    Directory.CreateDirectory root |> ignore
    let binary = Path.Combine(root,"cvc5.exe")
    File.WriteAllText(binary,"discovery fixture")
    if Host.findSolver root<>binary then failwith "Windows solver discovery changed"
    if not (Host.samePath binary (binary.ToUpperInvariant())) then failwith "Windows source paths lost case-insensitive comparison"
    printfn "Windows solver discovery checks passed."
finally
    Directory.Delete(root,true)
