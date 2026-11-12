#load "../../../src/Compiler/Utilities/HostTools.Linux.fs"
#load "../../../src/Compiler/Utilities/HostTools.fs"

open System
open System.IO
module Host = Clef.Compiler.Utilities.HostTools

if not (OperatingSystem.IsLinux()) then failwith "Run on Linux."
let root = Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__,"../../../artifacts/scratch/linux-solver-" + Guid.NewGuid().ToString("N")))
let first = Path.Combine(root,"first","cvc5")
let second = Path.Combine(root,"second","cvc5")
try
    for file in [first;second] do Directory.CreateDirectory(Path.GetDirectoryName file) |> ignore
    File.WriteAllText(first,"not executable")
    File.SetUnixFileMode(first,UnixFileMode.UserRead ||| UnixFileMode.UserWrite)
    File.CreateSymbolicLink(second,"/bin/true") |> ignore
    let selected = Host.findSolver (Path.GetDirectoryName first + ":" + Path.GetDirectoryName second)
    if selected<>second then failwithf "Automatic solver discovery selected non-executable %s instead of %s" selected second
    File.SetUnixFileMode(first,UnixFileMode.UserRead ||| UnixFileMode.UserWrite ||| UnixFileMode.UserExecute)
    if Host.findSolver (Path.GetDirectoryName first + ":" + Path.GetDirectoryName second)<>first then
        failwith "Executable PATH entries no longer retain their original order"
    printfn "Linux solver PATH execution checks passed."
finally
    if Directory.Exists root then Directory.Delete(root,true)
