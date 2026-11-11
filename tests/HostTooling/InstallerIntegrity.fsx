#load "../../tools/SolverInstallation.fsx"
#load "../../src/Compiler/Utilities/HostTools.Linux.fs"
#load "../../src/Compiler/Utilities/HostTools.fs"

open System
open System.IO

let root = Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__,"../../artifacts/scratch/solver-integrity-" + Guid.NewGuid().ToString("N")))
Directory.CreateDirectory root |> ignore
let binary = Path.Combine(root,if OperatingSystem.IsWindows() then "cvc5.exe" else "cvc5")
try
    for bytes in [Array.empty<byte>; Text.Encoding.UTF8.GetBytes "not a solver"] do
        File.WriteAllBytes(binary,bytes)
        let refused = try SolverInstallation.verifyExisting binary; false with _ -> true
        if not refused then failwith "Existing unusable solver was accepted as successful setup"
        if File.ReadAllBytes(binary)<>bytes then failwith "Refused installation was modified"
    let solver =
        match Environment.GetEnvironmentVariable "CLEF_CVC5" with
        | null | "" -> Clef.Compiler.Utilities.HostTools.findSolver (Environment.GetEnvironmentVariable "PATH")
        | explicit -> explicit
    SolverInstallation.verifyExisting solver
    let before = File.ReadAllBytes solver
    SolverInstallation.verifyExisting solver
    if File.ReadAllBytes(solver)<>before then failwith "Valid existing installation was modified"
    printfn "Existing solver mutation checks passed."
finally
    Directory.Delete(root,true)
