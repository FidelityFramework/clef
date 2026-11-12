#I "../../artifacts/bin/Clef.Compiler.Service/Debug/net10.0"
#r "Clef.Compiler.Service.dll"

open System
open System.IO
module Solver = Clef.Compiler.Nanopass.ObligationDischarge

let equal label expected actual =
    if expected <> actual then failwithf "%s: expected %A, got %A" label expected actual
let executable = if OperatingSystem.IsWindows() then "cvc5.exe" else "cvc5"
let root = Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__, "../../artifacts/scratch/host discovery"))
let first = Path.Combine(root, "first solver", executable)
let second = Path.Combine(root, "second solver", executable)
let path = String.Join(string Path.PathSeparator, [Path.GetDirectoryName first; Path.GetDirectoryName second])
equal "PATH returns the selected executable, including spaces" first (Solver.resolveSolver path (fun p -> p = first || p = second))
equal "empty PATH does not search the working directory" executable (Solver.resolveSolver null (fun p -> p = executable))
let installed =
    if OperatingSystem.IsWindows() then
        Path.Combine(Environment.GetFolderPath Environment.SpecialFolder.LocalApplicationData, "Clef", "toolchains", "cvc5-1.3.0", "bin", executable)
    else Path.Combine(Environment.GetFolderPath Environment.SpecialFolder.UserProfile, ".local", "toolchains", "cvc5-1.3.0", "bin", executable)
equal "current user installation" installed (Solver.resolveSolver "" ((=) installed))
if OperatingSystem.IsWindows() then
    if Solver.solverToolchainPaths |> List.exists (fun p -> p.StartsWith("/")) then
        failwith "Windows discovery contains Unix toolchain roots"
let repository = Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__, "../.."))
let start = Diagnostics.ProcessStartInfo("git", WorkingDirectory = repository, UseShellExecute = false, RedirectStandardOutput = true)
start.ArgumentList.Add "ls-files"
let child = Diagnostics.Process.Start start
let tracked = child.StandardOutput.ReadToEnd().Split('\n', StringSplitOptions.RemoveEmptyEntries)
child.WaitForExit()
if child.ExitCode <> 0 then failwith "Cannot inspect tracked checkout paths"
let collisions = tracked |> Array.groupBy (fun p -> p.TrimEnd('\r').ToUpperInvariant()) |> Array.filter (fun (_, paths) -> paths.Length > 1)
if collisions.Length > 0 then failwithf "Windows checkout collisions: %A" collisions
let alternate = first.Replace(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar)
if not (Clef.Compiler.Utilities.HostTools.samePath first alternate) then failwith "Alternate host separators do not identify the same source"
if OperatingSystem.IsWindows() && not (Clef.Compiler.Utilities.HostTools.samePath first (first.ToUpperInvariant())) then
    failwith "Windows source membership is case-sensitive"
printfn "CCS host discovery and checkout checks passed."
