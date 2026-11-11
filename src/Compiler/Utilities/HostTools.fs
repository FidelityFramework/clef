module Clef.Compiler.Utilities.HostTools

open System
open System.IO

let samePath left right =
    String.Equals(Path.GetFullPath left, Path.GetFullPath right,
                  if OperatingSystem.IsWindows() then StringComparison.OrdinalIgnoreCase else StringComparison.Ordinal)

let solverName = if OperatingSystem.IsWindows() then "cvc5.exe" else "cvc5"

let solverToolchainPaths =
    let root =
        if OperatingSystem.IsWindows() then
            Path.Combine(Environment.GetFolderPath Environment.SpecialFolder.LocalApplicationData, "Clef", "toolchains")
        else Path.Combine(Environment.GetFolderPath Environment.SpecialFolder.UserProfile, ".local", "toolchains")
    [ yield Path.Combine(root, "cvc5-1.3.0", "bin", solverName)
      if OperatingSystem.IsLinux() then
          for node in ["one"; "two"; "three"] do
              yield Path.Combine("/mnt/apps", "gpu-" + node, "toolchains", "cvc5-1.3.0", "bin", solverName)
          yield Path.Combine(Path.GetTempPath(), "cvc5-toolchain", "bin", solverName) ]

let resolveSolver (pathVariable: string | null) (exists: string -> bool) =
    let path = match pathVariable with null -> "" | value -> value
    let candidates =
        path.Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
        |> Array.filter (String.IsNullOrWhiteSpace >> not)
        |> Array.map (fun directory -> Path.Combine(directory, solverName))
        |> Array.toList
    candidates @ solverToolchainPaths |> List.tryFind exists |> Option.defaultValue solverName

let findSolver pathVariable =
    resolveSolver pathVariable (fun path ->
        File.Exists path && (not (OperatingSystem.IsLinux()) || LinuxHostTools.canExecute path))
