#load "SolverInstallation.fsx"

open System
open System.IO
open System.IO.Compression
open System.Net.Http
open System.Security.Cryptography

// Official cvc5 1.3.0 release archives and their published SHA-256 digests.
let package, digest =
    if Runtime.InteropServices.RuntimeInformation.OSArchitecture <> Runtime.InteropServices.Architecture.X64 then
        failwith "This installer currently supports Windows x64 and Linux x64. Set CLEF_CVC5 for another host."
    elif OperatingSystem.IsWindows() then
        "cvc5-Win64-x86_64-static", "5300696af29c92fde8c360c5eec11a17c2e1812a3871754426a3733f6c462134"
    elif OperatingSystem.IsLinux() then
        "cvc5-Linux-x86_64-static", "1e5a30c66f8fc3b65ddac69a3ac299bf03914cc58fc562e0ab6c730bf6bbfe6f"
    else failwith "Set CLEF_CVC5 to a solver for this host."

let root =
    if OperatingSystem.IsWindows() then
        Path.Combine(Environment.GetFolderPath Environment.SpecialFolder.LocalApplicationData, "Clef", "toolchains")
    else Path.Combine(Environment.GetFolderPath Environment.SpecialFolder.UserProfile, ".local", "toolchains")
let destination = Path.Combine(root, "cvc5-1.3.0")
let executable = if OperatingSystem.IsWindows() then "cvc5.exe" else "cvc5"
let binary = Path.Combine(destination, "bin", executable)
if Directory.Exists destination then
    SolverInstallation.verifyExisting binary
    printfn "Using existing installation (not modified): %s" binary
else
    let scratch = Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__, "../artifacts/scratch/solver-install", Guid.NewGuid().ToString("N")))
    Directory.CreateDirectory scratch |> ignore
    try
        let archive = Path.Combine(scratch, package + ".zip")
        use client = new HttpClient(Timeout = TimeSpan.FromMinutes 5.)
        let url = "https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.0/" + package + ".zip"
        let bytes = client.GetByteArrayAsync(url).GetAwaiter().GetResult()
        let actual = SHA256.HashData bytes |> Convert.ToHexString |> _.ToLowerInvariant()
        if actual <> digest then failwithf "Solver archive checksum mismatch: expected %s, got %s" digest actual
        File.WriteAllBytes(archive, bytes)
        let unpacked = Path.Combine(scratch, "unpacked")
        ZipFile.ExtractToDirectory(archive, unpacked)
        let source = Path.Combine(unpacked, package)
        let sourceBinary = Path.Combine(source, "bin", executable)
        if not (File.Exists sourceBinary) then failwith "Solver archive has an unexpected layout"
        if not (OperatingSystem.IsWindows()) then
            File.SetUnixFileMode(sourceBinary, UnixFileMode.UserRead ||| UnixFileMode.UserWrite ||| UnixFileMode.UserExecute ||| UnixFileMode.GroupRead ||| UnixFileMode.GroupExecute ||| UnixFileMode.OtherRead ||| UnixFileMode.OtherExecute)
        Directory.CreateDirectory root |> ignore
        // The temporary destination stays on the install volume for an atomic rename.
        let staging = Path.Combine(root, ".cvc5-" + Guid.NewGuid().ToString("N"))
        Directory.CreateDirectory staging |> ignore
        try
            for directory in Directory.GetDirectories(source, "*", SearchOption.AllDirectories) do
                Directory.CreateDirectory(Path.Combine(staging, Path.GetRelativePath(source, directory))) |> ignore
            for file in Directory.GetFiles(source, "*", SearchOption.AllDirectories) do
                let target = Path.Combine(staging, Path.GetRelativePath(source, file))
                File.Copy(file, target)
                if not (OperatingSystem.IsWindows()) then File.SetUnixFileMode(target, File.GetUnixFileMode file)
            Directory.Move(staging, destination)
        finally
            if Directory.Exists staging then Directory.Delete(staging, true)
        printfn "Installed checksum-verified cvc5 1.3.0: %s" binary
    finally
        Directory.Delete(scratch, true)
