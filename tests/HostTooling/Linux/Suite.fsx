#load "Discovery.fsx"
#load "../InstallerIntegrity.fsx"

open System
open System.IO

let root = Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__,"../../../artifacts/scratch/linux-calibration-" + Guid.NewGuid().ToString("N")))
try
    Directory.CreateDirectory root |> ignore
    let binary = Path.Combine(root,"cvc5")
    File.WriteAllText(binary,"#!/bin/sh\nif [ \"$1\" = \"--version\" ]; then echo 'This is cvc5 version fixture'; else echo unsat; fi\n")
    File.SetUnixFileMode(binary,UnixFileMode.UserRead ||| UnixFileMode.UserWrite ||| UnixFileMode.UserExecute)
    let refused = try SolverInstallation.verifyExisting binary; false with error -> error.Message.Contains "SAT/UNSAT"
    if not refused then failwith "An always-unsat solver passed existing-install calibration"
    printfn "Linux false solver mutation refused."
finally
    Directory.Delete(root,true)
