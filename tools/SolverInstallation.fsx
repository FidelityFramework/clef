module SolverInstallation

open System
open System.IO
open System.Diagnostics
open System.Threading
open System.Threading.Tasks

let private run binary arguments input =
    let info = ProcessStartInfo(binary,UseShellExecute=false,RedirectStandardInput=true,RedirectStandardOutput=true,RedirectStandardError=true)
    for argument in arguments do info.ArgumentList.Add argument
    use child = Process.Start info
    use deadline = new CancellationTokenSource(TimeSpan.FromSeconds 15.)
    let output = child.StandardOutput.ReadToEndAsync(deadline.Token)
    let errors = child.StandardError.ReadToEndAsync(deadline.Token)
    try
        child.StandardInput.Write(input: string)
        child.StandardInput.Close()
        Task.WhenAll([|child.WaitForExitAsync(deadline.Token);output :> Task;errors :> Task|]).GetAwaiter().GetResult()
        if child.ExitCode<>0 then failwithf "Existing solver exited %d: %s" child.ExitCode errors.Result
        output.Result
    finally
        if not child.HasExited then
            child.Kill(true)
            child.WaitForExit()

let verifyExisting binary =
    if not (File.Exists binary) then failwithf "Existing solver installation is incomplete: %s. It was not overwritten." binary
    let version = run binary ["--version"] ""
    if not (version.Contains("cvc5 version",StringComparison.OrdinalIgnoreCase)) then
        failwithf "Existing file does not identify itself as cvc5: %s. It was not overwritten." binary
    let script = "(set-logic QF_LIA)\n(declare-fun x () Int)\n(assert (= x 1))\n(check-sat)\n(push 1)\n(assert (= x 2))\n(check-sat)\n"
    let answers = (run binary ["--lang=smt2";"--incremental"] script).Split([|'\r';'\n'|],StringSplitOptions.RemoveEmptyEntries) |> Array.map _.Trim()
    if answers<>[|"sat";"unsat"|] then
        failwithf "Existing solver failed SAT/UNSAT calibration: %s. It was not overwritten." binary
