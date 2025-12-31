namespace FSharp.Native.Compiler.Service.Tests

[<AutoOpen>]
module CompilerTestHelpers =

    let (|Warning|_|) (exn: System.Exception) =
        match exn with
        | :? FSharp.Native.Compiler.DiagnosticsLogger.DiagnosticWithText as e -> Some (e.number, e.message)
        | _ -> None
