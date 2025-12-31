// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.
// Copyright (c) SpeakEZ, Inc.  All Rights Reserved.  Native scaffolding for FNCS.

/// Diagnostics utilities scaffolding for FNCS.
/// Provides minimal diagnostic output functionality.

module FSharp.Compiler.AbstractIL.Diagnostics

open System.IO

/// Output channel for diagnostics
let mutable out: TextWriter = System.Console.Out

/// Set the diagnostic output channel
let setDiagnosticsChannel (tw: TextWriter) =
    out <- tw

/// Print a diagnostic message with newline
let dprintfn fmt =
    Printf.kprintf (fun s -> out.WriteLine(s)) fmt

/// Print a diagnostic message without newline
let dprintf fmt =
    Printf.kprintf (fun s -> out.Write(s)) fmt

/// Print debug output (conditional)
let dprintnln s =
    dprintfn "%s" s
