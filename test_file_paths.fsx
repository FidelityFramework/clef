#!/usr/bin/env dotnet fsi
#r "artifacts/bin/FSharp.Native.Compiler.Service/Debug/net9.0/FSharp.Native.Compiler.Service.dll"

open System.IO
open FSharp.Native.Compiler.NativeService
open FSharp.Native.Compiler.Checking.Native.SemanticGraph

// Two files with different path styles
let source1 = """
module Core
let x = 1
"""

let source2 = """
module Main
open Core
let main () = x
"""

// Use different path styles
let file1 = "/home/hhh/repos/Alloy/src/Core.fs"
let file2 = "samples/Main.fs"  // Relative path

printfn "Parsing with paths:"
printfn "  File1: %s" file1
printfn "  File2: %s" file2

let parsed1 = parseStringWithDefaults source1 file1
let parsed2 = parseStringWithDefaults source2 file2

match parsed1, parsed2 with
| ParseSuccess input1, ParseSuccess input2 ->
    let result = checkParsedInputs [input1; input2]

    printfn "\nUnique Range.File values in graph:"
    result.Graph.Nodes
    |> Map.values
    |> Seq.map (fun n -> n.Range.File)
    |> Seq.distinct
    |> Seq.iter (fun f -> printfn "  '%s'" f)

    printfn "\nNow testing lookups..."

    // Test lookup with exact path
    let findNodes file =
        result.Graph.Nodes
        |> Map.values
        |> Seq.filter (fun n -> n.Range.File = file)
        |> Seq.toList

    printfn "\n  Looking for file1 ('%s'):" file1
    printfn "    Found %d nodes" (findNodes file1 |> List.length)

    printfn "\n  Looking for file2 ('%s'):" file2
    printfn "    Found %d nodes" (findNodes file2 |> List.length)

    printfn "\n  Looking for 'Main.fs':"
    printfn "    Found %d nodes" (findNodes "Main.fs" |> List.length)

    // What path does GetFullPath produce?
    printfn "\n  Path.GetFullPath('%s') = %s" file2 (Path.GetFullPath(file2))

| _ -> printfn "Parse failed"
