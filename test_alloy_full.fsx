#!/usr/bin/env dotnet fsi
#r "artifacts/bin/FSharp.Native.Compiler.Service/Debug/net9.0/FSharp.Native.Compiler.Service.dll"

open System.IO
open FSharp.Native.Compiler.NativeService
open FSharp.Native.Compiler.Checking.Native.SemanticGraph

// Alloy path
let alloyPath = "/home/hhh/repos/Alloy/src"

// Core files in order
let coreFiles = ["Core.fs"; "Math.fs"; "Memory.fs"; "Text.fs"; "Platform.fs"; "Console.fs"]
let allFiles = Directory.GetFiles(alloyPath, "*.fs") |> Array.toList

let orderedCore =
    coreFiles |> List.choose (fun name -> allFiles |> List.tryFind (fun f -> Path.GetFileName(f) = name))

let remaining = allFiles |> List.filter (fun f -> not (coreFiles |> List.contains (Path.GetFileName(f))))

let alloySources = orderedCore @ remaining

// User's file
let userSource = """
module HelloWorldDirect

open Alloy
open Alloy.Console

let main () =
    Write "Hello"
"""
let userFile = "/home/hhh/repos/Firefly/samples/console/FidelityHelloWorld/01_HelloWorldDirect/01_HelloWorldDirect.fs"

printfn "Loading %d Alloy files + 1 user file" (List.length alloySources)

// Parse all
let parseResults =
    (alloySources @ [userFile])
    |> List.mapi (fun i path ->
        let source = if path = userFile then userSource else File.ReadAllText(path)
        printfn "  [%d] %s" i (Path.GetFileName(path))
        match parseStringWithDefaults source path with
        | ParseSuccess input -> Some input
        | ParseError e ->
            printfn "    ERROR: %A" e
            None)
    |> List.choose id

printfn "\nParsed %d files, checking..." (List.length parseResults)

let result = checkParsedInputs parseResults

printfn "\nGraph has %d nodes" result.Graph.Nodes.Count
printfn "Entry points: %A" result.Graph.EntryPoints

// Group by file
let byFile =
    result.Graph.Nodes
    |> Map.values
    |> Seq.groupBy (fun n -> Path.GetFileName(n.Range.File))
    |> Seq.map (fun (f, nodes) -> (f, Seq.length nodes))
    |> Seq.sortByDescending snd
    |> Seq.toList

printfn "\nNodes by file (top 10):"
for (file, count) in byFile |> List.truncate 10 do
    printfn "  %s: %d nodes" file count

// Specifically check user's file
printfn "\n\nUser file nodes (01_HelloWorldDirect.fs):"
let userNodes =
    result.Graph.Nodes
    |> Map.values
    |> Seq.filter (fun n ->
        n.Range.File.Contains("01_HelloWorldDirect") ||
        n.Range.File = userFile)
    |> Seq.toList

printfn "Found %d nodes:" (List.length userNodes)
for node in userNodes |> List.sortBy (fun n -> n.Range.Start.Line) do
    let kindStr = sprintf "%A" node.Kind
    let kindPreview = if kindStr.Length > 50 then kindStr.Substring(0, 50) + "..." else kindStr
    printfn "  L%d:%d - %A: %s (Children: %A)"
        node.Range.Start.Line
        node.Range.Start.Column
        node.Id
        kindPreview
        node.Children

printfn "\nDiagnostics: %d" (List.length result.Diagnostics)
for d in result.Diagnostics |> List.truncate 5 do
    printfn "  [%A] %s: %s" d.Severity d.Code d.Message
