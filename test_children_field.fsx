#!/usr/bin/env dotnet fsi
#r "artifacts/bin/FSharp.Native.Compiler.Service/Debug/net9.0/FSharp.Native.Compiler.Service.dll"

open FSharp.Native.Compiler.NativeService
open FSharp.Native.Compiler.Checking.Native.SemanticGraph

// Simple test source
let testSource = """
module HelloWorld

let greeting = "Hello"
let main () = greeting
"""

printfn "Checking test source..."
match parseAndCheck testSource "test.fs" with
| Success result ->
    printfn "Graph has %d nodes" result.Graph.Nodes.Count
    printfn ""

    // Check each node
    for node in result.Graph.Nodes |> Map.values do
        printfn "Node %A:" node.Id
        printfn "  Kind: %A" node.Kind
        printfn "  Children (in node.Children): %A" node.Children

        // Check if SemanticKind.ModuleDef has childIds
        match node.Kind with
        | SemanticKind.ModuleDef(name, childIds) ->
            printfn "  ModuleDef childIds: %A" childIds
            if node.Children <> childIds then
                printfn "  *** MISMATCH! node.Children <> childIds ***"
        | SemanticKind.Binding(name, _, _) ->
            printfn "  Binding: %s" name
        | SemanticKind.Lambda(_, bodyId, _, _, _) ->
            printfn "  Lambda body: %A" bodyId
        | _ -> ()
        printfn ""

    printfn "Declaration roots: %A" result.Graph.DeclarationRoots

| _ -> printfn "Failed"
