/// Tests for the F# Native Compiler Service (FNCS)
/// Validates the full pipeline from F# source to SemanticGraph
module NativeChecker.NativeServiceTests

open Xunit
open FSharp.Native.Compiler.NativeService
open FSharp.Native.Compiler.Checking.Native.SemanticGraph
open FSharp.Native.Compiler.Checking.Native.NativeTypes

//-------------------------------------------------------------------------
// Parsing Tests
//-------------------------------------------------------------------------

[<Fact>]
let ``parseString - simple let binding parses successfully`` () =
    let source = """
module Test
let x = 42
"""
    match parseStringWithDefaults source "test.fs" with
    | ParseSuccess _ -> ()
    | ParseError errors -> failwithf "Parse failed: %A" errors

[<Fact>]
let ``parseString - module with function parses successfully`` () =
    let source = """
module Test
let add a b = a + b
"""
    match parseStringWithDefaults source "test.fs" with
    | ParseSuccess _ -> ()
    | ParseError errors -> failwithf "Parse failed: %A" errors

[<Fact>]
let ``parseString - syntax error returns ParseError`` () =
    let source = """
module Test
let x =
"""
    match parseStringWithDefaults source "test.fs" with
    | ParseSuccess _ -> failwith "Should have failed to parse"
    | ParseError _ -> ()

//-------------------------------------------------------------------------
// Type Checking Tests
//-------------------------------------------------------------------------

[<Fact>]
let ``parseAndCheck - simple let binding produces SemanticGraph`` () =
    let source = """
module Test
let x = 42
"""
    match parseAndCheck source "test.fs" with
    | Success result ->
        // Should have nodes in the graph
        Assert.True(result.Graph.Nodes.Count > 0, "Graph should have nodes")
        // Should have entry points
        Assert.True(result.Graph.EntryPoints.Length > 0, "Should have entry points")
    | ParseFailure errors -> failwithf "Parse failed: %A" errors
    | CheckFailure result -> failwithf "Check failed with diagnostics: %A" result.Diagnostics

[<Fact>]
let ``parseAndCheck - string literal produces Literal node`` () =
    let source = """
module Test
let s = "hello"
"""
    match parseAndCheck source "test.fs" with
    | Success result ->
        let literals =
            result.Graph.Nodes
            |> Map.values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.Literal value -> Some value
                | _ -> None)
            |> Seq.toList
        Assert.True(literals.Length > 0, "Should have at least one Literal node")
        // Check that we have a string literal
        let hasStringLiteral =
            literals |> List.exists (function
                | LiteralValue.String "hello" -> true
                | _ -> false)
        Assert.True(hasStringLiteral, sprintf "Should have string literal 'hello', got: %A" literals)
    | ParseFailure errors -> failwithf "Parse failed: %A" errors
    | CheckFailure result -> failwithf "Check failed with diagnostics: %A" result.Diagnostics

[<Fact>]
let ``parseAndCheck - int literal produces Literal node with Int32`` () =
    let source = """
module Test
let x = 42
"""
    match parseAndCheck source "test.fs" with
    | Success result ->
        let literals =
            result.Graph.Nodes
            |> Map.values
            |> Seq.choose (fun node ->
                match node.Kind with
                | SemanticKind.Literal value -> Some value
                | _ -> None)
            |> Seq.toList
        Assert.True(literals.Length > 0, "Should have at least one Literal node")
        let hasIntLiteral =
            literals |> List.exists (function
                | LiteralValue.Int32 42 -> true
                | _ -> false)
        Assert.True(hasIntLiteral, sprintf "Should have int literal 42, got: %A" literals)
    | ParseFailure errors -> failwithf "Parse failed: %A" errors
    | CheckFailure result -> failwithf "Check failed with diagnostics: %A" result.Diagnostics

//-------------------------------------------------------------------------
// Traversal Tests
//-------------------------------------------------------------------------

[<Fact>]
let ``foldPostOrder - visits all reachable nodes`` () =
    let source = """
module Test
let x = 42
let y = x + 1
"""
    match parseAndCheck source "test.fs" with
    | Success result ->
        let nodeCount =
            Traversal.foldPostOrder (fun count _ -> count + 1) 0 result.Graph
        // Should visit at least: ModuleDef, 2 Bindings, 2 Literals (42 and 1), VarRef, Application
        Assert.True(nodeCount >= 4, sprintf "Should visit at least 4 nodes, got: %d" nodeCount)
    | ParseFailure errors -> failwithf "Parse failed: %A" errors
    | CheckFailure result -> failwithf "Check failed with diagnostics: %A" result.Diagnostics

[<Fact>]
let ``foldPostOrder - collects binding names`` () =
    let source = """
module Test
let foo = 1
let bar = 2
let baz = 3
"""
    match parseAndCheck source "test.fs" with
    | Success result ->
        let bindingNames =
            Traversal.foldPostOrder (fun names node ->
                match node.Kind with
                | SemanticKind.Binding(name, _, _) -> name :: names
                | _ -> names) [] result.Graph
        Assert.Contains("foo", bindingNames)
        Assert.Contains("bar", bindingNames)
        Assert.Contains("baz", bindingNames)
    | ParseFailure errors -> failwithf "Parse failed: %A" errors
    | CheckFailure result -> failwithf "Check failed with diagnostics: %A" result.Diagnostics

//-------------------------------------------------------------------------
// Module Structure Tests
//-------------------------------------------------------------------------

[<Fact>]
let ``parseAndCheck - preserves module name`` () =
    let source = """
module MyTestModule
let x = 1
"""
    match parseAndCheck source "test.fs" with
    | Success result ->
        // Check that we have the module in the modules map
        Assert.True(result.Graph.Modules.Count > 0, "Should have modules")
        let hasModule =
            result.Graph.Modules
            |> Map.exists (fun k _ -> k.Contains("MyTestModule"))
        Assert.True(hasModule, sprintf "Should have module 'MyTestModule', got: %A" (result.Graph.Modules |> Map.keys |> Seq.toList))
    | ParseFailure errors -> failwithf "Parse failed: %A" errors
    | CheckFailure result -> failwithf "Check failed with diagnostics: %A" result.Diagnostics

//-------------------------------------------------------------------------
// Type Attachment Tests
//-------------------------------------------------------------------------

[<Fact>]
let ``parseAndCheck - bindings have types attached`` () =
    let source = """
module Test
let x = 42
"""
    match parseAndCheck source "test.fs" with
    | Success result ->
        let bindings = getBindings result
        Assert.True(bindings.Length > 0, "Should have bindings")
        // Check that bindings have non-unit types
        for binding in bindings do
            match binding.ResolvedType with
            | Some ty ->
                // Should have a real type, not just Unknown
                match ty with
                | NativeType.Unknown _ -> failwithf "Binding should have resolved type, got Unknown"
                | _ -> ()
            | None -> failwithf "Binding %A should have a type attached" binding.Kind
    | ParseFailure errors -> failwithf "Parse failed: %A" errors
    | CheckFailure result -> failwithf "Check failed with diagnostics: %A" result.Diagnostics
