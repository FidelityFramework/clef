/// Tests for the native type checker (CCS)
module FSharp.Native.Compiler.Service.Tests.TypeChecker.NativeTypeCheckerTests

open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.NativeGlobals
open FSharp.Native.Compiler.Checking.Native.SemanticGraph
open FSharp.Native.Compiler.Checking.Native.CheckExpr
open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Text
open Xunit

//-------------------------------------------------------------------------
// Test Helpers
//-------------------------------------------------------------------------

/// Create a test environment
let createTestEnv () =
    let globals = createNativeGlobals()
    createTypeEnv globals

/// Parse a simple expression (just for testing)
/// In real use, this comes from FCS parsing
let parseSimpleExpr (source: string) : SynExpr =
    // For testing, we'll create synthetic SynExpr nodes
    // In production, FCS parser provides these
    let range = Range.mkRange "test.fs" (Position.mkPos 1 0) (Position.mkPos 1 (source.Length))

    // Handle simple literals
    if source = "()" then
        SynExpr.Const(SynConst.Unit, range)
    elif source = "true" then
        SynExpr.Const(SynConst.Bool true, range)
    elif source = "false" then
        SynExpr.Const(SynConst.Bool false, range)
    elif source.StartsWith("\"") && source.EndsWith("\"") then
        let s = source.Substring(1, source.Length - 2)
        SynExpr.Const(SynConst.String(s, SynStringKind.Regular, range), range)
    else
        // Try to parse as int
        match System.Int32.TryParse(source) with
        | true, n -> SynExpr.Const(SynConst.Int32 n, range)
        | _ ->
            // Default to error
            SynExpr.FromParseError(
                SynExpr.Const(SynConst.Unit, range),
                range
            )

//-------------------------------------------------------------------------
// Type Checking Tests
//-------------------------------------------------------------------------

[<Fact>]
let ``Unit literal has unit type`` () =
    let env = createTestEnv()
    let builder = NodeBuilder()
    let expr = parseSimpleExpr "()"

    let (node, _constraints) = checkAndSolve env builder expr

    match node.Type with
    | NativeType.TApp(tc, []) when tc.Name = "unit" -> ()
    | ty -> failwith $"Expected unit type, got {ty}"

[<Fact>]
let ``Bool literal has bool type`` () =
    let env = createTestEnv()
    let builder = NodeBuilder()
    let expr = parseSimpleExpr "true"

    let (node, _constraints) = checkAndSolve env builder expr

    match node.Type with
    | NativeType.TApp(tc, []) when tc.Name = "bool" -> ()
    | ty -> failwith $"Expected bool type, got {ty}"

[<Fact>]
let ``Int literal has int type`` () =
    let env = createTestEnv()
    let builder = NodeBuilder()
    let expr = parseSimpleExpr "42"

    let (node, _constraints) = checkAndSolve env builder expr

    match node.Type with
    | NativeType.TApp(tc, []) when tc.Name = "int" -> ()
    | ty -> failwith $"Expected int type, got {ty}"

[<Fact>]
let ``String literal has string type`` () =
    let env = createTestEnv()
    let builder = NodeBuilder()
    let expr = parseSimpleExpr "\"hello\""

    let (node, _constraints) = checkAndSolve env builder expr

    match node.Type with
    | NativeType.TApp(tc, []) when tc.Name = "string" -> ()
    | ty -> failwith $"Expected string type, got {ty}"

[<Fact>]
let ``Semantic node has correct kind for literal`` () =
    let env = createTestEnv()
    let builder = NodeBuilder()
    let expr = parseSimpleExpr "42"

    let (node, _) = checkAndSolve env builder expr

    match node.Kind with
    | SemanticKind.Literal(LiteralValue.Int32 42) -> ()
    | k -> failwith $"Expected Int32 literal, got {k}"

[<Fact>]
let ``NodeBuilder tracks created nodes`` () =
    let env = createTestEnv()
    let builder = NodeBuilder()

    let expr1 = parseSimpleExpr "1"
    let expr2 = parseSimpleExpr "2"

    let _ = checkAndSolve env builder expr1
    let _ = checkAndSolve env builder expr2

    Assert.Equal(2, builder.Nodes.Count)

//-------------------------------------------------------------------------
// Globals Tests
//-------------------------------------------------------------------------

[<Fact>]
let ``NativeGlobals has all primitive types`` () =
    let globals = createNativeGlobals()

    Assert.NotNull(box globals.StringType)
    Assert.NotNull(box globals.IntType)
    Assert.NotNull(box globals.BoolType)
    Assert.NotNull(box globals.UnitType)
    Assert.NotNull(box globals.ExnType)

[<Fact>]
let ``tryFindBuiltinTyCon finds int`` () =
    match tryFindBuiltinTyCon "int" with
    | Some tc -> Assert.Equal("int", tc.Name)
    | None -> failwith "Expected to find int type"

[<Fact>]
let ``tryFindBuiltinTyCon finds option`` () =
    match tryFindBuiltinTyCon "option" with
    | Some tc ->
        Assert.Equal("option", tc.Name)
        Assert.Equal(1, tc.Arity)
    | None -> failwith "Expected to find option type"

[<Fact>]
let ``tryFindBuiltinTyCon finds Expr (quotation type)`` () =
    match tryFindBuiltinTyCon "Expr" with
    | Some tc ->
        Assert.Equal("Expr", tc.Name)
        Assert.Equal(1, tc.Arity)
    | None -> failwith "Expected to find Expr type"
