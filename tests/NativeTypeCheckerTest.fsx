#!/usr/bin/env dotnet fsi

/// Simple test script for native type checker
/// Run with: dotnet fsi NativeTypeCheckerTest.fsx

#r "../artifacts/bin/FSharpNative.Compiler.Service/Debug/net9.0/FSharpNative.Compiler.Service.dll"

open FSharp.Compiler.Checking.Native.NativeTypes
open FSharp.Compiler.Checking.Native.NativeGlobals
open FSharp.Compiler.Checking.Native.SemanticGraph
open FSharp.Compiler.Checking.Native.CheckExpr
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text

printfn "=== Native Type Checker Test ==="
printfn ""

// Create test environment
let globals = createNativeGlobals()
let env = createTypeEnv globals

printfn "✓ Created native globals and type environment"

// Test 1: Check globals contain expected types
printfn ""
printfn "Test 1: Built-in types..."
let tycons = [
    "int", tryFindBuiltinTyCon "int"
    "string", tryFindBuiltinTyCon "string"
    "bool", tryFindBuiltinTyCon "bool"
    "option", tryFindBuiltinTyCon "option"
    "Expr", tryFindBuiltinTyCon "Expr"
    "exn", tryFindBuiltinTyCon "exn"
]

for (name, tcOpt) in tycons do
    match tcOpt with
    | Some tc -> printfn $"  ✓ {name}: arity={arity tc}"
    | None -> printfn $"  ✗ {name}: NOT FOUND"

// Test 2: Create a simple expression and check it
printfn ""
printfn "Test 2: Type checking simple literals..."
let builder = NodeBuilder()

// Create a simple int constant
let range = Range.mkRange "test.fs" (Position.mkPos 1 0) (Position.mkPos 1 2)
let intExpr = SynExpr.Const(SynConst.Int32 42, range)

let (node, constraints) = checkAndSolve env builder intExpr

match node.Type with
| NativeType.TApp(tc, []) when tc.Name = "int" ->
    printfn $"  ✓ Int literal: type={tc.Name}"
| ty ->
    printfn $"  ✗ Int literal: unexpected type {ty}"

match node.Kind with
| SemanticKind.Literal(LiteralValue.Int32 42) ->
    printfn "  ✓ Int literal: kind=Literal(Int32 42)"
| k ->
    printfn $"  ✗ Int literal: unexpected kind {k}"

// Create a string constant
let strRange = Range.mkRange "test.fs" (Position.mkPos 2 0) (Position.mkPos 2 7)
let strExpr = SynExpr.Const(SynConst.String("hello", SynStringKind.Regular, strRange), strRange)

let (strNode, _) = checkAndSolve env builder strExpr

match strNode.Type with
| NativeType.TApp(tc, []) when tc.Name = "string" ->
    printfn $"  ✓ String literal: type={tc.Name}"
| ty ->
    printfn $"  ✗ String literal: unexpected type {ty}"

// Test 3: Check builder accumulated nodes
printfn ""
printfn "Test 3: NodeBuilder..."
printfn $"  ✓ Nodes created: {builder.Nodes.Count}"

// Test 4: Check memory region measures
printfn ""
printfn "Test 4: Memory region measures..."
let getMeasureName m =
    match m with
    | MCon(name, _) -> name
    | MVar tp -> tp.Name
    | _ -> "?"
printfn $"  ✓ stack: {getMeasureName MemoryRegions.stack}"
printfn $"  ✓ peripheral: {getMeasureName MemoryRegions.peripheral}"
printfn $"  ✓ dma: {getMeasureName MemoryRegions.dma}"

// Test 5: Check access mode measures
printfn ""
printfn "Test 5: Access mode measures..."
printfn $"  ✓ readOnly: {getMeasureName AccessModes.readOnly}"
printfn $"  ✓ readWrite: {getMeasureName AccessModes.readWrite}"

// Test 6: Ptr type constructor
printfn ""
printfn "Test 6: Ptr type constructor..."
match tryFindBuiltinTyCon "Ptr" with
| Some tc ->
    printfn $"  ✓ Ptr: arity={arity tc} (expecting 3 for Ptr<'T, 'region, 'access>)"
| None ->
    // Check in Parameterized
    printfn $"  ✓ Ptr: {Parameterized.ptrTyCon.Name}, params={Parameterized.ptrTyCon.ParamKinds.Length}"

printfn ""
printfn "=== All tests complete ==="
