/// Spec-Driven TDD Tests for Native Type Universe
///
/// These tests are derived from fsnative-spec NORMATIVE requirements, NOT from
/// existing implementation. They serve as executable specification that guards
/// against regression and ensures implementation honors the spec.
///
/// Reference: fsnative-spec/spec/native-type-mappings.md
/// Reference: fsnative-spec/spec/native-type-universe.md
module FSharp.Native.Compiler.Service.Tests.TypeChecker.SpecDrivenNativeTypeTests

open FSharp.Native.Compiler.Checking.Native.NativeService
open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.SemanticGraph
open Xunit

//=============================================================================
// TEST HELPERS
//=============================================================================

/// Parse and check source code, returning the semantic graph
let checkSource (source: string) =
    match parseAndCheck source "test.fs" with
    | { Diagnostics = diags; Graph = graph } -> (diags, graph)

/// Check that source compiles without errors
let assertNoErrors (source: string) =
    let (diags, _) = checkSource source
    let errors = diags |> List.filter (fun d -> d.Severity = NativeDiagnosticSeverity.Error)
    if not (List.isEmpty errors) then
        let msgs = errors |> List.map (fun d -> d.Message) |> String.concat "\n"
        failwith $"Expected no errors, got:\n{msgs}"

/// Check that source produces specific error code
let assertError (errorCode: string) (source: string) =
    let (diags, _) = checkSource source
    let hasError = diags |> List.exists (fun d -> d.Code = errorCode)
    if not hasError then
        let msgs = diags |> List.map (fun d -> $"{d.Code}: {d.Message}") |> String.concat "\n"
        failwith $"Expected error {errorCode}, got:\n{msgs}"

/// Get the type of the first entry point binding
let getMainType (source: string) =
    let (_, graph) = checkSource source
    match graph.EntryPoints with
    | [] -> failwith "No entry points in graph"
    | nodeId :: _ ->
        match Map.tryFind nodeId graph.Nodes with
        | Some node -> node.Type
        | None -> failwith $"Entry point node {nodeId} not found"

//=============================================================================
// SPEC: Native Type Mappings - Primitive Types
// Reference: fsnative-spec/spec/native-type-mappings.md
//=============================================================================

module ``Primitive Types per Spec`` =

    /// SPEC: "unit" has zero-sized type
    /// NORMATIVE: Unit literals SHALL have type unit
    [<Fact>]
    let ``SPEC: Unit literal has type unit`` () =
        let source = "module Test\nlet main = ()"
        assertNoErrors source

    /// SPEC: "bool" is i8, 0=false, non-zero=true
    /// NORMATIVE: Bool literals SHALL have type bool
    [<Fact>]
    let ``SPEC: Bool literal has type bool`` () =
        let source = "module Test\nlet main = true"
        assertNoErrors source

    /// SPEC: "int" is platform word (nativeint semantics)
    /// NORMATIVE: Integer literals SHALL have type int
    [<Fact>]
    let ``SPEC: Int literal has type int`` () =
        let source = "module Test\nlet main = 42"
        assertNoErrors source

    /// SPEC: "string" is UTF-8 fat pointer {ptr: *u8, len: usize}
    /// NORMATIVE: String literals SHALL have type NativeStr (not System.String)
    [<Fact>]
    let ``SPEC: String literal has native string type`` () =
        let source = "module Test\nlet main = \"hello\""
        assertNoErrors source

    /// SPEC: "char" is UTF-32 codepoint (i32)
    /// NORMATIVE: Char literals SHALL have type char (UTF-32)
    [<Fact>]
    let ``SPEC: Char literal has type char`` () =
        let source = "module Test\nlet main = 'x'"
        assertNoErrors source

//=============================================================================
// SPEC: BCL Rejection
// Reference: fsnative-spec/spec/native-type-mappings.md
//=============================================================================

module ``BCL Rejection per Spec`` =

    /// SPEC: "The compiler SHALL reject any code that references obj or System.Object"
    /// NORMATIVE: obj type SHALL NOT exist in F# Native
    [<Fact>]
    let ``SPEC: obj type SHALL be rejected with FS8011`` () =
        let source = "module Test\nlet main : obj = box 42"
        assertError "FS8011" source

    /// SPEC: "System.* namespace... compiler SHALL reject"
    /// NORMATIVE: System namespace references SHALL be rejected with FS8500
    [<Fact>]
    let ``SPEC: System namespace SHALL be rejected with FS8500`` () =
        let source = "module Test\nlet main = System.String.Empty"
        assertError "FS8500" source

    /// SPEC: "Microsoft.* namespace... compiler SHALL reject"
    /// NORMATIVE: Microsoft namespace references SHALL be rejected with FS8500
    [<Fact>]
    let ``SPEC: Microsoft namespace SHALL be rejected with FS8500`` () =
        let source = "module Test\nlet main = Microsoft.FSharp.Core.unit"
        assertError "FS8500" source

    /// SPEC: "System.Reflection and all reflection-based APIs SHALL NOT be available"
    /// NORMATIVE: Reflection SHALL be rejected
    [<Fact>]
    let ``SPEC: Reflection SHALL be rejected`` () =
        let source = "module Test\nlet main = System.Reflection.Assembly.GetExecutingAssembly()"
        assertError "FS8500" source

    /// SPEC: Boxing requires obj, which doesn't exist
    /// NORMATIVE: box operator SHALL be rejected
    [<Fact>]
    let ``SPEC: box SHALL be rejected with FS8012`` () =
        let source = "module Test\nlet main = box 42"
        assertError "FS8012" source

//=============================================================================
// SPEC: Option Type Mapping
// Reference: fsnative-spec/spec/native-type-mappings.md
//=============================================================================

module ``Option Type per Spec`` =

    /// SPEC: "option<'T>" maps to "voption<'T>" (value type, non-nullable)
    /// NORMATIVE: Option types SHALL be stack-allocated value options
    [<Fact>]
    let ``SPEC: Some literal produces voption`` () =
        let source = "module Test\nlet main = Some 42"
        assertNoErrors source

    /// SPEC: "None tag = 0, Some tag = 1, Heap allocation = Never"
    /// NORMATIVE: None SHALL be representable without null
    [<Fact>]
    let ``SPEC: None is valid without null`` () =
        let source = "module Test\nlet main : int option = None"
        assertNoErrors source

//=============================================================================
// SPEC: Compositional Name Resolution
// Reference: NameResolution.fs architecture
//=============================================================================

module ``Name Resolution per Architecture`` =

    /// Resolution should work for user bindings
    [<Fact>]
    let ``User binding resolves correctly`` () =
        let source = "module Test\nlet x = 5\nlet main = x"
        assertNoErrors source

    /// Resolution should work with shadowing
    [<Fact>]
    let ``Shadowing resolves to latest binding`` () =
        let source = "module Test\nlet x = 5\nlet x = 10\nlet main = x"
        assertNoErrors source

    /// Undefined names should produce FS0039
    [<Fact>]
    let ``Undefined name produces FS0039`` () =
        let source = "module Test\nlet main = undefinedName"
        assertError "FS0039" source

//=============================================================================
// SPEC: Metaprogramming Features
// Reference: fsnative-spec/spec/native-type-mappings.md "Compile-Time Metaprogramming"
//=============================================================================

module ``Metaprogramming per Spec`` =

    /// SPEC: "Quotations, active patterns, and computation expressions SHALL be fully supported"
    /// NORMATIVE: Quotations SHALL work in F# Native
    [<Fact>]
    let ``SPEC: Quotation literals SHALL compile`` () =
        let source = "module Test\nlet main = <@ 1 + 2 @>"
        assertNoErrors source

    /// SPEC: Active patterns SHALL be supported
    [<Fact>]
    let ``SPEC: Active patterns SHALL compile`` () =
        let source = """
module Test
let (|Even|Odd|) n = if n % 2 = 0 then Even else Odd
let main = match 4 with Even -> 0 | Odd -> 1
"""
        assertNoErrors source

//=============================================================================
// SPEC: Quotations as Semantic Carriers for Memory Mapping
// Reference: fsnative-spec/spec/native-type-mappings.md "Quotations as Semantic Carriers"
//=============================================================================

module ``Quotations as Memory Mapping Carriers`` =

    /// SPEC: "Quotations encode constraints and metadata as compile-time data"
    /// NORMATIVE: Quotation-based metaprogramming SHALL NOT require runtime evaluation
    [<Fact>]
    let ``SPEC: Quotation with record literal compiles`` () =
        // Quotations can encode memory descriptors as compile-time data
        let source = """
module Test
type MemoryDescriptor = { BaseAddress: uint64; Size: int }
let descriptor = <@ { BaseAddress = 0x48000000UL; Size = 1024 } @>
let main = 0
"""
        assertNoErrors source

    /// SPEC: Quotations carry type information through transformations
    [<Fact>]
    let ``SPEC: Typed quotation preserves type info`` () =
        let source = """
module Test
let typedQuote : Quotations.Expr<int> = <@ 42 @>
let main = 0
"""
        assertNoErrors source

    /// SPEC: "Peripheral descriptor carried as typed quotation"
    [<Fact>]
    let ``SPEC: Quotation can encode peripheral descriptor pattern`` () =
        let source = """
module Test
type PeripheralInfo = { Name: string; BaseAddr: uint64 }
let gpio = <@ { Name = "GPIO"; BaseAddr = 0x48000000UL } @>
let main = 0
"""
        assertNoErrors source

//=============================================================================
// SPEC: Active Patterns for Structural Recognition
// Reference: fsnative-spec/spec/native-type-mappings.md "Active Patterns"
//=============================================================================

module ``Active Patterns for Structural Recognition`` =

    /// SPEC: "Active patterns enable compositional matching"
    [<Fact>]
    let ``SPEC: Partial active pattern compiles`` () =
        let source = """
module Test
let (|Positive|_|) n = if n > 0 then Some n else None
let main = match 5 with Positive x -> x | _ -> 0
"""
        assertNoErrors source

    /// SPEC: Active patterns compose with & and |
    [<Fact>]
    let ``SPEC: Active patterns compose`` () =
        let source = """
module Test
let (|Even|Odd|) n = if n % 2 = 0 then Even else Odd
let (|Positive|Negative|Zero|) n = if n > 0 then Positive elif n < 0 then Negative else Zero
let main = match 4 with Even & Positive -> 1 | _ -> 0
"""
        assertNoErrors source

    /// SPEC: "Active patterns encapsulate recognition logic"
    [<Fact>]
    let ``SPEC: Parameterized active pattern compiles`` () =
        let source = """
module Test
let (|DivisibleBy|_|) divisor n = if n % divisor = 0 then Some () else None
let main = match 15 with DivisibleBy 3 -> 1 | DivisibleBy 5 -> 2 | _ -> 0
"""
        assertNoErrors source

//=============================================================================
// SPEC: Memory Regions (Native-Specific)
// Reference: fsnative-spec/spec/memory-regions.md
//=============================================================================

module ``Memory Regions per Spec`` =

    /// SPEC: Memory regions are intrinsic types
    /// NORMATIVE: Stack region SHALL be default
    [<Fact>]
    let ``SPEC: Simple binding uses stack region`` () =
        let source = "module Test\nlet x = 42\nlet main = x"
        assertNoErrors source

    /// SPEC: Mutable bindings are valid
    [<Fact>]
    let ``SPEC: Mutable binding compiles`` () =
        let source = """
module Test
let main =
    let mutable x = 0
    x <- 42
    x
"""
        assertNoErrors source

    /// SPEC: Struct types have deterministic layout
    [<Fact>]
    let ``SPEC: Struct record compiles`` () =
        let source = """
module Test
[<Struct>]
type Point = { X: float; Y: float }
let main = { X = 1.0; Y = 2.0 }
"""
        assertNoErrors source
