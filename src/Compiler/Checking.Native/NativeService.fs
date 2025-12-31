// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Public API for F# Native Compiler Services.
/// Provides native type checking for Firefly consumption.
///
/// CURRENT STATUS: Core type checking API. Parser integration pending.
/// For now, accepts SynExpr and SynModuleDecl directly.
/// Full parsing integration will be added when ready.
module FSharp.Native.Compiler.NativeService

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.Text
open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.NativeGlobals
open FSharp.Native.Compiler.Checking.Native.SemanticGraph
open FSharp.Native.Compiler.Checking.Native.CheckExpr
open FSharp.Native.Compiler.Checking.Native.Unify

//-------------------------------------------------------------------------
// Check Options
//-------------------------------------------------------------------------

/// Options for project checking
type CheckOptions = {
    /// Conditional compilation defines (e.g., ["DEBUG"; "TRACE"])
    Defines: string list
}

/// Default check options
let defaultCheckOptions = {
    Defines = []
}

//-------------------------------------------------------------------------
// Type Checking: Expression Level
//-------------------------------------------------------------------------

/// Check a single expression and return a semantic node.
/// This is the low-level API for testing the type checker.
let checkExpression (expr: SynExpr) : CheckResult =
    // Initialize native globals
    let globals = createNativeGlobals()
    let env = createTypeEnv globals
    let builder = NodeBuilder()

    // Reset state
    NodeId.reset()

    // Check the expression
    let node = checkExpr env builder expr

    // Solve any remaining constraints
    let diagnostics =
        match solveConstraints env.Constraints with
        | Solved -> []
        | Deferred _ -> []
        | Failed errors ->
            errors |> List.map (fun e ->
                let range =
                    match e with
                    | TypeMismatch(_, _, r) -> r
                    | InfiniteType(_, _, r) -> r
                    | ArityMismatch(_, _, r) -> r
                    | TupleLengthMismatch(_, _, r) -> r
                    | TupleKindMismatch(_, _, r) -> r
                    | ByrefKindMismatch(_, _, r) -> r
                {
                    Severity = DiagnosticSeverity.Error
                    Code = "FS0001"
                    Message = formatError e
                    Range = range
                    RelatedNodes = []
                }
            )

    // Build the graph
    let graph = {
        Nodes = builder.Nodes
        EntryPoints = [node.Id]
        Modules = Map.empty
        Types = Map.empty
    }

    {
        Graph = graph
        Diagnostics = diagnostics
    }

//-------------------------------------------------------------------------
// Type Checking: Binding Level
//-------------------------------------------------------------------------

/// Check a single let binding and return a semantic node.
let checkLetBinding (binding: SynBinding) : CheckResult =
    // Initialize native globals
    let globals = createNativeGlobals()
    let env = createTypeEnv globals
    let builder = NodeBuilder()

    // Reset state
    NodeId.reset()

    // Check the binding
    let node = checkBinding env builder binding

    // Solve constraints
    let diagnostics =
        match solveConstraints env.Constraints with
        | Solved -> []
        | Deferred _ -> []
        | Failed errors ->
            errors |> List.map (fun e ->
                let range =
                    match e with
                    | TypeMismatch(_, _, r) -> r
                    | InfiniteType(_, _, r) -> r
                    | ArityMismatch(_, _, r) -> r
                    | TupleLengthMismatch(_, _, r) -> r
                    | TupleKindMismatch(_, _, r) -> r
                    | ByrefKindMismatch(_, _, r) -> r
                {
                    Severity = DiagnosticSeverity.Error
                    Code = "FS0001"
                    Message = formatError e
                    Range = range
                    RelatedNodes = []
                }
            )

    // Build the graph
    let graph = {
        Nodes = builder.Nodes
        EntryPoints = [node.Id]
        Modules = Map.empty
        Types = Map.empty
    }

    {
        Graph = graph
        Diagnostics = diagnostics
    }

//-------------------------------------------------------------------------
// Type Checking: Module Level
//-------------------------------------------------------------------------

/// Check a list of module declarations
let rec private checkModuleDecls (env: TypeEnv) (builder: NodeBuilder) (decls: SynModuleDecl list) : SemanticNode list =
    decls |> List.collect (fun decl -> checkModuleDecl env builder decl)

/// Check a single module declaration
and private checkModuleDecl (env: TypeEnv) (builder: NodeBuilder) (decl: SynModuleDecl) : SemanticNode list =
    match decl with
    | SynModuleDecl.Let(_isRec, bindings, _range, _trivia) ->
        // Check let bindings
        bindings |> List.map (fun binding ->
            checkBinding env builder binding
        )

    | SynModuleDecl.Expr(expr, _range) ->
        // Check a module-level expression
        [checkExpr env builder expr]

    | SynModuleDecl.Types(typeDefns, _range) ->
        // Type definitions - for now, just create placeholder nodes
        typeDefns |> List.map (fun typeDef ->
            let range = rangeToSourceRange typeDef.Range
            builder.Create(
                SemanticKind.TypeDef("type", TypeDefKind.ClassDef, []),
                env.Globals.UnitType,
                range
            )
        )

    | SynModuleDecl.NestedModule(info, isRec, decls, isContinued, range, trivia) ->
        // Recursively check nested module
        checkModuleDecls env builder decls

    | SynModuleDecl.Open _ ->
        // Open statements don't produce semantic nodes
        []

    | SynModuleDecl.HashDirective _ ->
        // Hash directives don't produce semantic nodes
        []

    | SynModuleDecl.ModuleAbbrev _ ->
        // Module abbreviations don't produce semantic nodes
        []

    | SynModuleDecl.Attributes _ ->
        // Standalone attributes don't produce semantic nodes for now
        []

    | SynModuleDecl.Exception(exnDefn, range) ->
        // Exception definitions - placeholder
        let range = rangeToSourceRange range
        [builder.Create(
            SemanticKind.TypeDef("exception", TypeDefKind.ClassDef, []),
            env.Globals.ExnType,
            range
        )]

    | SynModuleDecl.NamespaceFragment _ ->
        // Namespace fragments are handled at a higher level
        []

/// Check a list of module declarations (public API)
let checkModuleDeclarations (decls: SynModuleDecl list) : CheckResult =
    // Initialize native globals
    let globals = createNativeGlobals()
    let env = createTypeEnv globals
    let builder = NodeBuilder()

    // Reset state
    NodeId.reset()

    // Check all declarations
    let nodes = checkModuleDecls env builder decls

    // Solve constraints
    let diagnostics =
        match solveConstraints env.Constraints with
        | Solved -> []
        | Deferred _ -> []
        | Failed errors ->
            errors |> List.map (fun e ->
                let range =
                    match e with
                    | TypeMismatch(_, _, r) -> r
                    | InfiniteType(_, _, r) -> r
                    | ArityMismatch(_, _, r) -> r
                    | TupleLengthMismatch(_, _, r) -> r
                    | TupleKindMismatch(_, _, r) -> r
                    | ByrefKindMismatch(_, _, r) -> r
                {
                    Severity = DiagnosticSeverity.Error
                    Code = "FS0001"
                    Message = formatError e
                    Range = range
                    RelatedNodes = []
                }
            )

    // Find entry points
    let entryPoints =
        nodes
        |> List.filter (fun node ->
            match node.Kind with
            | SemanticKind.Binding(name, _, _) when name = "main" -> true
            | SemanticKind.Application _ -> true
            | _ -> false
        )
        |> List.map (fun n -> n.Id)

    // Build the graph
    let graph = {
        Nodes = builder.Nodes
        EntryPoints = if List.isEmpty entryPoints then nodes |> List.map (fun n -> n.Id) else entryPoints
        Modules = Map.empty
        Types = Map.empty
    }

    // Hard prune unreachable nodes
    let prunedGraph = Reachability.pruneUnreachable graph

    {
        Graph = prunedGraph
        Diagnostics = diagnostics
    }

//-------------------------------------------------------------------------
// Type Checking: Full Module (with parsing from ParsedInput)
//-------------------------------------------------------------------------

/// Check a parsed implementation file
let checkImplFile (implFile: ParsedImplFileInput) : CheckResult =
    let (ParsedImplFileInput(fileName, isScript, qualifiedNameOfFile, hashDirectives, contents, flags, trivia, identifiers)) = implFile

    // Initialize native globals
    let globals = createNativeGlobals()
    let env = createTypeEnv globals
    let builder = NodeBuilder()

    // Reset state
    NodeId.reset()

    // Process each module or namespace
    let allNodes =
        contents |> List.collect (fun moduleOrNs ->
            let (SynModuleOrNamespace(longId, isRec, kind, decls, xmlDoc, attribs, accessibility, range, trivia)) = moduleOrNs
            checkModuleDecls env builder decls
        )

    // Solve constraints
    let diagnostics =
        match solveConstraints env.Constraints with
        | Solved -> []
        | Deferred _ -> []
        | Failed errors ->
            errors |> List.map (fun e ->
                let range =
                    match e with
                    | TypeMismatch(_, _, r) -> r
                    | InfiniteType(_, _, r) -> r
                    | ArityMismatch(_, _, r) -> r
                    | TupleLengthMismatch(_, _, r) -> r
                    | TupleKindMismatch(_, _, r) -> r
                    | ByrefKindMismatch(_, _, r) -> r
                {
                    Severity = DiagnosticSeverity.Error
                    Code = "FS0001"
                    Message = formatError e
                    Range = range
                    RelatedNodes = []
                }
            )

    // Find entry points
    let entryPoints =
        allNodes
        |> List.filter (fun node ->
            match node.Kind with
            | SemanticKind.Binding(name, _, _) when name = "main" -> true
            | SemanticKind.Application _ -> true
            | _ -> false
        )
        |> List.map (fun n -> n.Id)

    // Build the graph
    let graph = {
        Nodes = builder.Nodes
        EntryPoints = if List.isEmpty entryPoints then allNodes |> List.map (fun n -> n.Id) else entryPoints
        Modules = Map.empty
        Types = Map.empty
    }

    // Hard prune unreachable nodes
    let prunedGraph = Reachability.pruneUnreachable graph

    {
        Graph = prunedGraph
        Diagnostics = diagnostics
    }

/// Check parsed input (implementation or signature file)
let checkParsedInput (input: ParsedInput) : CheckResult =
    match input with
    | ParsedInput.ImplFile implFile -> checkImplFile implFile
    | ParsedInput.SigFile _ ->
        // Signature files not yet supported
        {
            Graph = { Nodes = Map.empty; EntryPoints = []; Modules = Map.empty; Types = Map.empty }
            Diagnostics = [{
                Severity = DiagnosticSeverity.Warning
                Code = "FS0000"
                Message = "Signature files not yet supported in native checker"
                Range = dummyRange
                RelatedNodes = []
            }]
        }

//-------------------------------------------------------------------------
// Utilities
//-------------------------------------------------------------------------

/// Get all bindings from a check result
let getBindings (result: CheckResult) : SemanticNode list =
    SemanticGraph.bindings result.Graph

/// Get a node by ID from a check result
let getNode (id: NodeId) (result: CheckResult) : SemanticNode option =
    SemanticGraph.tryGetNode id result.Graph

/// Check if the result has any errors
let hasErrors (result: CheckResult) : bool =
    CheckResult.hasErrors result

/// Get the native globals (for type reference)
let getNativeGlobals () : NativeGlobals =
    createNativeGlobals()

/// Create a fresh type environment
let createFreshTypeEnv () : TypeEnv =
    let globals = createNativeGlobals()
    createTypeEnv globals
