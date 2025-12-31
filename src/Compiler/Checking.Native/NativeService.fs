// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Public API for F# Native Compiler Services.
/// Provides native type checking for Firefly consumption.
///
/// This module builds a unified SemanticGraph where:
/// - Types are attached during construction (not post-hoc)
/// - Module structure is preserved
/// - Source locations are properly tracked
/// - Hard prune is applied before returning
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
// Diagnostic Helpers
//-------------------------------------------------------------------------

/// Convert unification errors to diagnostics
let private errorsToDiagnostics (errors: UnificationError list) : Diagnostic list =
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

/// Solve constraints and return diagnostics
let private solveAndGetDiagnostics (constraints: Constraint list) : Diagnostic list =
    match solveConstraints constraints with
    | Solved -> []
    | Deferred _ -> []  // Deferred SRTP constraints handled later
    | Failed errors -> errorsToDiagnostics errors

//-------------------------------------------------------------------------
// Entry Point Detection
//-------------------------------------------------------------------------

/// Determine entry points from checked nodes
let private findEntryPoints (nodes: SemanticNode list) : NodeId list =
    let candidates =
        nodes
        |> List.filter (fun node ->
            match node.Kind with
            | SemanticKind.Binding(name, _, _) when name = "main" -> true
            | SemanticKind.Application _ -> true
            | _ -> false
        )
        |> List.map (fun n -> n.Id)

    // If no explicit entry points, use all top-level nodes
    if List.isEmpty candidates then
        nodes |> List.map (fun n -> n.Id)
    else
        candidates

//-------------------------------------------------------------------------
// Graph Building Helpers
//-------------------------------------------------------------------------

/// Build a CheckResult from builder state and diagnostics
let private buildResult (builder: NodeBuilder) (topLevelNodes: SemanticNode list) (modulePaths: Map<ModulePath, NodeId list>) (diagnostics: Diagnostic list) : CheckResult =
    let entryPoints = findEntryPoints topLevelNodes

    let graph = {
        Nodes = builder.Nodes
        EntryPoints = entryPoints
        Modules = modulePaths
        Types = Map.empty  // TODO: Populate from type definitions
    }

    // Hard prune unreachable nodes (not soft-delete!)
    let prunedGraph = Reachability.pruneUnreachable graph

    {
        Graph = prunedGraph
        Diagnostics = diagnostics
    }

//-------------------------------------------------------------------------
// Type Checking: Expression Level
//-------------------------------------------------------------------------

/// Check a single expression and return a semantic node.
/// This is the low-level API for testing the type checker.
let checkExpression (expr: SynExpr) : CheckResult =
    let globals = createNativeGlobals()
    let env = createTypeEnv globals
    let builder = NodeBuilder()
    NodeId.reset()

    let node = checkExpr env builder expr
    let diagnostics = solveAndGetDiagnostics env.Constraints

    buildResult builder [node] Map.empty diagnostics

//-------------------------------------------------------------------------
// Type Checking: Binding Level
//-------------------------------------------------------------------------

/// Check a single let binding and return a semantic node.
let checkLetBinding (binding: SynBinding) : CheckResult =
    let globals = createNativeGlobals()
    let env = createTypeEnv globals
    let builder = NodeBuilder()
    NodeId.reset()

    let node = checkBinding env builder binding
    let diagnostics = solveAndGetDiagnostics env.Constraints

    buildResult builder [node] Map.empty diagnostics

//-------------------------------------------------------------------------
// Type Checking: Module Level
//-------------------------------------------------------------------------

/// Context for module checking - tracks current module path
type private ModuleContext = {
    Path: ModulePath
    IsRecursive: bool
}

/// Check a single module declaration
let rec private checkModuleDecl (env: TypeEnv) (builder: NodeBuilder) (ctx: ModuleContext) (decl: SynModuleDecl) : SemanticNode list =
    match decl with
    | SynModuleDecl.Let(isRec, bindings, bindingRange, _trivia) ->
        // Let bindings - check each binding
        // isRec affects how bindings can reference each other
        let range = rangeToSourceRange bindingRange
        bindings |> List.map (fun binding ->
            // For recursive bindings, we'd need to add all names to env first
            // For now, just check each binding
            let _ = isRec  // TODO: Handle recursive bindings properly
            let _ = range  // Range is already captured in binding
            checkBinding env builder binding
        )

    | SynModuleDecl.Expr(expr, exprRange) ->
        // Module-level expression (e.g., do expr)
        let _ = rangeToSourceRange exprRange  // Could be used for diagnostics
        [checkExpr env builder expr]

    | SynModuleDecl.Types(typeDefns, typesRange) ->
        // Type definitions
        let _ = rangeToSourceRange typesRange  // Range for the whole types block
        typeDefns |> List.map (fun typeDef ->
            let range = rangeToSourceRange typeDef.Range
            // TODO: Extract actual type name and kind from typeDef
            builder.Create(
                SemanticKind.TypeDef("type", TypeDefKind.ClassDef, []),
                env.Globals.UnitType,
                range
            )
        )

    | SynModuleDecl.NestedModule(moduleInfo, isRecursive, nestedDecls, _isContinued, moduleRange, _trivia) ->
        // Nested module - create ModuleDef node wrapping its contents
        let range = rangeToSourceRange moduleRange

        // Extract module name from moduleInfo
        let moduleName =
            let (SynComponentInfo(_, _, _, longId, _, _, _, _)) = moduleInfo
            longId |> List.map (fun id -> id.idText) |> String.concat "."

        // Create nested context with extended path
        let nestedPath = ctx.Path @ [moduleName]
        let nestedCtx = { Path = nestedPath; IsRecursive = isRecursive }

        // Check all declarations in the nested module
        let childNodes = checkModuleDecls env builder nestedCtx nestedDecls
        let childIds = childNodes |> List.map (fun n -> n.Id)

        // Create a ModuleDef node for the nested module
        let moduleNode = builder.Create(
            SemanticKind.ModuleDef(moduleName, childIds),
            env.Globals.UnitType,
            range,
            children = childIds
        )

        [moduleNode]

    | SynModuleDecl.Open _ ->
        // Open statements affect name resolution but don't produce semantic nodes
        // TODO: Track opened namespaces in environment for name resolution
        []

    | SynModuleDecl.HashDirective _ ->
        // Hash directives (#if, #nowarn, etc.) - preprocessing, no semantic nodes
        []

    | SynModuleDecl.ModuleAbbrev _ ->
        // Module abbreviations (module M = Long.Path) - affects name resolution
        // TODO: Track in environment
        []

    | SynModuleDecl.Attributes _ ->
        // Standalone attributes (assembly-level, etc.)
        // TODO: Capture for assembly metadata
        []

    | SynModuleDecl.Exception(exnDefn, exnRange) ->
        // Exception type definition
        let range = rangeToSourceRange exnRange
        // Extract exception name from definition
        let exnName =
            let (SynExceptionDefn(repr, _, _, _)) = exnDefn
            let (SynExceptionDefnRepr(_, unionCase, _, _, _, _)) = repr
            let (SynUnionCase(_, synIdent, _, _, _, _, _)) = unionCase
            let (SynIdent(ident, _)) = synIdent
            ident.idText
        [builder.Create(
            SemanticKind.TypeDef(exnName, TypeDefKind.ClassDef, []),
            env.Globals.ExnType,
            range
        )]

    | SynModuleDecl.NamespaceFragment _ ->
        // Namespace fragments are handled at a higher level in checkModuleOrNamespace
        []

/// Check a list of module declarations
and private checkModuleDecls (env: TypeEnv) (builder: NodeBuilder) (ctx: ModuleContext) (decls: SynModuleDecl list) : SemanticNode list =
    decls |> List.collect (checkModuleDecl env builder ctx)

/// Check a list of module declarations (public API)
let checkModuleDeclarations (decls: SynModuleDecl list) : CheckResult =
    let globals = createNativeGlobals()
    let env = createTypeEnv globals
    let builder = NodeBuilder()
    NodeId.reset()

    let ctx = { Path = []; IsRecursive = false }
    let nodes = checkModuleDecls env builder ctx decls
    let diagnostics = solveAndGetDiagnostics env.Constraints

    buildResult builder nodes Map.empty diagnostics

//-------------------------------------------------------------------------
// Type Checking: Module or Namespace Level
//-------------------------------------------------------------------------

/// Check a module or namespace and return its semantic nodes
let private checkModuleOrNamespace (env: TypeEnv) (builder: NodeBuilder) (moduleOrNs: SynModuleOrNamespace) : ModulePath * SemanticNode list =
    let (SynModuleOrNamespace(longId, isRecursive, kind, decls, _xmlDoc, _attribs, _accessibility, nsRange, _trivia)) = moduleOrNs

    // Build the module path from the long identifier
    let modulePath: ModulePath = longId |> List.map (fun id -> id.idText)
    let range = rangeToSourceRange nsRange

    // Determine if this is a namespace or module
    let isNamespace =
        match kind with
        | SynModuleOrNamespaceKind.NamedModule -> false
        | SynModuleOrNamespaceKind.AnonModule -> false
        | SynModuleOrNamespaceKind.DeclaredNamespace -> true
        | SynModuleOrNamespaceKind.GlobalNamespace -> true

    // Create context for checking declarations
    let ctx = { Path = modulePath; IsRecursive = isRecursive }

    // Check all declarations
    let contentNodes = checkModuleDecls env builder ctx decls

    if isNamespace then
        // Namespaces don't get a wrapper node - just return content
        (modulePath, contentNodes)
    else
        // Modules get a ModuleDef wrapper node
        let moduleName = modulePath |> List.tryLast |> Option.defaultValue ""
        let childIds = contentNodes |> List.map (fun n -> n.Id)

        let moduleNode = builder.Create(
            SemanticKind.ModuleDef(moduleName, childIds),
            env.Globals.UnitType,
            range,
            children = childIds
        )

        (modulePath, [moduleNode])

//-------------------------------------------------------------------------
// Type Checking: Full Implementation File
//-------------------------------------------------------------------------

/// Check a parsed implementation file
let checkImplFile (implFile: ParsedImplFileInput) : CheckResult =
    let (ParsedImplFileInput(fileName, _isScript, qualifiedNameOfFile, _hashDirectives, contents, _flags, _trivia, _identifiers)) = implFile

    let globals = createNativeGlobals()
    let env = createTypeEnv globals
    let builder = NodeBuilder()
    NodeId.reset()

    // Track which file we're processing (for diagnostics)
    let _ = fileName  // Could be added to CheckResult metadata
    let _ = qualifiedNameOfFile  // The qualified name can be used for module resolution

    // Process each module or namespace in the file
    let moduleResults = contents |> List.map (checkModuleOrNamespace env builder)

    // Collect all nodes and build module path mapping
    let allNodes = moduleResults |> List.collect snd
    let modulePaths =
        moduleResults
        |> List.map (fun (path, nodes) -> (path, nodes |> List.map (fun n -> n.Id)))
        |> Map.ofList

    let diagnostics = solveAndGetDiagnostics env.Constraints

    buildResult builder allNodes modulePaths diagnostics

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
