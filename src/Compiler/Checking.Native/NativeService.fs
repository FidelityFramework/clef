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
open FSharp.Native.Compiler.DiagnosticsLogger
open FSharp.Native.Compiler.Features
open FSharp.Native.Compiler.Lexhelp
open FSharp.Native.Compiler.UnicodeLexing
open FSharp.Native.Compiler.LexFilter
open FSharp.Native.Compiler.IO
open FSharp.Native.Compiler.Xml
open FSharp.Native.Compiler.SyntaxTrivia
open Internal.Utilities.Text.Lexing
open Internal.Utilities

//-------------------------------------------------------------------------
// Parsing
//-------------------------------------------------------------------------

/// Parse options for the parser
type ParseOptions = {
    /// Conditional compilation defines (e.g., ["DEBUG"; "TRACE"])
    Defines: string list
    /// Whether to use indentation-aware syntax (default: true)
    IndentationAware: bool
}

/// Default parse options
let defaultParseOptions = {
    Defines = []
    IndentationAware = true
}

/// Parse result containing either success or error
type ParseResult =
    | ParseSuccess of ParsedInput
    | ParseError of errors: string list

/// Convert ParsedImplFileFragment to SynModuleOrNamespace
let private fragmentToModuleOrNamespace (fragment: ParsedImplFileFragment) : SynModuleOrNamespace =
    match fragment with
    | ParsedImplFileFragment.AnonModule(decls, range) ->
        // Anonymous module - create a module with empty name
        SynModuleOrNamespace(
            [],  // longId - empty for anonymous
            false,  // isRecursive
            SynModuleOrNamespaceKind.AnonModule,
            decls,
            PreXmlDoc.Empty,
            [],  // attribs
            None,  // accessibility
            range,
            { LeadingKeyword = SynModuleOrNamespaceLeadingKeyword.None }
        )
    | ParsedImplFileFragment.NamedModule namedModule ->
        namedModule
    | ParsedImplFileFragment.NamespaceFragment(longId, isRecursive, kind, decls, xmlDoc, attributes, range, trivia) ->
        SynModuleOrNamespace(
            longId,
            isRecursive,
            kind,
            decls,
            xmlDoc,
            attributes,
            None,  // accessibility
            range,
            trivia
        )

/// Convert ParsedImplFile to ParsedImplFileInput
let private implFileToInput (fileName: string) (implFile: ParsedImplFile) : ParsedImplFileInput =
    let (ParsedImplFile(hashDirectives, fragments)) = implFile

    // Convert fragments to SynModuleOrNamespace list
    let contents = fragments |> List.map fragmentToModuleOrNamespace

    // Create qualified name from file name
    let baseName = System.IO.Path.GetFileNameWithoutExtension(fileName)
    let qualifiedName = QualifiedNameOfFile(Ident(baseName, Range.range0))

    ParsedImplFileInput(
        fileName,
        false,  // isScript
        qualifiedName,
        hashDirectives,
        contents,
        (true, false),  // flags: (isLastCompiland, isExe)
        { ConditionalDirectives = []; WarnDirectives = []; CodeComments = [] },  // trivia
        Set.empty  // identifiers
    )

/// Parse F# source code from a string.
/// This is the entry point for testing the full pipeline from source to SemanticGraph.
///
/// Parameters:
///   source - The F# source code to parse
///   fileName - The file name to associate with the source (for error messages and ranges)
///   options - Parse options (defaults to defaultParseOptions)
///
/// Returns:
///   ParseResult - Either ParseSuccess with the ParsedInput, or ParseError with error messages
let parseString (source: string) (fileName: string) (options: ParseOptions) : ParseResult =
    try
        // Create the lexbuf from the source string
        let strictIndentation = if options.IndentationAware then Some true else None
        let lexbuf = StringAsLexbuf(false, LanguageVersion.Default, strictIndentation, source)

        // Set up position info with the file name
        resetLexbufPos fileName lexbuf

        // Create the diagnostics logger for capturing errors
        let diagnosticsLogger = CapturingDiagnosticsLogger("parseString")

        // Create lexer arguments
        let resourceManager = LexResourceManager()
        let indentationSyntaxStatus = IndentationAwareSyntaxStatus(options.IndentationAware, warn = true)
        let lexargs = mkLexargs(
            options.Defines,
            indentationSyntaxStatus,
            resourceManager,
            [],  // ifdefStack
            diagnosticsLogger,
            PathMap.empty,  // pathMap
            true  // applyLineDirectives
        )

        // Create the raw lexer function
        // skipWhitespaceTokens = true (as in FCS) - critical for proper parsing
        let skipWhitespaceTokens = true
        let rawLexer (lexbuf: LexBuffer<char>) =
            FSharp.Native.Compiler.Lexer.token lexargs skipWhitespaceTokens lexbuf

        // Create the LexFilter for indentation-aware parsing
        let lexFilter = LexFilter(
            indentationSyntaxStatus,
            false,  // compilingFSharpCore
            rawLexer,
            lexbuf,
            false   // debug
        )

        // Create the token function for the parser
        let tokenFunc (_lexbuf: LexBuffer<char>) =
            lexFilter.GetToken()

        // Parse the implementation file
        let parsedImplFile = FSharp.Native.Compiler.Parser.implementationFile tokenFunc lexbuf

        // Debug: Print parsed fragments
        let (ParsedImplFile(hashDirectives, fragments)) = parsedImplFile
        printfn "[FNCS Parse Debug] Parsed %d fragments, %d hash directives" (List.length fragments) (List.length hashDirectives)
        for i, frag in List.indexed fragments do
            match frag with
            | ParsedImplFileFragment.AnonModule(decls, range) ->
                printfn "[FNCS Parse Debug]   Fragment %d: AnonModule with %d decls at %A" i (List.length decls) range
            | ParsedImplFileFragment.NamedModule modOrNs ->
                let (SynModuleOrNamespace(longId, _, _kind, decls, _, _, _, _, _)) = modOrNs
                let name = longId |> List.map (fun id -> id.idText) |> String.concat "."
                printfn "[FNCS Parse Debug]   Fragment %d: NamedModule '%s' with %d decls" i name (List.length decls)
            | ParsedImplFileFragment.NamespaceFragment(longId, _, _, decls, _, _, _, _) ->
                let name = longId |> List.map (fun id -> id.idText) |> String.concat "."
                printfn "[FNCS Parse Debug]   Fragment %d: NamespaceFragment '%s' with %d decls" i name (List.length decls)

        // Convert to ParsedImplFileInput and wrap in ParsedInput
        let implFileInput = implFileToInput fileName parsedImplFile
        let parsedInput = ParsedInput.ImplFile implFileInput

        // Check for diagnostics - convert any errors
        let errors =
            diagnosticsLogger.Diagnostics
            |> List.choose (fun diag ->
                if diag.Phase = BuildPhase.Parse then
                    Some (sprintf "%s" (diag.Exception.Message))
                else
                    None)

        if List.isEmpty errors then
            ParseSuccess parsedInput
        else
            ParseError errors

    with
    | ex ->
        ParseError [sprintf "Parse error: %s" ex.Message]

/// Parse F# source code from a string using default options.
let parseStringWithDefaults (source: string) (fileName: string) : ParseResult =
    parseString source fileName defaultParseOptions

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

/// Check a single module declaration, returning updated environment and nodes
/// Environment threading is critical so that later declarations can see earlier bindings
let rec private checkModuleDecl (env: TypeEnv) (builder: NodeBuilder) (ctx: ModuleContext) (decl: SynModuleDecl) : TypeEnv * SemanticNode list =
    match decl with
    | SynModuleDecl.Let(isRec, bindings, bindingRange, _trivia) ->
        // Let bindings - check each binding and add to environment
        // isRec affects how bindings can reference each other
        let range = rangeToSourceRange bindingRange
        let _ = range  // Range captured in individual bindings

        // For recursive bindings, we should add all names to env first
        // For now, we at least thread the environment through sequentially
        let (finalEnv, nodes) =
            bindings |> List.fold (fun (accEnv, accNodes) binding ->
                let _ = isRec  // TODO: Handle recursive bindings properly
                let node = checkBinding accEnv builder binding
                // Add the binding to environment so later bindings can reference it
                let name = getBindingName binding
                let updatedEnv = addBinding name node.Type false (Some node.Id) accEnv
                (updatedEnv, node :: accNodes)
            ) (env, [])
        (finalEnv, List.rev nodes)

    | SynModuleDecl.Expr(expr, exprRange) ->
        // Module-level expression (e.g., do expr)
        let _ = rangeToSourceRange exprRange  // Could be used for diagnostics
        (env, [checkExpr env builder expr])

    | SynModuleDecl.Types(typeDefns, typesRange) ->
        // Type definitions
        let _ = rangeToSourceRange typesRange  // Range for the whole types block
        let nodes = typeDefns |> List.map (fun typeDef ->
            let range = rangeToSourceRange typeDef.Range
            // TODO: Extract actual type name and kind from typeDef
            builder.Create(
                SemanticKind.TypeDef("type", TypeDefKind.ClassDef, []),
                env.Globals.UnitType,
                range
            )
        )
        (env, nodes)

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
        let (nestedEnv, childNodes) = checkModuleDecls env builder nestedCtx nestedDecls
        let childIds = childNodes |> List.map (fun n -> n.Id)

        // Create a ModuleDef node for the nested module
        let moduleNode = builder.Create(
            SemanticKind.ModuleDef(moduleName, childIds),
            env.Globals.UnitType,
            range,
            children = childIds
        )

        (nestedEnv, [moduleNode])

    | SynModuleDecl.Open _ ->
        // Open statements affect name resolution but don't produce semantic nodes
        // TODO: Track opened namespaces in environment for name resolution
        (env, [])

    | SynModuleDecl.HashDirective _ ->
        // Hash directives (#if, #nowarn, etc.) - preprocessing, no semantic nodes
        (env, [])

    | SynModuleDecl.ModuleAbbrev _ ->
        // Module abbreviations (module M = Long.Path) - affects name resolution
        // TODO: Track in environment
        (env, [])

    | SynModuleDecl.Attributes _ ->
        // Standalone attributes (assembly-level, etc.)
        // TODO: Capture for assembly metadata
        (env, [])

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
        (env, [builder.Create(
            SemanticKind.TypeDef(exnName, TypeDefKind.ClassDef, []),
            env.Globals.ExnType,
            range
        )])

    | SynModuleDecl.NamespaceFragment _ ->
        // Namespace fragments are handled at a higher level in checkModuleOrNamespace
        (env, [])

/// Check a list of module declarations, threading environment through
and private checkModuleDecls (env: TypeEnv) (builder: NodeBuilder) (ctx: ModuleContext) (decls: SynModuleDecl list) : TypeEnv * SemanticNode list =
    let (finalEnv, allNodes) =
        decls |> List.fold (fun (accEnv, accNodes) decl ->
            let (updatedEnv, nodes) = checkModuleDecl accEnv builder ctx decl
            (updatedEnv, accNodes @ nodes)
        ) (env, [])
    (finalEnv, allNodes)

/// Check a list of module declarations (public API)
let checkModuleDeclarations (decls: SynModuleDecl list) : CheckResult =
    let globals = createNativeGlobals()
    let env = createTypeEnv globals
    let builder = NodeBuilder()
    NodeId.reset()

    let ctx = { Path = []; IsRecursive = false }
    let (_finalEnv, nodes) = checkModuleDecls env builder ctx decls
    let diagnostics = solveAndGetDiagnostics env.Constraints

    buildResult builder nodes Map.empty diagnostics

//-------------------------------------------------------------------------
// Type Checking: Module or Namespace Level
//-------------------------------------------------------------------------

/// Check a module or namespace and return updated environment and semantic nodes
let private checkModuleOrNamespace (env: TypeEnv) (builder: NodeBuilder) (moduleOrNs: SynModuleOrNamespace) : TypeEnv * ModulePath * SemanticNode list =
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
    let (updatedEnv, contentNodes) = checkModuleDecls env builder ctx decls

    if isNamespace then
        // Namespaces don't get a wrapper node - just return content
        (updatedEnv, modulePath, contentNodes)
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

        (updatedEnv, modulePath, [moduleNode])

//-------------------------------------------------------------------------
// Type Checking: Full Implementation File
//-------------------------------------------------------------------------

/// Check a parsed implementation file
let checkImplFile (implFile: ParsedImplFileInput) : CheckResult =
    let (ParsedImplFileInput(fileName, _isScript, qualifiedNameOfFile, _hashDirectives, contents, _flags, _trivia, _identifiers)) = implFile

    let globals = createNativeGlobals()
    let initialEnv = createTypeEnv globals
    let builder = NodeBuilder()
    NodeId.reset()

    // Track which file we're processing (for diagnostics)
    let _ = fileName  // Could be added to CheckResult metadata
    let _ = qualifiedNameOfFile  // The qualified name can be used for module resolution

    // Process each module or namespace in the file, threading environment
    let (_finalEnv, moduleResults) =
        contents |> List.fold (fun (accEnv, accResults) moduleOrNs ->
            let (updatedEnv, path, nodes) = checkModuleOrNamespace accEnv builder moduleOrNs
            (updatedEnv, (path, nodes) :: accResults)
        ) (initialEnv, [])

    // Collect all nodes and build module path mapping (reverse to preserve order)
    let moduleResultsOrdered = List.rev moduleResults
    let allNodes = moduleResultsOrdered |> List.collect snd
    let modulePaths =
        moduleResultsOrdered
        |> List.map (fun (path, nodes) -> (path, nodes |> List.map (fun n -> n.Id)))
        |> Map.ofList

    let diagnostics = solveAndGetDiagnostics initialEnv.Constraints

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

/// Result of parsing and checking combined
type ParseAndCheckResult =
    | Success of CheckResult
    | ParseFailure of errors: string list
    | CheckFailure of CheckResult

/// Parse and check F# source in one step.
/// This is the primary API for testing the full pipeline from source to SemanticGraph.
///
/// Parameters:
///   source - The F# source code to parse and check
///   fileName - The file name to associate with the source
///
/// Returns:
///   ParseAndCheckResult - Success with CheckResult, or failure details
let parseAndCheck (source: string) (fileName: string) : ParseAndCheckResult =
    match parseStringWithDefaults source fileName with
    | ParseError errors -> ParseFailure errors
    | ParseSuccess parsedInput ->
        let result = checkParsedInput parsedInput
        if CheckResult.hasErrors result then
            CheckFailure result
        else
            Success result

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
