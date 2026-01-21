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
open FSharp.Native.Compiler.NativeTypedTree.NativeTypes
open FSharp.Native.Compiler.NativeTypedTree.NativeGlobals
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Core
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Builder
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Reachability
open FSharp.Native.Compiler.NativeTypedTree.NameResolution
open FSharp.Native.Compiler.NativeTypedTree.Expressions.Coordinator
open FSharp.Native.Compiler.NativeTypedTree.Expressions.Types
open FSharp.Native.Compiler.NativeTypedTree.Expressions.Bindings

// Infrastructure modules - use qualified names to avoid conflicts
module PhaseConfig = FSharp.Native.Compiler.NativeTypedTree.Infrastructure.PhaseConfig
module PhaseTypes = FSharp.Native.Compiler.NativeTypedTree.Infrastructure.PhaseTypes
module PhaseEmitter = FSharp.Native.Compiler.NativeTypedTree.Infrastructure.PhaseEmitter

// Baker modules - HOF decomposition (PRD-13a)
module HOFDecomposition = FSharp.Native.Compiler.Baker.HOFDecomposition

// Nanopass modules - Four-pass elaboration pipeline (January 2026)
module IntrinsicElaboration = FSharp.Native.Compiler.Nanopass.IntrinsicElaboration
module BakerSaturation = FSharp.Native.Compiler.Nanopass.BakerSaturation
module RecipeSerialization = FSharp.Native.Compiler.Nanopass.Serialization

open FSharp.Native.Compiler.NativeTypedTree.UnionFind
open FSharp.Native.Compiler.NativeTypedTree.Unify
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
    let baseName =
        match System.IO.Path.GetFileNameWithoutExtension(fileName) with
        | null -> failwith $"Cannot extract base name from file: {fileName}"
        | name -> name
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
/// NOTE: Temporarily using Warning instead of Error to allow compilation to proceed
/// while type issues in Alloy are resolved. These should become errors again.
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
            Severity = NativeDiagnosticSeverity.Error
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
/// Entry points are bindings that are either:
/// - Named "main", or
/// - Have the [<EntryPoint>] attribute
let private findEntryPoints (allNodes: Map<NodeId, SemanticNode>) (topLevelNodes: SemanticNode list) : NodeId list =
    // Helper to check if a node is an entry point
    let isEntryPointBinding node =
        match node with
        | Some memberNode ->
            match memberNode.Kind with
            | SemanticKind.Binding(name, _, _, isEntryPoint) ->
                name = "main" || isEntryPoint
            | _ -> false
        | None -> false

    // Helper to look up a node by ID
    let tryGetNode (nodeId: NodeId) =
        Map.tryFind nodeId allNodes

    // Find modules that contain an entry point binding
    let entryModules =
        topLevelNodes
        |> List.filter (fun node ->
            match node.Kind with
            | SemanticKind.ModuleDef (_, memberIds) ->
                // Check if this module contains an entry point binding
                memberIds |> List.exists (fun memberId ->
                    isEntryPointBinding (tryGetNode memberId))
            | SemanticKind.Binding(name, _, _, isEntryPoint) ->
                name = "main" || isEntryPoint
            | _ -> false
        )
        |> List.map (fun n -> n.Id)

    // If no entry point found, this is a library - return empty
    entryModules

//-------------------------------------------------------------------------
// Graph Building Helpers
//-------------------------------------------------------------------------

/// Truncate SemanticKind to avoid huge output
let private truncateKind (s: string) =
    if s.Length > 200 then s.[..197] + "..."
    else s

/// Helper to emit a phase if enabled
let private emitPhaseIfEnabled (phase: PhaseTypes.PhaseId) (graph: SemanticGraph) (diagnostics: Diagnostic list) : unit =
    if not (PhaseConfig.shouldEmitPhase phase.Number) then ()
    else
        let (reachable, _unreachable) =
            if phase.Number >= 4 then getReachabilityStats graph
            else (Map.count graph.Nodes, 0)
        
        let nodeOutputs =
            graph.Nodes
            |> Map.toList
            |> List.map (fun (id, node) ->
                let kindStr = node.Kind |> sprintf "%A" |> truncateKind
                let typeStr = node.Type |> sprintf "%A"
                let parentId = node.Parent |> Option.map NodeId.value
                let emissionStr =
                    match node.EmissionStrategy with
                    | EmissionStrategy.Inline -> None  // Default, don't clutter output
                    | EmissionStrategy.SeparateFunction n -> Some (sprintf "SeparateFunction(%d)" n)
                    | EmissionStrategy.MainPrologue -> Some "MainPrologue"
                // Extract elaboration info from metadata (unified scheme)
                // Check new keys first, fall back to legacy Baker keys for transition
                let elaborationKind =
                    match Map.tryFind ElaborationMetadata.Kind node.Metadata with
                    | Some (MetadataValue.String kind) -> Some kind
                    | _ ->
                        // Legacy Baker key fallback
                        match Map.tryFind "BakerExpanded" node.Metadata with
                        | Some (MetadataValue.Bool true) -> Some "Baker"
                        | _ -> None
                let elaborationFor =
                    match Map.tryFind ElaborationMetadata.For node.Metadata with
                    | Some (MetadataValue.String forConstruct) -> Some forConstruct
                    | _ ->
                        // Legacy Baker key fallback
                        match Map.tryFind "ExpandedFrom" node.Metadata with
                        | Some (MetadataValue.String name) -> Some name
                        | _ -> None
                let elaborationId =
                    match Map.tryFind ElaborationMetadata.Id node.Metadata with
                    | Some (MetadataValue.Int id) -> Some id
                    | _ ->
                        // Legacy Baker key fallback
                        match Map.tryFind "ExpansionId" node.Metadata with
                        | Some (MetadataValue.Int id) -> Some id
                        | _ -> None
                { PhaseTypes.PhaseNodeOutput.Id = NodeId.value id
                  PhaseTypes.PhaseNodeOutput.Kind = kindStr
                  PhaseTypes.PhaseNodeOutput.Type = typeStr
                  PhaseTypes.PhaseNodeOutput.IsReachable = node.IsReachable
                  PhaseTypes.PhaseNodeOutput.Children = node.Children |> List.map NodeId.value
                  PhaseTypes.PhaseNodeOutput.Parent = parentId
                  PhaseTypes.PhaseNodeOutput.Range = Some (sprintf "%s:%d:%d" node.Range.File node.Range.Start.Line node.Range.Start.Column)
                  PhaseTypes.PhaseNodeOutput.SRTPResolution = node.SRTPResolution |> Option.map (sprintf "%A")
                  PhaseTypes.PhaseNodeOutput.Body = None
                  PhaseTypes.PhaseNodeOutput.EmissionStrategy = emissionStr
                  // Elaboration fields (unified - source-based nodes have None)
                  PhaseTypes.PhaseNodeOutput.ElaborationKind = elaborationKind
                  PhaseTypes.PhaseNodeOutput.ElaborationFor = elaborationFor
                  PhaseTypes.PhaseNodeOutput.ElaborationId = elaborationId })
        
        let summary =
            if phase.Number >= 4 then
                PhaseTypes.createSummaryWithReachability phase (Map.count graph.Nodes) reachable (List.length graph.EntryPoints) 0L
            else
                PhaseTypes.createSummary phase (Map.count graph.Nodes) (List.length graph.EntryPoints) 0L
        
        let diagStrings = diagnostics |> List.map (fun d -> d.Message)
        let errorCount = diagnostics |> List.filter (fun d -> d.Severity = NativeDiagnosticSeverity.Error) |> List.length
        let summaryWithDiags = summary |> PhaseTypes.withDiagnostics (List.length diagnostics) errorCount
        
        let output : PhaseTypes.PhaseOutput = {
            Summary = summaryWithDiags
            Nodes = nodeOutputs
            EntryPoints = graph.EntryPoints |> List.map NodeId.value
            Diagnostics = diagStrings
        }
        
        PhaseEmitter.emitPhase output

/// Build a CheckResult from builder state and diagnostics
let private buildResult (builder: NodeBuilder) (topLevelNodes: SemanticNode list) (modulePaths: Map<ModulePath, NodeId list>) (diagnostics: Diagnostic list) : CheckResult =
    let entryPoints = findEntryPoints builder.Nodes topLevelNodes

    // CRITICAL: Apply type substitutions to resolve type variables after constraint solving.
    // During type checking, nodes are created with fresh type variables that get unified
    // with concrete types. The substitutions are stored in UnionFind but not automatically
    // applied to node types. We must apply them here to get concrete types in the output.
    let resolvedNodes =
        builder.Nodes
        |> Map.map (fun _id node ->
            { node with Type = applySubst node.Type })

    let graph = {
        Nodes = resolvedNodes
        EntryPoints = entryPoints
        Modules = modulePaths
        // Types extracted lazily from witnessed TypeDef nodes (codata pattern)
        Types = SemanticGraph.mkTypesIndex resolvedNodes
        // Platform context is set by the project checker based on .fidproj
        Platform = None
        // Module classifications computed lazily from EmissionStrategy
        ModuleClassifications = SemanticGraph.mkModuleClassifications resolvedNodes
        // Seq saturation computed lazily from SeqExpr nodes (codata pattern)
        SeqSaturation = SemanticGraph.mkSeqSaturation resolvedNodes
    }

    // Phase 1: Emit structural construction result
    emitPhaseIfEnabled PhaseTypes.PhaseId.Structural graph diagnostics

    // Phase 4: Reachability analysis
    // Use soft-delete (mark IsReachable = false) or hard prune based on config
    let reachableGraph =
        if PhaseConfig.useSoftDeleteReachability() then
            let markedGraph = markUnreachable graph
            emitPhaseIfEnabled PhaseTypes.PhaseId.Reachability markedGraph diagnostics
            markedGraph
        else
            let prunedGraph = pruneUnreachable graph
            emitPhaseIfEnabled PhaseTypes.PhaseId.Reachability prunedGraph diagnostics
            prunedGraph

    //=========================================================================
    // Four-Pass Elaboration Pipeline (January 2026)
    // See: docs/PSG_Elaboration_Fold_Architecture.md
    //
    // PSG₀ (reachableGraph) → Pass 1 → Intrinsic Recipes → Pass 2 → PSG₁
    //                       → Pass 3 → Saturation Recipes → Pass 4 → PSG₂
    //=========================================================================

    // Pass 1: Intrinsic Fan-Out - Create intrinsic elaboration recipes
    let intrinsicRecipes = IntrinsicElaboration.fanOut reachableGraph
    RecipeSerialization.emitIntrinsicRecipes intrinsicRecipes  // Artifact 02

    // Pass 2: Intrinsic Fold-In - Build PSG₁ with intrinsic elaborations
    let psg1 = IntrinsicElaboration.foldIn intrinsicRecipes reachableGraph
    if PhaseConfig.shouldEmit() then
        emitPhaseIfEnabled PhaseTypes.PhaseId.BakerModuleInit psg1 diagnostics  // Artifact 03

    // Pass 3: Saturation Fan-Out - Create Baker decomposition recipes
    let saturationRecipes = BakerSaturation.fanOut psg1
    RecipeSerialization.emitSaturationRecipes saturationRecipes  // Artifact 04

    // Pass 4: Saturation Fold-In - Build PSG₂ with decomposed structures
    let finalGraph = BakerSaturation.foldIn saturationRecipes psg1

    // Phase 5: Emit final result
    emitPhaseIfEnabled PhaseTypes.PhaseId.Final finalGraph diagnostics

    // Emit FSharpNativeExpr view (expression-centric representation)
    PhaseEmitter.emitExpressionView finalGraph
    PhaseEmitter.emitExpressionText finalGraph

    // Filter diagnostics to only those from source files with reachable code
    // This prevents reporting errors from unreachable dependency code (e.g., unused
    // parts of transitive dependencies like BAREWire)
    // 
    // Strategy: Get all source files that have reachable nodes, then filter
    // diagnostics to only those from files with reachable code.
    let reachableSourceFiles =
        finalGraph.Nodes
        |> Map.values
        |> Seq.map (fun node -> node.Range.File)
        |> Seq.filter (fun f -> f <> "")  // Filter out empty/dummy ranges
        |> Set.ofSeq
    
    let filteredDiagnostics =
        diagnostics
        |> List.filter (fun d ->
            // Keep diagnostic if its source file has reachable code
            // If no file info (empty string), keep the diagnostic (conservative)
            let file = d.Range.File
            file = "" || Set.contains file reachableSourceFiles)

    {
        Graph = finalGraph
        Diagnostics = filteredDiagnostics
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
    let diagnostics = solveAndGetDiagnostics !(env.Constraints)

    buildResult builder [node] Map.empty diagnostics

//-------------------------------------------------------------------------
// Type Checking: Binding Level
//-------------------------------------------------------------------------

/// Check a single let binding and return a semantic node.
/// Note: The inline body is intentionally discarded here because:
/// 1. This checks a single binding in isolation (no subsequent bindings to inline into)
/// 2. The Lambda node's child already contains the checked body for code generation
/// 3. InlineBody is for environment-based name resolution during multi-binding checking
let checkLetBinding (binding: SynBinding) : CheckResult =
    let globals = createNativeGlobals()
    let env = createTypeEnv globals
    let builder = NodeBuilder()
    NodeId.reset()

    // InlineBody, isMutable and literalValue discarded - see function doc comment for rationale
    let (node, _inlineBody, _isMutable, _literalValue) = checkBinding checkExpr checkSynType env builder binding None
    let diagnostics = solveAndGetDiagnostics !(env.Constraints)

    buildResult builder [node] Map.empty diagnostics

//-------------------------------------------------------------------------
// Type Checking: Module Level
//-------------------------------------------------------------------------

/// Context for module checking - tracks current module path
type private ModuleContext = {
    Path: ModulePath
    IsRecursive: bool
}

/// Check if a type definition has the [<Struct>] attribute
let private hasStructAttribute (attrs: SynAttributes) : bool =
    attrs |> List.exists (fun attrList ->
        attrList.Attributes |> List.exists (fun attr ->
            match attr.TypeName.LongIdent with
            | [id] -> id.idText = "Struct" || id.idText = "StructAttribute"
            | _ -> false
        )
    )

/// Check if a type definition has the [<RequireQualifiedAccess>] attribute
/// Per fsnative-spec: When true, field labels are NOT added to FieldLabels table
let private hasRequireQualifiedAccessAttribute (attrs: SynAttributes) : bool =
    attrs |> List.exists (fun attrList ->
        attrList.Attributes |> List.exists (fun attr ->
            match attr.TypeName.LongIdent with
            | [id] -> id.idText = "RequireQualifiedAccess" || id.idText = "RequireQualifiedAccessAttribute"
            | _ -> false
        )
    )

/// Check a single module declaration, returning updated environment and nodes
/// Environment threading is critical so that later declarations can see earlier bindings
let rec private checkModuleDecl (env: TypeEnv) (builder: NodeBuilder) (ctx: ModuleContext) (decl: SynModuleDecl) : TypeEnv * SemanticNode list =
    match decl with
    | SynModuleDecl.Let(isRec, bindings, bindingRange, _trivia) ->
        // Let bindings - check each binding and add to environment
        // isRec affects how bindings can reference each other
        let range = rangeToSourceRange bindingRange
        let _ = range  // Range captured in individual bindings

        // Compute qualified name suffixes for bindings (like we do for types)
        // This enables lookups like "Console.write" for a binding in Console module
        // and "Platform.Bindings.foo" for nested modules
        //
        // For path = ["Console"], produces: ["Console.write", "write"]
        // For path = ["Platform"; "Console"], produces:
        //   ["Platform.Console.write", "Console.write", "write"]
        let bindingNameSuffixes simpleName =
            match ctx.Path with
            | [] -> [simpleName]  // No module path - just the simple name
            | path ->
                // Compute all suffix paths from the module path
                let rec allSuffixes = function
                    | [] -> [[]]
                    | x :: xs -> (x :: xs) :: allSuffixes xs
                path
                |> allSuffixes
                |> List.map (fun modPath ->
                    match modPath with
                    | [] -> simpleName
                    | _ -> (modPath |> String.concat ".") + "." + simpleName)

        // Capture function bodies for `inline` functions (escape analysis)
        // Handle recursive vs non-recursive bindings differently
        let (finalEnv, nodes) =
            match isRec with
            | true ->
                // PRD-13: RECURSIVE BINDINGS - Pre-create Binding nodes for NodeIds
                // This enables self-referential VarRefs to resolve correctly
                let preCreatedBindings =
                    bindings
                    |> List.map (fun binding ->
                        let simpleName = getBindingName binding
                        let placeholderTy = freshTypeVar range
                        let (SynBinding(_, _, _, isMutable, attrs, _, _, _, _, _, _, _, _)) = binding
                        let isEntryPoint = hasEntryPointAttribute attrs
                        let node = builder.Create(
                            SemanticKind.Binding(simpleName, isMutable, true, isEntryPoint),
                            placeholderTy,
                            range,
                            children = [])
                        (binding, simpleName, placeholderTy, node))

                // Add all bindings to environment WITH their NodeIds
                let envWithAllNames =
                    preCreatedBindings
                    |> List.fold (fun accEnv (_, simpleName, placeholderTy, preCreatedNode) ->
                        bindingNameSuffixes simpleName
                        |> List.fold (fun env qname ->
                            addBinding qname placeholderTy false (Some preCreatedNode.Id) true env  // Module-level bindings
                        ) accEnv
                    ) env

                // Check all bodies - VarRefs now resolve to pre-created NodeIds
                let (updatedEnv, checkedBindings) =
                    preCreatedBindings
                    |> List.fold (fun (accEnv, accResults) (binding, simpleName, placeholderTy, preCreatedNode) ->
                        let (node, inlineBodyOpt, isMutable, literalValueOpt) =
                            checkBinding checkExpr checkSynType envWithAllNames builder binding (Some preCreatedNode)

                        // Unify placeholder type with inferred type
                        addConstraint (Constraint.Equals(placeholderTy, node.Type, range)) accEnv

                        // Update environment with actual types and inline bodies
                        let envWithNode =
                            bindingNameSuffixes simpleName
                            |> List.fold (fun env qname ->
                                match inlineBodyOpt, literalValueOpt with
                                | Some inlineBody, _ -> addInlineBinding qname node.Type (Some node.Id) inlineBody env
                                | None, Some litVal -> addLiteralBinding qname node.Type (Some node.Id) litVal env
                                | None, None -> addBinding qname node.Type isMutable (Some node.Id) true env  // Module-level bindings
                            ) accEnv

                        (envWithNode, (node, inlineBodyOpt, simpleName) :: accResults)
                    ) (envWithAllNames, [])

                let nodes = checkedBindings |> List.map (fun (node, _, _) -> node) |> List.rev
                (updatedEnv, nodes)
            | false ->
                // NON-RECURSIVE BINDINGS: Sequential processing (existing behavior)
                // Each binding can only reference bindings that came before it
                bindings |> List.fold (fun (accEnv, accNodes) binding ->
                    let (node, inlineBodyOpt, isMutable, literalValueOpt) = checkBinding checkExpr checkSynType accEnv builder binding None
                    // Add the binding to environment so later bindings can reference it
                    // Register under all qualified name suffixes (handles AutoOpen modules)
                    // CRITICAL: Use actual isMutable flag for module-level mutable variables
                    // [<Literal>] bindings are registered for compile-time substitution
                    let simpleName = getBindingName binding
                    let updatedEnv =
                        bindingNameSuffixes simpleName
                        |> List.fold (fun env qname ->
                            // Use addInlineBinding for functions, addLiteralBinding for literals
                            match inlineBodyOpt, literalValueOpt with
                            | Some inlineBody, _ -> addInlineBinding qname node.Type (Some node.Id) inlineBody env
                            | None, Some litVal -> addLiteralBinding qname node.Type (Some node.Id) litVal env
                            | None, None -> addBinding qname node.Type isMutable (Some node.Id) true env  // Module-level bindings
                        ) accEnv
                    (updatedEnv, node :: accNodes)
                ) (env, [])
                |> fun (finalEnv, nodes) -> (finalEnv, List.rev nodes)
        (finalEnv, nodes)

    | SynModuleDecl.Expr(expr, exprRange) ->
        // Module-level expression (e.g., do expr)
        let _ = rangeToSourceRange exprRange  // Could be used for diagnostics
        (env, [checkExpr env builder expr])

    | SynModuleDecl.Types(typeDefns, typesRange) ->
        // Type definitions - process each and potentially update environment
        let _ = rangeToSourceRange typesRange  // Range for the whole types block

        // Process each type definition, threading environment for abbreviations
        let (finalEnv, nodes) =
            typeDefns |> List.fold (fun (accEnv, accNodes) typeDef ->
                let (SynTypeDefn(typeInfo, typeRepr, _members, _implicitCtor, typeRange, _trivia)) = typeDef
                let range = rangeToSourceRange typeRange

                // Extract type name from SynComponentInfo
                let simpleTypeName =
                    let (SynComponentInfo(_, _, _, longId, _, _, _, _)) = typeInfo
                    longId |> List.map (fun id -> id.idText) |> String.concat "."
                
                // For nested modules, we need to register types with qualified names
                // so they can be looked up as "ModuleName.TypeName"
                // The module path relative to namespace (skip the namespace prefix)
                // For path ["Alloy"; "Internal"] we want to prefix with "Internal."
                // 
                // Additionally, for [<AutoOpen>] modules, types inside them should be
                // accessible without the AutoOpen module prefix. Since we don't track
                // AutoOpen attributes, we register under ALL suffix variations to be safe.
                // E.g., for path ["Alloy", "Fsil", "Internal"] and type "Condition":
                //   - "Fsil.Internal.Condition"
                //   - "Internal.Condition" 
                //   - "Condition"
                let typeNameSuffixes =
                    match ctx.Path with
                    | [] | [_] -> [simpleTypeName]  // No nested module or just namespace
                    | _ :: rest -> 
                        // Generate all suffix variations of the module path
                        let rec allSuffixes = function
                            | [] -> [[]]
                            | x :: xs -> (x :: xs) :: allSuffixes xs
                        
                        rest
                        |> allSuffixes
                        |> List.map (fun modPath ->
                            match modPath with
                            | [] -> simpleTypeName
                            | _ -> (modPath |> String.concat ".") + "." + simpleTypeName)
                
                // Primary name for semantic graph node (use most qualified)
                let typeName = List.head typeNameSuffixes

                // Check if this is a type abbreviation
                match typeRepr with
                | SynTypeDefnRepr.Simple(SynTypeDefnSimpleRepr.TypeAbbrev(_detail, rhsType, _), _) ->
                    // Type abbreviation like `type I32 = int32`
                    // Resolve the target type using the current environment
                    let targetTy = checkSynType accEnv rhsType
                    // Register under all name suffixes (handles AutoOpen modules)
                    let updatedEnv = 
                        typeNameSuffixes 
                        |> List.fold (fun env name -> addTypeAbbrev name targetTy env) accEnv

                    // Create a TypeDef node for the abbreviation
                    let node = builder.Create(
                        SemanticKind.TypeDef(typeName, TypeDefKind.AbbreviationDef targetTy, []),
                        targetTy,
                        range
                    )
                    (updatedEnv, node :: accNodes)

                | SynTypeDefnRepr.Simple(SynTypeDefnSimpleRepr.Union(_, cases, _), _) ->
                    // Discriminated union - FIRST CLASS F# SUPPORT
                    // Extract type parameters from SynComponentInfo
                    let (SynComponentInfo(_, typars, _, _, _, _, _, _)) = typeInfo
                    let arity = match typars with Some tp -> tp.TyparDecls.Length | None -> 0

                    // Helper to estimate type size for layout computation
                    let estimateTypeSize (ty: NativeType) : int =
                        match ty with
                        | NativeType.TApp(tc, _) ->
                            match tc.Layout with
                            | TypeLayout.Inline(size, _) -> size
                            | TypeLayout.PlatformWord -> 8  // 64-bit platform
                            | _ -> 8
                        | NativeType.TTuple(elems, _) -> elems.Length * 8
                        | _ -> 8  // Default to word size

                    // Process union cases to extract case info
                    // Each case is: CaseName of field1: type1 * field2: type2 * ...
                    // Format for TypeDefKind.UnionDef: (caseName, [(fieldNameOpt, fieldType), ...])
                    let caseInfos =
                        cases |> List.map (fun synCase ->
                            match synCase with
                            | SynUnionCase(_, SynIdent(caseIdent, _), caseKind, _, _, _, _) ->
                                let caseName = caseIdent.idText
                                let fields : (string option * NativeType) list =
                                    match caseKind with
                                    | SynUnionCaseKind.Fields synFields ->
                                        synFields |> List.map (fun synField ->
                                            match synField with
                                            | SynField(_, _, idOpt, fieldType, _, _, _, _, _) ->
                                                let fieldName = idOpt |> Option.map (fun id -> id.idText)
                                                let fieldTy = checkSynType accEnv fieldType
                                                (fieldName, fieldTy)
                                        )
                                    | SynUnionCaseKind.FullType(synType, _) ->
                                        // Full type annotation: Case: T1 * T2 -> UnionType
                                        [(None, checkSynType accEnv synType)]
                                (caseName, fields)
                        )

                    // Compute union layout: tag byte + max payload size
                    // Per Fidelity memory model: deterministic, compiler-controlled layout
                    let maxPayloadSize =
                        caseInfos
                        |> List.map (fun (_, fields) ->
                            fields |> List.sumBy (fun (_, ty) -> estimateTypeSize ty))
                        |> List.fold max 0
                    let unionSize = 1 + maxPayloadSize  // 1 byte tag + payload
                    let unionAlign = 8  // Align to word boundary
                    let layout = TypeLayout.Inline(unionSize, unionAlign)

                    // Create TypeConRef for the union type
                    let tyCon = mkTypeConRef typeName arity layout
                    let unionType = mkSimpleType tyCon

                    // Register type definition under all name suffixes
                    let envWithType =
                        typeNameSuffixes
                        |> List.fold (fun env name -> addTypeDef name tyCon env) accEnv

                    // CRITICAL: Register case constructors as bindings
                    // For `type Number = Int of int | Float of float`:
                    //   Int : int -> Number
                    //   Float : float -> Number
                    // Register case constructors as bindings with UnionCaseInfo
                    // This enables SynExpr.App to detect DU constructor calls and create
                    // SemanticKind.UnionCase nodes instead of regular Application nodes
                    let envWithCases =
                        caseInfos |> List.indexed |> List.fold (fun env (caseIndex, (caseName, fields)) ->
                            let fieldTypes = fields |> List.map snd
                            let constructorType =
                                match fieldTypes with
                                | [] ->
                                    // Nullary case (e.g., None): just the union type
                                    unionType
                                | [singleField] ->
                                    // Single field case (e.g., Int of int): field -> union
                                    NativeType.TFun(singleField, unionType)
                                | multipleFields ->
                                    // Multiple fields (e.g., Ok of int * string): tuple -> union
                                    let tupleType = NativeType.TTuple(multipleFields, false)
                                    NativeType.TFun(tupleType, unionType)
                            // Add constructor binding with case info for proper UnionCase node creation
                            let caseInfo: FSharp.Native.Compiler.NativeTypedTree.NameResolution.UnionCaseInfo = {
                                CaseName = caseName
                                UnionType = unionType
                                CaseIndex = caseIndex
                            }
                            // Register case constructor with BOTH simple and qualified names
                            // Simple: "Free" (for open Fidelity.Signal.Types access)
                            // Qualified: "EffectState.Free", "Types.EffectState.Free" (for explicit access)
                            let qualifiedCaseNames =
                                typeNameSuffixes
                                |> List.map (fun typeName -> typeName + "." + caseName)
                            // Register under all qualified names first, then simple name
                            let envWithQualifiedCases =
                                qualifiedCaseNames
                                |> List.fold (fun accEnv qualifiedName ->
                                    addUnionCaseBinding qualifiedName constructorType caseInfo accEnv
                                ) env
                            // Also register under simple name for unqualified access
                            addUnionCaseBinding caseName constructorType caseInfo envWithQualifiedCases
                        ) envWithType

                    // Create TypeDef node with case metadata for Alex
                    // TypeDefKind.UnionDef expects: (caseName, [(fieldNameOpt, fieldType), ...]) list
                    let node = builder.Create(
                        SemanticKind.TypeDef(typeName, TypeDefKind.UnionDef caseInfos, []),
                        unionType,
                        range
                    )
                    (envWithCases, node :: accNodes)

                | SynTypeDefnRepr.Simple(SynTypeDefnSimpleRepr.Record(_, fields, _), _) ->
                    // Record type
                    // Per fsnative-spec: Field order determines memory layout
                    // "Fidelity makes ALL memory layout decisions - MLIR/LLVM never determine layout"
                    let (SynComponentInfo(attrs, typars, _, _, _, _, _, _)) = typeInfo
                    let _arity = match typars with Some tp -> tp.TyparDecls.Length | None -> 0
                    let requireQualifiedAccess = hasRequireQualifiedAccessAttribute attrs
                    
                    // Extract field names and types from SynField list
                    // Per spec: fields are processed in declaration order (= memory order)
                    let fieldInfos =
                        fields
                        |> List.choose (fun synField ->
                            match synField with
                            | SynField(_, _, idOpt, fieldType, _, _, _, _, _) ->
                                match idOpt with
                                | Some ident ->
                                    let fieldName = ident.idText
                                    let nativeType = checkSynType accEnv fieldType
                                    Some (fieldName, nativeType)
                                | None ->
                                    // Anonymous field (tuple-style) - skip for now
                                    // Full implementation would handle this case
                                    None
                        )
                    
                    // Compute memory layout from fields
                    // Per spec Step 4: "Initialize offset = 0, max_align = 1..."
                    let layout = computeRecordLayout fieldInfos

                    // Create TypeConRef with computed layout
                    // Field info is accessed via SemanticGraph.Types lookup (TypeDef node)
                    let tyCon = mkRecordTypeConRef typeName ctx.Path layout (List.length fieldInfos)
                    
                    // Register under all name suffixes (handles AutoOpen modules)
                    let updatedEnv = 
                        typeNameSuffixes 
                        |> List.fold (fun env name -> addTypeDef name tyCon env) accEnv
                    
                    // Create RecordTypeInfo and register in environment
                    // This populates RecordDefs and (unless RequireQualifiedAccess) FieldLabels
                    let recordInfo: RecordTypeInfo = {
                        TypeCon = tyCon
                        Fields = fieldInfos
                        Module = ctx.Path
                        RequireQualifiedAccess = requireQualifiedAccess
                    }
                    let updatedEnv = addRecordDef recordInfo updatedEnv
                    
                    // Also register the record constructor as a binding
                    // Record constructor takes field values and returns the record type
                    // Use TApp - field information is carried in the TypeDef node (SemanticGraph.Types lookup)
                    // This follows the FCS pattern: TyconRef.Deref for metadata, not embedded in type refs
                    let recordType = mkSimpleType tyCon
                    let updatedEnv = addBinding typeName recordType false None true updatedEnv  // Type constructors are module-level
                    
                    // Create semantic node with field information for downstream consumers
                    let fieldDefs = fieldInfos |> List.map (fun (name, ty) -> (name, ty))
                    let node = builder.Create(
                        SemanticKind.TypeDef(typeName, TypeDefKind.RecordDef fieldDefs, []),
                        recordType,
                        range
                    )
                    (updatedEnv, node :: accNodes)

                | SynTypeDefnRepr.Simple(SynTypeDefnSimpleRepr.Enum(_, _), _) ->
                    // Enum type
                    let tyCon = mkTypeConRef typeName 0 (TypeLayout.Inline(4, 4))  // Enums are typically i32
                    // Register under all name suffixes (handles AutoOpen modules)
                    let updatedEnv = 
                        typeNameSuffixes 
                        |> List.fold (fun env name -> addTypeDef name tyCon env) accEnv
                    let node = builder.Create(
                        SemanticKind.TypeDef(typeName, TypeDefKind.EnumDef [], []),
                        mkSimpleType tyCon,
                        range
                    )
                    (updatedEnv, node :: accNodes)

                | SynTypeDefnRepr.ObjectModel(kind, _members, _) ->
                    // Class/struct/interface
                    let (SynComponentInfo(attrs, typars, _, _, _, _, _, _)) = typeInfo
                    let arity = match typars with Some tp -> tp.TyparDecls.Length | None -> 0
                    // Check for [<Struct>] attribute in addition to SynTypeDefnKind.Struct
                    let isStruct = match kind with SynTypeDefnKind.Struct -> true | _ -> hasStructAttribute attrs
                    let layout = if isStruct then TypeLayout.Opaque else TypeLayout.Reference ArenaAffinity.CurrentActor
                    let tyCon = mkTypeConRef typeName arity layout
                    // Register under all name suffixes (handles AutoOpen modules)
                    let updatedEnv = 
                        typeNameSuffixes 
                        |> List.fold (fun env name -> addTypeDef name tyCon env) accEnv
                    // For structs (including [<Struct>] attributed), register constructor as binding
                    let structType = mkSimpleType tyCon
                    let updatedEnv = if isStruct then addBinding typeName structType false None true updatedEnv else updatedEnv  // Type constructors are module-level
                    let defKind =
                        if isStruct then TypeDefKind.StructDef
                        else match kind with
                             | SynTypeDefnKind.Interface -> TypeDefKind.InterfaceDef
                             | _ -> TypeDefKind.ClassDef
                    let node = builder.Create(
                        SemanticKind.TypeDef(typeName, defKind, []),
                        structType,
                        range
                    )
                    (updatedEnv, node :: accNodes)

                | _ ->
                    // Other type definitions (delegates, etc.)
                    let node = builder.Create(
                        SemanticKind.TypeDef(typeName, TypeDefKind.ClassDef, []),
                        accEnv.Globals.UnitType,
                        range
                    )
                    (accEnv, node :: accNodes)
            ) (env, [])

        (finalEnv, List.rev nodes)

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

    | SynModuleDecl.Open(target, range) ->
        // Open statements affect name resolution - compose into resolver
        // FNCS has NO BCL - only source-defined modules can be opened
        let updatedEnv =
            match target with
            | SynOpenDeclTarget.ModuleOrNamespace(longId, _) ->
                let ns = longId.LongIdent |> List.map (fun id -> id.idText) |> String.concat "."
                // Whitelist: FSharp.Native.* IS native compilation - always allow
                // Blacklist: Other FSharp.*, System.*, Microsoft.* are BCL - block
                if ns.StartsWith("FSharp.Native.") || ns = "FSharp.Native" then
                    // Native compilation namespace - allow
                    addOpen ns env
                elif ns.StartsWith("System.") || ns.StartsWith("FSharp.") || ns.StartsWith("Microsoft.") then
                    addNativeError DiagnosticCodes.FS8500_BclReferenceNotAllowed range
                        (sprintf "Cannot open namespace '%s'. BCL namespaces are not available in native compilation. Use intrinsics instead." ns) env
                    env
                else
                    addOpen ns env
            | SynOpenDeclTarget.Type _ ->
                // open type - not currently supported in native
                env
        (updatedEnv, [])

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
    let diagnostics = solveAndGetDiagnostics !(env.Constraints)

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

    let diagnostics = solveAndGetDiagnostics !(initialEnv.Constraints)

    buildResult builder allNodes modulePaths diagnostics

/// Check multiple parsed implementation files together.
/// Files are processed in order, with earlier files' bindings available to later files.
/// This is essential for multi-file compilation where dependencies must be loaded first.
/// After checking, reachability analysis prunes the graph to only what's used.
let checkParsedInputs (inputs: ParsedInput list) : CheckResult =
    let globals = createNativeGlobals()
    let initialEnv = createTypeEnv globals
    let builder = NodeBuilder()
    NodeId.reset()

    // Process all files in order, threading environment
    let (_finalEnv, allModuleResults) =
        inputs |> List.fold (fun (accEnv, accResults) input ->
            match input with
            | ParsedInput.ImplFile implFile ->
                let (ParsedImplFileInput(_, _, _, _, contents, _, _, _)) = implFile
                // Process each module in this file
                let (updatedEnv, fileResults) =
                    contents |> List.fold (fun (env, results) moduleOrNs ->
                        let (newEnv, path, nodes) = checkModuleOrNamespace env builder moduleOrNs
                        (newEnv, (path, nodes) :: results)
                    ) (accEnv, [])
                (updatedEnv, (List.rev fileResults) @ accResults)
            | ParsedInput.SigFile _ ->
                // Skip signature files for now
                (accEnv, accResults)
        ) (initialEnv, [])

    // Collect all nodes and build module path mapping
    let moduleResultsOrdered = List.rev allModuleResults
    let allNodes = moduleResultsOrdered |> List.collect snd
    let modulePaths =
        moduleResultsOrdered
        |> List.map (fun (path, nodes) -> (path, nodes |> List.map (fun n -> n.Id)))
        |> Map.ofList

    // Solve constraints - now using ref cells, all environment copies share same constraints
    let constraintDiags = solveAndGetDiagnostics !(initialEnv.Constraints)
    let allDiagnostics = constraintDiags @ (List.rev !(initialEnv.Diagnostics))

    buildResult builder allNodes modulePaths allDiagnostics

/// Check parsed input (implementation or signature file)
let checkParsedInput (input: ParsedInput) : CheckResult =
    match input with
    | ParsedInput.ImplFile implFile -> checkImplFile implFile
    | ParsedInput.SigFile _ ->
        // Signature files not yet supported
        {
            Graph = { Nodes = Map.empty; EntryPoints = []; Modules = Map.empty; Types = lazy Map.empty; Platform = None; ModuleClassifications = lazy Map.empty; SeqSaturation = lazy Map.empty }
            Diagnostics = [{
                Severity = NativeDiagnosticSeverity.Warning
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
