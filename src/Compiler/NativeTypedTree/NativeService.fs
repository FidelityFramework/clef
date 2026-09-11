// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.

/// Public API for Clef Compiler Service.
/// Provides native type checking for Composer consumption.
///
/// This module builds a unified SemanticGraph where:
/// - Types are attached during construction (not post-hoc)
/// - Module structure is preserved
/// - Source locations are properly tracked
/// - Hard prune is applied before returning
module Clef.Compiler.NativeService

open Clef.Compiler.Syntax
open Clef.Compiler.Text
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.NativeTypedTree.MeasureEnvironment
open Clef.Compiler.NativeTypedTree.NativeTypes

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.PSGSaturation.SemanticGraph.Reachability
module DepthAnalysis = Clef.Compiler.PSGSaturation.SemanticGraph.DepthAnalysis
module PlatformDeclaration = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformDeclaration
module RangeAnalysis = Clef.Compiler.PSGSaturation.SemanticGraph.RangeAnalysis
module Placement = Clef.Compiler.PSGSaturation.SemanticGraph.Placement
module Curry = Clef.Compiler.PSGSaturation.SemanticGraph.Curry
module FunctionPointers = Clef.Compiler.PSGSaturation.SemanticGraph.FunctionPointers
module Escape = Clef.Compiler.PSGSaturation.SemanticGraph.Escape
module Meets = Clef.Compiler.PSGSaturation.SemanticGraph.Meets
module PlatformBindings = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformBindings
module Roots = Clef.Compiler.PSGSaturation.SemanticGraph.Roots
open Clef.Compiler.NativeTypedTree.NameResolution
module NameResolution = Clef.Compiler.NativeTypedTree.NameResolution
open Clef.Compiler.NativeTypedTree.Expressions.Types

// Handler module aliases for qualified dispatch
module Literals = Clef.Compiler.NativeTypedTree.Expressions.Literals
module Identity = Clef.Compiler.NativeTypedTree.Expressions.Identity
module Applications = Clef.Compiler.NativeTypedTree.Expressions.Applications
module Bindings = Clef.Compiler.NativeTypedTree.Expressions.Bindings
module Collections = Clef.Compiler.NativeTypedTree.Expressions.Collections
module ControlFlow = Clef.Compiler.NativeTypedTree.Expressions.ControlFlow
module TypeOperations = Clef.Compiler.NativeTypedTree.Expressions.TypeOperations
module Patterns = Clef.Compiler.NativeTypedTree.Expressions.Patterns

// Infrastructure modules - use qualified names to avoid conflicts
module PhaseConfig = Clef.Compiler.NativeTypedTree.Infrastructure.PhaseConfig
module PhaseTypes = Clef.Compiler.NativeTypedTree.Infrastructure.PhaseTypes
module PhaseEmitter = Clef.Compiler.NativeTypedTree.Infrastructure.PhaseEmitter

// Nanopass modules - Four-pass elaboration pipeline (January 2026)
module Monomorphization = Clef.Compiler.Nanopass.Monomorphization
module IntrinsicElaboration = Clef.Compiler.Nanopass.IntrinsicElaboration
module BakerSaturation = Clef.Compiler.Nanopass.BakerSaturation
module RecipeSerialization = Clef.Compiler.Nanopass.Serialization
module ObligationElaboration = Clef.Compiler.Nanopass.ObligationElaboration
module ObligationDischarge = Clef.Compiler.Nanopass.ObligationDischarge

open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.NativeTypedTree.Unify
open Clef.Compiler.DiagnosticsLogger
open Clef.Compiler.Features
open Clef.Compiler.Lexhelp
open Clef.Compiler.UnicodeLexing
open Clef.Compiler.LexFilter
open Clef.Compiler.IO
open Clef.Compiler.Xml
open Clef.Compiler.SyntaxTrivia
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

        // Create the diagnostics logger for capturing errors, and install it, with the Parse phase,
        // for the duration of the parse: the parser reports through the thread-installed logger
        // (ParseHelpers.reportParseErrorAt is `errorR`), not through the logger handed to the lexer,
        // so without this installation every parse error went to the discarding default logger and
        // a damaged tree reached the checker with no diagnostic (found 2026-09-04 by the dimensional
        // vetting harness: a syntax error surfaced downstream as "No declaration roots found in PSG").
        let diagnosticsLogger = CapturingDiagnosticsLogger("parseString")
        use _installedLogger = UseDiagnosticsLogger diagnosticsLogger
        use _installedPhase = UseBuildPhase BuildPhase.Parse

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
            Clef.Compiler.Lexer.token lexargs skipWhitespaceTokens lexbuf

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
        let parsedImplFile = Clef.Compiler.Parser.implementationFile tokenFunc lexbuf

        // Convert to ParsedImplFileInput and wrap in ParsedInput
        let implFileInput = implFileToInput fileName parsedImplFile
        let parsedInput = ParsedInput.ImplFile implFileInput

        // Every error-severity diagnostic the parse logged is a parse failure. The message is
        // located where the exception carries a range; the parser family takes its CCS codes with
        // the step-4 mapping table (Dimensional_Vetting_Plan.md D3), so no code is minted here.
        // An inherited lexer or parser diagnostic keeps its F# number under the CCS prefix
        // (error-handling.md, the CCS code table): F# number 10 is CCS0010, 58 is CCS0058.
        let located (number: int) (m: range) (text: string) =
            sprintf "CCS%04d: %s(%d,%d): %s" number m.FileName m.StartLine (m.StartColumn + 1) text
        let rec render (exn: exn) =
            match exn with
            | DiagnosticWithText(number, text, m) -> located number m text
            | Clef.Compiler.ParseHelpers.IndentationProblem(text, m) -> located 58 m text
            | Clef.Compiler.ParseHelpers.SyntaxError(_, m) -> located 10 m "Syntax error: unexpected token"
            | WrappedError(inner, m) ->
                match inner with
                | DiagnosticWithText _ | Clef.Compiler.ParseHelpers.IndentationProblem _ | Clef.Compiler.ParseHelpers.SyntaxError _ -> render inner
                | _ -> located 0 m inner.Message
            | _ -> exn.Message
        let errors =
            diagnosticsLogger.Diagnostics
            |> List.choose (fun diag ->
                if diag.Severity = Clef.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error then
                    Some (render diag.Exception)
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

/// Convert unification errors to diagnostics. A measure failure carries its own code (design b.5:
/// CCS8040 with both sides rendered plus the residual, CCS8041 for no integer solution, the
/// CCS8048 family for an unrepresentable exponent); every other case carries its own CCS code (D3, error-handling.md's table) since
/// the D3 mapping table lands with CS-7.
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
            | MeasureMismatch(_, _, _, r) -> r
            | NoIntegerSolution(_, _, _, r) -> r
            | MeasureExponentOutOfRange(_, _, r) -> r
            | NotNumeric(_, _, r) -> r
            | OperandKindMismatch(_, _, _, r) -> r
        let code =
            match e with
            | NotNumeric(op, _, _) when isConversionSource op -> DiagnosticCodes.CCS8002_ConversionSourceNotNumeric
            | NotNumeric _ | OperandKindMismatch _ -> DiagnosticCodes.CCS8000_NotNumeric
            | MeasureMismatch _ -> DiagnosticCodes.CCS8040_MeasureMismatch
            | NoIntegerSolution _ -> DiagnosticCodes.CCS8041_NoIntegerSolution
            | MeasureExponentOutOfRange _ -> DiagnosticCodes.CCS8048_RationalMeasureExponent
            | TypeMismatch _ -> DiagnosticCodes.CCS8003_TypeMismatch
            | InfiniteType _ -> DiagnosticCodes.CCS8005_InfiniteType
            | ArityMismatch _ -> DiagnosticCodes.CCS8004_ArityMismatch
            | TupleLengthMismatch _ | TupleKindMismatch _ -> DiagnosticCodes.CCS8006_TupleMismatch
            | ByrefKindMismatch _ -> DiagnosticCodes.CCS8007_ByrefKindMismatch
        {
            Severity = NativeDiagnosticSeverity.Error
            Code = code
            Message = formatError e
            Range = range
            RelatedNodes = []
            Reachability = ReachabilityContext.Unknown
        }
    )

/// Discharge member constraints against the record table. `resolveFieldType` defers `x.Field`
/// to `HasMember(x, Field, result)` when the type of `x` is still a variable (the constraint
/// that determines it has been accumulated but not solved); once the equality constraints are
/// solved the base type is known and `result` is unified with the field's type. One discharge
/// can resolve the base of another (`(Array.get xs i).Field.Other`), so this repeats until no
/// constraint makes progress. A constraint whose base never resolves stays open, as before.
let private dischargeMemberConstraints (env: TypeEnv) (constraints: Constraint list) : UnificationError list =
    let memberOf (baseTy: NativeType) (name: string) : NativeType option =
        match name with
        | "Length" when isStringType baseTy || isArrayType baseTy -> Some Types.intType
        | _ -> tryResolveRecordFieldType baseTy name env
    let rec loop (pending: Constraint list) (errors: UnificationError list) =
        let mutable progress = false
        let mutable remaining = []
        let mutable errs = errors
        for c in pending do
            match c with
            | Constraint.HasMember (ty, name, resultTy, range) ->
                match memberOf (applySubst ty) name with
                | Some fieldTy ->
                    progress <- true
                    match tryUnify resultTy fieldTy range with
                    | Result.Ok () -> ()
                    | Result.Error e -> errs <- e :: errs
                | None -> remaining <- c :: remaining
            | _ -> ()
        if progress && not (List.isEmpty remaining) then loop (List.rev remaining) errs
        else List.rev errs
    loop (constraints |> List.filter (function Constraint.HasMember _ -> true | _ -> false)) []

/// Solve constraints and return diagnostics. Equality constraints first (they determine the
/// base types), then the deferred member constraints against the environment's record table.
let private solveAndGetDiagnostics (env: TypeEnv) (constraints: Constraint list) : Diagnostic list =
    let solveErrors =
        match solveConstraints constraints with
        | Solved | Deferred _ -> []
        | Failed errors -> errors
    let memberErrors = dischargeMemberConstraints env constraints
    errorsToDiagnostics (solveErrors @ memberErrors)

//-------------------------------------------------------------------------
// Let-polymorphism for top-level functions
//-------------------------------------------------------------------------

/// Number of constraints already solved incrementally (constraints are prepended, so the
/// unsolved ones are the head of the list). Reset at the start of every check.
let mutable private solvedConstraintCount = 0

/// Solve the constraints accumulated since the last incremental solve. Unification is
/// order-independent for equality constraints, so solving early yields the same final
/// substitution as the batch solve at the end; diagnostics are reported by that final solve.
let private solveNewConstraints (env: TypeEnv) : unit =
    let all = !(env.Constraints)
    let total = List.length all
    let fresh = total - solvedConstraintCount
    if fresh > 0 then
        let newOnes = all |> List.take fresh
        solveConstraints newOnes |> ignore
        dischargeMemberConstraints env newOnes |> ignore
        solvedConstraintCount <- total

/// A binding node whose right-hand side is a function expression (its one child is a Lambda).
let private isFunctionBindingNode (builder: NodeBuilder) (node: SemanticNode) : bool =
    match node.Kind, node.Children with
    | SemanticKind.Binding _, [childId] ->
        match Map.tryFind childId builder.Nodes with
        | Some { Kind = SemanticKind.Lambda _ } -> true
        | _ -> false
    | _ -> false

/// The parent of every node, read from the children lists, which are complete by construction:
/// the `Parent` field is set only where a checker arm calls `SetParent`, and an expression node's
/// is usually still `None` here (the graph's links are completed by a later pass). Every walk up
/// the tree in this file reads this index.
let private parentIndex (nodes: Map<NodeId, SemanticNode>) : Map<NodeId, NodeId> =
    nodes
    |> Map.fold (fun index _ node ->
        node.Children |> List.fold (fun index child -> Map.add child node.Id index) index) Map.empty

/// Whether `ancestorId` is an ancestor of `node` in the graph.
let private hasAncestor (parents: Map<NodeId, NodeId>) (ancestorId: NodeId) (node: SemanticNode) : bool =
    let rec up (id: NodeId option) =
        match id with
        | None -> false
        | Some i when i = ancestorId -> true
        | Some i -> up (Map.tryFind i parents)
    up (Map.tryFind node.Id parents)

/// The ids of the measure variables (in numeric positions) and carrier variables free in a type.
let private freeMeasureAndCarrierIds (ty: NativeType) : Set<int> =
    let measures = freeMeasureVars ty |> List.map (fun v -> v.Id)
    let carriers = collectFreeTypeParams ty |> List.filter (fun tp -> tp.Kind = TypeParamKind.Carrier) |> List.map (fun tp -> tp.Id)
    Set.ofList (measures @ carriers)

/// The measure and carrier variables free in the environment at a top-level binding (design b.4
/// step 2), resolved through the stores: those of every other binding the checker has not
/// generalised, outside the binding's own subtree (its locals are its own). The resolvers are
/// functions and cannot be enumerated, so the bindings checked so far are read from the graph.
let private envFreeMeasureAndCarrierIds (builder: NodeBuilder) (binding: SemanticNode) : Set<int> =
    let parents = parentIndex builder.Nodes
    builder.Nodes
    |> Map.toSeq
    |> Seq.map snd
    |> Seq.filter (fun n ->
        match n.Kind with
        | SemanticKind.Binding _ -> n.Id <> binding.Id && not (hasAncestor parents binding.Id n)
        | _ -> false)
    |> Seq.map (fun n ->
        match applySubst n.Type with
        | NativeType.TForall _ -> Set.empty
        | ty -> freeMeasureAndCarrierIds ty)
    |> Set.unionMany

/// Generalize a top-level, non-recursive, non-inline, non-extern function binding whose type
/// still has free type, carrier or measure variables after solving the constraints so far
/// (design b.4). The Binding node and the environment carry the TForall scheme (each use
/// instantiates it freshly, see Identity); the Lambda keeps the monotype and is monomorphized
/// per instantiation later (carrier instantiations split bodies; measure-only ones do not, d.3).
let private generalizeTopLevelFunction (builder: NodeBuilder) (env: TypeEnv) (node: SemanticNode) (isInline: bool) : NativeType =
    let isFunctionBinding =
        match node.Kind with
        | SemanticKind.Binding (_, false, false, None) -> isFunctionBindingNode builder node
        | _ -> false
    let isExtern = node.Metadata.ContainsKey "FidelityExtern.Library"
    if isFunctionBinding && not isInline && not isExtern then
        solveNewConstraints env
        let resolved = applySubst node.Type
        // The environment is walked only when there is a measure or carrier variable to subtract.
        let envFree = if hasFreeMeasureOrCarrierVars resolved then envFreeMeasureAndCarrierIds builder node else Set.empty
        let captured = env.BindingTypes |> Map.toSeq |> Seq.map (snd >> applySubst >> freeTypeVars) |> Set.unionMany
        let envFree = Set.union envFree captured
        match generalizeType envFree resolved with
        | NativeType.TForall _ as scheme ->
            builder.SetType(node.Id, scheme)
            scheme
        | _ -> node.Type
    else
        node.Type

//-------------------------------------------------------------------------
// The residual check at non-generalisable bindings (design b.4, c.1; CCS8047, CCS8001)
//-------------------------------------------------------------------------

/// The variables a binding's type may leave open because an enclosing binding quantifies them:
/// the parameters of every enclosing scheme, and the free measure and carrier variables of every
/// enclosing function binding the checker did not generalise (a recursive or nested function,
/// generalisable by the spec and monomorphic here by this checker's gap). `None` under an
/// `inline` function: its body is re-checked at every expansion site, so its variables are
/// quantified by expansion and nothing under it is reported.
let private quantifiedByEnclosing (builder: NodeBuilder) (parents: Map<NodeId, NodeId>) (node: SemanticNode) : Set<int> option =
    let rec up (id: NodeId option) (acc: Set<int>) : Set<int> option =
        match id |> Option.bind (fun i -> Map.tryFind i builder.Nodes) with
        | None -> Some acc
        | Some parent when parent.Metadata.ContainsKey "Inline" -> None
        | Some parent ->
            let acc =
                match parent.Kind, applySubst parent.Type with
                | SemanticKind.Binding _, NativeType.TForall(typars, _) ->
                    typars |> List.fold (fun s tp -> Set.add tp.Id s) acc
                | SemanticKind.Binding _, ty when isFunctionBindingNode builder parent ->
                    Set.union acc (freeMeasureAndCarrierIds ty)
                | _ -> acc
            up (Map.tryFind parent.Id parents) acc
    up (Map.tryFind node.Id parents) Set.empty

/// After every constraint of the program is solved: a value binding (a binding whose right-hand
/// side is not a function expression, the spec's non-generalisable case as this checker draws
/// it) whose resolved type still mentions a measure variable no enclosing scheme quantifies is
/// CCS8047; one that still mentions a carrier variable, or the `+` dispatch variable, is
/// CCS8001. Never defaulted (design b.4, c.1). One diagnostic per code per binding, at the
/// binding's range. Function bindings are not checked here: a generalised one carries its
/// scheme, and a recursive or nested one is generalisable by the spec. A binding whose range
/// already carries an error (`reported`) is not checked, and the variables its type leaves open
/// are not reported at any other binding either: a variable left open by a failed unification
/// is that failure's, not a second one.
let private residualDiagnostics (builder: NodeBuilder) (reported: Diagnostic list) : Diagnostic list =
    let alreadyFailed (node: SemanticNode) =
        reported
        |> List.exists (fun d ->
            d.Severity = NativeDiagnosticSeverity.Error
            && d.Range.File = node.Range.File
            && d.Range.Start.Line >= node.Range.Start.Line
            && d.Range.Start.Line <= node.Range.End.Line)
    let openVariableIds (ty: NativeType) : Set<int> =
        let dispatch = collectFreeTypeParams ty |> List.filter (fun tp -> (operandOf tp).IsSome) |> List.map (fun tp -> tp.Id)
        Set.union (freeMeasureAndCarrierIds ty) (Set.ofList dispatch)
    let tainted =
        builder.Nodes
        |> Map.toSeq
        |> Seq.map snd
        |> Seq.filter (fun n -> match n.Kind with SemanticKind.Binding _ -> alreadyFailed n | _ -> false)
        |> Seq.map (fun n -> openVariableIds (applySubst n.Type))
        |> Set.unionMany
    let diagnostic (code: string) (message: string) (node: SemanticNode) : Diagnostic =
        { Severity = NativeDiagnosticSeverity.Error
          Code = code
          Message = message
          Range = node.Range
          RelatedNodes = []
          Reachability = ReachabilityContext.Unknown }
    let parents = parentIndex builder.Nodes
    // A variable is reported once, at the first binding in node order whose type leaves it open;
    // a later binding that inherits the same open variable (`let _ = v`) is that report's.
    let (_, diagnostics) =
        builder.Nodes
        |> Map.toList
        |> List.fold (fun (reportedIds: Set<int>, acc: Diagnostic list) (_, node) ->
            match node.Kind with
            | SemanticKind.Binding(name, _, _, _)
                when not (isFunctionBindingNode builder node)
                     && not (node.Metadata.ContainsKey "FidelityExtern.Library")
                     && not (alreadyFailed node) ->
                match applySubst node.Type with
                | NativeType.TForall _ -> (reportedIds, acc)
                | ty ->
                    match quantifiedByEnclosing builder parents node with
                    | None -> (reportedIds, acc)
                    | Some quantified ->
                        let excused (id: int) = Set.contains id quantified || Set.contains id tainted || Set.contains id reportedIds
                        let measures = freeMeasureVars ty |> List.filter (fun v -> not (excused v.Id))
                        let operands =
                            collectFreeTypeParams ty
                            |> List.filter (fun tp ->
                                not (excused tp.Id)
                                && (tp.Kind = TypeParamKind.Carrier || (operandOf tp).IsSome))
                        let here =
                            [ match measures with
                              | _ :: _ ->
                                  yield diagnostic DiagnosticCodes.CCS8047_UnresolvedMeasure
                                            $"The measure of '{name}' could not be resolved and this binding is not generalisable; annotate it" node
                              | [] -> ()
                              match operands with
                              | tp :: _ ->
                                  let op = operandOf tp |> Option.defaultValue "(unknown)"
                                  yield diagnostic DiagnosticCodes.CCS8001_OperandKindUndetermined
                                            $"The kind of the operands of '{op}' cannot be determined at this binding; annotate an operand" node
                              | [] -> () ]
                        let nowReported =
                            (measures |> List.map (fun v -> v.Id)) @ (operands |> List.map (fun tp -> tp.Id))
                            |> List.fold (fun s id -> Set.add id s) reportedIds
                        (nowReported, List.rev here @ acc)
            | _ -> (reportedIds, acc)) (Set.empty, [])
    List.rev diagnostics

//-------------------------------------------------------------------------
// Entry Point Detection
//-------------------------------------------------------------------------

/// Determine declaration roots from checked nodes.
/// Declaration roots are bindings that are either:
/// - Named "main" (implies DeclRoot.EntryPoint), or
/// - Have [<EntryPoint>] attribute (DeclRoot.EntryPoint), or
/// - Have [<HardwareModule>] attribute (DeclRoot.HardwareModule)
let private findDeclarationRoots (allNodes: Map<NodeId, SemanticNode>) (topLevelNodes: SemanticNode list) : (NodeId * DeclRoot) list =
    // Helper to get DeclRoot for a binding node
    let getBindingDeclRoot node =
        match node with
        | Some memberNode ->
            match memberNode.Kind with
            | SemanticKind.Binding(name, _, _, declRoot) ->
                match declRoot with
                | Some root -> Some (memberNode.Id, root)
                | None when name = "main" -> Some (memberNode.Id, DeclRoot.EntryPoint)
                | None -> None
            | _ -> None
        | None -> None

    // Helper to look up a node by ID
    let tryGetNode (nodeId: NodeId) =
        Map.tryFind nodeId allNodes

    // Find declaration roots: modules containing root bindings, or top-level root bindings
    let roots =
        topLevelNodes
        |> List.collect (fun node ->
            match node.Kind with
            | SemanticKind.ModuleDef (_, memberIds) ->
                // Check if this module contains a declaration root binding
                let hasRoot =
                    memberIds |> List.exists (fun memberId ->
                        (getBindingDeclRoot (tryGetNode memberId)).IsSome)
                if hasRoot then
                    // Return the module's NodeId paired with the first root's DeclRoot flavor
                    let firstRoot =
                        memberIds
                        |> List.tryPick (fun memberId -> getBindingDeclRoot (tryGetNode memberId))
                    match firstRoot with
                    | Some (_, root) -> [(node.Id, root)]
                    | None -> []
                else []
            | SemanticKind.Binding(name, _, _, declRoot) ->
                match declRoot with
                | Some root -> [(node.Id, root)]
                | None when name = "main" -> [(node.Id, DeclRoot.EntryPoint)]
                | None -> []
            | _ -> []
        )

    roots

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
                  // The analysed range, once RangeAnalysis has run (CS-10)
                  PhaseTypes.PhaseNodeOutput.ValueRange = node.ValueRange |> Option.map ValueRange.render
                  // Elaboration fields (unified - source-based nodes have None)
                  PhaseTypes.PhaseNodeOutput.ElaborationKind = elaborationKind
                  PhaseTypes.PhaseNodeOutput.ElaborationFor = elaborationFor
                  PhaseTypes.PhaseNodeOutput.ElaborationId = elaborationId })
        
        let summary =
            if phase.Number >= 4 then
                PhaseTypes.createSummaryWithReachability phase (Map.count graph.Nodes) reachable (List.length graph.DeclarationRoots) 0L
            else
                PhaseTypes.createSummary phase (Map.count graph.Nodes) (List.length graph.DeclarationRoots) 0L
        
        let diagStrings = diagnostics |> List.map (fun d -> d.Message)
        let errorCount = diagnostics |> List.filter (fun d -> d.Severity = NativeDiagnosticSeverity.Error) |> List.length
        let summaryWithDiags = summary |> PhaseTypes.withDiagnostics (List.length diagnostics) errorCount
        
        let output : PhaseTypes.PhaseOutput = {
            Summary = summaryWithDiags
            Nodes = nodeOutputs
            EntryPoints = graph.DeclarationRoots |> List.map (fun (id, _) -> NodeId.value id)
            Diagnostics = diagStrings
            Edges =
                graph.Edges |> List.map (fun e ->
                    { PhaseTypes.PhaseEdgeOutput.Sources = e.Sources |> List.map NodeId.value
                      Target = NodeId.value e.Target
                      Class = sprintf "%A" e.Class
                      Role = sprintf "%A" e.Role
                      Ordinal = e.Ordinal })
        }
        
        PhaseEmitter.emitPhase output

/// Record on every Application node whose function is a use of a generalised binding the instance
/// of the scheme at that use, as the node's own annotation (design b.4 step 4): hover shows the
/// instance while the binding keeps its scheme. Read from the resolved node map, before
/// monomorphisation repoints the use sites.
let private annotateInstantiations (nodes: Map<NodeId, SemanticNode>) : Map<NodeId, SemanticNode> =
    nodes
    |> Map.map (fun _ node ->
        match node.Kind with
        | SemanticKind.Application(fn, _) ->
            match Map.tryFind fn nodes with
            | Some { Kind = SemanticKind.VarRef(_, Some def); Type = instance } ->
                match Map.tryFind def nodes with
                | Some { Type = NativeType.TForall _ } ->
                    { node with Metadata = Map.add SchemeMetadata.Instantiation (MetadataValue.Type instance) node.Metadata }
                | _ -> node
            | _ -> node
        | _ -> node)

//-------------------------------------------------------------------------
// The saturation residual (sequence CS-8; design 0.4, b.4, (h) 13; I2)
//-------------------------------------------------------------------------

/// The one place types leave the stores is `buildResult`, where every node's type is resolved
/// through the substitution, the measure store and the carrier store (`applySubst`). This is the
/// assertion at that boundary: a node whose resolved type still mentions a measure or carrier
/// variable that no enclosing scheme quantifies is CCS8047, at the node, naming the binding that
/// encloses it, once per binding. Nothing is defaulted to `1`, and the node map that leaves the
/// boundary is the immutable input to monomorphisation and every nanopass (I2). The binding-level
/// residual check above reports a value binding's own type; this one reaches the nodes under a
/// binding whose own type is closed, the `0.0<_> + 1.0<_>` inside a result that is not measured.
/// A binding already reported, by that check or by a failed unification at its range, is not
/// reported again; a function binding's own variables are its subtree's to use (the checker's
/// generalisation gap, as the binding-level check draws it); a node under an `inline` function
/// is quantified by expansion.
let private saturationResidual (builder: NodeBuilder) (resolved: Map<NodeId, SemanticNode>) (reported: Diagnostic list) : Diagnostic list =
    let failedAt (node: SemanticNode) =
        reported
        |> List.exists (fun d ->
            d.Severity = NativeDiagnosticSeverity.Error
            && d.Range.File = node.Range.File
            && d.Range.Start.Line >= node.Range.Start.Line
            && d.Range.Start.Line <= node.Range.End.Line)
    let parents = parentIndex resolved
    let rec enclosingBinding (node: SemanticNode) : SemanticNode option =
        match node.Kind with
        | SemanticKind.Binding _ -> Some node
        | _ ->
            match Map.tryFind node.Id parents |> Option.bind (fun i -> Map.tryFind i resolved) with
            | Some parent -> enclosingBinding parent
            | None -> None
    // The open variables of every binding that already failed are that failure's, not a second one.
    let tainted =
        resolved
        |> Map.toSeq
        |> Seq.map snd
        |> Seq.filter (fun n -> match n.Kind with SemanticKind.Binding _ -> failedAt n | _ -> false)
        |> Seq.map (fun n -> freeMeasureAndCarrierIds n.Type)
        |> Set.unionMany
    let (_, diagnostics) =
        resolved
        |> Map.toList
        |> List.map snd
        |> List.fold (fun (reportedBindings: Set<NodeId>, acc: Diagnostic list) node ->
            let isFunction = (match node.Kind with SemanticKind.Binding _ -> isFunctionBindingNode builder node | _ -> false)
            let residual =
                if isFunction then Set.empty
                else
                    match freeMeasureAndCarrierIds node.Type with
                    | open' when Set.isEmpty open' -> Set.empty
                    | open' ->
                        match quantifiedByEnclosing builder parents node with
                        | None -> Set.empty
                        | Some quantified -> Set.difference (Set.difference open' quantified) tainted
            if Set.isEmpty residual then (reportedBindings, acc)
            else
                match enclosingBinding node with
                | Some binding when not (Set.contains binding.Id reportedBindings) && not (failedAt binding) ->
                    let name = (match binding.Kind with SemanticKind.Binding(n, _, _, _) -> n | _ -> "(binding)")
                    let diagnostic =
                        { Severity = NativeDiagnosticSeverity.Error
                          Code = DiagnosticCodes.CCS8047_UnresolvedMeasure
                          Message = $"The measure of a value in '{name}' could not be resolved at saturation and no enclosing scheme quantifies it; annotate it"
                          Range = node.Range
                          RelatedNodes = [ binding.Id ]
                          Reachability = ReachabilityContext.Unknown }
                    (Set.add binding.Id reportedBindings, diagnostic :: acc)
                | _ -> (reportedBindings, acc)) (Set.empty, [])
    List.rev diagnostics

//-------------------------------------------------------------------------
// Quotations have no run-time value (D9)
//-------------------------------------------------------------------------

/// A quotation is compile-time data: the compiler reads it (a platform description, a binding
/// descriptor, a predicate) and executed code cannot hold, pass or evaluate it. Every quotation
/// reachable from the entry point is CCS8066: a module-level one at each reachable reference to
/// the binding that holds it, a local or expression-position one at the quotation itself. Read
/// from the saturated graph, after reachability, so that a declaration nothing executes is never
/// reported.
let private quotationDiagnostics (graph: SemanticGraph) : Diagnostic list =
    let nodes = graph.Nodes
    let parents = parentIndex nodes
    /// The binding a quotation is the value of, through an annotation, when it is module-level.
    let moduleLevelOwner (quote: SemanticNode) : NodeId option =
        let rec up (id: NodeId) =
            match Map.tryFind id parents |> Option.bind (fun p -> Map.tryFind p nodes) with
            | Some ({ Kind = SemanticKind.TypeAnnotation _ } : SemanticNode as p) -> up p.Id
            | Some ({ Kind = SemanticKind.Binding _ } : SemanticNode as b) ->
                match Map.tryFind b.Id parents |> Option.bind (fun p -> Map.tryFind p nodes) with
                | Some ({ Kind = SemanticKind.ModuleDef _ } : SemanticNode) -> Some b.Id
                | _ -> None
            | _ -> None
        up quote.Id
    let diagnostic (node: SemanticNode) : Diagnostic =
        { Severity = NativeDiagnosticSeverity.Error
          Code = DiagnosticCodes.CCS8066_QuotationHasNoRuntimeValue
          Message = "A quotation has no run-time value: it is read by the compiler at compile time and cannot be referenced from executed code"
          Range = node.Range
          RelatedNodes = [ node.Id ]
          Reachability = ReachabilityContext.Reachable }
    let reachableQuotes =
        nodes |> Map.toList |> List.map snd |> List.filter (fun n -> n.IsReachable && (match n.Kind with SemanticKind.Quote _ -> true | _ -> false))
    let owned, standing = reachableQuotes |> List.partition (fun q -> (moduleLevelOwner q).IsSome)
    let ownedBindings = owned |> List.choose moduleLevelOwner |> Set.ofList
    /// A reference made from inside another quotation is compile-time structure (a descriptor
    /// citing a descriptor), not executed code.
    let rec insideQuotation (id: NodeId) =
        match Map.tryFind id parents |> Option.bind (fun p -> Map.tryFind p nodes) with
        | Some ({ Kind = SemanticKind.Quote _ } : SemanticNode) -> true
        | Some p -> insideQuotation p.Id
        | None -> false
    let atReferences =
        nodes
        |> Map.toList
        |> List.choose (fun (_, n) ->
            match n.Kind with
            | SemanticKind.VarRef (_, Some bindingId) when n.IsReachable && Set.contains bindingId ownedBindings && not (insideQuotation n.Id) -> Some (diagnostic n)
            | _ -> None)
    atReferences @ (standing |> List.map diagnostic)

//-------------------------------------------------------------------------
// `+` on strings is concat (design c.3, D5; sequence CS-9)
//-------------------------------------------------------------------------

/// `+` is one intrinsic whose typing dispatches on the kind of its operands: the operand variable
/// binds to a numeric type or to string in the unifier (`fireOperandDispatch`), and the unifier
/// has no node to rewrite. This is the one place the dispatch reaches the graph: at the store
/// boundary, over the resolved node map after monomorphisation (so a generalised `x + y` used at
/// strings is rewritten in its string clone), every application of `op_Addition` whose resolved
/// type is string has its function node carry the `String.concat2` intrinsic that Alex witnesses
/// atomically. Composer transcribes; it never decides which `+` this is. A `+` whose type is still
/// a variable here is the CCS8001 the binding-level check reports, never rewritten.
let private dispatchStringAddition (nodes: Map<NodeId, SemanticNode>) : Map<NodeId, SemanticNode> =
    let concat2 =
        { Module = IntrinsicModule.String; Operation = "concat2"; Category = IntrinsicCategory.StringOp; FullName = "String.concat2" }
    let isAddition (fn: NodeId) =
        match Map.tryFind fn nodes with
        | Some { Kind = SemanticKind.Intrinsic info } -> info.Module = IntrinsicModule.Operators && info.Operation = "op_Addition"
        | _ -> false
    let stringAdditions =
        nodes
        |> Map.toSeq
        |> Seq.choose (fun (_, node) ->
            match node.Kind with
            | SemanticKind.Application (fn, _) when isStringType node.Type && isAddition fn -> Some fn
            | _ -> None)
        |> Set.ofSeq
    if Set.isEmpty stringAdditions then nodes
    else
        nodes
        |> Map.map (fun id node ->
            if Set.contains id stringAdditions then { node with Kind = SemanticKind.Intrinsic concat2 } else node)

/// A source-reference check before monomorphisation or pruning. Project ownership
/// comes from .fidproj; dependency exports and library APIs are not unused locals.
let private unusedBindingDiagnostics (ownedSources: Set<string>) (graph: SemanticGraph) (diagnostics: Diagnostic list) =
    let rec functionType = function
        | NativeType.TFun _ -> true
        | NativeType.TForall(_, body) -> functionType body
        | _ -> false
    let hasEntry = graph.Nodes.Values |> Seq.exists (fun node ->
        match node.Kind with
        | SemanticKind.Binding(name, _, _, root) -> name = "main" || root.IsSome
        | _ -> false)
    if Set.isEmpty ownedSources || not hasEntry then []
    else
        let within (outer: SourceRange) (inner: SourceRange) =
            outer.File = inner.File
            && (outer.Start.Line, outer.Start.Column) <= (inner.Start.Line, inner.Start.Column)
            && (inner.End.Line, inner.End.Column) <= (outer.End.Line, outer.End.Column)
        let qualified = buildQualifiedBindingIndex graph
        let references =
            graph.Nodes.Values
            |> Seq.choose (fun node ->
                let target =
                    match node.Kind with
                    | SemanticKind.VarRef(_, Some target) -> Some target
                    | _ -> getStringLiteralBindingRef node qualified
                target |> Option.map (fun target -> target, node.Range))
            |> Seq.groupBy fst
            |> Seq.map (fun (target, uses) -> target, uses |> Seq.map snd |> Seq.toList)
            |> Map.ofSeq
        graph.Nodes.Values |> Seq.choose (fun node ->
            match node.Kind, Map.tryFind "SourceBinding.NameRange" node.Metadata, Map.tryFind "SourceBinding.FullRange" node.Metadata with
            | SemanticKind.Binding(name, false, _, None), Some (MetadataValue.SourceRange nameRange), Some (MetadataValue.SourceRange fullRange)
                when name <> "main" && not (name.StartsWith("_", System.StringComparison.Ordinal))
                     && Set.contains nameRange.File ownedSources
                     && (functionType node.Type || Map.tryFind "SourceBinding.Local" node.Metadata = Some (MetadataValue.Bool true))
                     && not (Map.containsKey "FidelityExtern.Library" node.Metadata) ->
                let used = Map.tryFind node.Id references |> Option.defaultValue [] |> List.exists (fun useRange -> not (within fullRange useRange))
                let failed = diagnostics |> List.exists (fun diagnostic -> diagnostic.Severity = NativeDiagnosticSeverity.Error && within fullRange diagnostic.Range)
                if used || failed then None
                else Some {
                    Severity = NativeDiagnosticSeverity.Warning
                    Code = DiagnosticCodes.CCS8500_UnusedBinding
                    Message =
                        if functionType node.Type then sprintf "The function '%s' is not referenced in this executable project." name
                        else sprintf "The local value '%s' is not referenced." name
                    Range = nameRange
                    RelatedNodes = [node.Id]
                    Reachability = ReachabilityContext.Unknown
                }
            | _ -> None)
        // Inline expansion can revisit the same source let. Its original
        // identifier receives one diagnostic, regardless of expansion count.
        |> Seq.distinctBy (fun diagnostic -> diagnostic.Range)
        |> Seq.toList

/// Build a CheckResult from builder state and diagnostics
/// platformContext: Optional platform context for freestanding builds (enables entry point elaboration)
let private buildResult (builder: NodeBuilder) (topLevelNodes: SemanticNode list) (modulePaths: Map<ModulePath, NodeId list>) (diagnostics: Diagnostic list) (platformContext: PlatformContext option) (ownedSources: Set<string>) : CheckResult =
    let declRoots = findDeclarationRoots builder.Nodes topLevelNodes

    // CRITICAL: Apply type substitutions to resolve type variables after constraint solving.
    // During type checking, nodes are created with fresh type variables that get unified
    // with concrete types. The substitutions are stored in UnionFind but not automatically
    // applied to node types. Resolve them throughout node metadata as well, without choosing
    // representations or retiring type structure consumed by later stages.
    let resolvedNodes =
        builder.Nodes
        |> Map.map (fun _id node -> SemanticGraph.mapNodeTypes applySubst node)
        // An application of a generalised binding records its instance (design b.4 step 4).
        |> annotateInstantiations
    // The saturation residual (CS-8): asserted here, where types have left the stores and before
    // the map is copied per instantiation; from here the node map is immutable (I2).
    let residual = saturationResidual builder resolvedNodes diagnostics
    let sourceNodes = resolvedNodes
    let resolvedNodes =
        resolvedNodes
        // Generic (TForall) top-level functions are compiled once per instantiation.
        |> Monomorphization.run
        // `+` resolved at the string kind carries the concat intrinsic (design c.3, D5).
        |> dispatchStringAddition

    let graph = {
        Nodes = resolvedNodes
        DeclarationRoots = declRoots
        Modules = modulePaths
        // Types extracted lazily from witnessed TypeDef nodes (codata pattern)
        Types = SemanticGraph.mkTypesIndex resolvedNodes
        // Platform context - set by project checker for freestanding builds
        // This must be set BEFORE entry point elaboration runs in the nanopass pipeline
        Platform = platformContext
        // Module classifications computed lazily from EmissionStrategy
        ModuleClassifications = SemanticGraph.mkModuleClassifications resolvedNodes
        // Seq saturation computed lazily from SeqExpr nodes (codata pattern)
        SeqSaturation = SemanticGraph.mkSeqSaturation resolvedNodes
        // Per-field record ranges: written by RangeAnalysis at saturation (CS-10)
        FieldRanges = lazy Map.empty
        ElementRanges = lazy Map.empty
        Layouts = lazy Map.empty
        StaticStringPool = None
        Escaping = lazy Map.empty
        Codata = lazy Codata.empty
        // F is empty at construction; enrichment mints into it at saturation.
        Edges = []
    }

    // Phase 1: Emit structural construction result
    let unusedBindings = unusedBindingDiagnostics ownedSources { graph with Nodes = sourceNodes } (diagnostics @ residual)
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
    RecipeSerialization.emitIntrinsicDiagnostics intrinsicRecipes.Diagnostics  // Artifact 02a

    // Pass 2: Intrinsic Fold-In - Build PSG₁ with intrinsic elaborations
    let psg1 = IntrinsicElaboration.foldIn intrinsicRecipes reachableGraph
    if PhaseConfig.shouldEmit() then
        emitPhaseIfEnabled PhaseTypes.PhaseId.BakerModuleInit psg1 diagnostics  // Artifact 03

    // Pass 2.5: Entry Point Elaboration (Freestanding mode only)
    // Adds _start wrapper that calls main with argc/argv from stack
    let psg1WithDeclRoots = IntrinsicElaboration.elaborateEntryPoints psg1

    // Pass 3: Saturation Fan-Out - Create Baker decomposition recipes
    let saturationRecipes = BakerSaturation.fanOut psg1WithDeclRoots
    RecipeSerialization.emitSaturationRecipes saturationRecipes  // Artifact 04
    RecipeSerialization.emitSaturationDiagnostics saturationRecipes.Diagnostics  // Artifact 04a

    // Pass 4: Saturation Fold-In - Build PSG₂ with decomposed structures
    let foldedGraph = BakerSaturation.foldIn saturationRecipes psg1WithDeclRoots

    // Pass 4.5: Recompute Reachability After Fold-In
    // Baker fold-in replaces Application nodes with decomposed sub-trees.
    // Original intrinsic function nodes (e.g., String.concat2 intrinsic) may become
    // orphaned - they have parent pointers but are not in any children lists.
    // Recompute reachability to mark these orphans as unreachable.
    let finalGraph =
        if PhaseConfig.useSoftDeleteReachability() then
            markUnreachable foldedGraph
        else
            pruneUnreachable foldedGraph

    //=========================================================================
    // Pass 5: Obligation Elaboration -- the declared platform, cross-compiled
    // into this graph, cross-applied with the saturated program. Obligations
    // are minted into V and F by the Baker obligation recipes (C-01 14.5;
    // Obligation_Residency 3) and discharged from F at design time (06a/06b).
    // Runs after final reachability: the layout obligation ranges over the
    // complete reachable literal set. Obligation nodes are off the emission
    // spine; the witness never sees them (PHG paper 2.4).
    //=========================================================================
    let finalGraph = ObligationElaboration.foldIn (ObligationElaboration.elaborate finalGraph) finalGraph

    //=========================================================================
    // The declared platform fills the context (plan D8, L-13): the graph is
    // complete, the description compiled into it is read once, and its width
    // dimensions and representations become the context Composer reads. Every
    // reachable sealed site is then checked against that declaration (CCS8203,
    // CCS8204). This is the one place the context's Dimensions are written.
    //=========================================================================
    let platformContext = PlatformDeclaration.fill platformContext finalGraph
    let finalGraph = { finalGraph with Platform = platformContext }

    //=========================================================================
    // The range pass (CS-10, Dimensional_Range_Design.md §1): every reachable
    // integer carries its analysed range as a coeffect beside its type, every
    // record type its per-field ranges, and an unobservable range is CCS8011.
    // Runs on every substrate over the complete graph, after the declared
    // platform has filled the context (its representations are the widening
    // thresholds) and before the declaration is checked.
    //=========================================================================
    let finalGraph, rangeDiagnostics = RangeAnalysis.run platformContext finalGraph

    //=========================================================================
    // Placement (CS-11 slice 0, Dimensional_Range_Design.md ruling 2): every
    // reachable record, union, tuple, option and Result type takes its settled
    // layout from its fields' selections and the declared Pointer width, and
    // the graph carries it (Layouts). Composer reads it and computes no size.
    //=========================================================================
    let finalGraph = Placement.settle platformContext finalGraph
    let finalGraph, staticLayoutDiagnostics = Clef.Compiler.PSGSaturation.SemanticGraph.StaticStringLayout.settle finalGraph
    let settledObligations, realLiteralDiagnostics = ObligationElaboration.elaborateSettled finalGraph
    let finalGraph = ObligationElaboration.foldIn settledObligations finalGraph
    ObligationDischarge.emit finalGraph  // Both structural and settled numeric obligations.

    //=========================================================================
    // Emission codata (CCS_Architecture.md, the coeffect table): the curried
    // chains normalised, and every fact Composer's witnesses read settled on the
    // graph: the escape of each allocating site, the partial applications, the
    // meets, the closure environments, the platform call sites and the pins, the
    // declaration roots' lambdas. Composer reads Codata and computes none of it.
    //=========================================================================
    let finalGraph, curry = Curry.normalize finalGraph
    let functionPointers, functionPointerDiagnostics = FunctionPointers.settle finalGraph
    let mmio, mmioDiagnostics = Clef.Compiler.PSGSaturation.SemanticGraph.DeviceAccess.settle (diagnostics @ residual @ rangeDiagnostics) finalGraph
    let finalGraph =
        let settled = finalGraph
        { finalGraph with
            Codata = lazy {
                Escapes = Escape.analyze settled
                Curry = curry
                Meets = Meets.derive platformContext settled curry
                ReturnMeets = Meets.returns platformContext settled
                Closures = Placement.closures platformContext settled
                Bindings = PlatformBindings.resolve platformContext settled
                Pins = PlatformBindings.pins settled
                DeclarationRootLambdas = Roots.declarationRootLambdas settled
                FunctionPointers = functionPointers
                Mmio = mmio } }

    let declarationDiagnostics = PlatformDeclaration.check platformContext finalGraph
    let quotationErrors = quotationDiagnostics finalGraph

    // Phase 5: Emit final result
    emitPhaseIfEnabled PhaseTypes.PhaseId.Final finalGraph diagnostics

    // Emit ClefExpr view (expression-centric representation)
    PhaseEmitter.emitExpressionView finalGraph
    PhaseEmitter.emitExpressionText finalGraph

    // Tag diagnostics with reachability context.
    // Strategy: Build a (file, line) → IsReachable index from the graph.
    // If ANY node at a diagnostic's source line is reachable, the diagnostic is Reachable.
    // If ALL nodes at that line are unreachable, the diagnostic is Unreachable.
    // If no nodes found (e.g., empty range), conservative Unknown.
    let reachableLines =
        finalGraph.Nodes
        |> Map.values
        |> Seq.filter (fun node -> node.Range.File <> "" && node.IsReachable)
        |> Seq.collect (fun node ->
            seq { for line in node.Range.Start.Line .. node.Range.End.Line do
                    yield (node.Range.File, line) })
        |> Set.ofSeq

    let tagReachability (d: Diagnostic) =
        if d.Range.File = "" then { d with Reachability = ReachabilityContext.Unknown }
        else
            let lineRange = d.Range.Start.Line
            if Set.contains (d.Range.File, lineRange) reachableLines then
                { d with Reachability = ReachabilityContext.Reachable }
            else
                { d with Reachability = ReachabilityContext.Unreachable }

    let taggedDiagnostics = (diagnostics @ residual) |> List.map tagReachability

    // Layer 1: Combinational depth analysis (FPGA-only structural heuristic)
    // Walks the final PSG bottom-up, counting weighted operation depth.
    // Reports paths exceeding threshold as Info diagnostics.
    let depthDiagnostics = DepthAnalysis.analyze platformContext finalGraph

    {
        Graph = finalGraph
        Diagnostics = taggedDiagnostics @ rangeDiagnostics @ staticLayoutDiagnostics @ realLiteralDiagnostics @ declarationDiagnostics @ quotationErrors @ depthDiagnostics @ unusedBindings @ functionPointerDiagnostics @ mmioDiagnostics
        PlatformContext = platformContext
    }

//-------------------------------------------------------------------------
// Type Checking: Expression Level
//-------------------------------------------------------------------------

/// Check a single expression and return a semantic node.
/// This is the low-level API for testing the type checker.
//-------------------------------------------------------------------------
// Expression Dispatch: Routes SynExpr to handler modules
// This is a PURE ROUTING function with ZERO type logic.
// All type checking logic lives in the handler modules.
//-------------------------------------------------------------------------

/// Check a pattern and return bindings
let rec private checkPattern (env: TypeEnv) (pat: SynPat) (expectedTy: NativeType) (range: SourceRange) : Pattern * (string * NativeType) list =
    Patterns.checkPattern env pat expectedTy range

/// Check a match clause with scrutinee ID for record pattern field extraction
and private checkMatchClause (env: TypeEnv) (builder: NodeBuilder) (scrutineeId: NodeId) (scrutineeTy: NativeType) (resultTy: NativeType) (clause: SynMatchClause) : MatchCase =
    checkMatchClause' checkExpr checkPattern env builder scrutineeId scrutineeTy resultTy clause

/// Internal match clause checker
and private checkMatchClause' (checkExpr: CheckExprFn) (checkPattern: TypeEnv -> SynPat -> NativeType -> SourceRange -> Pattern * (string * NativeType) list) (env: TypeEnv) (builder: NodeBuilder) (scrutineeId: NodeId) (scrutineeTy: NativeType) (resultTy: NativeType) (clause: SynMatchClause) : MatchCase =
    Bindings.checkMatchClause checkExpr checkPattern env builder scrutineeId scrutineeTy resultTy clause

/// Main expression checker. Routes SynExpr to appropriate handlers.
/// This is a pure dispatcher - all type logic lives in handler modules.
and private checkExpr (env: TypeEnv) (builder: NodeBuilder) (syn: SynExpr) : SemanticNode =
    let range = rangeToSourceRange syn.Range

    match syn with
    //---------------------------------------------------------------------
    // Literals
    //---------------------------------------------------------------------
    | SynExpr.Const(constant, _) ->
        Literals.warnSuffix syn.Range constant env
        match Literals.checkConst env constant with
        | Result.Ok (ty, litVal) ->
            let node = builder.Create(SemanticKind.Literal litVal, ty, range)
            match Literals.realLiteralMetadata constant with
            | Some metadata -> builder.SetMetadata(node.Id, "Numeric.RealLiteral", metadata)
            | None -> node
        | Result.Error failure ->
            // CCS8018 (plan L-3) or a measure failure (design a.4): an error node, not a type.
            Literals.addConstFailure syn.Range failure env
            let msg = Literals.constFailureMessage failure
            builder.Create(SemanticKind.Error msg, NativeType.TError msg, range)

    //---------------------------------------------------------------------
    // Parenthesized expressions (transparent)
    //---------------------------------------------------------------------
    | SynExpr.Paren(innerExpr, _, _, _) ->
        checkExpr env builder innerExpr

    //---------------------------------------------------------------------
    // Variable references (includes intrinsic dispatch)
    //---------------------------------------------------------------------
    | SynExpr.Ident(ident) ->
        Identity.resolveIdentifier [ident.idText] env builder range ident.idRange

    | SynExpr.LongIdent(_, longDotId, _, _) ->
        let parts = longDotId.LongIdent |> List.map (fun id -> id.idText)
        Identity.resolveIdentifier parts env builder range syn.Range

    //---------------------------------------------------------------------
    // Type annotations
    //---------------------------------------------------------------------
    | SynExpr.Typed(innerExpr, synType, _) ->
        TypeOperations.checkTyped checkExpr env builder innerExpr synType range

    //---------------------------------------------------------------------
    // Tuples
    //---------------------------------------------------------------------
    | SynExpr.Tuple(isStruct, exprs, _, _) ->
        Collections.checkTuple checkExpr env builder isStruct exprs range

    //---------------------------------------------------------------------
    // F# 6 dotless indexer syntax: expr[index]
    //---------------------------------------------------------------------
    | SynExpr.App(_, _, objExpr, SynExpr.ArrayOrListComputed(false, indexExpr, _), _) ->
        Collections.checkDotlessIndexGet checkExpr env builder objExpr indexExpr range

    //---------------------------------------------------------------------
    // Sequence expression: seq { ... }
    //---------------------------------------------------------------------
    | SynExpr.App(_, _, SynExpr.Ident(ident), SynExpr.ComputationExpr(_, compExpr, _), _)
        when ident.idText = "seq" ->
        Collections.checkSeq checkExpr Applications.computeCaptures env builder compExpr range

    //---------------------------------------------------------------------
    // Function application
    //---------------------------------------------------------------------
    // `a || b` and `a && b` are the conditionals F# defines them as (`if a then true else b`,
    // `if a then b else false`): the right operand is evaluated only when the left one does not
    // decide. Lowering them as an eager `ori`/`andi` over both operands runs the right operand
    // unconditionally (a guarded division faults), so they are desugared here, before checking.
    | SynExpr.App(_, false, SynExpr.App(_, true, (SynExpr.Ident opIdent | SynExpr.LongIdent(_, SynLongIdent([opIdent], _, _), _, _)), leftExpr, _), rightExpr, appRange)
        when opIdent.idText = "op_BooleanOr" || opIdent.idText = "op_BooleanAnd" ->
        let boolConst (b: bool) = SynExpr.Const(SynConst.Bool b, appRange)
        let (thenExpr, elseExpr) =
            if opIdent.idText = "op_BooleanOr" then (boolConst true, rightExpr)
            else (rightExpr, boolConst false)
        let trivia : SynExprIfThenElseTrivia =
            { IfKeyword = appRange; IsElif = false; ThenKeyword = appRange; ElseKeyword = None; IfToThenRange = appRange }
        checkExpr env builder (SynExpr.IfThenElse(leftExpr, thenExpr, Some elseExpr, DebugPointAtBinding.NoneAtInvisible, false, appRange, trivia))

    | SynExpr.App(_, _isInfix, funcExpr, argExpr, _) ->
        Applications.checkApp checkExpr env builder funcExpr argExpr syn.Range range

    //---------------------------------------------------------------------
    // Lambda expressions
    //---------------------------------------------------------------------
    | SynExpr.Lambda(_, _, args, bodyExpr, _, _, _) ->
        Applications.checkLambda checkExpr Bindings.extractLambdaParams env builder args bodyExpr range

    //---------------------------------------------------------------------
    // Let bindings
    //---------------------------------------------------------------------
    | SynExpr.LetOrUse(letOrUse) ->
        Bindings.checkLetOrUse checkExpr env builder letOrUse range

    //---------------------------------------------------------------------
    // Sequential expressions
    //---------------------------------------------------------------------
    | SynExpr.Sequential(_, _, expr1, expr2, _, _) ->
        ControlFlow.checkSequential checkExpr env builder expr1 expr2 range

    //---------------------------------------------------------------------
    // If-then-else
    //---------------------------------------------------------------------
    | SynExpr.IfThenElse(condExpr, thenExpr, elseExprOpt, _, _, _, _) ->
        ControlFlow.checkIfThenElse checkExpr env builder condExpr thenExpr elseExprOpt range

    //---------------------------------------------------------------------
    // While loops
    //---------------------------------------------------------------------
    | SynExpr.While(_, guardExpr, bodyExpr, _) ->
        ControlFlow.checkWhile checkExpr env builder guardExpr bodyExpr range

    //---------------------------------------------------------------------
    // For loops
    //---------------------------------------------------------------------
    | SynExpr.For(_, _, ident, _, startExpr, direction, endExpr, bodyExpr, _) ->
        ControlFlow.checkFor checkExpr env builder ident startExpr direction endExpr bodyExpr range

    //---------------------------------------------------------------------
    // Match expressions
    //---------------------------------------------------------------------
    | SynExpr.Match(_, scrutinee, clauses, _, _) ->
        ControlFlow.checkMatch checkExpr checkMatchClause env builder scrutinee clauses range

    //---------------------------------------------------------------------
    // Record expressions
    //---------------------------------------------------------------------
    | SynExpr.Record(_, copyInfo, fields, recordRange) ->
        Collections.checkRecord checkExpr env builder copyInfo fields recordRange range

    //---------------------------------------------------------------------
    // Array/list expressions
    //---------------------------------------------------------------------
    | SynExpr.ArrayOrList(isArray, exprs, _) ->
        Collections.checkArrayOrList checkExpr env builder isArray exprs range

    //---------------------------------------------------------------------
    // Try-with expressions
    //---------------------------------------------------------------------
    | SynExpr.TryWith(tryExpr, withCases, _, _, _, _) ->
        ControlFlow.checkTryWith checkExpr checkMatchClause env builder tryExpr withCases range

    //---------------------------------------------------------------------
    // Try-finally expressions
    //---------------------------------------------------------------------
    | SynExpr.TryFinally(tryExpr, finallyExpr, _, _, _, _) ->
        ControlFlow.checkTryFinally checkExpr env builder tryExpr finallyExpr range

    //---------------------------------------------------------------------
    // Field access
    //---------------------------------------------------------------------
    | SynExpr.DotGet(expr, _, longDotId, _) ->
        Collections.checkDotGet checkExpr env builder expr longDotId range

    //---------------------------------------------------------------------
    // Assignment - F# 6 dotless indexer set: expr[index] <- value
    //---------------------------------------------------------------------
    | SynExpr.Set(SynExpr.App(_, _, objExpr, SynExpr.ArrayOrListComputed(false, indexExpr, _), _), valueExpr, _) ->
        Collections.checkDotlessIndexSet checkExpr env builder objExpr indexExpr valueExpr range

    //---------------------------------------------------------------------
    // Assignment - General case
    //---------------------------------------------------------------------
    | SynExpr.Set(targetExpr, valueExpr, _) ->
        Bindings.checkSet checkExpr env builder targetExpr valueExpr range

    //---------------------------------------------------------------------
    // Do expressions
    //---------------------------------------------------------------------
    | SynExpr.Do(expr, _) ->
        checkExpr env builder expr

    //---------------------------------------------------------------------
    // Null - REJECTED in Clef (CCS8010)
    //---------------------------------------------------------------------
    | SynExpr.Null r ->
        addNullError r env
        builder.Create(
            SemanticKind.Error "null is not supported in native F#",
            NativeType.TError "null not supported",
            rangeToSourceRange r)

    //---------------------------------------------------------------------
    // Quote expressions
    //---------------------------------------------------------------------
    | SynExpr.Quote(_, isRaw, quotedExpr, _, _) ->
        TypeOperations.checkQuote checkExpr env builder isRaw quotedExpr range

    //---------------------------------------------------------------------
    // Interpolated strings
    //---------------------------------------------------------------------
    | SynExpr.InterpolatedString(contents, _synStringKind, synRange) ->
        Literals.checkInterpolatedString checkExpr env builder contents synRange range

    //---------------------------------------------------------------------
    // AddressOf: &expr or &&expr
    //---------------------------------------------------------------------
    | SynExpr.AddressOf(isByref, innerExpr, _, _) ->
        TypeOperations.checkAddressOf checkExpr env builder isByref innerExpr range

    //---------------------------------------------------------------------
    // TypeApp: expr<type1, type2, ...>
    //---------------------------------------------------------------------
    | SynExpr.TypeApp(funcExpr, _, typeArgs, _, _, _, _) ->
        Applications.checkTypeApp checkExpr env builder funcExpr typeArgs syn.Range range

    //---------------------------------------------------------------------
    // ForEach: for x in collection do body
    //---------------------------------------------------------------------
    | SynExpr.ForEach(_, _, _, _, pat, enumExpr, bodyExpr, _) ->
        ControlFlow.checkForEach checkExpr env builder pat enumExpr bodyExpr range

    //---------------------------------------------------------------------
    // TraitCall: SRTP member invocation
    //---------------------------------------------------------------------
    | SynExpr.TraitCall(supportTys, memberSig, argExpr, _) ->
        Applications.checkTraitCall checkExpr env builder supportTys memberSig argExpr range

    //---------------------------------------------------------------------
    // Upcast: expr :> type
    //---------------------------------------------------------------------
    | SynExpr.Upcast(innerExpr, targetType, _) ->
        TypeOperations.checkUpcast checkExpr env builder innerExpr targetType range

    //---------------------------------------------------------------------
    // InferredUpcast: upcast expr
    //---------------------------------------------------------------------
    | SynExpr.InferredUpcast(innerExpr, _) ->
        TypeOperations.checkInferredUpcast checkExpr env builder innerExpr range

    //---------------------------------------------------------------------
    // Downcast: expr :?> type
    //---------------------------------------------------------------------
    | SynExpr.Downcast(innerExpr, targetType, _) ->
        TypeOperations.checkDowncast checkExpr env builder innerExpr targetType range

    //---------------------------------------------------------------------
    // InferredDowncast: downcast expr
    //---------------------------------------------------------------------
    | SynExpr.InferredDowncast(innerExpr, _) ->
        TypeOperations.checkInferredDowncast checkExpr env builder innerExpr range

    //---------------------------------------------------------------------
    // TypeTest: expr :? type
    //---------------------------------------------------------------------
    | SynExpr.TypeTest(innerExpr, targetType, _) ->
        TypeOperations.checkTypeTest checkExpr env builder innerExpr targetType range

    //---------------------------------------------------------------------
    // DotIndexedGet: expr.[index]
    //---------------------------------------------------------------------
    | SynExpr.DotIndexedGet(objExpr, indexArgs, _, _) ->
        Collections.checkDotIndexedGet checkExpr env builder objExpr indexArgs range

    //---------------------------------------------------------------------
    // DotIndexedSet: expr.[index] <- value
    //---------------------------------------------------------------------
    | SynExpr.DotIndexedSet(objExpr, indexArgs, valueExpr, _, _, _) ->
        Collections.checkDotIndexedSet checkExpr env builder objExpr indexArgs valueExpr range

    //---------------------------------------------------------------------
    // DotSet: expr.field <- value
    //---------------------------------------------------------------------
    | SynExpr.DotSet(objExpr, SynLongIdent(longId, _, _), valueExpr, _) ->
        Bindings.checkDotSet checkExpr env builder objExpr longId valueExpr range

    //---------------------------------------------------------------------
    // LongIdentSet: Module.value <- expr
    //---------------------------------------------------------------------
    | SynExpr.LongIdentSet(SynLongIdent(longId, _, _), valueExpr, _) ->
        Bindings.checkLongIdentSet checkExpr env builder longId valueExpr range

    //---------------------------------------------------------------------
    // Lazy: lazy expr
    //---------------------------------------------------------------------
    | SynExpr.Lazy(innerExpr, _) ->
        Collections.checkLazy checkExpr Applications.computeCaptures env builder innerExpr range

    //---------------------------------------------------------------------
    // Assert: assert expr
    //---------------------------------------------------------------------
    | SynExpr.Assert(condExpr, _) ->
        ControlFlow.checkAssert checkExpr env builder condExpr range

    //---------------------------------------------------------------------
    // New: new Type(args)
    //---------------------------------------------------------------------
    | SynExpr.New(_, synType, argExpr, _) ->
        Applications.checkNew checkExpr env builder synType argExpr range

    //---------------------------------------------------------------------
    // ObjExpr: { new Interface with ... }
    //---------------------------------------------------------------------
    | SynExpr.ObjExpr(objType, argOption, _, bindings, members, extraImpls, _, _) ->
        Applications.checkObjExpr checkExpr env builder objType argOption bindings members extraImpls range

    //---------------------------------------------------------------------
    // AnonRecd: {| field = value |}
    //---------------------------------------------------------------------
    | SynExpr.AnonRecd(isStruct, copyInfo, recordFields, _, _trivia) ->
        Collections.checkAnonRecd checkExpr env builder isStruct copyInfo recordFields range

    //---------------------------------------------------------------------
    // MatchLambda: function | pat -> expr
    //---------------------------------------------------------------------
    | SynExpr.MatchLambda(_isExnMatch, _keywordRange, clauses, _matchSeqPoint, _) ->
        Collections.checkMatchLambda checkExpr checkMatchClause env builder clauses range

    //---------------------------------------------------------------------
    // ArrayOrListComputed: [| for x in xs -> f x |] or [ for x in xs -> f x ]
    //---------------------------------------------------------------------
    | SynExpr.ArrayOrListComputed(isArray, compExpr, _) ->
        Collections.checkArrayOrListComputed checkExpr env builder isArray compExpr range

    //---------------------------------------------------------------------
    // ComputationExpr: seq { ... } or other { ... }
    //---------------------------------------------------------------------
    | SynExpr.ComputationExpr(hasSeqBuilder, compExpr, _) ->
        if hasSeqBuilder then
            Collections.checkSeq checkExpr Applications.computeCaptures env builder compExpr range
        else
            let compNode = checkExpr env builder compExpr
            builder.Create(
                SemanticKind.Sequential [compNode.Id],
                compNode.Type,
                range,
                children = [compNode.Id])

    //---------------------------------------------------------------------
    // YieldOrReturn: yield expr or return expr
    //---------------------------------------------------------------------
    | SynExpr.YieldOrReturn((isYield, _isReturn), expr, _, _trivia) ->
        if isYield && env.EnclosingSeqExpr.IsSome then
            Collections.checkYield checkExpr env builder expr range
        else
            checkExpr env builder expr

    //---------------------------------------------------------------------
    // YieldOrReturnFrom: yield! expr or return! expr
    //---------------------------------------------------------------------
    | SynExpr.YieldOrReturnFrom((isYield, _isReturn), expr, _, _trivia) ->
        if isYield && env.EnclosingSeqExpr.IsSome then
            Collections.checkYieldBang checkExpr env builder expr range
        else
            checkExpr env builder expr

    //---------------------------------------------------------------------
    // DoBang: do! expr
    //---------------------------------------------------------------------
    | SynExpr.DoBang(expr, _, _trivia) ->
        let exprNode = checkExpr env builder expr
        builder.Create(
            SemanticKind.Sequential [exprNode.Id],
            Types.unitType,
            range,
            children = [exprNode.Id])

    //---------------------------------------------------------------------
    // MatchBang: match! expr with ...
    //---------------------------------------------------------------------
    | SynExpr.MatchBang(_, expr, clauses, _, _) ->
        ControlFlow.checkMatchBang checkExpr checkPattern env builder expr clauses range

    //---------------------------------------------------------------------
    // WhileBang: while! expr do body
    //---------------------------------------------------------------------
    | SynExpr.WhileBang(_, guardExpr, bodyExpr, _) ->
        let guardNode = checkExpr env builder guardExpr
        let bodyNode = checkExpr env builder bodyExpr
        builder.Create(
            SemanticKind.WhileLoop(guardNode.Id, bodyNode.Id),
            Types.unitType,
            range,
            children = [guardNode.Id; bodyNode.Id])

    //---------------------------------------------------------------------
    // ImplicitZero: implicit unit in computation expressions
    //---------------------------------------------------------------------
    | SynExpr.ImplicitZero _ ->
        builder.Create(
            SemanticKind.Literal NativeLiteral.Unit,
            Types.unitType,
            range)

    //---------------------------------------------------------------------
    // SequentialOrImplicitYield: expr1; expr2 in comp expr
    //---------------------------------------------------------------------
    | SynExpr.SequentialOrImplicitYield(_, expr1, expr2, _, _) ->
        let node1 = checkExpr env builder expr1
        let node2 = checkExpr env builder expr2
        builder.Create(
            SemanticKind.Sequential [node1.Id; node2.Id],
            node2.Type,
            range,
            children = [node1.Id; node2.Id])

    //---------------------------------------------------------------------
    // Fixed: fixed expr — C-marshaling vocabulary (GC pinning); no GC here,
    // no pointer surface. Grammar is inherited unforked; the construct errors.
    //---------------------------------------------------------------------
    | SynExpr.Fixed _ ->
        builder.Create(
            SemanticKind.Error "'fixed' is not supported in native compilation",
            NativeType.TError "fixed expression",
            range)

    //---------------------------------------------------------------------
    // Dynamic: expr?name (dynamic member access)
    //---------------------------------------------------------------------
    | SynExpr.Dynamic(objExpr, _, memberExpr, _) ->
        let objNode = checkExpr env builder objExpr
        let memberNode = checkExpr env builder memberExpr
        builder.Create(
            SemanticKind.Application(objNode.Id, [memberNode.Id]),
            freshTypeVar range,
            range,
            children = [objNode.Id; memberNode.Id])

    //---------------------------------------------------------------------
    // DotLambda: _.Property (shorthand lambda)
    //---------------------------------------------------------------------
    | SynExpr.DotLambda(innerExpr, _, _) ->
        let innerNode = checkExpr env builder innerExpr
        let argType = freshTypeVar range
        let paramNode = builder.Create(
            SemanticKind.PatternBinding("_"),
            argType,
            range)
        let lambdaNode = builder.Create(
            SemanticKind.Lambda([("_", argType, paramNode.Id)], innerNode.Id, [], env.EnclosingFunction, LambdaContext.RegularClosure),
            NativeType.TFun(argType, innerNode.Type),
            range,
            children = [paramNode.Id; innerNode.Id])
        builder.SetEmissionStrategy(innerNode.Id, EmissionStrategy.SeparateFunction 0)
        lambdaNode

    //---------------------------------------------------------------------
    // DotNamedIndexedPropertySet: obj.Prop[idx] <- value
    //---------------------------------------------------------------------
    | SynExpr.DotNamedIndexedPropertySet(objExpr, SynLongIdent(longId, _, _), indexExpr, valueExpr, _) ->
        Bindings.checkDotNamedIndexedPropertySet checkExpr env builder objExpr longId indexExpr valueExpr range

    //---------------------------------------------------------------------
    // NamedIndexedPropertySet: Prop(idx) <- value
    //---------------------------------------------------------------------
    | SynExpr.NamedIndexedPropertySet(SynLongIdent(longId, _, _), indexExpr, valueExpr, _) ->
        let indexNode = checkExpr env builder indexExpr
        let valueNode = checkExpr env builder valueExpr
        let propName = longId |> List.map (fun id -> id.idText) |> String.concat "."
        builder.Create(
            SemanticKind.Error $"NamedIndexedPropertySet '{propName}' - requires context",
            Types.unitType,
            range,
            children = [indexNode.Id; valueNode.Id])

    //---------------------------------------------------------------------
    // Typar: 'a (type parameter in expression position)
    //---------------------------------------------------------------------
    | SynExpr.Typar(SynTypar(ident, _, _), _) ->
        let typarName = ident.idText
        builder.Create(
            SemanticKind.Error $"Type parameter '{typarName}' in expression position",
            freshTypeVar range,
            range)

    //---------------------------------------------------------------------
    // IndexRange: expr.[start..finish]
    //---------------------------------------------------------------------
    | SynExpr.IndexRange(startOpt, _, finishOpt, _, _, _) ->
        let startNode = startOpt |> Option.map (checkExpr env builder)
        let finishNode = finishOpt |> Option.map (checkExpr env builder)
        let children = [startNode; finishNode] |> List.choose id |> List.map (fun n -> n.Id)
        builder.Create(
            SemanticKind.Error "IndexRange - requires slice support",
            freshTypeVar range,
            range,
            children = children)

    //---------------------------------------------------------------------
    // IndexFromEnd: ^expr (index from end)
    //---------------------------------------------------------------------
    | SynExpr.IndexFromEnd(expr, _) ->
        let exprNode = checkExpr env builder expr
        builder.Create(
            SemanticKind.Application(exprNode.Id, []),
            Types.intType,
            range,
            children = [exprNode.Id])

    //---------------------------------------------------------------------
    // JoinIn: join ... in ... (query syntax)
    //---------------------------------------------------------------------
    | SynExpr.JoinIn(expr1, _, expr2, _) ->
        let node1 = checkExpr env builder expr1
        let node2 = checkExpr env builder expr2
        builder.Create(
            SemanticKind.Error "JoinIn - query syntax not supported",
            freshTypeVar range,
            range,
            children = [node1.Id; node2.Id])

    //---------------------------------------------------------------------
    // DebugPoint: debugging information (transparent)
    //---------------------------------------------------------------------
    | SynExpr.DebugPoint(_, _, innerExpr) ->
        checkExpr env builder innerExpr

    //---------------------------------------------------------------------
    // ArbitraryAfterError: parse recovery node
    //---------------------------------------------------------------------
    | SynExpr.ArbitraryAfterError(_, _) ->
        builder.Create(
            SemanticKind.Error "Parse error recovery node",
            NativeType.TError "parse error",
            range)

    //---------------------------------------------------------------------
    // FromParseError: parse error wrapper
    //---------------------------------------------------------------------
    | SynExpr.FromParseError(innerExpr, _) ->
        let innerNode = checkExpr env builder innerExpr
        builder.Create(
            SemanticKind.Error "Expression contains parse error",
            innerNode.Type,
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // DiscardAfterMissingQualificationAfterDot: A. (incomplete dot access)
    //---------------------------------------------------------------------
    | SynExpr.DiscardAfterMissingQualificationAfterDot(innerExpr, _, _) ->
        let innerNode = checkExpr env builder innerExpr
        builder.Create(
            SemanticKind.Error "Incomplete member access (missing qualifier after dot)",
            freshTypeVar range,
            range,
            children = [innerNode.Id])

    //---------------------------------------------------------------------
    // LibraryOnlyILAssembly: inline IL (FSharp.Core internal)
    //---------------------------------------------------------------------
    | SynExpr.LibraryOnlyILAssembly _ ->
        builder.Create(
            SemanticKind.Error "Inline IL assembly is not supported in native compilation",
            NativeType.TError "IL assembly",
            range)

    //---------------------------------------------------------------------
    // LibraryOnlyStaticOptimization: static optimization (FSharp.Core internal)
    //---------------------------------------------------------------------
    | SynExpr.LibraryOnlyStaticOptimization _ ->
        builder.Create(
            SemanticKind.Error "Static optimization is not supported in native compilation",
            NativeType.TError "static optimization",
            range)

    //---------------------------------------------------------------------
    // LibraryOnlyUnionCaseFieldGet: internal union field access
    //---------------------------------------------------------------------
    | SynExpr.LibraryOnlyUnionCaseFieldGet(expr, _, _, _) ->
        let exprNode = checkExpr env builder expr
        builder.Create(
            SemanticKind.Error "Library-only union case field get",
            freshTypeVar range,
            range,
            children = [exprNode.Id])

    //---------------------------------------------------------------------
    // LibraryOnlyUnionCaseFieldSet: internal union field set
    //---------------------------------------------------------------------
    | SynExpr.LibraryOnlyUnionCaseFieldSet(expr, _, _, valueExpr, _) ->
        let exprNode = checkExpr env builder expr
        let valueNode = checkExpr env builder valueExpr
        builder.Create(
            SemanticKind.Error "Library-only union case field set",
            Types.unitType,
            range,
            children = [exprNode.Id; valueNode.Id])

let checkExpression (expr: SynExpr) : CheckResult =
    let env = createTypeEnv()
    let builder = NodeBuilder()
    NodeId.reset()

    let node = checkExpr env builder expr
    let diagnostics = solveAndGetDiagnostics env !(env.Constraints)

    buildResult builder [node] Map.empty diagnostics None Set.empty

//-------------------------------------------------------------------------
// Type Checking: Binding Level
//-------------------------------------------------------------------------

/// Check a single let binding and return a semantic node.
/// Note: The inline body is intentionally discarded here because:
/// 1. This checks a single binding in isolation (no subsequent bindings to inline into)
/// 2. The Lambda node's child already contains the checked body for code generation
/// 3. InlineBody is for environment-based name resolution during multi-binding checking
let checkLetBinding (binding: SynBinding) : CheckResult =
    let env = createTypeEnv()
    let builder = NodeBuilder()
    NodeId.reset()

    // InlineBody, isMutable and literalValue discarded - see function doc comment for rationale
    let (node, _inlineBody, _isMutable, _literalValue) = Bindings.checkBinding checkExpr env builder binding None
    let diagnostics = solveAndGetDiagnostics env !(env.Constraints)

    buildResult builder [node] Map.empty diagnostics None Set.empty

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

/// Check if a type definition has the [<Measure>] attribute
let private hasMeasureAttribute (attrs: SynAttributes) : bool =
    attrs |> List.exists (fun attrList ->
        attrList.Attributes |> List.exists (fun attr ->
            match attr.TypeName.LongIdent with
            | [id] -> id.idText = "Measure" || id.idText = "MeasureAttribute"
            | _ -> false
        )
    )

/// Register the `[<Measure>] type` declarations of one group into the measure environment
/// (design a.3; sequence CS-4). A primitive is a declaration with no representation; an
/// abbreviation's right-hand side is read through the one translator (`dimensionOfSyntax`, as
/// `MeasureSyntax.Type`) against the environment as it stands, in the order
/// `MeasureEnv.registerGroup` derives from the names each body references (`measureReferences`).
/// Every failure is reported at its own declaration: registration returns the first failure and
/// registers nothing, so the declaration the failure lies in is set aside and the rest register,
/// until the group registers or no declaration remains. A declaration with a type
/// representation (a union, a record, `class end`) is not a measure: CCS8045 at the declaration.
/// No type node is produced: a measure lives in the environment, not in the graph.
let private registerMeasureDeclarations (ctx: ModuleContext) (env: TypeEnv) (measureDefns: SynTypeDefn list) : TypeEnv =
    let declOf (typeDef: SynTypeDefn) : Result<MeasureDecl<SynType>, MeasureFailure> =
        let (SynTypeDefn(SynComponentInfo(_, typars, _, longId, _, _, _, _), typeRepr, _, _, typeRange, _)) = typeDef
        let name = longId |> List.map (fun id -> id.idText) |> String.concat "."
        let parameters =
            match typars with
            | Some decls -> decls.TyparDecls |> List.map (fun (SynTyparDecl(_, SynTypar(id, _, _), _, _)) -> id.idText)
            | None -> []
        let body =
            match typeRepr with
            | SynTypeDefnRepr.Simple(SynTypeDefnSimpleRepr.None _, _) -> Ok None
            | SynTypeDefnRepr.Simple(SynTypeDefnSimpleRepr.TypeAbbrev(_, rhs, _), _) -> Ok (Some rhs)
            | _ -> Result.Error (MeasureFailure.SortMismatch(name, typeRange))
        body
        |> Result.map (fun body ->
            { Measure = ({ Name = name; Module = ctx.Path } : BaseMeasure)
              Parameters = parameters
              Body = body
              Range = typeRange })
    let decls, malformed =
        measureDefns
        |> List.fold
            (fun (decls, failures) typeDef ->
                match declOf typeDef with
                | Ok decl -> (decl :: decls, failures)
                | Result.Error failure -> (decls, failure :: failures))
            ([], [])
        |> fun (decls, failures) -> (List.rev decls, List.rev failures)
    malformed |> List.iter (fun failure -> addMeasureFailure failure env)
    let references (body: SynType) = measureReferences (MeasureSyntax.Type body)
    let translate (measures: MeasureEnv) (body: SynType) =
        translateDimension { env with Measures = measures } (MeasureSyntax.Type body)
    let rec register (pending: MeasureDecl<SynType> list) (measures: MeasureEnv) : MeasureEnv =
        match pending with
        | [] -> measures
        | _ ->
            match MeasureEnv.registerGroup references translate pending measures with
            | Ok registered -> registered
            | Result.Error failure ->
                addMeasureFailure failure env
                let _, _, at = describeMeasureFailure failure
                let failed, rest = pending |> List.partition (fun decl -> Range.rangeContainsRange decl.Range at)
                match failed with
                | [] -> measures   // the failure lies in no pending declaration: reported; nothing more registers
                | _ -> register rest measures
    { env with Measures = register decls env.Measures }

/// Check if a type definition has the [<RequireQualifiedAccess>] attribute
/// Per clef-lang-spec: When true, field labels are NOT added to FieldLabels table
let private hasRequireQualifiedAccessAttribute (attrs: SynAttributes) : bool =
    attrs |> List.exists (fun attrList ->
        attrList.Attributes |> List.exists (fun attr ->
            match attr.TypeName.LongIdent with
            | [id] -> id.idText = "RequireQualifiedAccess" || id.idText = "RequireQualifiedAccessAttribute"
            | _ -> false
        )
    )

let private checkModuleAttributes (attrs: SynAttributes) (at: range) (env: TypeEnv) =
    let hasAutoOpen =
        attrs |> List.exists (fun group -> group.Attributes |> List.exists (fun attr ->
            attr.TypeName.LongIdent |> List.tryLast
            |> Option.exists (fun id -> id.idText = "AutoOpen" || id.idText = "AutoOpenAttribute")))
    if hasAutoOpen then
        addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct at
            "Clef does not support AutoOpen. Import the module explicitly with 'open'." env

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
                        let simpleName = Bindings.getBindingName binding
                        let placeholderTy = freshTypeVar range
                        let (SynBinding(_, _, _, isMutable, attrs, _, _, _, _, _, _, _, _)) = binding
                        let declRoot =
                            if hasEntryPointAttribute attrs then Some DeclRoot.EntryPoint
                            elif hasHardwareModuleAttribute attrs then Some DeclRoot.HardwareModule
                            elif hasKernelModuleAttribute attrs then Some DeclRoot.KernelModule
                            else None
                        let node = builder.Create(
                            SemanticKind.Binding(simpleName, isMutable, true, declRoot),
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
                            Bindings.checkBinding checkExpr envWithAllNames builder binding (Some preCreatedNode)
                        Bindings.recordSourceBinding false builder binding node (inlineBodyOpt.IsSome || literalValueOpt.IsSome)

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

                let updatedEnv, nodes =
                    checkedBindings |> List.rev |> List.fold (fun (current, nodes) (node, inlineBody, name) ->
                        let node = Bindings.generalizeRecursiveBinding env builder node
                        let current = bindingNameSuffixes name |> List.fold (fun current qualified ->
                            match inlineBody with
                            | Some body -> addInlineBinding qualified node.Type (Some node.Id) body current
                            | None -> addBinding qualified node.Type false (Some node.Id) true current) current
                        current, nodes @ [node]) (updatedEnv, [])
                (updatedEnv, nodes)
            | false ->
                // NON-RECURSIVE BINDINGS: Sequential processing (existing behavior)
                // Each binding can only reference bindings that came before it
                bindings |> List.fold (fun (accEnv, accNodes) binding ->
                    let (node, inlineBodyOpt, isMutable, literalValueOpt) = Bindings.checkBinding checkExpr accEnv builder binding None
                    Bindings.recordSourceBinding false builder binding node (inlineBodyOpt.IsSome || literalValueOpt.IsSome)
                    // Let-polymorphism: a top-level function with free type variables left after
                    // solving the constraints so far becomes a TForall scheme (Binding node + env).
                    let bindingType = generalizeTopLevelFunction builder accEnv node inlineBodyOpt.IsSome
                    // Add the binding to environment so later bindings can reference it
                    // Register lexical aliases and the canonical export path
                    // CRITICAL: Use actual isMutable flag for module-level mutable variables
                    // [<Literal>] bindings are registered for compile-time substitution
                    let simpleName = Bindings.getBindingName binding
                    let updatedEnv =
                        bindingNameSuffixes simpleName
                        |> List.fold (fun env qname ->
                            // Use addInlineBinding for functions, addLiteralBinding for literals
                            match inlineBodyOpt, literalValueOpt with
                            | Some inlineBody, _ -> addInlineBinding qname bindingType (Some node.Id) inlineBody env
                            | None, Some litVal -> addLiteralBinding qname bindingType (Some node.Id) litVal env
                            | None, None -> addBinding qname bindingType isMutable (Some node.Id) true env  // Module-level bindings
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

        // Keep lexical shorthand inside this declaration scope. Only canonical paths escape
        // its boundary; retain the existing primary TypeCon name used by graph consumers.
        let typeNameSuffixesOf (simpleTypeName: string) : string list =
            let localNames =
                match ctx.Path with
                | [] | [_] -> [simpleTypeName]
                | _ :: rest ->
                    let rec allSuffixes = function
                        | [] -> [[]]
                        | x :: xs -> (x :: xs) :: allSuffixes xs
                    rest |> allSuffixes |> List.map (fun path -> String.concat "." (path @ [simpleTypeName]))
            (localNames @ [String.concat "." (ctx.Path @ [simpleTypeName])]) |> List.distinct

        // `[<Measure>] type` declarations of the group register into the measure environment and
        // produce no type node (design a.3; sequence CS-4); the remaining members are checked
        // against the grown environment, so an abbreviation `type metres = float<m>` beside its
        // measure resolves.
        let measureDefns, typeDefns =
            typeDefns
            |> List.partition (fun (SynTypeDefn(SynComponentInfo(attrs, _, _, _, _, _, _, _), _, _, _, _, _)) ->
                hasMeasureAttribute attrs)
        let env = registerMeasureDeclarations ctx env measureDefns

        // Recursive types: a member of this group may mention itself or a later member in a case
        // payload or a field (`Node = Leaf of int | Branch of Node`; `Field = { Type: T } and
        // T = P of string | S of Field array`). Resolving those names needs the group's type
        // constructors registered before any member's fields are resolved, so every union and
        // record member is registered twice: first as a placeholder (Opaque layout: a reference
        // to it counts as one word in the layout estimates), then, once its fields have resolved
        // against the placeholders, as its final constructor. The fold below reuses these final
        // constructors, so every reference to a group member carries the same TypeConRef.
        // Each declaration owns parameter identities shared by its fields, constructor and aliases.
        let declarationScopes =
            typeDefns |> List.map (fun (SynTypeDefn(SynComponentInfo(_, declarations, _, longId, _, _, _, _), _, _, _, _, _)) ->
                let name = longId |> List.map (fun ident -> ident.idText) |> String.concat "."
                name, withDeclaredTypeParameters declarations env)
            |> Map.ofList
        let declarationEnv name current =
            let scoped, _ = declarationScopes.[name]
            { current with TypeParameters = scoped.TypeParameters; MeasureScope = scoped.MeasureScope }
        let withParameterKinds name (constructor: TypeConRef) =
            let _, parameters = declarationScopes.[name]
            { constructor with ParamKinds = parameters |> List.map (fun parameter -> parameter.Kind) }

        let groupMembers =
            typeDefns |> List.choose (fun typeDef ->
                let (SynTypeDefn(typeInfo, typeRepr, _, _, _, _)) = typeDef
                let (SynComponentInfo(_, typars, _, longId, _, _, _, _)) = typeInfo
                let simpleTypeName = longId |> List.map (fun id -> id.idText) |> String.concat "."
                let arity = match typars with Some tp -> tp.TyparDecls.Length | None -> 0
                match typeRepr with
                | SynTypeDefnRepr.Simple(SynTypeDefnSimpleRepr.Union(_, cases, _), _) ->
                    Some (Choice1Of2 (simpleTypeName, arity, cases))
                | SynTypeDefnRepr.Simple(SynTypeDefnSimpleRepr.Record(_, fields, _), _) ->
                    Some (Choice2Of2 (simpleTypeName, arity, fields))
                | _ -> None)
        let placeholderEnv =
            groupMembers |> List.fold (fun e m ->
                let (simpleName, tycon) =
                    match m with
                    | Choice1Of2 (simpleName, arity, cases) ->
                        (simpleName, mkUnionTypeConRef (List.head (typeNameSuffixesOf simpleName)) arity TypeLayout.Opaque (List.length cases))
                    | Choice2Of2 (simpleName, arity, fields) ->
                        (simpleName, mkRecordTypeConRef (List.head (typeNameSuffixesOf simpleName)) ctx.Path arity TypeLayout.Opaque (List.length fields))
                let tycon = withParameterKinds simpleName tycon
                typeNameSuffixesOf simpleName |> List.fold (fun e n -> addTypeDef n tycon e) e) env
        let groupTycons : Map<string, TypeConRef> =
            groupMembers |> List.map (fun m ->
                match m with
                | Choice1Of2 (simpleName, arity, cases) ->
                    let typeName = List.head (typeNameSuffixesOf simpleName)
                    // The layout is the union's identity; its tag and payload slot are settled at
                    // saturation (Placement), where the platform's representations are known.
                    (typeName, mkUnionTypeConRef typeName arity TypeLayout.Union (List.length cases) |> withParameterKinds simpleName)
                | Choice2Of2 (simpleName, arity, fields) ->
                    let typeName = List.head (typeNameSuffixesOf simpleName)
                    let fieldInfosWithPins =
                        fields |> List.choose (fun (SynField(fieldAttrs, _, idOpt, fieldType, _, _, _, _, _)) ->
                            idOpt |> Option.map (fun ident ->
                                (ident.idText, resolveSynType (declarationEnv simpleName placeholderEnv) fieldType, extractFieldPinNames fieldAttrs)))
                    let fieldInfos = fieldInfosWithPins |> List.map (fun (n, t, _) -> (n, t))
                    let pinAttrs =
                        fieldInfosWithPins
                        |> List.choose (fun (n, _, pins) -> if List.isEmpty pins then None else Some (n, pins))
                        |> Map.ofList
                    let layout = TypeLayout.Record
                    let tycon =
                        if Map.isEmpty pinAttrs then mkRecordTypeConRef typeName ctx.Path arity layout (List.length fieldInfos)
                        else mkRecordTypeConRefWithPins typeName ctx.Path arity layout (List.length fieldInfos) pinAttrs
                    (typeName, withParameterKinds simpleName tycon))
            |> Map.ofList
        let preEnv =
            groupMembers |> List.fold (fun e m ->
                let simpleName = match m with Choice1Of2 (n, _, _) | Choice2Of2 (n, _, _) -> n
                let tycon = groupTycons.[List.head (typeNameSuffixesOf simpleName)]
                typeNameSuffixesOf simpleName |> List.fold (fun e n -> addTypeDef n tycon e) e) env

        // Process each type definition, threading environment for abbreviations
        let (finalEnv, nodes) =
            typeDefns |> List.fold (fun (accEnv, accNodes) typeDef ->
                let (SynTypeDefn(typeInfo, typeRepr, _members, _implicitCtor, typeRange, _trivia)) = typeDef
                let range = rangeToSourceRange typeRange

                // Extract type name from SynComponentInfo
                let simpleTypeName =
                    let (SynComponentInfo(_, _, _, longId, _, _, _, _)) = typeInfo
                    longId |> List.map (fun id -> id.idText) |> String.concat "."
                
                let typeNameSuffixes = typeNameSuffixesOf simpleTypeName
                
                // Primary name for semantic graph node (use most qualified)
                let typeName = List.head typeNameSuffixes

                let typeEnv = declarationEnv simpleTypeName accEnv
                let _, typeParameters = declarationScopes.[simpleTypeName]
                let typeArguments = typeParameters |> List.map typeParameterArgument

                // Check if this is a type abbreviation
                match typeRepr with
                | SynTypeDefnRepr.Simple(SynTypeDefnSimpleRepr.TypeAbbrev(_detail, rhsType, _), _) ->
                    // Type abbreviation like `type I32 = int32`
                    // Resolve the target type using the current environment
                    let targetTy = resolveSynType typeEnv rhsType
                    let targetTy = if typeParameters.IsEmpty then targetTy else NativeType.TForall(typeParameters, targetTy)
                    // Register lexical aliases and the canonical export path
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
                                                let fieldTy = resolveSynType typeEnv fieldType
                                                (fieldName, fieldTy)
                                        )
                                    | SynUnionCaseKind.FullType(synType, _) ->
                                        // Full type annotation: Case: T1 * T2 -> UnionType
                                        [(None, resolveSynType accEnv synType)]
                                (caseName, fields)
                        )

                    // The union's layout is its identity (tag, then the payload slot of the widest
                    // case); the bytes are settled at saturation by Placement from the declared
                    // representations (Dimensional_Range_Design.md ruling 2), never estimated here.
                    let layout = TypeLayout.Union

                    // Create TypeConRef for the union type
                    let caseCount = List.length caseInfos
                    let tyCon =
                        match Map.tryFind typeName groupTycons with
                        | Some pre -> pre   // the group's pre-registered constructor (recursive types)
                        | None -> mkUnionTypeConRef typeName arity layout caseCount
                    let unionType = NativeType.TApp(tyCon, typeArguments)

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
                            let constructorType = if typeParameters.IsEmpty then constructorType else NativeType.TForall(typeParameters, constructorType)
                            // Add constructor binding with case info for proper UnionCase node creation
                            let caseInfo: Clef.Compiler.NativeTypedTree.NameResolution.UnionCaseInfo = {
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
                            let (SynComponentInfo(attrs, _, _, _, _, _, _, _)) = typeInfo
                            if hasRequireQualifiedAccessAttribute attrs then envWithQualifiedCases
                            else
                                // Opening the containing module exposes its cases, but never
                                // flattens a child module or a qualified-access union.
                                envWithQualifiedCases
                                |> addUnionCaseBinding (String.concat "." (ctx.Path @ [caseName])) constructorType caseInfo
                                |> addUnionCaseBinding caseName constructorType caseInfo
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
                    // Per clef-lang-spec: Field order determines memory layout
                    // "Fidelity makes ALL memory layout decisions - MLIR/LLVM never determine layout"
                    let (SynComponentInfo(attrs, typars, _, _, _, _, _, _)) = typeInfo
                    let typeArity = match typars with Some tp -> tp.TyparDecls.Length | None -> 0
                    let requireQualifiedAccess = hasRequireQualifiedAccessAttribute attrs
                    
                    // Extract field names, types, and pin attributes from SynField list
                    // Per spec: fields are processed in declaration order (= memory order)
                    let fieldInfosWithPins =
                        fields
                        |> List.choose (fun synField ->
                            match synField with
                            | SynField(fieldAttrs, _, idOpt, fieldType, _, _, _, _, _) ->
                                match idOpt with
                                | Some ident ->
                                    let fieldName = ident.idText
                                    let nativeType = resolveSynType typeEnv fieldType
                                    let pinNames = extractFieldPinNames fieldAttrs
                                    Some (fieldName, nativeType, pinNames)
                                | None ->
                                    // Anonymous field (tuple-style) - skip for now
                                    // Full implementation would handle this case
                                    None
                        )

                    let fieldInfos = fieldInfosWithPins |> List.map (fun (name, ty, _) -> (name, ty))

                    // Build pin attribute map (only non-empty entries)
                    let pinAttrs =
                        fieldInfosWithPins
                        |> List.choose (fun (name, _, pins) ->
                            if List.isEmpty pins then None
                            else Some (name, pins))
                        |> Map.ofList

                    // The record's layout is its identity: field by field in declaration order.
                    // Its offsets and size are settled at saturation by Placement from each
                    // field's selected representation and the declared Pointer width (ruling 2).
                    let layout = TypeLayout.Record

                    // Create TypeConRef with computed layout and pin attributes
                    // Field info is accessed via SemanticGraph.Types lookup (TypeDef node)
                    let tyCon =
                        match Map.tryFind typeName groupTycons with
                        | Some pre -> pre   // the group's pre-registered constructor (recursive types)
                        | None ->
                            if Map.isEmpty pinAttrs then
                                mkRecordTypeConRef typeName ctx.Path typeArity layout (List.length fieldInfos)
                            else
                                mkRecordTypeConRefWithPins typeName ctx.Path typeArity layout (List.length fieldInfos) pinAttrs
                    
                    // Register lexical aliases and the canonical export path
                    let updatedEnv = 
                        typeNameSuffixes 
                        |> List.fold (fun env name -> addTypeDef name tyCon env) accEnv
                    
                    // Create RecordTypeInfo and register in environment
                    // This populates RecordDefs and (unless RequireQualifiedAccess) FieldLabels
                    let recordInfo: RecordTypeInfo = {
                        TypeCon = tyCon
                        TypeParameters = typeParameters
                        MutableFields = fields |> List.choose (fun (SynField(isMutable = isMutable; idOpt = ident)) ->
                            if isMutable then ident |> Option.map (fun name -> name.idText) else None) |> Set.ofList
                        Fields = fieldInfos
                        Module = ctx.Path
                        RequireQualifiedAccess = requireQualifiedAccess
                    }
                    let updatedEnv = addRecordDef recordInfo updatedEnv
                    
                    // Also register the record constructor as a binding
                    // Record constructor takes field values and returns the record type
                    // Use TApp - field information is carried in the TypeDef node (SemanticGraph.Types lookup)
                    // This follows the FCS pattern: TyconRef.Deref for metadata, not embedded in type refs
                    let recordType = NativeType.TApp(tyCon, typeArguments)
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
                    // Register lexical aliases and the canonical export path
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
                    // Register lexical aliases and the canonical export path
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
                        Types.unitType,
                        range
                    )
                    (accEnv, node :: accNodes)
            ) (preEnv, [])

        (finalEnv, List.rev nodes)

    | SynModuleDecl.NestedModule(moduleInfo, isRecursive, nestedDecls, _isContinued, moduleRange, _trivia) ->
        // Nested module - create ModuleDef node wrapping its contents
        let range = rangeToSourceRange moduleRange

        // Extract module name from moduleInfo
        let (SynComponentInfo(attrs, _, _, longId, _, _, _, _)) = moduleInfo
        let moduleParts = longId |> List.map (fun id -> id.idText)
        let moduleName = String.concat "." moduleParts
        checkModuleAttributes attrs moduleRange env

        // Create nested context with extended path
        let nestedPath = ctx.Path @ moduleParts
        let nestedCtx = { Path = nestedPath; IsRecursive = isRecursive }

        // Check all declarations in the nested module
        let declaredEnv =
            { env with Resolution = NameResolution.registerModule nestedPath false (hasRequireQualifiedAccessAttribute attrs) env.Resolution }
        let (nestedEnv, childNodes) = checkModuleDecls (enterModuleScope nestedPath declaredEnv) builder nestedCtx nestedDecls
        let childIds = childNodes |> List.map (fun n -> n.Id)

        // Create a ModuleDef node for the nested module
        let moduleNode = builder.Create(
            SemanticKind.ModuleDef(moduleName, childIds),
            Types.unitType,
            range,
            children = childIds
        )

        (leaveModuleScope nestedPath declaredEnv nestedEnv, [moduleNode])

    | SynModuleDecl.Open(target, range) ->
        // Open statements affect name resolution - compose into resolver
        // CCS has NO BCL - only source-defined modules can be opened
        let updatedEnv =
            match target with
            | SynOpenDeclTarget.ModuleOrNamespace(longId, _) ->
                let ns = longId.LongIdent |> List.map (fun id -> id.idText) |> String.concat "."
                // BCL namespaces are not available in native compilation: System.*, FSharp.*, Microsoft.*
                // are blocked. (The former FSharp.Native.* whitelist was a pre-NTU vestige; nothing opens it.)
                if ns.StartsWith("System.") || ns.StartsWith("FSharp.") || ns.StartsWith("Microsoft.") then
                    addNativeError DiagnosticCodes.CCS8080_BclReferenceNotAllowed range
                        (sprintf "Cannot open namespace '%s'. BCL namespaces are not available in native compilation. Use intrinsics instead." ns) env
                    env
                else
                    match NameResolution.tryResolveModule ns env.Resolution with
                    | Some (_, scope) when scope.RequireQualifiedAccess ->
                        addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct range
                            (sprintf "Module '%s' requires qualified access and cannot be opened." ns) env
                        env
                    | Some (path, _) -> addOpen path env
                    | None ->
                        addNativeError DiagnosticCodes.CCS8009_UndefinedValue range
                            (sprintf "Module or namespace '%s' is not defined in this scope." ns) env
                        env
            | SynOpenDeclTarget.Type _ ->
                addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct range
                    "Opening a type is not supported by the native checker." env
                env
        (updatedEnv, [])

    | SynModuleDecl.HashDirective _ ->
        // Hash directives (#if, #nowarn, etc.) - preprocessing, no semantic nodes
        (env, [])

    | SynModuleDecl.ModuleAbbrev(ident, longId, range) ->
        let name = longId |> List.map (fun id -> id.idText) |> String.concat "."
        match NameResolution.tryResolveModule name env.Resolution with
        | Some (path, scope) when not scope.IsNamespace ->
            ({ env with Resolution = NameResolution.addModuleAlias ident.idText path env.Resolution }, [])
        | _ ->
            addNativeError DiagnosticCodes.CCS8009_UndefinedValue range
                (sprintf "Module abbreviation '%s' must name an accessible module; '%s' does not." ident.idText name) env
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
            Types.stringType,  // TODO: Define proper exception type
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
    let env = createTypeEnv()
    let builder = NodeBuilder()
    NodeId.reset()
    solvedConstraintCount <- 0

    let ctx = { Path = []; IsRecursive = false }
    let (finalEnv, nodes) = checkModuleDecls env builder ctx decls
    let diagnostics = solveAndGetDiagnostics finalEnv !(env.Constraints)

    buildResult builder nodes Map.empty diagnostics None Set.empty

//-------------------------------------------------------------------------
// Type Checking: Module or Namespace Level
//-------------------------------------------------------------------------

/// Check a module or namespace and return updated environment and semantic nodes
let private checkModuleOrNamespace (env: TypeEnv) (builder: NodeBuilder) (moduleOrNs: SynModuleOrNamespace) : TypeEnv * ModulePath * SemanticNode list =
    let (SynModuleOrNamespace(longId, isRecursive, kind, decls, _xmlDoc, attrs, _accessibility, nsRange, _trivia)) = moduleOrNs

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
    checkModuleAttributes attrs nsRange env
    let declaredEnv =
        { env with Resolution = NameResolution.registerModule modulePath isNamespace (hasRequireQualifiedAccessAttribute attrs) env.Resolution }
    let (innerEnv, contentNodes) = checkModuleDecls (enterModuleScope modulePath declaredEnv) builder ctx decls
    let updatedEnv = leaveModuleScope modulePath declaredEnv innerEnv

    if isNamespace then
        // Namespaces don't get a wrapper node - just return content
        (updatedEnv, modulePath, contentNodes)
    else
        // Modules get a ModuleDef wrapper node
        let moduleName = modulePath |> String.concat "."
        let childIds = contentNodes |> List.map (fun n -> n.Id)

        let moduleNode = builder.Create(
            SemanticKind.ModuleDef(moduleName, childIds),
            Types.unitType,
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

    let initialEnv = createTypeEnv()
    let builder = NodeBuilder()
    NodeId.reset()
    solvedConstraintCount <- 0

    // Track which file we're processing (for diagnostics)
    let _ = fileName  // Could be added to CheckResult metadata
    let _ = qualifiedNameOfFile  // The qualified name can be used for module resolution

    // Process each module or namespace in the file, threading environment
    let (finalEnv, moduleResults) =
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
        |> List.fold (fun paths (path, nodes) ->
            Map.change path (fun previous -> Some (Option.defaultValue [] previous @ nodes)) paths) Map.empty

    let solved = solveAndGetDiagnostics finalEnv !(initialEnv.Constraints)
    let reported = solved @ List.rev !(initialEnv.Diagnostics)
    let diagnostics = reported @ residualDiagnostics builder reported

    buildResult builder allNodes modulePaths diagnostics None Set.empty

/// Check multiple parsed implementation files together with optional platform context.
/// Files are processed in order, with earlier files' bindings available to later files.
/// This is essential for multi-file compilation where dependencies must be loaded first.
/// After checking, reachability analysis prunes the graph to only what's used.
///
/// platformContext: Optional platform context. When Some, enables entry point elaboration
/// for freestanding builds (adds _start wrapper that calls main).
let checkParsedInputsWithPlatformAndSources (inputs: ParsedInput list) (platformContext: PlatformContext option) (ownedSources: Set<string>) : CheckResult =
    let initialEnv = createTypeEnv()
    let builder = NodeBuilder()
    NodeId.reset()
    solvedConstraintCount <- 0

    // Process all files in order, threading environment
    let (finalEnv, allModuleResults) =
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
        |> List.fold (fun paths (path, nodes) ->
            Map.change path (fun previous -> Some (Option.defaultValue [] previous @ nodes)) paths) Map.empty

    // Solve constraints - now using ref cells, all environment copies share same constraints
    let constraintDiags = solveAndGetDiagnostics finalEnv !(initialEnv.Constraints)
    let reported = constraintDiags @ (List.rev !(initialEnv.Diagnostics))
    let allDiagnostics = reported @ residualDiagnostics builder reported

    buildResult builder allNodes modulePaths allDiagnostics platformContext ownedSources

/// The general checking API has no project ownership facts, so it does not
/// classify public declarations as unused application helpers.
let checkParsedInputsWithPlatform (inputs: ParsedInput list) (platformContext: PlatformContext option) : CheckResult =
    checkParsedInputsWithPlatformAndSources inputs platformContext Set.empty

/// Check multiple parsed implementation files together (backward compatible version).
/// Use checkParsedInputsWithPlatform for freestanding builds that need entry point elaboration.
let checkParsedInputs (inputs: ParsedInput list) : CheckResult =
    checkParsedInputsWithPlatform inputs None

/// Check parsed input (implementation or signature file)
let checkParsedInput (input: ParsedInput) : CheckResult =
    match input with
    | ParsedInput.ImplFile implFile -> checkImplFile implFile
    | ParsedInput.SigFile _ ->
        // A signature file has no checker yet: the input contributes no graph, and that is an
        // error rather than a warning, because a warning would let the program lose a file silently.
        {
            Graph = { Nodes = Map.empty; DeclarationRoots = []; Modules = Map.empty; Types = lazy Map.empty; Platform = None; ModuleClassifications = lazy Map.empty; SeqSaturation = lazy Map.empty; FieldRanges = lazy Map.empty; ElementRanges = lazy Map.empty; Layouts = lazy Map.empty; StaticStringPool = None; Escaping = lazy Map.empty; Codata = lazy Codata.empty; Edges = [] }
            Diagnostics = [{
                Severity = NativeDiagnosticSeverity.Error
                Code = DiagnosticCodes.CCS8401_UnsupportedConstruct
                Message = "Signature files are not supported by the checker; the file contributes nothing"
                Range = dummyRange
                RelatedNodes = []
                Reachability = ReachabilityContext.Unknown
            }]
            PlatformContext = None
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

/// Create a fresh type environment
let createFreshTypeEnv () : TypeEnv =
    createTypeEnv()
