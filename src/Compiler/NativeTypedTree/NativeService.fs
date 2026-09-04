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
open Clef.Compiler.NativeTypedTree.NameResolution
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
        let located (m: range) (text: string) =
            sprintf "%s(%d,%d): %s" m.FileName m.StartLine (m.StartColumn + 1) text
        let rec render (exn: exn) =
            match exn with
            | DiagnosticWithText(_, text, m) -> located m text
            | Clef.Compiler.ParseHelpers.IndentationProblem(text, m) -> located m text
            | Clef.Compiler.ParseHelpers.SyntaxError(_, m) -> located m "Syntax error: unexpected token"
            | WrappedError(inner, m) ->
                match inner with
                | DiagnosticWithText _ | Clef.Compiler.ParseHelpers.IndentationProblem _ | Clef.Compiler.ParseHelpers.SyntaxError _ -> render inner
                | _ -> located m inner.Message
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
/// CCS8048 family for an unrepresentable exponent); the other cases keep the FS0001 blanket until
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
        let code =
            match e with
            | NotNumeric _ -> DiagnosticCodes.CCS8000_NotNumeric
            | MeasureMismatch _ -> DiagnosticCodes.CCS8040_MeasureMismatch
            | NoIntegerSolution _ -> DiagnosticCodes.CCS8041_NoIntegerSolution
            | MeasureExponentOutOfRange _ -> DiagnosticCodes.CCS8048_RationalMeasureExponent
            | TypeMismatch _ | InfiniteType _ | ArityMismatch _
            | TupleLengthMismatch _ | TupleKindMismatch _ | ByrefKindMismatch _ -> DiagnosticCodes.FS0001_GenericError
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

/// Whether `ancestorId` is an ancestor of `node` in the graph.
let private hasAncestor (builder: NodeBuilder) (ancestorId: NodeId) (node: SemanticNode) : bool =
    let rec up (id: NodeId option) =
        match id with
        | None -> false
        | Some i when i = ancestorId -> true
        | Some i -> Map.tryFind i builder.Nodes |> Option.bind (fun n -> n.Parent) |> up
    up node.Parent

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
    builder.Nodes
    |> Map.toSeq
    |> Seq.map snd
    |> Seq.filter (fun n ->
        match n.Kind with
        | SemanticKind.Binding _ -> n.Id <> binding.Id && not (hasAncestor builder binding.Id n)
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
let private quantifiedByEnclosing (builder: NodeBuilder) (node: SemanticNode) : Set<int> option =
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
            up parent.Parent acc
    up node.Parent Set.empty

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
    builder.Nodes
    |> Map.toList
    |> List.collect (fun (_, node) ->
        match node.Kind with
        | SemanticKind.Binding(name, _, _, _)
            when not (isFunctionBindingNode builder node)
                 && not (node.Metadata.ContainsKey "FidelityExtern.Library")
                 && not (alreadyFailed node) ->
            match applySubst node.Type with
            | NativeType.TForall _ -> []
            | ty ->
                match quantifiedByEnclosing builder node with
                | None -> []
                | Some quantified ->
                    let excused (id: int) = Set.contains id quantified || Set.contains id tainted
                    let measures = freeMeasureVars ty |> List.filter (fun v -> not (excused v.Id))
                    let operands =
                        collectFreeTypeParams ty
                        |> List.filter (fun tp ->
                            not (excused tp.Id)
                            && (tp.Kind = TypeParamKind.Carrier || (operandOf tp).IsSome))
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
        | _ -> [])

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

/// Build a CheckResult from builder state and diagnostics
/// platformContext: Optional platform context for freestanding builds (enables entry point elaboration)
let private buildResult (builder: NodeBuilder) (topLevelNodes: SemanticNode list) (modulePaths: Map<ModulePath, NodeId list>) (diagnostics: Diagnostic list) (platformContext: PlatformContext option) : CheckResult =
    let declRoots = findDeclarationRoots builder.Nodes topLevelNodes

    // CRITICAL: Apply type substitutions to resolve type variables after constraint solving.
    // During type checking, nodes are created with fresh type variables that get unified
    // with concrete types. The substitutions are stored in UnionFind but not automatically
    // applied to node types. We must apply them here to get concrete types in the output.
    let resolvedNodes =
        builder.Nodes
        |> Map.map (fun _id node ->
            { node with Type = applySubst node.Type })
        // An application of a generalised binding records its instance (design b.4 step 4).
        |> annotateInstantiations
        // Generic (TForall) top-level functions are compiled once per instantiation.
        |> Monomorphization.run

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
        // F is empty at construction; enrichment mints into it at saturation.
        Edges = []
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
    ObligationDischarge.emit finalGraph  // Artifacts 06a/06b: the design-time dispatch

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

    let taggedDiagnostics = diagnostics |> List.map tagReachability

    // Layer 1: Combinational depth analysis (FPGA-only structural heuristic)
    // Walks the final PSG bottom-up, counting weighted operation depth.
    // Reports paths exceeding threshold as Info diagnostics.
    let depthDiagnostics = DepthAnalysis.analyze platformContext finalGraph

    {
        Graph = finalGraph
        Diagnostics = taggedDiagnostics @ depthDiagnostics
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
        match Literals.checkConst env constant with
        | Result.Ok (ty, litVal) ->
            builder.Create(SemanticKind.Literal litVal, ty, range)
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
    // Null - REJECTED in Clef (FS8100)
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

    buildResult builder [node] Map.empty diagnostics None

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

    buildResult builder [node] Map.empty diagnostics None

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
                    let (node, inlineBodyOpt, isMutable, literalValueOpt) = Bindings.checkBinding checkExpr accEnv builder binding None
                    // Let-polymorphism: a top-level function with free type variables left after
                    // solving the constraints so far becomes a TForall scheme (Binding node + env).
                    let bindingType = generalizeTopLevelFunction builder accEnv node inlineBodyOpt.IsSome
                    // Add the binding to environment so later bindings can reference it
                    // Register under all qualified name suffixes (handles AutoOpen modules)
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

        // Every name a type is registered under: for a type inside nested modules, each suffix of
        // the module path (AutoOpen modules are not tracked, so all suffixes are registered).
        let typeNameSuffixesOf (simpleTypeName: string) : string list =
            match ctx.Path with
            | [] | [_] -> [simpleTypeName]
            | _ :: rest ->
                let rec allSuffixes = function
                    | [] -> [[]]
                    | x :: xs -> (x :: xs) :: allSuffixes xs
                rest
                |> allSuffixes
                |> List.map (fun modPath ->
                    match modPath with
                    | [] -> simpleTypeName
                    | _ -> (modPath |> String.concat ".") + "." + simpleTypeName)

        // Layout estimate of a union case payload (one word for anything without an inline layout)
        let estimatePayloadSize (ty: NativeType) : int =
            match ty with
            | NativeType.TApp _ | NativeType.TNum _ ->
                match layoutOf ty with
                | TypeLayout.Inline(size, _) -> size
                | TypeLayout.PlatformWord -> 8
                | _ -> 8
            | NativeType.TTuple(elems, _) -> elems.Length * 8
            | _ -> 8

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
                typeNameSuffixesOf simpleName |> List.fold (fun e n -> addTypeDef n tycon e) e) env
        let groupTycons : Map<string, TypeConRef> =
            groupMembers |> List.map (fun m ->
                match m with
                | Choice1Of2 (simpleName, arity, cases) ->
                    let typeName = List.head (typeNameSuffixesOf simpleName)
                    let payloadSizes =
                        cases |> List.map (fun (SynUnionCase(_, _, caseKind, _, _, _, _)) ->
                            match caseKind with
                            | SynUnionCaseKind.Fields synFields ->
                                synFields |> List.sumBy (fun (SynField(_, _, _, fieldType, _, _, _, _, _)) ->
                                    estimatePayloadSize (resolveSynType placeholderEnv fieldType))
                            | SynUnionCaseKind.FullType(synType, _) ->
                                estimatePayloadSize (resolveSynType placeholderEnv synType))
                    let unionSize = 1 + (payloadSizes |> List.fold max 0)
                    (typeName, mkUnionTypeConRef typeName arity (TypeLayout.Inline(unionSize, 8)) (List.length cases))
                | Choice2Of2 (simpleName, arity, fields) ->
                    let typeName = List.head (typeNameSuffixesOf simpleName)
                    let fieldInfosWithPins =
                        fields |> List.choose (fun (SynField(fieldAttrs, _, idOpt, fieldType, _, _, _, _, _)) ->
                            idOpt |> Option.map (fun ident ->
                                (ident.idText, resolveSynType placeholderEnv fieldType, extractFieldPinNames fieldAttrs)))
                    let fieldInfos = fieldInfosWithPins |> List.map (fun (n, t, _) -> (n, t))
                    let pinAttrs =
                        fieldInfosWithPins
                        |> List.choose (fun (n, _, pins) -> if List.isEmpty pins then None else Some (n, pins))
                        |> Map.ofList
                    let layout = computeRecordLayout fieldInfos
                    let tycon =
                        if Map.isEmpty pinAttrs then mkRecordTypeConRef typeName ctx.Path arity layout (List.length fieldInfos)
                        else mkRecordTypeConRefWithPins typeName ctx.Path arity layout (List.length fieldInfos) pinAttrs
                    (typeName, tycon))
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
                    let targetTy = resolveSynType accEnv rhsType
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
                        | NativeType.TApp _ | NativeType.TNum _ ->
                            match layoutOf ty with
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
                                                let fieldTy = resolveSynType accEnv fieldType
                                                (fieldName, fieldTy)
                                        )
                                    | SynUnionCaseKind.FullType(synType, _) ->
                                        // Full type annotation: Case: T1 * T2 -> UnionType
                                        [(None, resolveSynType accEnv synType)]
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
                    let caseCount = List.length caseInfos
                    let tyCon =
                        match Map.tryFind typeName groupTycons with
                        | Some pre -> pre   // the group's pre-registered constructor (recursive types)
                        | None -> mkUnionTypeConRef typeName arity layout caseCount
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
                                    let nativeType = resolveSynType accEnv fieldType
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

                    // Compute memory layout from fields
                    // Per spec Step 4: "Initialize offset = 0, max_align = 1..."
                    let layout = computeRecordLayout fieldInfos

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
            Types.unitType,
            range,
            children = childIds
        )

        (nestedEnv, [moduleNode])

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

    buildResult builder nodes Map.empty diagnostics None

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
        |> Map.ofList

    let solved = solveAndGetDiagnostics finalEnv !(initialEnv.Constraints)
    let diagnostics = solved @ residualDiagnostics builder solved

    buildResult builder allNodes modulePaths diagnostics None

/// Check multiple parsed implementation files together with optional platform context.
/// Files are processed in order, with earlier files' bindings available to later files.
/// This is essential for multi-file compilation where dependencies must be loaded first.
/// After checking, reachability analysis prunes the graph to only what's used.
///
/// platformContext: Optional platform context. When Some, enables entry point elaboration
/// for freestanding builds (adds _start wrapper that calls main).
let checkParsedInputsWithPlatform (inputs: ParsedInput list) (platformContext: PlatformContext option) : CheckResult =
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
        |> Map.ofList

    // Solve constraints - now using ref cells, all environment copies share same constraints
    let constraintDiags = solveAndGetDiagnostics finalEnv !(initialEnv.Constraints)
    let reported = constraintDiags @ (List.rev !(initialEnv.Diagnostics))
    let allDiagnostics = reported @ residualDiagnostics builder reported

    buildResult builder allNodes modulePaths allDiagnostics platformContext

/// Check multiple parsed implementation files together (backward compatible version).
/// Use checkParsedInputsWithPlatform for freestanding builds that need entry point elaboration.
let checkParsedInputs (inputs: ParsedInput list) : CheckResult =
    checkParsedInputsWithPlatform inputs None

/// Check parsed input (implementation or signature file)
let checkParsedInput (input: ParsedInput) : CheckResult =
    match input with
    | ParsedInput.ImplFile implFile -> checkImplFile implFile
    | ParsedInput.SigFile _ ->
        // Signature files not yet supported
        {
            Graph = { Nodes = Map.empty; DeclarationRoots = []; Modules = Map.empty; Types = lazy Map.empty; Platform = None; ModuleClassifications = lazy Map.empty; SeqSaturation = lazy Map.empty; Edges = [] }
            Diagnostics = [{
                Severity = NativeDiagnosticSeverity.Warning
                Code = "FS0000"
                Message = "Signature files not yet supported in native checker"
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
