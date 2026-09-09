// Copyright (c) 2025 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Pattern checking for Clef.
/// Handles: Pattern matching cases (Const, Wild, Named, Typed, Tuple, etc.)
module Clef.Compiler.NativeTypedTree.Expressions.Patterns

open Clef.Compiler.Syntax
open Clef.Compiler.NativeTypedTree.NativeTypes

open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.NativeTypedTree.Expressions.Types
open Clef.Compiler.NativeTypedTree.Expressions.Literals

//-------------------------------------------------------------------------
// Pattern Checking
//-------------------------------------------------------------------------

/// Check a pattern and return (Pattern, bindings)
let rec checkPattern
    (env: TypeEnv)
    (pat: SynPat)
    (expectedTy: NativeType)
    (range: SourceRange)
    : Pattern * (string * NativeType) list =

    match pat with
    | SynPat.Const(constant, constRange) ->
        warnSuffix constRange constant env
        match checkConst env constant with
        | Result.Ok (literalType, literal) ->
            addConstraint (Constraint.Equals(expectedTy, literalType, range)) env
            (Pattern.Const literal, [])
        | Result.Error failure ->
            // CCS8018 (plan L-3) or a measure failure; the diagnostic is an Error, so nothing runs
            // on the wildcard.
            addConstFailure constRange failure env
            (Pattern.Wildcard, [])  // Wildcard for error recovery

    | SynPat.Wild _ ->
        (Pattern.Wildcard, [])

    | SynPat.Named(SynIdent(ident, _), _, _, _) ->
        let name = ident.idText
        (Pattern.Var(name, expectedTy), [(name, expectedTy)])

    | SynPat.Typed(innerPat, synType, _) ->
        let annotatedTy = resolveSynType env synType
        addConstraint (Constraint.Equals(expectedTy, annotatedTy, range)) env
        checkPattern env innerPat annotatedTy range

    | SynPat.Tuple(_, pats, _, _) ->
        let elementTypes = pats |> List.map (fun _ -> freshTypeVar range)
        let tupleTy = NativeType.TTuple(elementTypes, false)
        addConstraint (Constraint.Equals(expectedTy, tupleTy, range)) env

        let (patterns, bindings) =
            List.zip pats elementTypes
            |> List.map (fun (p, ty) -> checkPattern env p ty range)
            |> List.unzip

        (Pattern.Tuple patterns, List.concat bindings)

    | SynPat.Paren(innerPat, _) ->
        checkPattern env innerPat expectedTy range

    | SynPat.Null _ ->
        (Pattern.Null, [])

    | SynPat.LongIdent(SynLongIdent(idents, _, _), _, _, argPats, _, _) ->
        // Constructor or identifier pattern
        let caseName = idents |> List.map (fun id -> id.idText) |> String.concat "."
        match idents, argPats with
        | [ident], SynArgPats.Pats [] when not (System.Char.IsUpper(ident.idText.[0])) ->
            (Pattern.Var(caseName, expectedTy), [(caseName, expectedTy)])
        | _ ->
            let payloadTypes, tagIndex =
                match tryLookupBinding caseName env with
                | Some binding ->
                    let constructorType =
                        match binding.Type with
                        | NativeType.TForall(parameters, body) ->
                            let arguments = parameters |> List.map (fun tp ->
                                freshInstanceOf tp range)
                            instantiate parameters arguments body
                        | ty -> ty
                    let rec extractDomains ty acc =
                        match ty with
                        | NativeType.TFun(domain, result) -> extractDomains result (domain :: acc)
                        | result -> List.rev acc, result
                    let fields, result = extractDomains constructorType []
                    // The payload and the scrutinee share this use's fresh variables.
                    addConstraint (Constraint.Equals(expectedTy, result, range)) env
                    fields, (binding.UnionCaseInfo |> Option.map (fun info -> info.CaseIndex) |> Option.defaultValue 0)
                | None ->
                    addNativeError DiagnosticCodes.CCS8008_UndefinedConstructor pat.Range $"The constructor '{caseName}' is not defined." env
                    [], 0

            match argPats with
            | SynArgPats.Pats pats ->
                let rec tupleElements pat =
                    match pat with
                    | SynPat.Paren(inner, _) -> tupleElements inner
                    | SynPat.Tuple(_, elements, _, _) -> Some elements
                    | _ -> None
                let pats =
                    match pats with
                    | [tuple] when payloadTypes.Length > 1 -> tupleElements tuple |> Option.defaultValue pats
                    | _ -> pats
                if pats.Length <> payloadTypes.Length then
                    addNativeError DiagnosticCodes.CCS8004_ArityMismatch pat.Range $"Constructor '{caseName}' expects {payloadTypes.Length} fields, got {pats.Length}" env
                let patterns, bindings =
                    pats |> List.mapi (fun index pat ->
                        let ty = payloadTypes |> List.tryItem index |> Option.defaultValue (NativeType.TError "constructor arity")
                        checkPattern env pat ty range) |> List.unzip
                let payload = if patterns.IsEmpty then None else Some(Pattern.Tuple patterns)
                Pattern.Union(caseName, tagIndex, payload, expectedTy), List.concat bindings
            | SynArgPats.NamePatPairs _ ->
                addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct pat.Range "Named constructor field patterns are not supported" env
                Pattern.Union(caseName, tagIndex, None, expectedTy), []

    | SynPat.As(lhsPat, rhsPat, _) ->
        // Pattern alias: pat as name
        let (lhsPattern, lhsBindings) = checkPattern env lhsPat expectedTy range
        let (_, rhsBindings) = checkPattern env rhsPat expectedTy range
        (lhsPattern, lhsBindings @ rhsBindings)

    | SynPat.Or(lhsPat, rhsPat, _, _) ->
        // Alternation pattern
        let (lhsPattern, lhsBindings) = checkPattern env lhsPat expectedTy range
        let (_rhsPattern, _rhsBindings) = checkPattern env rhsPat expectedTy range
        // Use left pattern, but both branches should bind same names
        (lhsPattern, lhsBindings)

    | SynPat.ArrayOrList(isArray, pats, _) ->
        let elemTy = freshTypeVar range
        let listTy = if isArray then NativeType.TApp(Types.arrayTyCon, [elemTy]) else NativeType.TList elemTy
        addConstraint (Constraint.Equals(expectedTy, listTy, range)) env
        let (patterns, bindings) =
            pats
            |> List.map (fun p -> checkPattern env p elemTy range)
            |> List.unzip
        (Pattern.Array patterns, List.concat bindings)

    | SynPat.Record(fields, _) ->
        // Record pattern: { field1 = pat1; ... }
        // Look up actual field types from record type, not fresh type variables.
        // Hard failure if lookup fails - surfaces root cause immediately.
        let fieldPats =
            fields
            |> List.map (fun field ->
                let fieldName = field.FieldName.LongIdent |> List.map (fun id -> id.idText) |> String.concat "."
                let pat = field.Pattern
                // Look up the field type from the record type (expectedTy)
                let fieldTy =
                    match Types.tryResolveRecordFieldType expectedTy fieldName env with
                    | Some ty -> ty
                    | None ->
                        // HARD FAILURE: Field lookup failed - emit diagnostic and fail
                        // This surfaces the root cause immediately rather than creating
                        // unbound type variables that cause cryptic downstream errors.
                        let resolvedTy = applySubst expectedTy
                        let tyName =
                            match resolvedTy with
                            | NativeType.TApp(tycon, _) -> tycon.Name
                            | NativeType.TNum _ -> formatType resolvedTy
                            | NativeType.TVar tv -> sprintf "'%s (unresolved type variable)" tv.Name
                            | _ -> sprintf "%A" resolvedTy
                        addDiagnostic {
                            Severity = NativeDiagnosticSeverity.Error
                            Code = DiagnosticCodes.CCS8702_UndefinedField
                            Message = sprintf "Record pattern field '%s' not found in type '%s'. Record type may not be registered in RecordDefs, or expectedTy is not resolved." fieldName tyName
                            Range = range
                            RelatedNodes = []
                            Reachability = ReachabilityContext.Unknown
                        } env
                        // Return a placeholder type for error recovery, but the error is logged
                        Types.unitType
                let (pattern, bindings) = checkPattern env pat fieldTy range
                ((fieldName, pattern), bindings))
        let patterns = fieldPats |> List.map fst
        let bindings = fieldPats |> List.collect snd
        (Pattern.Record(patterns, expectedTy), bindings)

    | SynPat.IsInst(synType, _) ->
        // Type test pattern: :? Type
        let testTy = resolveSynType env synType
        (Pattern.IsType testTy, [])

    | SynPat.OptionalVal(ident, _) ->
        // Optional parameter pattern: ?x
        let name = ident.idText
        let innerTy = freshTypeVar range
        let optTy = NativeType.TApp(Types.optionTyCon, [innerTy])
        addConstraint (Constraint.Equals(expectedTy, optTy, range)) env
        (Pattern.Var(name, optTy), [(name, optTy)])

    | SynPat.ListCons(lhsPat, rhsPat, _, _) ->
        // List cons pattern: x :: xs
        let elemTy = freshTypeVar range
        let listTy = NativeType.TList elemTy
        addConstraint (Constraint.Equals(expectedTy, listTy, range)) env
        let (lhsPattern, lhsBindings) = checkPattern env lhsPat elemTy range
        let (rhsPattern, rhsBindings) = checkPattern env rhsPat listTy range
        // Represent as a tuple pattern for head :: tail
        (Pattern.Tuple [lhsPattern; rhsPattern], lhsBindings @ rhsBindings)

    | SynPat.Ands(pats, _) ->
        // Conjunction pattern: pat1 & pat2 & ...
        let (patterns, bindings) =
            pats
            |> List.map (fun p -> checkPattern env p expectedTy range)
            |> List.unzip
        match patterns with
        | [single] -> (single, List.concat bindings)
        | _ -> (Pattern.And(List.head patterns, Pattern.Tuple (List.tail patterns)), List.concat bindings)

    | SynPat.Attrib(innerPat, _, _) ->
        // Attributed pattern - ignore attributes, check inner pattern
        checkPattern env innerPat expectedTy range

    | SynPat.QuoteExpr(_, _) ->
        // Quote expression pattern - not supported in native compilation
        addDiagnostic {
            Severity = NativeDiagnosticSeverity.Error
            Code = DiagnosticCodes.CCS8063_QuotePatternNotSupported
            Message = "Quote expression patterns are not a Clef construct."
            Range = range
            RelatedNodes = []
            Reachability = ReachabilityContext.Unknown
        } env
        (Pattern.Wildcard, [])  // Wildcard for error recovery

    | SynPat.FromParseError(innerPat, _) ->
        // Parse error recovery - check inner pattern
        checkPattern env innerPat expectedTy range

    | SynPat.InstanceMember _ ->
        // Instance member pattern - for object expressions (not supported in native)
        addDiagnostic {
            Severity = NativeDiagnosticSeverity.Error
            Code = DiagnosticCodes.CCS8064_InstanceMemberPatternNotSupported
            Message = "Instance member patterns (object expressions) are not a Clef construct."
            Range = range
            RelatedNodes = []
            Reachability = ReachabilityContext.Unknown
        } env
        (Pattern.Wildcard, [])  // Wildcard for error recovery
