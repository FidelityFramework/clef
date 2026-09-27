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

    | SynPat.Null sourceRange ->
        addNullError sourceRange env
        (Pattern.Wildcard, [])

    | SynPat.LongIdent(SynLongIdent(idents, _, _), _, _, argPats, _, _) ->
        // Constructor or identifier pattern
        let caseName = idents |> List.map (fun id -> id.idText) |> String.concat "."
        // A name bound to a [<Literal>] is a constant pattern: the scrutinee equals that value.
        let literal =
            match argPats with
            | SynArgPats.Pats [] ->
                tryLookupBinding caseName env
                |> Option.bind (fun binding -> binding.NativeLiteral |> Option.map (fun value -> value, binding.Type))
            | _ -> None
        match idents, argPats, literal with
        | [ident], SynArgPats.Pats [], _ when not (System.Char.IsUpper(ident.idText.[0])) ->
            (Pattern.Var(caseName, expectedTy), [(caseName, expectedTy)])
        | _, _, Some(value, literalTy) ->
            addConstraint (Constraint.Equals(expectedTy, literalTy, range)) env
            (Pattern.Const value, [])
        | _ ->
            let payloadTypes, tagIndex =
                match tryLookupBinding caseName env |> Option.map (fun binding -> binding, binding.UnionCaseInfo) with
                | Some(_, None) ->
                    // A bound value that is neither a union case nor a [<Literal>] has no
                    // constructor tag; it is never read as a test of tag 0.
                    addNativeError DiagnosticCodes.CCS8008_UndefinedConstructor pat.Range
                        $"CCS source checking did not settle a union case for constructor pattern '{caseName}': the name is bound to a value that is neither a union case nor a [<Literal>], and has no pattern elaboration." env
                    [], 0
                | Some(binding, Some caseInfo) ->
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
                    fields, caseInfo.CaseIndex
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
        let (rhsPattern, rhsBindings) = checkPattern env rhsPat expectedTy range
        match rhsPattern with
        | Pattern.Var(name, _) -> (Pattern.As(lhsPattern, name), lhsBindings @ rhsBindings)
        | _ ->
            // The alias's right side is a name; any other pattern there would be dropped.
            addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct rhsPat.Range
                "CCS source checking did not settle an alias for this 'as' pattern: the right side of 'as' is not a name, and a refutable right side has no pattern form." env
            (Pattern.Wildcard, lhsBindings @ rhsBindings)

    | SynPat.Or(lhsPat, rhsPat, _, _) ->
        // Alternation pattern
        let (lhsPattern, lhsBindings) = checkPattern env lhsPat expectedTy range
        let (rhsPattern, _rhsBindings) = checkPattern env rhsPat expectedTy range
        // Both alternatives are retained; the right one is never dropped. Both branches bind
        // the same names, so the left branch's bindings name the case's variables.
        (Pattern.Or(lhsPattern, rhsPattern), lhsBindings)

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
        let _testTy = resolveSynType env synType
        // There is no run-time type information to test; the pattern is refused, never carried
        // as an IsType test nothing below can realize.
        addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct pat.Range
            "CCS source checking did not settle an elaboration for this type test pattern ':?': type tests have no native graph form." env
        (Pattern.Wildcard, [])

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
        let (_, lhsBindings) = checkPattern env lhsPat elemTy range
        let (_, rhsBindings) = checkPattern env rhsPat listTy range
        // The pattern graph has no cons form; a tuple of head and tail would test a list as a
        // tuple. Refused at the site.
        addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct pat.Range
            "CCS source checking did not settle a pattern form for this list cons pattern 'head :: tail': the pattern graph has no cons form." env
        (Pattern.Wildcard, lhsBindings @ rhsBindings)

    | SynPat.Ands(pats, _) ->
        // Conjunction pattern: pat1 & pat2 & ...
        let (patterns, bindings) =
            pats
            |> List.map (fun p -> checkPattern env p expectedTy range)
            |> List.unzip
        (List.reduceBack (fun left right -> Pattern.And(left, right)) patterns, List.concat bindings)

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
