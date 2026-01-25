// Copyright (c) 2025 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Pattern checking for F# Native.
/// Handles: Pattern matching cases (Const, Wild, Named, Typed, Tuple, etc.)
module FSharp.Native.Compiler.NativeTypedTree.Expressions.Patterns

open FSharp.Native.Compiler.Syntax
open FSharp.Native.Compiler.NativeTypedTree.NativeTypes

open FSharp.Native.Compiler.NativeTypedTree.UnionFind
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Types
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Core
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Builder
open FSharp.Native.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open FSharp.Native.Compiler.NativeTypedTree.Expressions.Types
open FSharp.Native.Compiler.NativeTypedTree.Expressions.Literals

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
    | SynPat.Const(constant, _) ->
        (Pattern.Const(constToLiteral constant), [])

    | SynPat.Wild _ ->
        (Pattern.Wildcard, [])

    | SynPat.Named(SynIdent(ident, _), _, _, _) ->
        let name = ident.idText
        (Pattern.Var(name, expectedTy), [(name, expectedTy)])

    | SynPat.Typed(innerPat, _synType, _) ->
        let annotatedTy = failwith "ELIMINATE_SYNTYPE: Pattern type annotation - NTU type required"
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
        match argPats with
        | SynArgPats.Pats [] ->
            // No arguments - could be variable binding or nullary constructor
            // Lowercase single identifier = variable binding, otherwise = constructor
            match idents with
            | [ident] when not (System.Char.IsUpper(ident.idText.[0])) ->
                // Lowercase single identifier - treat as variable binding
                (Pattern.Var(caseName, expectedTy), [(caseName, expectedTy)])
            | _ ->
                // Uppercase or qualified - nullary constructor
                // Look up binding to get tag index from UnionCaseInfo
                let tagIndex =
                    match tryLookupBinding caseName env with
                    | Some binding ->
                        match binding.UnionCaseInfo with
                        | Some caseInfo -> caseInfo.CaseIndex
                        | None -> 0  // Fallback for non-DU constructors
                    | None -> 0  // Fallback
                (Pattern.Union(caseName, tagIndex, None, expectedTy), [])
        | SynArgPats.Pats pats ->
            // Constructor with arguments (e.g., Some x, Error e)
            // Look up constructor binding to get payload types and tag index (FCS TyconRef.Deref pattern)
            let (payloadTypes, tagIndex) =
                match tryLookupBinding caseName env with
                | Some binding ->
                    // Extract domain types from constructor's function type
                    // e.g., IntVal : int -> Number has type TFun(int, Number)
                    // e.g., Pair : int -> string -> T has type TFun(int, TFun(string, T))
                    // e.g., Some : forall 'a. 'a -> option<'a> (need to unwrap TForall first)
                    let rec extractDomains ty acc =
                        match ty with
                        | NativeType.TForall(_, inner) -> extractDomains inner acc  // Unwrap polymorphic types
                        | NativeType.TFun(domain, range) -> extractDomains range (domain :: acc)
                        | _ -> List.rev acc
                    let types = extractDomains binding.Type []
                    // Extract tag index from UnionCaseInfo
                    let idx =
                        match binding.UnionCaseInfo with
                        | Some caseInfo -> caseInfo.CaseIndex
                        | None -> 0  // Fallback for non-DU constructors
                    (types, idx)
                | None ->
                    // Fallback: use fresh type variables (will be constrained later)
                    (pats |> List.map (fun _ -> freshTypeVar range), 0)

            let (argPatterns, argBindings) =
                List.zip pats payloadTypes
                |> List.map (fun (p, argTy) ->
                    checkPattern env p argTy range)
                |> List.unzip
            let payload = if List.isEmpty argPatterns then None else Some (Pattern.Tuple argPatterns)
            (Pattern.Union(caseName, tagIndex, payload, expectedTy), List.concat argBindings)
        | SynArgPats.NamePatPairs _ ->
            // Named pattern pairs (e.g., { Field = pat })
            // Look up binding to get tag index from UnionCaseInfo
            let tagIndex =
                match tryLookupBinding caseName env with
                | Some binding ->
                    match binding.UnionCaseInfo with
                    | Some caseInfo -> caseInfo.CaseIndex
                    | None -> 0
                | None -> 0
            (Pattern.Union(caseName, tagIndex, None, expectedTy), [])

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
                            | NativeType.TVar tv -> sprintf "'%s (unresolved type variable)" tv.Name
                            | _ -> sprintf "%A" resolvedTy
                        addDiagnostic {
                            Severity = NativeDiagnosticSeverity.Error
                            Code = "FS8720"
                            Message = sprintf "Record pattern field '%s' not found in type '%s'. Record type may not be registered in RecordDefs, or expectedTy is not resolved." fieldName tyName
                            Range = range
                            RelatedNodes = []
                        } env
                        // Return a placeholder type for error recovery, but the error is logged
                        Types.unitType
                let (pattern, bindings) = checkPattern env pat fieldTy range
                ((fieldName, pattern), bindings))
        let patterns = fieldPats |> List.map fst
        let bindings = fieldPats |> List.collect snd
        (Pattern.Record(patterns, expectedTy), bindings)

    | SynPat.IsInst(_synType, _) ->
        // Type test pattern: :? Type
        let testTy = failwith "ELIMINATE_SYNTYPE: Type test pattern - NTU type required"
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
            Code = "FS8700"
            Message = "Quote expression patterns are not supported in native F# compilation."
            Range = range
            RelatedNodes = []
        } env
        (Pattern.Wildcard, [])  // Wildcard for error recovery

    | SynPat.FromParseError(innerPat, _) ->
        // Parse error recovery - check inner pattern
        checkPattern env innerPat expectedTy range

    | SynPat.InstanceMember _ ->
        // Instance member pattern - for object expressions (not supported in native)
        addDiagnostic {
            Severity = NativeDiagnosticSeverity.Error
            Code = "FS8701"
            Message = "Instance member patterns (object expressions) are not supported in native F# compilation."
            Range = range
            RelatedNodes = []
        } env
        (Pattern.Wildcard, [])  // Wildcard for error recovery
