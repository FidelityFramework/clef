// ClefExpr.fs - CCS's native typed expression representation
//
// This is CCS's own typed expression type that REPLACES FSharpExpr from FCS.
// It is a PROJECTION/VIEW over SemanticGraph - materialized from SemanticNode + SemanticKind on demand.
//
// Design principles:
// - Native types only (NativeType), no CLR types
// - SRTP resolution captured via WitnessResolution
// - Memory annotations for arena/stack affinity
// - BCL-free, freestanding capable
// - Expression-centric view for tooling, debugging, IDE integration
//
// The SemanticGraph already has all information (types attached during construction).
// ClefExpr provides an expression-centric view that's easier to:
// - Pretty-print for debugging
// - Serialize to JSON for intermediate inspection
// - Navigate for IDE features (hover, go-to-definition)

namespace Clef.Compiler.NativeTypedTree

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics

/// Native match case for pattern matching
[<NoComparison; NoEquality>]
type NativeMatchCase = {
    /// The pattern (simplified representation)
    Pattern: NativePattern
    /// Optional guard: when expr
    Guard: ClefExpr option
    /// The case body
    Body: ClefExpr
}

/// Pattern for match cases
and [<RequireQualifiedAccess; NoComparison; NoEquality>] NativePattern =
    /// Wildcard pattern: _
    | Wildcard
    /// Named pattern: x
    | Named of name: string * ty: NativeType
    /// Literal pattern: 1, "hello", etc.
    | Literal of value: NativeLiteral
    /// Constructor pattern: Some x, None, etc.
    | Constructor of caseName: string * args: NativePattern list
    /// Tuple pattern: (a, b, c)
    | Tuple of elements: NativePattern list
    /// Record pattern: { field1 = p1; field2 = p2 }
    | Record of fields: (string * NativePattern) list
    /// Or pattern: p1 | p2
    | Or of left: NativePattern * right: NativePattern
    /// And pattern: p1 & p2
    | And of left: NativePattern * right: NativePattern
    /// As pattern: p as x
    | As of pattern: NativePattern * name: string
    /// Typed pattern: (p : T)
    | Typed of pattern: NativePattern * ty: NativeType
    /// Null pattern: null
    | Null

/// ClefExpr - Expression-centric view over SemanticGraph
/// Materialized from SemanticNode + SemanticKind on demand
and [<RequireQualifiedAccess; NoComparison; NoEquality>] ClefExpr =
    // ═══════════════════════════════════════════════════════════════════════════
    // Bindings
    // ═══════════════════════════════════════════════════════════════════════════

    /// Let binding: let x = value in body
    | LetBinding of
        name: string *
        isMutable: bool *
        value: ClefExpr *
        body: ClefExpr option *
        ty: NativeType

    /// Recursive let bindings: let rec f = ... and g = ... in body
    | LetRecBindings of
        bindings: (string * ClefExpr) list *
        body: ClefExpr option

    // ═══════════════════════════════════════════════════════════════════════════
    // Functions
    // ═══════════════════════════════════════════════════════════════════════════

    /// Lambda expression: fun x y -> body
    /// enclosingFunction: None at module level, Some "parentName" for nested functions (PRD-13)
    | Lambda of
        parameters: (string * NativeType) list *
        body: ClefExpr *
        returnType: NativeType *
        srtp: WitnessResolution option *
        enclosingFunction: string option

    /// Function application: f arg1 arg2
    | Application of
        func: ClefExpr *
        args: ClefExpr list *
        returnType: NativeType *
        srtp: WitnessResolution option

    // ═══════════════════════════════════════════════════════════════════════════
    // Values
    // ═══════════════════════════════════════════════════════════════════════════

    /// Literal value
    | Literal of value: NativeLiteral * ty: NativeType

    /// Variable reference
    | Variable of
        name: string *
        ty: NativeType *
        isMutable: bool *
        definitionId: NodeId option

    // ═══════════════════════════════════════════════════════════════════════════
    // Control Flow
    // ═══════════════════════════════════════════════════════════════════════════

    /// If-then-else: if guard then thenBranch else elseBranch
    | IfThenElse of
        guard: ClefExpr *
        thenBranch: ClefExpr *
        elseBranch: ClefExpr option *
        ty: NativeType

    /// Match expression: match scrutinee with | case1 -> ... | case2 -> ...
    | Match of
        scrutinee: ClefExpr *
        cases: NativeMatchCase list *
        ty: NativeType

    /// Sequential expression: expr1; expr2; ...
    | Sequential of exprs: ClefExpr list * ty: NativeType

    /// While loop: while guard do body
    | WhileLoop of
        guard: ClefExpr *
        body: ClefExpr

    /// For loop: for var = start to/downto finish do body
    | ForLoop of
        var: string *
        start: ClefExpr *
        finish: ClefExpr *
        isUp: bool *
        body: ClefExpr

    /// For-each loop: for x in collection do body
    | ForEach of
        var: string *
        collection: ClefExpr *
        body: ClefExpr

    // ═══════════════════════════════════════════════════════════════════════════
    // Exception Handling
    // ═══════════════════════════════════════════════════════════════════════════

    /// Try-with: try body with handler
    | TryWith of
        body: ClefExpr *
        handler: ClefExpr

    /// Try-finally: try body finally cleanup
    | TryFinally of
        body: ClefExpr *
        cleanup: ClefExpr

    // ═══════════════════════════════════════════════════════════════════════════
    // Data Structures
    // ═══════════════════════════════════════════════════════════════════════════

    /// Record expression: { field1 = v1; field2 = v2 }
    | RecordExpr of
        fields: (string * ClefExpr) list *
        copyFrom: ClefExpr option *
        ty: NativeType

    /// Union case: Some x, None, etc.
    | UnionCase of
        caseName: string *
        payload: ClefExpr option *
        ty: NativeType

    /// Tuple expression: (e1, e2, ...)
    | TupleExpr of
        elements: ClefExpr list *
        ty: NativeType

    /// Tuple element access: fst tuple, snd tuple, or tuple destructuring
    | TupleGet of
        tuple: ClefExpr *
        index: int *
        ty: NativeType

    /// Array expression: [| e1; e2; ... |]
    | ArrayExpr of
        elements: ClefExpr list *
        ty: NativeType

    /// List expression: [ e1; e2; ... ]
    | ListExpr of
        elements: ClefExpr list *
        ty: NativeType

    // ═══════════════════════════════════════════════════════════════════════════
    // Field and Index Access
    // ═══════════════════════════════════════════════════════════════════════════

    /// Field get: expr.field
    | FieldGet of
        expr: ClefExpr *
        fieldName: string *
        ty: NativeType

    /// Field set: expr.field <- value
    | FieldSet of
        expr: ClefExpr *
        fieldName: string *
        value: ClefExpr

    /// Index get: expr.[index]
    | IndexGet of
        expr: ClefExpr *
        index: ClefExpr *
        ty: NativeType

    /// Index set: expr.[index] <- value
    | IndexSet of
        expr: ClefExpr *
        index: ClefExpr *
        value: ClefExpr

    // ═══════════════════════════════════════════════════════════════════════════
    // Type Operations
    // ═══════════════════════════════════════════════════════════════════════════

    /// Type annotation: (expr : T)
    | TypeAnnotation of
        expr: ClefExpr *
        annotatedType: NativeType

    /// Upcast: expr :> T
    | Upcast of
        expr: ClefExpr *
        targetType: NativeType

    /// Downcast: expr :?> T
    | Downcast of
        expr: ClefExpr *
        targetType: NativeType

    /// Type test: expr :? T
    | TypeTest of
        expr: ClefExpr *
        testType: NativeType

    // ═══════════════════════════════════════════════════════════════════════════
    // Pointer Operations
    // ═══════════════════════════════════════════════════════════════════════════

    /// Address-of: &expr or &&expr
    | AddressOf of
        expr: ClefExpr *
        isByref: bool *
        ty: NativeType

    /// Dereference: !expr (for ref cells)
    | Deref of expr: ClefExpr * ty: NativeType

    /// Assignment: expr <- value
    | Set of
        target: ClefExpr *
        value: ClefExpr

    // ═══════════════════════════════════════════════════════════════════════════
    // Platform Integration (CRITICAL for debugging writeStrOut)
    // ═══════════════════════════════════════════════════════════════════════════

    /// Platform binding call - maps to syscalls or platform-specific code
    /// Alex provides platform-specific implementations for these
    | PlatformBinding of
        entryPoint: string *
        args: ClefExpr list *
        ty: NativeType

    /// Compiler intrinsic function (e.g., Sys.write)
    | Intrinsic of
        info: IntrinsicInfo *
        args: ClefExpr list *
        ty: NativeType

    // ═══════════════════════════════════════════════════════════════════════════
    // SRTP (Statically Resolved Type Parameters)
    // ═══════════════════════════════════════════════════════════════════════════

    /// SRTP trait call: (^T : (member Name : ...) x)
    /// SRTP is resolved at compile time - no runtime dispatch
    | TraitCall of
        memberName: string *
        constrainedTypes: NativeType list *
        arg: ClefExpr *
        resolution: WitnessResolution option *
        ty: NativeType

    // ═══════════════════════════════════════════════════════════════════════════
    // Strings
    // ═══════════════════════════════════════════════════════════════════════════

    /// Interpolated string: $"prefix{expr1}middle{expr2}suffix"
    | InterpolatedString of
        parts: InterpolatedStringPart list *
        ty: NativeType

    // ═══════════════════════════════════════════════════════════════════════════
    // Modules and Definitions
    // ═══════════════════════════════════════════════════════════════════════════

    /// Module definition (for top-level structure)
    | ModuleDef of
        name: string *
        members: ClefExpr list

    /// Type definition
    | TypeDef of
        name: string *
        kind: TypeDefKind *
        members: ClefExpr list

    /// Member definition
    | MemberDef of
        name: string *
        kind: MemberKind *
        body: ClefExpr option

    // ═══════════════════════════════════════════════════════════════════════════
    // Error Recovery
    // ═══════════════════════════════════════════════════════════════════════════

    /// Error node (for recovery)
    | Error of message: string * range: SourceRange
    /// A proof obligation node. Not an expression: it is reached through F,
    /// never through the expression spine, and is shown so the view is honest.
    | Obligation of info: ObligationInfo * range: SourceRange

/// Part of an interpolated string
and [<RequireQualifiedAccess>] InterpolatedStringPart =
    | Text of string
    | Expr of ClefExpr * format: string option


// ═══════════════════════════════════════════════════════════════════════════
// Conversion Module: SemanticGraph → ClefExpr
// ═══════════════════════════════════════════════════════════════════════════

module ClefExpr =

    /// Create an empty source range for error cases
    let private emptyRange : SourceRange = {
        File = ""
        Start = { Line = 0; Column = 0 }
        End = { Line = 0; Column = 0 }
    }

    /// Materialize an expression tree from SemanticGraph starting at a node
    let rec fromNode (graph: SemanticGraph) (nodeId: NodeId) : ClefExpr =
        match graph.Nodes.TryFind nodeId with
        | None -> ClefExpr.Error($"Node {NodeId.value nodeId} not found in graph", emptyRange)
        | Some node ->
            match node.Kind with
            // Literals
            | SemanticKind.Literal value ->
                ClefExpr.Literal(value, node.Type)

            // Variable references
            | SemanticKind.VarRef(name, defId) ->
                let isMutable =
                    defId
                    |> Option.bind (fun id -> graph.Nodes.TryFind id)
                    |> Option.map (fun defNode ->
                        match defNode.Kind with
                        | SemanticKind.Binding(_, isMut, _, _) -> isMut
                        | _ -> false)
                    |> Option.defaultValue false
                ClefExpr.Variable(name, node.Type, isMutable, defId)

            // Function application
            | SemanticKind.Application(funcId, argIds) ->
                let funcExpr = fromNode graph funcId
                let argExprs = argIds |> List.map (fromNode graph)
                ClefExpr.Application(funcExpr, argExprs, node.Type, node.SRTPResolution)

            // Lambda expressions
            | SemanticKind.Lambda(parameters, bodyId, _captures, enclosingFunction, _context) ->
                let bodyExpr = fromNode graph bodyId
                let returnType = extractReturnType node.Type
                // Convert 3-tuple (name, type, nodeId) to 2-tuple (name, type) for ClefExpr
                let params2 = parameters |> List.map (fun (name, ty, _nodeId) -> (name, ty))
                // Note: captures are available via the SemanticKind but ClefExpr.Lambda
                // doesn't include them - they're accessed via the PSG node during code generation
                // PRD-13: Include enclosingFunction for debugging nested function identity
                ClefExpr.Lambda(params2, bodyExpr, returnType, node.SRTPResolution, enclosingFunction)

            // Bindings
            | SemanticKind.Binding(name, isMutable, _isRecursive, _declRoot) ->
                // Find the value and body from children
                match node.Children with
                | valueId :: rest ->
                    let valueExpr = fromNode graph valueId
                    let bodyExpr =
                        match rest with
                        | bodyId :: _ -> Some(fromNode graph bodyId)
                        | [] -> None
                    ClefExpr.LetBinding(name, isMutable, valueExpr, bodyExpr, node.Type)
                | [] ->
                    ClefExpr.Error($"Binding {name} has no value", node.Range)

            // Sequential expressions
            | SemanticKind.Sequential nodeIds ->
                let exprs = nodeIds |> List.map (fromNode graph)
                ClefExpr.Sequential(exprs, node.Type)

            // If-then-else
            | SemanticKind.IfThenElse(guardId, thenId, elseIdOpt) ->
                let guardExpr = fromNode graph guardId
                let thenExpr = fromNode graph thenId
                let elseExpr = elseIdOpt |> Option.map (fromNode graph)
                ClefExpr.IfThenElse(guardExpr, thenExpr, elseExpr, node.Type)

            // Match expression
            | SemanticKind.Match(scrutineeId, cases) ->
                let scrutineeExpr = fromNode graph scrutineeId
                let nativeCases = cases |> List.map (convertMatchCase graph)
                ClefExpr.Match(scrutineeExpr, nativeCases, node.Type)

            // CaseElimination — display as Match for source-level representation
            | SemanticKind.CaseElimination(scrutineeId, arms) ->
                let scrutineeExpr = fromNode graph scrutineeId
                let nativeCases = arms |> List.map (fun arm ->
                    { Pattern = convertPattern arm.Pattern
                      Guard = arm.Guard |> Option.map (fromNode graph)
                      Body = fromNode graph arm.Body } : NativeMatchCase)
                ClefExpr.Match(scrutineeExpr, nativeCases, node.Type)

            // While loop
            | SemanticKind.WhileLoop(guardId, bodyId) ->
                let guardExpr = fromNode graph guardId
                let bodyExpr = fromNode graph bodyId
                ClefExpr.WhileLoop(guardExpr, bodyExpr)

            // For loop
            | SemanticKind.ForLoop(var, startId, finishId, isUp, bodyId) ->
                let startExpr = fromNode graph startId
                let finishExpr = fromNode graph finishId
                let bodyExpr = fromNode graph bodyId
                ClefExpr.ForLoop(var, startExpr, finishExpr, isUp, bodyExpr)

            // For-each loop
            | SemanticKind.ForEach(var, collectionId, bodyId) ->
                let collectionExpr = fromNode graph collectionId
                let bodyExpr = fromNode graph bodyId
                ClefExpr.ForEach(var, collectionExpr, bodyExpr)

            // Try-with
            | SemanticKind.TryWith(bodyId, handlerId) ->
                let bodyExpr = fromNode graph bodyId
                let handlerExpr = fromNode graph handlerId
                ClefExpr.TryWith(bodyExpr, handlerExpr)

            // Try-finally
            | SemanticKind.TryFinally(bodyId, cleanupId) ->
                let bodyExpr = fromNode graph bodyId
                let cleanupExpr = fromNode graph cleanupId
                ClefExpr.TryFinally(bodyExpr, cleanupExpr)

            // Record expression
            | SemanticKind.RecordExpr(fields, copyFromIdOpt) ->
                let fieldExprs = fields |> List.map (fun (name, id) -> (name, fromNode graph id))
                let copyFromExpr = copyFromIdOpt |> Option.map (fromNode graph)
                ClefExpr.RecordExpr(fieldExprs, copyFromExpr, node.Type)

            // Union case
            | SemanticKind.UnionCase(caseName, _caseIndex, payloadIdOpt) ->
                let payloadExpr = payloadIdOpt |> Option.map (fromNode graph)
                ClefExpr.UnionCase(caseName, payloadExpr, node.Type)

            // DU Operations (January 2026) - internal compiler operations
            // These are lowered during code generation, not user-visible expressions
            | SemanticKind.DUGetTag (duValueId, _) ->
                // Represents tag extraction - use FieldGet representation for now
                let duExpr = fromNode graph duValueId
                ClefExpr.FieldGet(duExpr, "Tag", node.Type)

            | SemanticKind.DUEliminate (duValueId, _caseIndex, caseName, _payloadType) ->
                // Represents type-safe payload extraction - use FieldGet representation
                let duExpr = fromNode graph duValueId
                ClefExpr.FieldGet(duExpr, caseName, node.Type)

            | SemanticKind.DUConstruct (caseName, _caseIndex, payloadIdOpt, _arenaHint) ->
                // Represents DU construction - use UnionCase representation
                let payloadExpr = payloadIdOpt |> Option.map (fromNode graph)
                ClefExpr.UnionCase(caseName, payloadExpr, node.Type)

            // Tuple expression
            | SemanticKind.TupleExpr elementIds ->
                let elements = elementIds |> List.map (fromNode graph)
                ClefExpr.TupleExpr(elements, node.Type)

            // Tuple element access (tuple destructuring)
            | SemanticKind.TupleGet(tupleId, index) ->
                let tuple = fromNode graph tupleId
                ClefExpr.TupleGet(tuple, index, node.Type)

            // Array expression
            | SemanticKind.ArrayExpr elementIds ->
                let elements = elementIds |> List.map (fromNode graph)
                ClefExpr.ArrayExpr(elements, node.Type)

            // List expression
            | SemanticKind.ListExpr elementIds ->
                let elements = elementIds |> List.map (fromNode graph)
                ClefExpr.ListExpr(elements, node.Type)

            // Field get
            | SemanticKind.FieldGet(exprId, fieldName) ->
                let expr = fromNode graph exprId
                ClefExpr.FieldGet(expr, fieldName, node.Type)

            // Field set
            | SemanticKind.FieldSet(exprId, fieldName, valueId) ->
                let expr = fromNode graph exprId
                let value = fromNode graph valueId
                ClefExpr.FieldSet(expr, fieldName, value)

            // Index get
            | SemanticKind.IndexGet(exprId, indexId) ->
                let expr = fromNode graph exprId
                let index = fromNode graph indexId
                ClefExpr.IndexGet(expr, index, node.Type)

            // Index set
            | SemanticKind.IndexSet(exprId, indexId, valueId) ->
                let expr = fromNode graph exprId
                let index = fromNode graph indexId
                let value = fromNode graph valueId
                ClefExpr.IndexSet(expr, index, value)

            // Named indexed property set
            | SemanticKind.NamedIndexedPropertySet(exprId, _propName, indexId, valueId) ->
                // Treat as index set for now
                let expr = fromNode graph exprId
                let index = fromNode graph indexId
                let value = fromNode graph valueId
                ClefExpr.IndexSet(expr, index, value)

            // Type annotation
            | SemanticKind.TypeAnnotation(exprId, annotatedType) ->
                let expr = fromNode graph exprId
                ClefExpr.TypeAnnotation(expr, annotatedType)

            // Upcast
            | SemanticKind.Upcast(exprId, targetType) ->
                let expr = fromNode graph exprId
                ClefExpr.Upcast(expr, targetType)

            // Downcast
            | SemanticKind.Downcast(exprId, targetType) ->
                let expr = fromNode graph exprId
                ClefExpr.Downcast(expr, targetType)

            // Type test
            | SemanticKind.TypeTest(exprId, testType) ->
                let expr = fromNode graph exprId
                ClefExpr.TypeTest(expr, testType)

            // Address-of
            | SemanticKind.AddressOf(exprId, isByref) ->
                let expr = fromNode graph exprId
                ClefExpr.AddressOf(expr, isByref, node.Type)

            // Dereference
            | SemanticKind.Deref exprId ->
                let expr = fromNode graph exprId
                ClefExpr.Deref(expr, node.Type)

            // Set (assignment)
            | SemanticKind.Set(targetId, valueId) ->
                let target = fromNode graph targetId
                let value = fromNode graph valueId
                ClefExpr.Set(target, value)

            // Platform binding
            | SemanticKind.PlatformBinding name ->
                // Find args from children
                let args = node.Children |> List.map (fromNode graph)
                ClefExpr.PlatformBinding(name, args, node.Type)

            // Intrinsic
            | SemanticKind.Intrinsic info ->
                let args = node.Children |> List.map (fromNode graph)
                ClefExpr.Intrinsic(info, args, node.Type)

            // SRTP trait call
            | SemanticKind.TraitCall(memberName, constrainedTypes, argId) ->
                let argExpr = fromNode graph argId
                ClefExpr.TraitCall(memberName, constrainedTypes, argExpr, node.SRTPResolution, node.Type)

            // Quote expression
            | SemanticKind.Quote(exprId, _isTyped) ->
                // For now, just convert the inner expression
                fromNode graph exprId

            // Object expression
            | SemanticKind.ObjectExpr(_interfaceType, memberIds) ->
                // Convert to a pseudo-record for now
                let members = memberIds |> List.map (fromNode graph)
                ClefExpr.TupleExpr(members, node.Type)

            // Module definition
            | SemanticKind.ModuleDef(name, memberIds) ->
                let members = memberIds |> List.map (fromNode graph)
                ClefExpr.ModuleDef(name, members)

            // Type definition
            | SemanticKind.TypeDef(name, kind, memberIds) ->
                let members = memberIds |> List.map (fromNode graph)
                ClefExpr.TypeDef(name, kind, members)

            // Member definition
            | SemanticKind.MemberDef(name, kind, bodyIdOpt) ->
                let bodyExpr = bodyIdOpt |> Option.map (fromNode graph)
                ClefExpr.MemberDef(name, kind, bodyExpr)

            // Interpolated string
            | SemanticKind.InterpolatedString parts ->
                let nativeParts = parts |> List.map (convertInterpolatedPart graph)
                ClefExpr.InterpolatedString(nativeParts, node.Type)

            // Pattern binding - a variable introduced by a match pattern
            // This is a definition node; direct traversal returns the variable
            | SemanticKind.PatternBinding name ->
                ClefExpr.Variable(name, node.Type, false, Some nodeId)

            // Lazy expressions (PRD-14)
            | SemanticKind.LazyExpr(bodyId, _captures) ->
                // Convert lazy body to an expression
                let bodyExpr = fromNode graph bodyId
                // For now, wrap as a special intrinsic call - Alex will handle
                ClefExpr.Intrinsic(
                    { Module = IntrinsicModule.Lazy
                      Operation = "create"
                      Category = IntrinsicCategory.Pure
                      FullName = "Lazy.create" },
                    [bodyExpr],
                    node.Type)

            | SemanticKind.LazyForce lazyValueId ->
                let lazyExpr = fromNode graph lazyValueId
                ClefExpr.Intrinsic(
                    { Module = IntrinsicModule.Lazy
                      Operation = "force"
                      Category = IntrinsicCategory.Pure
                      FullName = "Lazy.force" },
                    [lazyExpr],
                    node.Type)

            // Seq expressions (PRD-15)
            | SemanticKind.SeqExpr(bodyId, _captures) ->
                // Convert seq body (MoveNext thunk) to an expression
                let bodyExpr = fromNode graph bodyId
                // For now, wrap as a special intrinsic call - Alex will handle
                ClefExpr.Intrinsic(
                    { Module = IntrinsicModule.Seq
                      Operation = "create"
                      Category = IntrinsicCategory.Pure
                      FullName = "Seq.create" },
                    [bodyExpr],
                    node.Type)

            | SemanticKind.Yield valueId ->
                let valueExpr = fromNode graph valueId
                ClefExpr.Intrinsic(
                    { Module = IntrinsicModule.Seq
                      Operation = "yield"
                      Category = IntrinsicCategory.Pure
                      FullName = "Seq.yield" },
                    [valueExpr],
                    node.Type)

            | SemanticKind.YieldBang seqId ->
                let seqExpr = fromNode graph seqId
                ClefExpr.Intrinsic(
                    { Module = IntrinsicModule.Seq
                      Operation = "yieldFrom"
                      Category = IntrinsicCategory.Pure
                      FullName = "Seq.yieldFrom" },
                    [seqExpr],
                    node.Type)

            // Error
            | SemanticKind.Error message ->
                ClefExpr.Error(message, node.Range)

            // Obligation: a graph citizen, not an expression
            | SemanticKind.Obligation info ->
                ClefExpr.Obligation(info, node.Range)

    /// Convert a match case from SemanticGraph to native representation
    and private convertMatchCase (graph: SemanticGraph) (case: MatchCase) : NativeMatchCase =
        {
            Pattern = convertPattern case.Pattern
            Guard = case.Guard |> Option.map (fromNode graph)
            Body = fromNode graph case.Body
        }

    /// Convert a pattern from SemanticGraph to native representation
    and private convertPattern (pattern: Pattern) : NativePattern =
        match pattern with
        | Pattern.Wildcard -> NativePattern.Wildcard
        | Pattern.Var(name, ty) -> NativePattern.Named(name, ty)
        | Pattern.Const value -> NativePattern.Literal value
        | Pattern.Union(caseName, _tagIndex, payload, _unionType) ->
            let args = payload |> Option.map (fun p -> [convertPattern p]) |> Option.defaultValue []
            NativePattern.Constructor(caseName, args)
        | Pattern.Tuple elements ->
            NativePattern.Tuple(elements |> List.map convertPattern)
        | Pattern.Record(fields, _recordType) ->
            NativePattern.Record(fields |> List.map (fun (n, p) -> (n, convertPattern p)))
        | Pattern.Or(left, right) ->
            NativePattern.Or(convertPattern left, convertPattern right)
        | Pattern.And(left, right) ->
            NativePattern.And(convertPattern left, convertPattern right)
        | Pattern.As(pat, name) ->
            NativePattern.As(convertPattern pat, name)
        | Pattern.IsType ty ->
            NativePattern.Typed(NativePattern.Wildcard, ty)
        | Pattern.Null -> NativePattern.Null
        | Pattern.Array elements ->
            // Arrays use same structure as tuples for pattern matching
            NativePattern.Tuple(elements |> List.map convertPattern)
        | Pattern.Exception(_exnType, _bindName) ->
            // Exception patterns simplified to wildcard for now
            NativePattern.Wildcard

    /// Convert an interpolated string part
    and private convertInterpolatedPart (graph: SemanticGraph) (part: InterpolatedPart) : InterpolatedStringPart =
        match part with
        | InterpolatedPart.StringPart text -> InterpolatedStringPart.Text text
        | InterpolatedPart.ExprPart exprId ->
            InterpolatedStringPart.Expr(fromNode graph exprId, None)

    /// Extract the return type from a function type
    and private extractReturnType (ty: NativeType) : NativeType =
        match ty with
        | NativeType.TFun(_, range) -> range
        | _ -> ty

    // ═══════════════════════════════════════════════════════════════════════════
    // Entry Point Helpers
    // ═══════════════════════════════════════════════════════════════════════════

    /// Get ClefExpr trees for all declaration roots in the graph
    let fromDeclarationRoots (graph: SemanticGraph) : ClefExpr list =
        graph.DeclarationRoots |> List.map (fun (id, _) -> fromNode graph id)

    /// Get a single ClefExpr for a named binding
    let fromBinding (graph: SemanticGraph) (name: string) : ClefExpr option =
        graph.Nodes
        |> Map.tryPick (fun id node ->
            match node.Kind with
            | SemanticKind.Binding(bindingName, _, _, _) when bindingName = name ->
                Some (fromNode graph id)
            | _ -> None)

    // ═══════════════════════════════════════════════════════════════════════════
    // Pretty Printing
    // ═══════════════════════════════════════════════════════════════════════════

    /// Pretty-print an expression for debugging
    let rec prettyPrint (indent: int) (expr: ClefExpr) : string =
        let pad = String.replicate indent "  "

        match expr with
        | ClefExpr.Literal(value, _ty) ->
            sprintf "%sLiteral(%A)" pad value

        | ClefExpr.Variable(name, _ty, isMut, defId) ->
            let mutStr = if isMut then "mutable " else ""
            let defStr = defId |> Option.map (fun id -> sprintf " -> %d" (NodeId.value id)) |> Option.defaultValue ""
            sprintf "%sVar(%s%s%s)" pad mutStr name defStr

        | ClefExpr.Application(func, args, _ty, srtp) ->
            let funcStr = prettyPrint 0 func
            let argsStr = args |> List.map (prettyPrint 0) |> String.concat ", "
            let srtpStr = srtp |> Option.map (fun r -> sprintf " [SRTP: %s -> %s]" r.Operator r.ResolvedMember) |> Option.defaultValue ""
            sprintf "%sApp(%s, [%s])%s" pad funcStr argsStr srtpStr

        | ClefExpr.Lambda(params', body, _retTy, _srtp, enclosingFunc) ->
            let paramsStr = params' |> List.map fst |> String.concat ", "
            let bodyStr = prettyPrint (indent + 1) body
            let enclosingStr = enclosingFunc |> Option.map (sprintf " [enclosing: %s]") |> Option.defaultValue ""
            sprintf "%sLambda(%s)%s ->\n%s" pad paramsStr enclosingStr bodyStr

        | ClefExpr.LetBinding(name, isMut, value, body, _ty) ->
            let mutStr = if isMut then "mutable " else ""
            let valueStr = prettyPrint (indent + 1) value
            let bodyStr = body |> Option.map (prettyPrint (indent + 1)) |> Option.defaultValue ""
            sprintf "%sLet %s%s =\n%s%s" pad mutStr name valueStr (if bodyStr = "" then "" else "\n" + bodyStr)

        | ClefExpr.Sequential(exprs, _ty) ->
            let exprsStr = exprs |> List.map (prettyPrint (indent + 1)) |> String.concat "\n"
            sprintf "%sSeq:\n%s" pad exprsStr

        | ClefExpr.IfThenElse(guard, thenBr, elseBr, _ty) ->
            let guardStr = prettyPrint 0 guard
            let thenStr = prettyPrint (indent + 1) thenBr
            let elseStr = elseBr |> Option.map (prettyPrint (indent + 1)) |> Option.defaultValue ""
            sprintf "%sIf %s then\n%s%s" pad guardStr thenStr (if elseStr = "" then "" else sprintf "\n%selse\n%s" pad elseStr)

        | ClefExpr.PlatformBinding(name, args, _ty) ->
            let argsStr = args |> List.map (prettyPrint 0) |> String.concat ", "
            sprintf "%sPlatformBinding(%s, [%s])" pad name argsStr

        | ClefExpr.TraitCall(memberName, _types, arg, resolution, _ty) ->
            let argStr = prettyPrint 0 arg
            let resStr = resolution |> Option.map (fun r -> sprintf " -> %s" r.ResolvedMember) |> Option.defaultValue " (UNRESOLVED)"
            sprintf "%sTraitCall(%s, %s)%s" pad memberName argStr resStr

        | ClefExpr.ModuleDef(name, members) ->
            let membersStr = members |> List.map (prettyPrint (indent + 1)) |> String.concat "\n"
            sprintf "%sModule %s:\n%s" pad name membersStr

        | ClefExpr.Error(message, range) ->
            sprintf "%sERROR: %s at %s" pad message (range.ToString())

        | ClefExpr.Obligation(info, _) ->
            sprintf "%sOBLIGATION %s [%s]: %s" pad info.Id info.Kind info.Statement

        | _ ->
            sprintf "%s%A" pad expr

    /// Get a compact string representation for logging
    let toCompactString (expr: ClefExpr) : string =
        match expr with
        | ClefExpr.Literal(value, _) -> sprintf "Literal(%A)" value
        | ClefExpr.Variable(name, _, _, _) -> sprintf "Var(%s)" name
        | ClefExpr.Application(_, args, _, _) -> sprintf "App(..., %d args)" (List.length args)
        | ClefExpr.Lambda(params', _, _, _, _) -> sprintf "Lambda(%d params)" (List.length params')
        | ClefExpr.LetBinding(name, _, _, _, _) -> sprintf "Let(%s)" name
        | ClefExpr.LetRecBindings(bindings, _) -> sprintf "LetRec(%d bindings)" (List.length bindings)
        | ClefExpr.Sequential(exprs, _) -> sprintf "Seq(%d)" (List.length exprs)
        | ClefExpr.IfThenElse(_, _, _, _) -> "IfThenElse"
        | ClefExpr.Match(_, cases, _) -> sprintf "Match(%d cases)" (List.length cases)
        | ClefExpr.WhileLoop(_, _) -> "While"
        | ClefExpr.ForLoop(var, _, _, _, _) -> sprintf "For(%s)" var
        | ClefExpr.ForEach(var, _, _) -> sprintf "ForEach(%s)" var
        | ClefExpr.TryWith(_, _) -> "TryWith"
        | ClefExpr.TryFinally(_, _) -> "TryFinally"
        | ClefExpr.RecordExpr(fields, _, _) -> sprintf "Record(%d fields)" (List.length fields)
        | ClefExpr.UnionCase(name, _, _) -> sprintf "Case(%s)" name
        | ClefExpr.TupleExpr(elements, _) -> sprintf "Tuple(%d)" (List.length elements)
        | ClefExpr.TupleGet(_, index, _) -> sprintf "TupleGet[%d]" index
        | ClefExpr.ArrayExpr(elements, _) -> sprintf "Array(%d)" (List.length elements)
        | ClefExpr.ListExpr(elements, _) -> sprintf "List(%d)" (List.length elements)
        | ClefExpr.FieldGet(_, name, _) -> sprintf "FieldGet(.%s)" name
        | ClefExpr.FieldSet(_, name, _) -> sprintf "FieldSet(.%s)" name
        | ClefExpr.IndexGet(_, _, _) -> "IndexGet"
        | ClefExpr.IndexSet(_, _, _) -> "IndexSet"
        | ClefExpr.TypeAnnotation(_, _) -> "TypeAnnotation"
        | ClefExpr.Upcast(_, _) -> "Upcast"
        | ClefExpr.Downcast(_, _) -> "Downcast"
        | ClefExpr.TypeTest(_, _) -> "TypeTest"
        | ClefExpr.AddressOf(_, isByref, _) -> if isByref then "AddressOfByref" else "AddressOf"
        | ClefExpr.Deref(_, _) -> "Deref"
        | ClefExpr.Set(_, _) -> "Set"
        | ClefExpr.PlatformBinding(name, _, _) -> sprintf "Platform(%s)" name
        | ClefExpr.Intrinsic(info, _, _) -> sprintf "Intrinsic(%s)" info.FullName
        | ClefExpr.TraitCall(name, _, _, res, _) ->
            let resolved = res |> Option.map (fun r -> sprintf "->%s" r.ResolvedMember) |> Option.defaultValue ""
            sprintf "TraitCall(%s%s)" name resolved
        | ClefExpr.InterpolatedString(parts, _) -> sprintf "Interpolated(%d parts)" (List.length parts)
        | ClefExpr.ModuleDef(name, _) -> sprintf "Module(%s)" name
        | ClefExpr.TypeDef(name, _, _) -> sprintf "Type(%s)" name
        | ClefExpr.MemberDef(name, _, _) -> sprintf "Member(%s)" name
        | ClefExpr.Error(msg, _) -> sprintf "Error(%s)" msg
        | ClefExpr.Obligation(info, _) -> sprintf "Obligation(%s)" info.Id
