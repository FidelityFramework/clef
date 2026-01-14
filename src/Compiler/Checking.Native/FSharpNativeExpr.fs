// FSharpNativeExpr.fs - FNCS's native typed expression representation
//
// This is FNCS's own typed expression type that REPLACES FSharpExpr from FCS.
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
// FSharpNativeExpr provides an expression-centric view that's easier to:
// - Pretty-print for debugging
// - Serialize to JSON for intermediate inspection
// - Navigate for IDE features (hover, go-to-definition)

namespace FSharp.Native.Compiler.Checking.Native

open FSharp.Native.Compiler.Checking.Native.NativeTypes
open FSharp.Native.Compiler.Checking.Native.SemanticGraph

/// Native match case for pattern matching
[<NoComparison; NoEquality>]
type NativeMatchCase = {
    /// The pattern (simplified representation)
    Pattern: NativePattern
    /// Optional guard: when expr
    Guard: FSharpNativeExpr option
    /// The case body
    Body: FSharpNativeExpr
}

/// Pattern for match cases
and [<RequireQualifiedAccess; NoComparison; NoEquality>] NativePattern =
    /// Wildcard pattern: _
    | Wildcard
    /// Named pattern: x
    | Named of name: string * ty: NativeType
    /// Literal pattern: 1, "hello", etc.
    | Literal of value: LiteralValue
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

/// FSharpNativeExpr - Expression-centric view over SemanticGraph
/// Materialized from SemanticNode + SemanticKind on demand
and [<RequireQualifiedAccess; NoComparison; NoEquality>] FSharpNativeExpr =
    // ═══════════════════════════════════════════════════════════════════════════
    // Bindings
    // ═══════════════════════════════════════════════════════════════════════════

    /// Let binding: let x = value in body
    | LetBinding of
        name: string *
        isMutable: bool *
        value: FSharpNativeExpr *
        body: FSharpNativeExpr option *
        ty: NativeType

    /// Recursive let bindings: let rec f = ... and g = ... in body
    | LetRecBindings of
        bindings: (string * FSharpNativeExpr) list *
        body: FSharpNativeExpr option

    // ═══════════════════════════════════════════════════════════════════════════
    // Functions
    // ═══════════════════════════════════════════════════════════════════════════

    /// Lambda expression: fun x y -> body
    | Lambda of
        parameters: (string * NativeType) list *
        body: FSharpNativeExpr *
        returnType: NativeType *
        srtp: WitnessResolution option

    /// Function application: f arg1 arg2
    | Application of
        func: FSharpNativeExpr *
        args: FSharpNativeExpr list *
        returnType: NativeType *
        srtp: WitnessResolution option

    // ═══════════════════════════════════════════════════════════════════════════
    // Values
    // ═══════════════════════════════════════════════════════════════════════════

    /// Literal value
    | Literal of value: LiteralValue * ty: NativeType

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
        guard: FSharpNativeExpr *
        thenBranch: FSharpNativeExpr *
        elseBranch: FSharpNativeExpr option *
        ty: NativeType

    /// Match expression: match scrutinee with | case1 -> ... | case2 -> ...
    | Match of
        scrutinee: FSharpNativeExpr *
        cases: NativeMatchCase list *
        ty: NativeType

    /// Sequential expression: expr1; expr2; ...
    | Sequential of exprs: FSharpNativeExpr list * ty: NativeType

    /// While loop: while guard do body
    | WhileLoop of
        guard: FSharpNativeExpr *
        body: FSharpNativeExpr

    /// For loop: for var = start to/downto finish do body
    | ForLoop of
        var: string *
        start: FSharpNativeExpr *
        finish: FSharpNativeExpr *
        isUp: bool *
        body: FSharpNativeExpr

    /// For-each loop: for x in collection do body
    | ForEach of
        var: string *
        collection: FSharpNativeExpr *
        body: FSharpNativeExpr

    // ═══════════════════════════════════════════════════════════════════════════
    // Exception Handling
    // ═══════════════════════════════════════════════════════════════════════════

    /// Try-with: try body with handler
    | TryWith of
        body: FSharpNativeExpr *
        handler: FSharpNativeExpr

    /// Try-finally: try body finally cleanup
    | TryFinally of
        body: FSharpNativeExpr *
        cleanup: FSharpNativeExpr

    // ═══════════════════════════════════════════════════════════════════════════
    // Data Structures
    // ═══════════════════════════════════════════════════════════════════════════

    /// Record expression: { field1 = v1; field2 = v2 }
    | RecordExpr of
        fields: (string * FSharpNativeExpr) list *
        copyFrom: FSharpNativeExpr option *
        ty: NativeType

    /// Union case: Some x, None, etc.
    | UnionCase of
        caseName: string *
        payload: FSharpNativeExpr option *
        ty: NativeType

    /// Tuple expression: (e1, e2, ...)
    | TupleExpr of
        elements: FSharpNativeExpr list *
        ty: NativeType

    /// Array expression: [| e1; e2; ... |]
    | ArrayExpr of
        elements: FSharpNativeExpr list *
        ty: NativeType

    /// List expression: [ e1; e2; ... ]
    | ListExpr of
        elements: FSharpNativeExpr list *
        ty: NativeType

    // ═══════════════════════════════════════════════════════════════════════════
    // Field and Index Access
    // ═══════════════════════════════════════════════════════════════════════════

    /// Field get: expr.field
    | FieldGet of
        expr: FSharpNativeExpr *
        fieldName: string *
        ty: NativeType

    /// Field set: expr.field <- value
    | FieldSet of
        expr: FSharpNativeExpr *
        fieldName: string *
        value: FSharpNativeExpr

    /// Index get: expr.[index]
    | IndexGet of
        expr: FSharpNativeExpr *
        index: FSharpNativeExpr *
        ty: NativeType

    /// Index set: expr.[index] <- value
    | IndexSet of
        expr: FSharpNativeExpr *
        index: FSharpNativeExpr *
        value: FSharpNativeExpr

    // ═══════════════════════════════════════════════════════════════════════════
    // Type Operations
    // ═══════════════════════════════════════════════════════════════════════════

    /// Type annotation: (expr : T)
    | TypeAnnotation of
        expr: FSharpNativeExpr *
        annotatedType: NativeType

    /// Upcast: expr :> T
    | Upcast of
        expr: FSharpNativeExpr *
        targetType: NativeType

    /// Downcast: expr :?> T
    | Downcast of
        expr: FSharpNativeExpr *
        targetType: NativeType

    /// Type test: expr :? T
    | TypeTest of
        expr: FSharpNativeExpr *
        testType: NativeType

    // ═══════════════════════════════════════════════════════════════════════════
    // Pointer Operations
    // ═══════════════════════════════════════════════════════════════════════════

    /// Address-of: &expr or &&expr
    | AddressOf of
        expr: FSharpNativeExpr *
        isByref: bool *
        ty: NativeType

    /// Dereference: !expr (for ref cells)
    | Deref of expr: FSharpNativeExpr * ty: NativeType

    /// Assignment: expr <- value
    | Set of
        target: FSharpNativeExpr *
        value: FSharpNativeExpr

    // ═══════════════════════════════════════════════════════════════════════════
    // Platform Integration (CRITICAL for debugging writeStrOut)
    // ═══════════════════════════════════════════════════════════════════════════

    /// Platform binding call - maps to syscalls or platform-specific code
    /// Alex provides platform-specific implementations for these
    | PlatformBinding of
        entryPoint: string *
        args: FSharpNativeExpr list *
        ty: NativeType

    /// Compiler intrinsic function (e.g., NativePtr.toNativeInt)
    | Intrinsic of
        info: IntrinsicInfo *
        args: FSharpNativeExpr list *
        ty: NativeType

    // ═══════════════════════════════════════════════════════════════════════════
    // SRTP (Statically Resolved Type Parameters)
    // ═══════════════════════════════════════════════════════════════════════════

    /// SRTP trait call: (^T : (member Name : ...) x)
    /// SRTP is resolved at compile time - no runtime dispatch
    | TraitCall of
        memberName: string *
        constrainedTypes: NativeType list *
        arg: FSharpNativeExpr *
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
        members: FSharpNativeExpr list

    /// Type definition
    | TypeDef of
        name: string *
        kind: TypeDefKind *
        members: FSharpNativeExpr list

    /// Member definition
    | MemberDef of
        name: string *
        kind: MemberKind *
        body: FSharpNativeExpr option

    // ═══════════════════════════════════════════════════════════════════════════
    // Error Recovery
    // ═══════════════════════════════════════════════════════════════════════════

    /// Error node (for recovery)
    | Error of message: string * range: SourceRange

/// Part of an interpolated string
and [<RequireQualifiedAccess>] InterpolatedStringPart =
    | Text of string
    | Expr of FSharpNativeExpr * format: string option


// ═══════════════════════════════════════════════════════════════════════════
// Conversion Module: SemanticGraph → FSharpNativeExpr
// ═══════════════════════════════════════════════════════════════════════════

module FSharpNativeExpr =

    /// Create an empty source range for error cases
    let private emptyRange : SourceRange = {
        File = ""
        Start = { Line = 0; Column = 0 }
        End = { Line = 0; Column = 0 }
    }

    /// Materialize an expression tree from SemanticGraph starting at a node
    let rec fromNode (graph: SemanticGraph) (nodeId: NodeId) : FSharpNativeExpr =
        match graph.Nodes.TryFind nodeId with
        | None -> FSharpNativeExpr.Error($"Node {NodeId.value nodeId} not found in graph", emptyRange)
        | Some node ->
            match node.Kind with
            // Literals
            | SemanticKind.Literal value ->
                FSharpNativeExpr.Literal(value, node.Type)

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
                FSharpNativeExpr.Variable(name, node.Type, isMutable, defId)

            // Function application
            | SemanticKind.Application(funcId, argIds) ->
                let funcExpr = fromNode graph funcId
                let argExprs = argIds |> List.map (fromNode graph)
                FSharpNativeExpr.Application(funcExpr, argExprs, node.Type, node.SRTPResolution)

            // Lambda expressions
            | SemanticKind.Lambda(parameters, bodyId) ->
                let bodyExpr = fromNode graph bodyId
                let returnType = extractReturnType node.Type
                // Convert 3-tuple (name, type, nodeId) to 2-tuple (name, type) for FSharpNativeExpr
                let params2 = parameters |> List.map (fun (name, ty, _nodeId) -> (name, ty))
                FSharpNativeExpr.Lambda(params2, bodyExpr, returnType, node.SRTPResolution)

            // Bindings
            | SemanticKind.Binding(name, isMutable, _isRecursive, _isEntryPoint) ->
                // Find the value and body from children
                match node.Children with
                | valueId :: rest ->
                    let valueExpr = fromNode graph valueId
                    let bodyExpr =
                        match rest with
                        | bodyId :: _ -> Some(fromNode graph bodyId)
                        | [] -> None
                    FSharpNativeExpr.LetBinding(name, isMutable, valueExpr, bodyExpr, node.Type)
                | [] ->
                    FSharpNativeExpr.Error($"Binding {name} has no value", node.Range)

            // Sequential expressions
            | SemanticKind.Sequential nodeIds ->
                let exprs = nodeIds |> List.map (fromNode graph)
                FSharpNativeExpr.Sequential(exprs, node.Type)

            // If-then-else
            | SemanticKind.IfThenElse(guardId, thenId, elseIdOpt) ->
                let guardExpr = fromNode graph guardId
                let thenExpr = fromNode graph thenId
                let elseExpr = elseIdOpt |> Option.map (fromNode graph)
                FSharpNativeExpr.IfThenElse(guardExpr, thenExpr, elseExpr, node.Type)

            // Match expression
            | SemanticKind.Match(scrutineeId, cases) ->
                let scrutineeExpr = fromNode graph scrutineeId
                let nativeCases = cases |> List.map (convertMatchCase graph)
                FSharpNativeExpr.Match(scrutineeExpr, nativeCases, node.Type)

            // While loop
            | SemanticKind.WhileLoop(guardId, bodyId) ->
                let guardExpr = fromNode graph guardId
                let bodyExpr = fromNode graph bodyId
                FSharpNativeExpr.WhileLoop(guardExpr, bodyExpr)

            // For loop
            | SemanticKind.ForLoop(var, startId, finishId, isUp, bodyId) ->
                let startExpr = fromNode graph startId
                let finishExpr = fromNode graph finishId
                let bodyExpr = fromNode graph bodyId
                FSharpNativeExpr.ForLoop(var, startExpr, finishExpr, isUp, bodyExpr)

            // For-each loop
            | SemanticKind.ForEach(var, collectionId, bodyId) ->
                let collectionExpr = fromNode graph collectionId
                let bodyExpr = fromNode graph bodyId
                FSharpNativeExpr.ForEach(var, collectionExpr, bodyExpr)

            // Try-with
            | SemanticKind.TryWith(bodyId, handlerId) ->
                let bodyExpr = fromNode graph bodyId
                let handlerExpr = fromNode graph handlerId
                FSharpNativeExpr.TryWith(bodyExpr, handlerExpr)

            // Try-finally
            | SemanticKind.TryFinally(bodyId, cleanupId) ->
                let bodyExpr = fromNode graph bodyId
                let cleanupExpr = fromNode graph cleanupId
                FSharpNativeExpr.TryFinally(bodyExpr, cleanupExpr)

            // Record expression
            | SemanticKind.RecordExpr(fields, copyFromIdOpt) ->
                let fieldExprs = fields |> List.map (fun (name, id) -> (name, fromNode graph id))
                let copyFromExpr = copyFromIdOpt |> Option.map (fromNode graph)
                FSharpNativeExpr.RecordExpr(fieldExprs, copyFromExpr, node.Type)

            // Union case
            | SemanticKind.UnionCase(caseName, _caseIndex, payloadIdOpt) ->
                let payloadExpr = payloadIdOpt |> Option.map (fromNode graph)
                FSharpNativeExpr.UnionCase(caseName, payloadExpr, node.Type)

            // Tuple expression
            | SemanticKind.TupleExpr elementIds ->
                let elements = elementIds |> List.map (fromNode graph)
                FSharpNativeExpr.TupleExpr(elements, node.Type)

            // Array expression
            | SemanticKind.ArrayExpr elementIds ->
                let elements = elementIds |> List.map (fromNode graph)
                FSharpNativeExpr.ArrayExpr(elements, node.Type)

            // List expression
            | SemanticKind.ListExpr elementIds ->
                let elements = elementIds |> List.map (fromNode graph)
                FSharpNativeExpr.ListExpr(elements, node.Type)

            // Field get
            | SemanticKind.FieldGet(exprId, fieldName) ->
                let expr = fromNode graph exprId
                FSharpNativeExpr.FieldGet(expr, fieldName, node.Type)

            // Field set
            | SemanticKind.FieldSet(exprId, fieldName, valueId) ->
                let expr = fromNode graph exprId
                let value = fromNode graph valueId
                FSharpNativeExpr.FieldSet(expr, fieldName, value)

            // Index get
            | SemanticKind.IndexGet(exprId, indexId) ->
                let expr = fromNode graph exprId
                let index = fromNode graph indexId
                FSharpNativeExpr.IndexGet(expr, index, node.Type)

            // Index set
            | SemanticKind.IndexSet(exprId, indexId, valueId) ->
                let expr = fromNode graph exprId
                let index = fromNode graph indexId
                let value = fromNode graph valueId
                FSharpNativeExpr.IndexSet(expr, index, value)

            // Named indexed property set
            | SemanticKind.NamedIndexedPropertySet(exprId, _propName, indexId, valueId) ->
                // Treat as index set for now
                let expr = fromNode graph exprId
                let index = fromNode graph indexId
                let value = fromNode graph valueId
                FSharpNativeExpr.IndexSet(expr, index, value)

            // Type annotation
            | SemanticKind.TypeAnnotation(exprId, annotatedType) ->
                let expr = fromNode graph exprId
                FSharpNativeExpr.TypeAnnotation(expr, annotatedType)

            // Upcast
            | SemanticKind.Upcast(exprId, targetType) ->
                let expr = fromNode graph exprId
                FSharpNativeExpr.Upcast(expr, targetType)

            // Downcast
            | SemanticKind.Downcast(exprId, targetType) ->
                let expr = fromNode graph exprId
                FSharpNativeExpr.Downcast(expr, targetType)

            // Type test
            | SemanticKind.TypeTest(exprId, testType) ->
                let expr = fromNode graph exprId
                FSharpNativeExpr.TypeTest(expr, testType)

            // Address-of
            | SemanticKind.AddressOf(exprId, isByref) ->
                let expr = fromNode graph exprId
                FSharpNativeExpr.AddressOf(expr, isByref, node.Type)

            // Dereference
            | SemanticKind.Deref exprId ->
                let expr = fromNode graph exprId
                FSharpNativeExpr.Deref(expr, node.Type)

            // Set (assignment)
            | SemanticKind.Set(targetId, valueId) ->
                let target = fromNode graph targetId
                let value = fromNode graph valueId
                FSharpNativeExpr.Set(target, value)

            // Platform binding
            | SemanticKind.PlatformBinding name ->
                // Find args from children
                let args = node.Children |> List.map (fromNode graph)
                FSharpNativeExpr.PlatformBinding(name, args, node.Type)

            // Intrinsic
            | SemanticKind.Intrinsic info ->
                let args = node.Children |> List.map (fromNode graph)
                FSharpNativeExpr.Intrinsic(info, args, node.Type)

            // SRTP trait call
            | SemanticKind.TraitCall(memberName, constrainedTypes, argId) ->
                let argExpr = fromNode graph argId
                FSharpNativeExpr.TraitCall(memberName, constrainedTypes, argExpr, node.SRTPResolution, node.Type)

            // Quote expression
            | SemanticKind.Quote(exprId, _isTyped) ->
                // For now, just convert the inner expression
                fromNode graph exprId

            // Object expression
            | SemanticKind.ObjectExpr(_interfaceType, memberIds) ->
                // Convert to a pseudo-record for now
                let members = memberIds |> List.map (fromNode graph)
                FSharpNativeExpr.TupleExpr(members, node.Type)

            // Module definition
            | SemanticKind.ModuleDef(name, memberIds) ->
                let members = memberIds |> List.map (fromNode graph)
                FSharpNativeExpr.ModuleDef(name, members)

            // Type definition
            | SemanticKind.TypeDef(name, kind, memberIds) ->
                let members = memberIds |> List.map (fromNode graph)
                FSharpNativeExpr.TypeDef(name, kind, members)

            // Member definition
            | SemanticKind.MemberDef(name, kind, bodyIdOpt) ->
                let bodyExpr = bodyIdOpt |> Option.map (fromNode graph)
                FSharpNativeExpr.MemberDef(name, kind, bodyExpr)

            // Interpolated string
            | SemanticKind.InterpolatedString parts ->
                let nativeParts = parts |> List.map (convertInterpolatedPart graph)
                FSharpNativeExpr.InterpolatedString(nativeParts, node.Type)

            // Pattern binding - a variable introduced by a match pattern
            // This is a definition node; direct traversal returns the variable
            | SemanticKind.PatternBinding name ->
                FSharpNativeExpr.Variable(name, node.Type, false, Some nodeId)

            // Error
            | SemanticKind.Error message ->
                FSharpNativeExpr.Error(message, node.Range)

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
        | Pattern.Union(caseName, payload, _unionType) ->
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

    /// Get FSharpNativeExpr trees for all entry points in the graph
    let fromEntryPoints (graph: SemanticGraph) : FSharpNativeExpr list =
        graph.EntryPoints |> List.map (fromNode graph)

    /// Get a single FSharpNativeExpr for a named binding
    let fromBinding (graph: SemanticGraph) (name: string) : FSharpNativeExpr option =
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
    let rec prettyPrint (indent: int) (expr: FSharpNativeExpr) : string =
        let pad = String.replicate indent "  "

        match expr with
        | FSharpNativeExpr.Literal(value, _ty) ->
            sprintf "%sLiteral(%A)" pad value

        | FSharpNativeExpr.Variable(name, _ty, isMut, defId) ->
            let mutStr = if isMut then "mutable " else ""
            let defStr = defId |> Option.map (fun id -> sprintf " -> %d" (NodeId.value id)) |> Option.defaultValue ""
            sprintf "%sVar(%s%s%s)" pad mutStr name defStr

        | FSharpNativeExpr.Application(func, args, _ty, srtp) ->
            let funcStr = prettyPrint 0 func
            let argsStr = args |> List.map (prettyPrint 0) |> String.concat ", "
            let srtpStr = srtp |> Option.map (fun r -> sprintf " [SRTP: %s -> %s]" r.Operator r.ResolvedMember) |> Option.defaultValue ""
            sprintf "%sApp(%s, [%s])%s" pad funcStr argsStr srtpStr

        | FSharpNativeExpr.Lambda(params', body, _retTy, _srtp) ->
            let paramsStr = params' |> List.map fst |> String.concat ", "
            let bodyStr = prettyPrint (indent + 1) body
            sprintf "%sLambda(%s) ->\n%s" pad paramsStr bodyStr

        | FSharpNativeExpr.LetBinding(name, isMut, value, body, _ty) ->
            let mutStr = if isMut then "mutable " else ""
            let valueStr = prettyPrint (indent + 1) value
            let bodyStr = body |> Option.map (prettyPrint (indent + 1)) |> Option.defaultValue ""
            sprintf "%sLet %s%s =\n%s%s" pad mutStr name valueStr (if bodyStr = "" then "" else "\n" + bodyStr)

        | FSharpNativeExpr.Sequential(exprs, _ty) ->
            let exprsStr = exprs |> List.map (prettyPrint (indent + 1)) |> String.concat "\n"
            sprintf "%sSeq:\n%s" pad exprsStr

        | FSharpNativeExpr.IfThenElse(guard, thenBr, elseBr, _ty) ->
            let guardStr = prettyPrint 0 guard
            let thenStr = prettyPrint (indent + 1) thenBr
            let elseStr = elseBr |> Option.map (prettyPrint (indent + 1)) |> Option.defaultValue ""
            sprintf "%sIf %s then\n%s%s" pad guardStr thenStr (if elseStr = "" then "" else sprintf "\n%selse\n%s" pad elseStr)

        | FSharpNativeExpr.PlatformBinding(name, args, _ty) ->
            let argsStr = args |> List.map (prettyPrint 0) |> String.concat ", "
            sprintf "%sPlatformBinding(%s, [%s])" pad name argsStr

        | FSharpNativeExpr.TraitCall(memberName, _types, arg, resolution, _ty) ->
            let argStr = prettyPrint 0 arg
            let resStr = resolution |> Option.map (fun r -> sprintf " -> %s" r.ResolvedMember) |> Option.defaultValue " (UNRESOLVED)"
            sprintf "%sTraitCall(%s, %s)%s" pad memberName argStr resStr

        | FSharpNativeExpr.ModuleDef(name, members) ->
            let membersStr = members |> List.map (prettyPrint (indent + 1)) |> String.concat "\n"
            sprintf "%sModule %s:\n%s" pad name membersStr

        | FSharpNativeExpr.Error(message, range) ->
            sprintf "%sERROR: %s at %s" pad message (range.ToString())

        | _ ->
            sprintf "%s%A" pad expr

    /// Get a compact string representation for logging
    let toCompactString (expr: FSharpNativeExpr) : string =
        match expr with
        | FSharpNativeExpr.Literal(value, _) -> sprintf "Literal(%A)" value
        | FSharpNativeExpr.Variable(name, _, _, _) -> sprintf "Var(%s)" name
        | FSharpNativeExpr.Application(_, args, _, _) -> sprintf "App(..., %d args)" (List.length args)
        | FSharpNativeExpr.Lambda(params', _, _, _) -> sprintf "Lambda(%d params)" (List.length params')
        | FSharpNativeExpr.LetBinding(name, _, _, _, _) -> sprintf "Let(%s)" name
        | FSharpNativeExpr.LetRecBindings(bindings, _) -> sprintf "LetRec(%d bindings)" (List.length bindings)
        | FSharpNativeExpr.Sequential(exprs, _) -> sprintf "Seq(%d)" (List.length exprs)
        | FSharpNativeExpr.IfThenElse(_, _, _, _) -> "IfThenElse"
        | FSharpNativeExpr.Match(_, cases, _) -> sprintf "Match(%d cases)" (List.length cases)
        | FSharpNativeExpr.WhileLoop(_, _) -> "While"
        | FSharpNativeExpr.ForLoop(var, _, _, _, _) -> sprintf "For(%s)" var
        | FSharpNativeExpr.ForEach(var, _, _) -> sprintf "ForEach(%s)" var
        | FSharpNativeExpr.TryWith(_, _) -> "TryWith"
        | FSharpNativeExpr.TryFinally(_, _) -> "TryFinally"
        | FSharpNativeExpr.RecordExpr(fields, _, _) -> sprintf "Record(%d fields)" (List.length fields)
        | FSharpNativeExpr.UnionCase(name, _, _) -> sprintf "Case(%s)" name
        | FSharpNativeExpr.TupleExpr(elements, _) -> sprintf "Tuple(%d)" (List.length elements)
        | FSharpNativeExpr.ArrayExpr(elements, _) -> sprintf "Array(%d)" (List.length elements)
        | FSharpNativeExpr.ListExpr(elements, _) -> sprintf "List(%d)" (List.length elements)
        | FSharpNativeExpr.FieldGet(_, name, _) -> sprintf "FieldGet(.%s)" name
        | FSharpNativeExpr.FieldSet(_, name, _) -> sprintf "FieldSet(.%s)" name
        | FSharpNativeExpr.IndexGet(_, _, _) -> "IndexGet"
        | FSharpNativeExpr.IndexSet(_, _, _) -> "IndexSet"
        | FSharpNativeExpr.TypeAnnotation(_, _) -> "TypeAnnotation"
        | FSharpNativeExpr.Upcast(_, _) -> "Upcast"
        | FSharpNativeExpr.Downcast(_, _) -> "Downcast"
        | FSharpNativeExpr.TypeTest(_, _) -> "TypeTest"
        | FSharpNativeExpr.AddressOf(_, isByref, _) -> if isByref then "AddressOfByref" else "AddressOf"
        | FSharpNativeExpr.Deref(_, _) -> "Deref"
        | FSharpNativeExpr.Set(_, _) -> "Set"
        | FSharpNativeExpr.PlatformBinding(name, _, _) -> sprintf "Platform(%s)" name
        | FSharpNativeExpr.Intrinsic(info, _, _) -> sprintf "Intrinsic(%s)" info.FullName
        | FSharpNativeExpr.TraitCall(name, _, _, res, _) ->
            let resolved = res |> Option.map (fun r -> sprintf "->%s" r.ResolvedMember) |> Option.defaultValue ""
            sprintf "TraitCall(%s%s)" name resolved
        | FSharpNativeExpr.InterpolatedString(parts, _) -> sprintf "Interpolated(%d parts)" (List.length parts)
        | FSharpNativeExpr.ModuleDef(name, _) -> sprintf "Module(%s)" name
        | FSharpNativeExpr.TypeDef(name, _, _) -> sprintf "Type(%s)" name
        | FSharpNativeExpr.MemberDef(name, _, _) -> sprintf "Member(%s)" name
        | FSharpNativeExpr.Error(msg, _) -> sprintf "Error(%s)" msg
