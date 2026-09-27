// Copyright (c) 2025 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Binding handling for Clef.
/// Handles: Let, LetRec, Lambda, pattern bindings, Set operations
module Clef.Compiler.NativeTypedTree.Expressions.Bindings

open Clef.Compiler.Syntax
open Clef.Compiler.SyntaxTrivia
open Clef.Compiler.Xml
open Clef.Compiler.NativeTypedTree.NativeTypes

open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.NodeBuilder
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.NativeTypedTree.NameResolution
open Clef.Compiler.NativeTypedTree.Expressions.Types
open Clef.Compiler.NativeTypedTree.Expressions.Literals
open Clef.Compiler.NativeTypedTree.Expressions.Applications

// Module alias for qualified access to shared utilities
module Types = Clef.Compiler.NativeTypedTree.Expressions.Types

//-------------------------------------------------------------------------
// Callback Types
//-------------------------------------------------------------------------

/// Callback for checking expressions (to avoid circular dependency)
type CheckExprFn = TypeEnv -> NodeBuilder -> SynExpr -> SemanticNode

/// Callback for checking patterns
type CheckPatternFn = TypeEnv -> SynPat -> NativeType -> SourceRange -> Pattern * (string * NativeType) list

//-------------------------------------------------------------------------
// Lambda Parameter Extraction
//-------------------------------------------------------------------------

/// Extract parameter names from lambda arguments
let extractLambdaParams
    (env: TypeEnv)
    (args: SynSimplePats)
    (range: SourceRange)
    : (string * NativeType) list =
    match args with
    | SynSimplePats.SimplePats([], _, _) ->
        // The parser represents the unit pattern by an empty simple-pattern
        // list. It still denotes one logical argument: preserve its formal
        // node just as for `let f () = ...` and Baker-created closures.
        [("_", Types.unitType)]
    | SynSimplePats.SimplePats(pats, _, _) ->
        // A parameter form with no named formal is refused at its range; the error node's
        // type stands in its place and the diagnostic stops the build.
        let unsupported (pat: SynSimplePat) (form: string) =
            let message = $"CCS source checking did not settle a named formal for this lambda parameter: {form} has no parameter elaboration."
            addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct pat.Range message env
            ("_", NativeType.TError message)
        pats |> List.map (fun pat ->
            match pat with
            | SynSimplePat.Id(ident, _, _, _, _, _) ->
                (ident.idText, freshTypeVar range)
            | SynSimplePat.Typed(SynSimplePat.Id(ident, _, _, _, _, _), synType, _) ->
                // Type annotation provided - convert to native type
                (ident.idText, resolveSynType env synType)
            | SynSimplePat.Typed(SynSimplePat.Typed _, _, _) ->
                unsupported pat "a doubly annotated parameter"
            | SynSimplePat.Typed(SynSimplePat.Attrib(innerInner, _, _), synType, _) ->
                // Typed attributed pattern - (name: Type) with attributes
                match innerInner with
                | SynSimplePat.Id(ident, _, _, _, _, _) ->
                    (ident.idText, resolveSynType env synType)
                | other ->
                    unsupported pat ("a typed attributed parameter of form " + other.GetType().Name)
            | SynSimplePat.Attrib(innerPat, _, _) ->
                // Attributed pattern - extract the inner identifier
                match innerPat with
                | SynSimplePat.Id(ident, _, _, _, _, _) ->
                    (ident.idText, freshTypeVar range)
                | SynSimplePat.Typed(SynSimplePat.Id(ident, _, _, _, _, _), synType, _) ->
                    (ident.idText, resolveSynType env synType)
                | other ->
                    unsupported pat ("an attributed parameter of form " + other.GetType().Name))

//-------------------------------------------------------------------------
// Binding Heads
//-------------------------------------------------------------------------

/// The head pattern of a let binding, read once where the binding is checked or
/// pre-created. A tuple head is elaborated by tuple destructuring into its
/// component bindings; a discard declares no name.
[<RequireQualifiedAccess>]
type BindingHead =
    | Named of string
    | Tuple
    | Discard

/// The names one checked binding declares into its scope.
[<RequireQualifiedAccess>]
type Declared =
    /// The binding node declares this name.
    | Name of string
    /// Tuple destructuring declares each named component at its own Binding node.
    | Components of (string * SemanticNode) list
    /// `let _ = e` and `let () = e` declare no name.
    | Nothing

/// What checking one binding settles.
type CheckedBinding =
    { Node: SemanticNode
      /// The body of a function explicitly marked `inline`, re-checked at each expansion site.
      InlineBody: InlineBody option
      IsMutable: bool
      /// The constant of a [<Literal>] binding.
      Literal: NativeLiteral option
      Declares: Declared }

/// Read the head pattern of a binding. A head with no binding elaboration is CCS8401 at
/// its range and is read as a discard, the diagnostic having stopped the build.
let getBindingHead (env: TypeEnv) (binding: SynBinding) : BindingHead =
    let (SynBinding(_, _, _, _, _, _, _, headPat, _, _, _, _, _)) = binding
    let rec read pat =
        match pat with
        | SynPat.Named(SynIdent(ident, _), _, _, _) -> Result.Ok (BindingHead.Named ident.idText)
        | SynPat.LongIdent(longDotId, _, _, _, _, _) -> Result.Ok (BindingHead.Named (List.last longDotId.LongIdent).idText)
        | SynPat.Paren(inner, _) | SynPat.Typed(inner, _, _) -> read inner
        | SynPat.Tuple _ -> Result.Ok BindingHead.Tuple
        | SynPat.Wild _ | SynPat.Const(SynConst.Unit, _) -> Result.Ok BindingHead.Discard
        | other -> Result.Error other
    match read headPat with
    | Result.Ok head -> head
    | Result.Error pattern ->
        addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct pattern.Range
            ("CCS source checking did not settle a binding name for this let pattern: a head pattern of form "
             + pattern.GetType().Name + " has no binding elaboration.") env
        BindingHead.Discard

/// A recursive group pre-creates one Binding node per member before any body is checked,
/// so a member declares at most one name. A tuple head in a recursive group is CCS8401 and
/// is read as a discard, the diagnostic having stopped the build.
let getRecursiveBindingHead (env: TypeEnv) (binding: SynBinding) : BindingHead =
    match getBindingHead env binding with
    | BindingHead.Tuple ->
        let (SynBinding(_, _, _, _, _, _, _, headPat, _, _, _, _, _)) = binding
        addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct headPat.Range
            "CCS source checking did not settle a recursive binding: a member of a recursive group declares one name, never a tuple of names." env
        BindingHead.Discard
    | head -> head

/// The name carried by a head's Binding node. A discard's node is named "_" and declares nothing.
let bindingNodeName (head: BindingHead) : string =
    match head with
    | BindingHead.Named name -> name
    | BindingHead.Tuple | BindingHead.Discard -> "_"

/// Check if a binding is mutable
let isBindingMutable (binding: SynBinding) : bool =
    let (SynBinding(_, _, _, isMutable, _, _, _, _, _, _, _, _, _)) = binding
    isMutable

/// Get the head pattern from a binding, unwrapping Paren
let getHeadPattern (binding: SynBinding) : SynPat =
    let (SynBinding(_, _, _, _, _, _, _, headPat, _, _, _, _, _)) = binding
    let rec unwrap pat =
        match pat with
        | SynPat.Paren(inner, _) -> unwrap inner
        | other -> other
    unwrap headPat

//-------------------------------------------------------------------------
// Function Parameter Extraction
//-------------------------------------------------------------------------

/// Keep a tuple pattern at one declared argument boundary. Its projections are
/// ordinary local bindings, so an unused component is not demanded by this
/// elaboration. The same body is retained for later inline instantiation.
let private lowerTupleParameters (headPat: SynPat) (body: SynExpr) =
    let rec isTuple = function
        | SynPat.Tuple _ -> true
        | SynPat.Paren(inner, _) | SynPat.Typed(inner, _, _) -> isTuple inner
        | _ -> false
    match headPat with
    | SynPat.LongIdent(name, extra, parameters, SynArgPats.Pats arguments, accessibility, range) ->
        let arguments, projections =
            arguments |> List.map (fun pattern ->
                if isTuple pattern then
                    let name = sprintf "__tuple_argument_%d" (NodeId.value (NodeId.fresh()))
                    let ident = Ident(name, pattern.Range)
                    let formal = SynPat.Named(SynIdent(ident, None), false, None, pattern.Range)
                    formal, Some(pattern, ident)
                else pattern, None)
            |> List.unzip
        let body =
            (projections |> List.choose id, body)
            ||> List.foldBack (fun (pattern, ident) body ->
                let binding =
                    SynBinding(None, SynBindingKind.Normal, false, false, [], PreXmlDoc.Empty,
                        SynValData(None, SynValInfo([], SynArgInfo([], false, None)), None),
                        pattern, None, SynExpr.Ident ident, pattern.Range,
                        DebugPointAtBinding.NoneAtInvisible, SynBindingTrivia.Zero)
                SynExpr.LetOrUse {
                    IsRecursive = false
                    Bindings = [binding]
                    Body = body
                    Range = body.Range
                    Trivia = SynLetOrUseTrivia.Zero
                    IsFromSource = false
                })
        SynPat.LongIdent(name, extra, parameters, SynArgPats.Pats arguments, accessibility, range), body
    | _ -> headPat, body

/// Extract function parameters from a LongIdent pattern
/// Each parameter retains its own identifier range for graph navigation and diagnostics.
/// For `let x = body`, returns None
let tryGetFunctionParams
    (headPat: SynPat)
    (env: TypeEnv)
    (range: SourceRange)
    : (string * NativeType * SourceRange) list option =
    let named (ident: Ident) ty = ident.idText, ty, rangeToSourceRange ident.idRange
    // A parameter pattern with no named formal (a refutable pattern, a constant, a
    // constructor) is refused at its range; it never becomes an unnamed `_` formal whose
    // test is dropped. A wildcard is the one unnamed formal.
    let refused (pattern: SynPat) =
        let message =
            "CCS source checking did not settle a named formal for this function parameter: a parameter pattern of form "
            + pattern.GetType().Name + " has no parameter elaboration; bind a name and match on it in the body."
        addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct pattern.Range message env
        ("_", NativeType.TError message, rangeToSourceRange pattern.Range)
    match headPat with
    | SynPat.LongIdent(_, _, _, argPats, _, _) ->
        match argPats with
        | SynArgPats.Pats pats when not (List.isEmpty pats) ->
            // Has parameters - this is a function definition. Tuple parameters were given
            // named formals by lowerTupleParameters before this reading.
            let extractedParameters = pats |> List.collect (fun pat ->
                match pat with
                | SynPat.Paren(innerPat, _) ->
                    // Parenthesized pattern like () or (x: Type)
                    match innerPat with
                    | SynPat.Const(SynConst.Unit, _) ->
                        // Unit literal - bind to dummy name
                        [("_", Types.unitType, rangeToSourceRange innerPat.Range)]
                    | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                        [named ident (freshTypeVar range)]
                    | SynPat.Wild _ ->
                        [("_", freshTypeVar range, rangeToSourceRange innerPat.Range)]
                    | SynPat.Typed(typedInner, synType, _) ->
                        // Typed pattern like (name: NativeStr)
                        let annotatedType = resolveSynType env synType
                        match typedInner with
                        | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                            [named ident annotatedType]
                        | SynPat.Wild _ -> [("_", annotatedType, rangeToSourceRange typedInner.Range)]
                        | _ -> [refused typedInner]
                    | _ -> [refused innerPat]
                | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                    [named ident (freshTypeVar range)]
                | SynPat.Const(SynConst.Unit, _) ->
                    // Unit literal - bind to dummy name
                    [("_", Types.unitType, rangeToSourceRange pat.Range)]
                | SynPat.Wild _ -> [("_", freshTypeVar range, rangeToSourceRange pat.Range)]
                | _ -> [refused pat]
            )
            Some extractedParameters
        | _ -> None
    | _ -> None

//-------------------------------------------------------------------------
// Binding Checking
//-------------------------------------------------------------------------

/// Check construction before inline expansion can hide an allocating call, then
/// check the elaborated value's storage. generalizeInEnv separately excludes
/// variables belonging to existing storage and captures.
let private isGeneralizableValue (env: TypeEnv) (builder: NodeBuilder) source (node: SemanticNode) =
    let rec sourceValue = function
        | SynExpr.Const _ | SynExpr.Ident _ | SynExpr.LongIdent _ | SynExpr.Lambda _ -> true
        | SynExpr.Paren(inner, _, _, _) | SynExpr.Typed(inner, _, _)
        | SynExpr.Lazy(inner, _) | SynExpr.Eager(inner, _) -> sourceValue inner
        | SynExpr.Tuple(_, items, _, _) | SynExpr.ArrayOrList(false, items, _) -> List.forall sourceValue items
        | SynExpr.ArrayOrListComputed(false, body, _) ->
            Clef.Compiler.NativeTypedTree.Expressions.Collections.tryLiteralCollectionElements body
            |> Option.exists (List.forall sourceValue)
        | SynExpr.Record(_, copied, fields, _) ->
            (copied |> Option.forall (fst >> sourceValue))
            && (fields |> List.forall (fun (SynExprRecordField(_, _, value, _, _)) -> value |> Option.exists sourceValue))
        | SynExpr.AnonRecd(_, copied, fields, _, _) ->
            (copied |> Option.forall (fst >> sourceValue))
            && (fields |> List.forall (fun (_, _, value) -> sourceValue value))
        | SynExpr.App(_, _, constructor, argument, _) -> unionConstructor constructor && sourceValue argument
        | _ -> false
    and unionConstructor = function
        | SynExpr.Ident ident ->
            tryLookupBinding ident.idText env |> Option.exists (fun binding -> binding.UnionCaseInfo.IsSome)
        | SynExpr.LongIdent(_, SynLongIdent(idents, _, _), _, _) ->
            let name = idents |> List.map (fun ident -> ident.idText) |> String.concat "."
            tryLookupBinding name env |> Option.exists (fun binding -> binding.UnionCaseInfo.IsSome)
        | SynExpr.Paren(inner, _, _, _) | SynExpr.TypeApp(inner, _, _, _, _, _, _) -> unionConstructor inner
        | SynExpr.App(_, _, constructor, argument, _) -> unionConstructor constructor && sourceValue argument
        | _ -> false
    // An application below an actual declared boundary retains arguments in
    // a residual callable; it does not execute the callable body. In
    // particular, result arrows of a fully applied factory are not formals.
    let rec remaining seen id =
        if Set.contains id seen then None
        else
            let seen = Set.add id seen
            match builder.Nodes.TryGetValue id with
            | true, value ->
                match value.Kind with
                | SemanticKind.Lambda(parameters, _, _, _, _) -> Some parameters.Length
                | SemanticKind.Binding(_, false, _, _) ->
                    match value.Children with [body] -> remaining seen body | _ -> None
                | SemanticKind.VarRef(_, Some definition) -> remaining seen definition
                | SemanticKind.TypeAnnotation(inner, _) -> remaining seen inner
                | SemanticKind.Application(callee, arguments) ->
                    remaining seen callee |> Option.bind (fun count ->
                        if arguments.Length < count then Some(count - arguments.Length) else None)
                | _ -> None
            | _ -> None
    let rec safe id =
        let node = builder.Nodes.[id]
        match node.Kind with
        | SemanticKind.Literal _ | SemanticKind.VarRef _ | SemanticKind.Lambda _ -> true
        | SemanticKind.Intrinsic _ when node.Children.IsEmpty -> true
        | SemanticKind.TypeAnnotation(inner, _) | SemanticKind.EagerExpr inner -> safe inner
        | SemanticKind.TupleExpr items | SemanticKind.ListExpr items -> List.forall safe items
        | SemanticKind.UnionCase(_, _, payload) -> payload |> Option.forall safe
        | SemanticKind.RecordExpr(fields, copied) ->
            let immutable =
                match applySubst node.Type with
                | NativeType.TApp(tycon, _) ->
                    tryLookupRecordDef tycon env
                    |> Option.exists (fun record -> record.TypeCon.Module = tycon.Module && record.MutableFields.IsEmpty)
                | NativeType.TAnon _ -> true
                | _ -> false
            immutable && (fields |> List.forall (snd >> safe)) && (copied |> Option.forall safe)
        | SemanticKind.LazyExpr(thunk, _) ->
            match builder.Nodes.[thunk].Kind with
            | SemanticKind.Lambda(_, body, _, _, _) -> safe body
            | _ -> false
        | SemanticKind.Application(callee, arguments) ->
            remaining Set.empty id |> Option.exists (fun count -> count > 0)
            && safe callee && List.forall safe arguments
        | _ -> false
    // Read the original source callee as well: inline expansion may produce
    // a Lambda (or partial application) from a fully invoked factory body.
    // That resulting shape does not establish a partial source invocation.
    let rec sourceResidual supplied = function
        | SynExpr.App(_, _, callee, argument, _) ->
            sourceValue argument && sourceResidual (supplied + 1) callee
        | SynExpr.Paren(inner, _, _, _) | SynExpr.TypeApp(inner, _, _, _, _, _, _) -> sourceResidual supplied inner
        | SynExpr.Ident ident -> sourceCallee supplied ident.idText
        | SynExpr.LongIdent(_, SynLongIdent(idents, _, _), _, _) ->
            sourceCallee supplied (idents |> List.map _.idText |> String.concat ".")
        | _ -> false
    and sourceCallee supplied name =
        tryLookupBinding name env
        |> Option.filter (fun binding -> not binding.IsMutable)
        |> Option.bind _.NodeId
        |> Option.bind (remaining Set.empty)
        |> Option.exists (fun count -> supplied > 0 && supplied < count)
    (sourceValue source || sourceResidual 0 source)
    && safe node.Id

/// Preserve the source identifier and RHS boundary before graph rewriting.
/// Substituted inline/literal bindings need separate use tracking and remain
/// exempt. The local marker distinguishes lexical values from module APIs.
let recordSourceBinding (isLocal: bool) (builder: NodeBuilder) (binding: SynBinding) (node: SemanticNode) (substituted: bool) =
    let (SynBinding(_, _, _, _, _, _, _, pattern, _, _, _, _, _)) = binding
    let rec identifier = function
        | SynPat.Named(SynIdent(ident, _), _, _, _) -> Some ident
        | SynPat.LongIdent(longId, _, _, _, _, _) -> longId.LongIdent |> List.tryLast
        | SynPat.Paren(inner, _) | SynPat.Typed(inner, _, _) -> identifier inner
        | _ -> None
    match node.Kind, identifier pattern with
    | SemanticKind.Binding _, Some ident when not substituted ->
        builder.SetMetadata(node.Id, "SourceBinding.NameRange", MetadataValue.SourceRange(rangeToSourceRange ident.idRange)) |> ignore
        builder.SetMetadata(node.Id, "SourceBinding.FullRange", MetadataValue.SourceRange(rangeToSourceRange binding.RangeOfBindingWithRhs)) |> ignore
        builder.SetMetadata(node.Id, "SourceBinding.Local", MetadataValue.Bool isLocal) |> ignore
    | _ -> ()

/// Check a single binding and settle what it declares into scope.
/// InlineBody is captured only for functions explicitly marked `inline` - this enables
/// escape analysis where allocations are lifted to the caller's frame.
/// The head is read once per binding by the caller: getBindingHead for an ordinary binding,
/// getRecursiveBindingHead at the pre-creation of a recursive group.
/// PRD-13: preCreatedBinding allows recursive bindings to provide a pre-created Binding node
/// so that VarRefs can resolve to it before the body is checked.
let private checkBindingInScope
    (isModuleLevel: bool)
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (binding: SynBinding)
    (head: BindingHead)
    (preCreatedBinding: SemanticNode option)
    : CheckedBinding =

    let (SynBinding(_, _, isInline, isMutable, attrs, _, _, headPat, returnInfo, expr, bindingRange, _, _)) = binding
    let declarations =
        match headPat with
        | SynPat.LongIdent(typarDecls = Some(SynValTyparDecls(declarations, _))) -> declarations
        | _ -> None
    let env, explicitParameters = withDeclaredTypeParameters declarations env
    let range = rangeToSourceRange bindingRange
    let name = bindingNodeName head
    let declares = match head with BindingHead.Named name -> Declared.Name name | BindingHead.Tuple | BindingHead.Discard -> Declared.Nothing
    // One measure variable per name for the whole binding (spec §Generalization of Measure
    // Variables): the names written in the parameter and return annotations are minted here, so
    // `(y: float<'u>) (z: float<'u>)` share `'u` and a use at two dimensions is CCS8040.
    let env =
        let rec annotations (p: SynPat) : SynType list =
            match p with
            | SynPat.Typed(inner, ty, _) -> ty :: annotations inner
            | SynPat.Paren(inner, _) -> annotations inner
            | SynPat.Tuple(_, ps, _, _) -> ps |> List.collect annotations
            | SynPat.LongIdent(_, _, _, SynArgPats.Pats ps, _, _) -> ps |> List.collect annotations
            | SynPat.Attrib(inner, _, _) -> annotations inner
            | _ -> []
        let returnAnnotation =
            match returnInfo with
            | Some (SynBindingReturnInfo(typeName = synType)) -> [ synType ]
            | None -> []
        let names = (annotations headPat @ returnAnnotation) |> List.collect (measureVariableNames env)
        withMeasureScope env names
    let headPat, expr = lowerTupleParameters headPat expr
    let declRoot =
        if hasEntryPointAttribute attrs then Some DeclRoot.EntryPoint
        elif hasHardwareModuleAttribute attrs then Some DeclRoot.HardwareModule
        elif hasKernelModuleAttribute attrs then Some DeclRoot.KernelModule
        else None
    let isLiteral = hasLiteralAttribute attrs
    let fidelityExtern = extractFidelityExternAttribute attrs

    // Extract literal value if this is a [<Literal>] binding with a constant expression
    let literalValue =
        if isLiteral then
            // `let X: T = c` carries its annotation on the right side; the constant is read
            // through it (the annotation is checked with the body below).
            let rec constantOf (e: SynExpr) =
                match e with
                | SynExpr.Typed(inner, _, _) | SynExpr.Paren(inner, _, _, _) -> constantOf inner
                | other -> other
            match constantOf expr with
            | SynExpr.Const(constant, _) ->
                match Literals.checkConst env constant with
                | Result.Ok (_, literal) -> Some literal
                | Result.Error _ -> None  // the failure is reported where the body is checked below
            | _ ->
                // A [<Literal>] whose right side is not a constant is never demoted to an
                // ordinary value binding.
                addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct expr.Range
                    $"CCS source checking did not settle a compile-time constant for [<Literal>] binding '{name}': its right side is not a constant." env
                None
        else
            None

    //-------------------------------------------------------------------------
    // PRD-13a: Tuple Destructuring
    // let (a, b) = expr  desugars to:
    //   let __tuple_N = expr
    //   let a = TupleGet(__tuple_N, 0)
    //   let b = TupleGet(__tuple_N, 1)
    //-------------------------------------------------------------------------
    let checkTupleDestructure () =
        // Retain tuple nesting, annotations, and each declaration's range.
        // Flattening names would change one tuple argument into unrelated
        // parameters and erase the relations inferred for measured fields.
        let rec describe (pattern: SynPat) =
            let patternRange = rangeToSourceRange pattern.Range
            match pattern with
            | SynPat.Paren(inner, _) -> describe inner
            | SynPat.Typed(inner, annotation, _) ->
                let ty, leaves = describe inner
                let annotated = resolveSynType env annotation
                addConstraint (Constraint.Equals(ty, annotated, patternRange)) env
                annotated, leaves
            | SynPat.Tuple(isStruct, elements, _, _) ->
                let elements = elements |> List.map describe
                let types = elements |> List.map fst
                let leaves =
                    elements |> List.mapi (fun index (ty, leaves) ->
                        leaves |> List.map (fun (name, wildcard, leafType, leafRange, path) ->
                            name, wildcard, leafType, leafRange, (index, ty) :: path))
                    |> List.concat
                NativeType.TTuple(types, isStruct), leaves
            | SynPat.Named(SynIdent(ident, _), _, _, _) ->
                let ty = freshTypeVar patternRange
                ty, [ident.idText, false, ty, rangeToSourceRange ident.idRange, []]
            | SynPat.Wild _ ->
                let ty = freshTypeVar patternRange
                ty, ["_", true, ty, patternRange, []]
            | SynPat.Const(SynConst.Unit, _) ->
                Types.unitType, ["_", true, Types.unitType, patternRange, []]
            | other ->
                let message =
                    "CCS source checking did not settle a component binding for this tuple destructuring: a component pattern of form "
                    + other.GetType().Name + " has no binding elaboration."
                addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct other.Range message env
                let ty = NativeType.TError message
                ty, ["_", true, ty, patternRange, []]
        let expectedTupleType, elementInfo = describe (getHeadPattern binding)

        // Check the RHS expression - this gives us the tuple value
        let tupleExprNode = checkExpr env builder expr

        // Constrain the complete tuple shape, including nested tuple kinds.
        addConstraint (Constraint.Equals(tupleExprNode.Type, expectedTupleType, range)) env

        // The tuple value is held by one binding named from its own expression node.
        let hiddenName = sprintf "__tuple_%d" (NodeId.value tupleExprNode.Id)
        let hiddenBinding = builder.Create(
            SemanticKind.Binding(hiddenName, isMutable, false, None),
            tupleExprNode.Type,
            range,
            children = [tupleExprNode.Id])
        builder.SetParent(tupleExprNode.Id, hiddenBinding.Id)

        // Each named component is a Binding over its TupleGet path. A wildcard component
        // declares nothing, so it has no projection and no binding.
        let components =
            elementInfo |> List.choose (fun (elemName, isWildcard, elemType, elemRange, path) ->
                if isWildcard then None else
                let tupleRef = builder.Create(
                    SemanticKind.VarRef(hiddenName, Some hiddenBinding.Id),
                    tupleExprNode.Type,
                    elemRange,
                    arena = env.CurrentArena)
                let tupleGetNode =
                    path |> List.fold (fun (value: SemanticNode) (index, ty) ->
                        let projection = builder.Create(
                            SemanticKind.TupleGet(value.Id, index), ty, elemRange,
                            children = [value.Id])
                        builder.SetParent(value.Id, projection.Id)
                        projection) tupleRef
                let elemBinding = builder.Create(
                    SemanticKind.Binding(elemName, isMutable, false, None),
                    elemType,
                    elemRange,
                    children = [tupleGetNode.Id])
                builder.SetParent(tupleGetNode.Id, elemBinding.Id)
                Some (elemName, elemBinding))

        let allBindingIds = hiddenBinding.Id :: (components |> List.map (fun (_, b) -> b.Id))

        // The type of the Sequential is unit (the bindings introduce names but produce no value)
        let seqNode = builder.Create(
            SemanticKind.Sequential allBindingIds,
            Types.unitType,
            range,
            children = allBindingIds)

        // Set parents
        for bindingId in allBindingIds do
            builder.SetParent(bindingId, seqNode.Id)

        { Node = seqNode; InlineBody = None; IsMutable = isMutable; Literal = None
          Declares = Declared.Components components }

    match head with
    | BindingHead.Tuple -> checkTupleDestructure ()
    | BindingHead.Named _ | BindingHead.Discard ->

    // Check if this is a function definition (has parameters)
    match tryGetFunctionParams headPat env range with
    | Some paramBindings ->
        // This is a function definition like `let f x = body` or `let f() = body`
        // Create a Lambda node wrapping the body

        // Create PatternBinding nodes for parameters and collect (name, type, nodeId)
        // These nodes are needed for SSA assignment to map parameters to %argN
        let paramNodesAndEnv =
            paramBindings
            |> List.fold (fun (acc, env) (paramName, paramTy, paramRange) ->
                let paramNode = builder.Create(
                    SemanticKind.PatternBinding(paramName),
                    paramTy,
                    paramRange,
                    arena = env.CurrentArena)
                let newEnv = addBinding paramName paramTy false (Some paramNode.Id) false env  // Parameters are always local
                ((paramName, paramTy, paramNode.Id) :: acc, newEnv)
            ) ([], env)

        let lambdaParams = List.rev (fst paramNodesAndEnv)
        let bodyEnvWithParams = snd paramNodesAndEnv
        
        // PRD-13: Set this function as the enclosing function for nested bindings
        // This enables qualified names like "factorialTail_loop" for nested functions
        let bodyEnv = { bodyEnvWithParams with EnclosingFunction = Some name; EnclosingSeqExpr = None }

        // Check body with extended environment
        // For [<FidelityExtern>] bindings, the body is a placeholder (Unchecked.defaultof<T>)
        // that would be rejected by BCL filtering. Skip body checking and create a
        // placeholder node using the return type annotation. Alex resolves these via ExternCall.
        let bodyNode =
            match fidelityExtern with
            | Some _ ->
                let retType =
                    match returnInfo with
                    | Some (SynBindingReturnInfo(typeName = synType)) -> resolveSynType env synType
                    | None ->
                        // The declaration is the one source of the foreign return type; it is
                        // never inferred from the uses of the binding.
                        let message =
                            "CCS source checking did not settle the return type of [<FidelityExtern>] binding '" + name
                            + "': the declaration carries no return type annotation."
                        addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct bindingRange message env
                        NativeType.TError message
                builder.Create(
                    SemanticKind.Literal(NativeLiteral.Unit),
                    retType,
                    range)
            | None ->
                checkExpr bodyEnv builder expr

        // Entry point constraint: string[] -> int
        // Per F# spec, [<EntryPoint>] functions must have signature: string[] -> int
        if declRoot = Some DeclRoot.EntryPoint then
            // Constrain parameter to string[] (argv)
            match lambdaParams with
            | [(_, paramTy, _)] ->
                let stringArrayType = NativeType.TApp(Types.arrayTyCon, [Types.stringType])
                addConstraint (Constraint.Equals(paramTy, stringArrayType, range)) env
            | parameters ->
                addNativeError DiagnosticCodes.CCS8004_ArityMismatch bindingRange
                    ("CCS source checking did not settle the entry point signature of '" + name
                     + "': [<EntryPoint>] takes one string[] parameter, got " + string parameters.Length + ".") env
            // Constrain return type to int
            addConstraint (Constraint.Equals(bodyNode.Type, Types.intType, range)) env

        // Build function type
        let paramTypes = lambdaParams |> List.map (fun (_, ty, _) -> ty)
        // For unit-parameterized functions like f(), the paramTypes might be empty
        // but it's still a function: unit -> returnType
        let funcType =
            if List.isEmpty paramTypes then
                mkFunctionType [Types.unitType] bodyNode.Type
            else
                mkFunctionType paramTypes bodyNode.Type

        let bindingType =
            if preCreatedBinding.IsSome || isMutable then applySubst funcType
            else
                let scheme = if isInline then generalizeInlineInEnv env funcType else generalizeInEnv env funcType
                if explicitParameters.IsEmpty then scheme
                else
                    let parameters, body = match scheme with NativeType.TForall(parameters, body) -> parameters, body | _ -> [], scheme
                    let additional = parameters |> List.filter (fun parameter -> explicitParameters |> List.forall (fun explicit -> explicit.Id <> parameter.Id))
                    NativeType.TForall(explicitParameters @ additional, body)

        // Create Lambda node with parameter NodeIds for SSA assignment
        // Children includes parameter PatternBindings + body for proper traversal
        // PRD-13: Pass enclosingFunction for qualified name generation in Alex
        let paramNodeIds = lambdaParams |> List.map (fun (_, _, nodeId) -> nodeId)
        let lambdaChildren = paramNodeIds @ [bodyNode.Id]

        // PRD-13: Compute captures for nested functions
        // Only declarations are module-level. A named function inside a
        // sequence/lazy/lexical expression can capture without an enclosing
        // named function; the source binding boundary supplies that scope.
        // Nested functions may capture variables from enclosing scope.
        // Exclude: the function's own parameters AND the function's own name (for recursive self-reference)
        let paramNames = lambdaParams |> List.map (fun (pname, _, _) -> pname) |> Set.ofList
        let excludeNames = Set.add name paramNames
        let captures =
            if not isModuleLevel then
                computeCaptures builder env bodyNode.Id excludeNames
            else
                []

        let lambdaNode = builder.Create(
            SemanticKind.Lambda(lambdaParams, bodyNode.Id, captures, env.EnclosingFunction, LambdaContext.RegularClosure),
            funcType,
            range,
            children = lambdaChildren)

        // PRD-13: Set parent on all children (params and body) for scope chain
        for childId in lambdaChildren do
            builder.SetParent(childId, lambdaNode.Id)
        
        // Architectural fix (January 2026): Mark Lambda body as SeparateFunction
        // The Lambda witness handles body emission; Alex's walk should skip it.
        // Pass capture count so SSA assignment starts body SSAs after capture extraction
        builder.SetEmissionStrategy(bodyNode.Id, EmissionStrategy.SeparateFunction (List.length captures))

        // PRD-13: Use pre-created Binding if provided (for recursive bindings)
        // Otherwise create a new Binding node wrapping the Lambda
        let bindingNode =
            match preCreatedBinding with
            | Some preCreated ->
                // Link pre-created Binding to the Lambda we just created
                addConstraint (Constraint.Equals(preCreated.Type, funcType, range)) env
                builder.SetChildren(preCreated.Id, [lambdaNode.Id])
                let declaredType =
                    if explicitParameters.IsEmpty then funcType
                    else NativeType.TForall(explicitParameters, funcType)
                builder.SetType(preCreated.Id, declaredType)
                builder.Nodes.[preCreated.Id]
            | None ->
                builder.Create(
                    SemanticKind.Binding(name, isMutable, false, declRoot),
                    bindingType,
                    range,
                    children = [lambdaNode.Id])

        // Establish bidirectional parent-child link
        // Lambda's Parent field must point back to Binding for SSA name assignment
        builder.SetParent(lambdaNode.Id, bindingNode.Id)

        // Propagate [<FidelityExtern>] metadata for Farscape-generated native bindings
        match fidelityExtern with
        | Some (library, symbol) ->
            builder.SetMetadata(bindingNode.Id, "FidelityExtern.Library", MetadataValue.String library) |> ignore
            builder.SetMetadata(bindingNode.Id, "FidelityExtern.Symbol", MetadataValue.String symbol) |> ignore
        | None -> ()

        // An `inline` function's own body is never emitted: it is re-checked at every expansion
        // site with the site's types, so the variables its definition leaves open are quantified
        // by expansion. The marker lets the residual check (NativeService) skip its subtree.
        if isInline then
            builder.SetMetadata(bindingNode.Id, "Inline", MetadataValue.Bool true) |> ignore

        // Capture inline body only for functions explicitly marked `inline`
        // This enables escape analysis - inline functions have their allocations
        // moved to the caller's frame, ensuring pointers remain valid.
        let inlineBodyOpt =
            if isInline then
                Some {
                    Parameters = lambdaParams |> List.map (fun (name, _, _) -> name)
                    Body = expr
                    Range = rangeToSourceRange bindingRange
                    DefinitionScope = {
                        Resolution = env.Resolution; BindingTypes = env.BindingTypes
                        TypeParameters = env.TypeParameters.Value; TypeDefs = env.TypeDefs
                        TypeAbbrevs = env.TypeAbbrevs; Measures = env.Measures; MeasureScope = env.MeasureScope
                        RecordDefs = env.RecordDefs; FieldLabels = env.FieldLabels
                    }
                }
            else
                None

        { Node = bindingNode; InlineBody = inlineBodyOpt; IsMutable = isMutable; Literal = literalValue; Declares = declares }

    | None ->
        // Regular value binding (not a function - no inline body)
        let exprNode = checkExpr env builder expr
        let bindingType =
            if not isMutable && preCreatedBinding.IsNone && isGeneralizableValue env builder expr exprNode then generalizeInEnv env exprNode.Type
            else applySubst exprNode.Type

        // A function-valued reference is an ordinary value: evaluate it at this binding,
        // including a snapshot of a mutable function slot. Turning it into a forwarding
        // lambda would delay that read until invocation and invent currying boundaries.
        // Baker elaborates references to actual named function declarations into pairs;
        // existing closure values and closure-factory results remain values here.

        // PRD-13: Use pre-created Binding if provided (for recursive bindings)
        let node =
            match preCreatedBinding with
            | Some preCreated ->
                addConstraint (Constraint.Equals(preCreated.Type, exprNode.Type, range)) env
                builder.SetChildren(preCreated.Id, [exprNode.Id])
                preCreated
            | None ->
                builder.Create(
                    SemanticKind.Binding(name, isMutable, false, declRoot),
                    bindingType,
                    range,
                    children = [exprNode.Id])
        // Establish bidirectional parent-child link
        builder.SetParent(exprNode.Id, node.Id)

        // Propagate [<FidelityExtern>] metadata for Farscape-generated native bindings
        match fidelityExtern with
        | Some (library, symbol) ->
            builder.SetMetadata(node.Id, "FidelityExtern.Library", MetadataValue.String library) |> ignore
            builder.SetMetadata(node.Id, "FidelityExtern.Symbol", MetadataValue.String symbol) |> ignore
        | None -> ()

        // Module-level value bindings need MainPrologue strategy for SSA scoping.
        // These are emitted at the start of main - SSAs flow into main's body.
        // A quotation is not a value (D9): it is compile-time data the compiler reads, so a
        // binding that holds one is a declaration, never a module-init slot.
        let rec holdsQuotation (id: NodeId) =
            match Map.tryFind id builder.Nodes with
            | Some { Kind = SemanticKind.Quote _ } -> true
            | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> holdsQuotation inner
            | _ -> false
        if isModuleLevel && declRoot.IsNone && not (holdsQuotation exprNode.Id) then
            builder.SetEmissionStrategy(node.Id, EmissionStrategy.MainPrologue)

        { Node = node; InlineBody = None; IsMutable = isMutable; Literal = literalValue; Declares = declares }

/// Module declaration entry. Lexical expression bindings use the explicit
/// local entry below, independently of whether a named function encloses them.
let checkBinding checkExpr env builder binding head preCreatedBinding =
    checkBindingInScope true checkExpr env builder binding head preCreatedBinding

//-------------------------------------------------------------------------
// Let/LetRec Handling
//-------------------------------------------------------------------------

/// Recursive references stay monomorphic while checking the entire group.
/// Only then quantify variables that are not captured from the outer scope.
let generalizeRecursiveBinding (env: TypeEnv) (builder: NodeBuilder) (node: SemanticNode) =
    match node.Kind, node.Children with
    | SemanticKind.Binding(isMutable = false), [child] ->
        match builder.Nodes.[child].Kind with
        | SemanticKind.Lambda _ ->
            let declared, body =
                match node.Type with NativeType.TForall(parameters, body) -> parameters, body | ty -> [], ty
            let inferred = generalizeInEnv env body
            let parameters, body =
                match inferred with NativeType.TForall(parameters, body) -> parameters, body | ty -> [], ty
            let additional = parameters |> List.filter (fun tp -> declared |> List.forall (fun explicit -> explicit.Id <> tp.Id))
            let parameters = declared @ additional
            let scheme = if parameters.IsEmpty then body else NativeType.TForall(parameters, body)
            builder.SetType(node.Id, scheme)
            builder.Nodes.[node.Id]
        | _ -> node
    | _ -> node

/// Check a let-or-use binding
/// PRD-13: For recursive bindings (let rec), pre-create Binding nodes to get NodeIds
/// so that self-referential VarRefs can resolve correctly.
let checkLetOrUse
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (letOrUse: SynLetOrUse)
    (range: SourceRange)
    : SemanticNode =

    if letOrUse.IsBang || letOrUse.IsUse then
        let message =
            if letOrUse.IsBang then
                let form = if letOrUse.IsUse then "use!" else "let!/and!"
                $"The '{form}' form has no admitted native bind or suspension semantics"
            else "Resource-use bindings require an admitted native resource lifecycle"
        addNativeError DiagnosticCodes.CCS8401_UnsupportedConstruct letOrUse.Range message env
        builder.Create(SemanticKind.Error message, NativeType.TError message, range)
    else

    let bindings = letOrUse.Bindings
    let bodyExpr = letOrUse.Body

    // Enter what each checked binding declares into the body's scope. A tuple destructuring
    // declares its named components at their own Binding nodes; a discard declares nothing.
    let extendEnvWithResults baseEnv bindingList (results: CheckedBinding list) =
        List.zip bindingList results
        |> List.fold (fun env (binding, (checkedBinding: CheckedBinding)) ->
            // Generated bindings and source parameters are outside this
            // named-let diagnostic. Resource-use forms are rejected above.
            if letOrUse.IsFromSource && not letOrUse.IsUse then
                recordSourceBinding true builder binding checkedBinding.Node
                    (checkedBinding.InlineBody.IsSome || checkedBinding.Literal.IsSome)
            let node = checkedBinding.Node
            match checkedBinding.Declares with
            | Declared.Nothing -> env
            | Declared.Components components ->
                components |> List.fold (fun env (name, (declared: SemanticNode)) ->
                    addBinding name declared.Type checkedBinding.IsMutable (Some declared.Id) false env) env
            | Declared.Name name ->
                match checkedBinding.InlineBody, checkedBinding.Literal with
                | Some inlineBody, _ ->
                    addInlineBindingInScope false name node.Type (Some node.Id) inlineBody env
                | None, Some litVal ->
                    addLiteralBindingInScope false name node.Type (Some node.Id) litVal env
                | None, None ->
                    addBinding name node.Type checkedBinding.IsMutable (Some node.Id) false env
        ) baseEnv

    // Helper: build final Sequential node
    // PRD-13: Sets bidirectional parent-child links so nested bindings know their scope
    let buildSequential bindingNodes bodyNode =
        let allIds = (bindingNodes |> List.map (fun (n: SemanticNode) -> n.Id)) @ [bodyNode.Id]
        let seqNode = builder.Create(
            SemanticKind.Sequential allIds,
            bodyNode.Type,
            range,
            children = allIds)
        // Set parent on all children (bidirectional link)
        for childId in allIds do
            builder.SetParent(childId, seqNode.Id)
        seqNode

    match letOrUse.IsRecursive with
    | true ->
        // PRD-13: RECURSIVE BINDINGS
        // Pre-create Binding nodes to get NodeIds before checking bodies
        let preCreatedBindings =
            bindings |> List.map (fun binding ->
                let head = getRecursiveBindingHead env binding
                let ty = freshTypeVar range
                let (SynBinding(_, _, _, isMutable, attrs, _, _, _, _, _, _, _, _)) = binding
                let declRoot =
                    if hasEntryPointAttribute attrs then Some DeclRoot.EntryPoint
                    elif hasHardwareModuleAttribute attrs then Some DeclRoot.HardwareModule
                    elif hasKernelModuleAttribute attrs then Some DeclRoot.KernelModule
                    else None
                let node = builder.Create(
                    SemanticKind.Binding(bindingNodeName head, isMutable, true, declRoot),
                    ty,
                    range,
                    children = [])
                (binding, head, ty, node))

        // Add every named member to the environment WITH its NodeId
        let envWithBindings =
            preCreatedBindings
            |> List.fold (fun env (_, head, ty, (node: SemanticNode)) ->
                match head with
                | BindingHead.Named name -> addBinding name ty false (Some node.Id) false env
                | BindingHead.Tuple | BindingHead.Discard -> env
            ) env

        // Check each binding body - VarRefs now resolve to pre-created NodeIds
        let bindingResults =
            preCreatedBindings
            |> List.map (fun (binding, head, _, preCreatedNode) ->
                let checkedBinding = checkBindingInScope false checkExpr envWithBindings builder binding head (Some preCreatedNode)
                { checkedBinding with Node = generalizeRecursiveBinding env builder checkedBinding.Node })

        let bindingNodes = bindingResults |> List.map _.Node
        let bodyEnv = extendEnvWithResults envWithBindings bindings bindingResults
        let bodyNode = checkExpr bodyEnv builder bodyExpr
        buildSequential bindingNodes bodyNode

    | false ->
        // NON-RECURSIVE BINDINGS: Standard sequential processing
        let bindingResults =
            bindings |> List.map (fun binding ->
                checkBindingInScope false checkExpr env builder binding (getBindingHead env binding) None)

        let bindingNodes = bindingResults |> List.map _.Node
        let bodyEnv = extendEnvWithResults env bindings bindingResults
        let bodyNode = checkExpr bodyEnv builder bodyExpr
        buildSequential bindingNodes bodyNode

//-------------------------------------------------------------------------
// Match Clause Handling
//-------------------------------------------------------------------------

/// Generate field extraction nodes for record pattern bindings
/// Returns list of (bindingName, extractionNodeId) pairs
let rec private generatePatternExtractions
    (builder: NodeBuilder)
    (pattern: Pattern)
    (sourceNodeId: NodeId)
    (range: SourceRange)
    (arena: ArenaAffinity)
    : (string * NodeId) list =

    match pattern with
    | Pattern.Var (name, _ty) ->
        // Simple variable binding - the source IS the value
        [(name, sourceNodeId)]

    | Pattern.Record (fields, _recordType) ->
        // Record pattern: extract each field and recurse into nested patterns
        fields
        |> List.collect (fun (fieldName, fieldPattern) ->
            // Create FieldGet to extract this field from the source
            // Type will be inferred from the nested pattern
            let fieldType =
                match fieldPattern with
                | Pattern.Var (_, ty) -> ty
                | _ -> freshTypeVar range  // Fresh type var for nested patterns
            let fieldGetNode = builder.Create(
                SemanticKind.FieldGet(sourceNodeId, fieldName),
                fieldType,
                range,
                arena = arena,
                children = [sourceNodeId])
            // Recurse into the field pattern with the FieldGet as the new source
            generatePatternExtractions builder fieldPattern fieldGetNode.Id range arena)

    | Pattern.Tuple _elements ->
        // Tuple pattern: would need TupleGet (not yet implemented for pattern matching)
        // For now, fall through to simple binding
        []

    | Pattern.Union (_caseName, _tagIndex, payloadOpt, _unionType) ->
        // Union pattern: would need payload extraction
        // For now, handle payload if present
        match payloadOpt with
        | Some payload -> generatePatternExtractions builder payload sourceNodeId range arena
        | None -> []

    | Pattern.As (inner, _name) ->
        // As pattern: recurse into inner
        generatePatternExtractions builder inner sourceNodeId range arena

    | Pattern.Or (left, _right) ->
        // Or pattern: both branches bind same vars, use left
        generatePatternExtractions builder left sourceNodeId range arena

    | Pattern.And (left, right) ->
        // And pattern: combine bindings from both
        generatePatternExtractions builder left sourceNodeId range arena @
        generatePatternExtractions builder right sourceNodeId range arena

    | Pattern.Array elements ->
        // Array pattern: would need indexed access
        elements
        |> List.collect (fun elem -> generatePatternExtractions builder elem sourceNodeId range arena)

    | Pattern.Const _ | Pattern.Wildcard | Pattern.Null | Pattern.IsType _ | Pattern.Exception _ ->
        // No bindings for these patterns
        []

/// Check a match clause with scrutinee ID for record pattern field extraction
let checkMatchClause
    (checkExpr: CheckExprFn)
    (checkPattern: CheckPatternFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (scrutineeId: NodeId)
    (scrutineeTy: NativeType)
    (resultTy: NativeType)
    (clause: SynMatchClause)
    : MatchCase =

    let (SynMatchClause(pat, guardOpt, bodyExpr, _, _, _)) = clause
    let range = rangeToSourceRange bodyExpr.Range

    // Check pattern and extract bindings
    let (pattern, patBindings) = checkPattern env pat scrutineeTy range

    // Generate field extraction nodes for record patterns
    // This creates FieldGet nodes that provide values for pattern bindings
    let extractions = generatePatternExtractions builder pattern scrutineeId range env.CurrentArena

    // Create a map from binding name to extraction NodeId
    let extractionMap = extractions |> Map.ofList

    // Create PSG nodes for pattern bindings and add to environment
    // For record patterns, the PatternBinding's "value" comes from the FieldGet
    // Following ML/FStar convention: pattern binding IS the definition
    // Collect NodeIds for inclusion in MatchCase (enables SSA assignment traversal)
    let (bodyEnv, patternBindingIds, _fieldGetIds) =
        patBindings
        |> List.fold (fun (env, bindingIds, fieldIds) (name, ty) ->
            // Check if this binding has a field extraction
            let (patternBindingNode, newFieldIds) =
                match Map.tryFind name extractionMap with
                | Some fieldGetId ->
                    // Create PatternBinding as a child of the FieldGet
                    // This connects the binding to its extracted value
                    let node = builder.Create(
                        SemanticKind.PatternBinding(name),
                        ty,
                        range,
                        arena = env.CurrentArena,
                        children = [fieldGetId])
                    (node, fieldGetId :: fieldIds)
                | None ->
                    // No extraction needed (e.g., simple variable pattern matching scrutinee directly)
                    let node = builder.Create(
                        SemanticKind.PatternBinding(name),
                        ty,
                        range,
                        arena = env.CurrentArena)
                    (node, fieldIds)
            let env' = addBinding name ty false (Some patternBindingNode.Id) false env
            (env', patternBindingNode.Id :: bindingIds, newFieldIds)
        ) (env, [], [])
    let patternBindingIds = List.rev patternBindingIds  // Preserve order

    // Check guard if present
    let guardNode = guardOpt |> Option.map (checkExpr bodyEnv builder)
    guardNode |> Option.iter (fun g ->
        addConstraint (Constraint.Equals(g.Type, Types.boolType, range)) env)

    // Check body
    let bodyNode = checkExpr bodyEnv builder bodyExpr

    // Body must match result type
    addConstraint (Constraint.Equals(bodyNode.Type, resultTy, range)) env

    { Pattern = pattern
      PatternBindings = patternBindingIds
      Guard = guardNode |> Option.map (fun n -> n.Id)
      Body = bodyNode.Id }


//-------------------------------------------------------------------------
// Set Operations: Assignment expressions
//-------------------------------------------------------------------------

/// Check Set: target <- value (general assignment)
let checkSet
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (targetExpr: SynExpr)
    (valueExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let targetNode = checkExpr env builder targetExpr
    let valueNode = checkExpr env builder valueExpr
    addConstraint (Constraint.Equals(targetNode.Type, valueNode.Type, range)) env
    builder.Create(
        SemanticKind.Set(targetNode.Id, valueNode.Id),
        Types.unitType,
        range,
        children = [targetNode.Id; valueNode.Id])

/// Check DotSet: expr.field <- value
let checkDotSet
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (objExpr: SynExpr)
    (longId: Ident list)
    (valueExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let objNode = checkExpr env builder objExpr
    let valueNode = checkExpr env builder valueExpr
    let fieldName = longId |> List.map (fun id -> id.idText) |> String.concat "."
    match tryResolveRecordFieldType objNode.Type fieldName env with
    | Some fieldType -> addConstraint (Constraint.Equals(fieldType, valueNode.Type, range)) env
    | None -> addNativeError DiagnosticCodes.CCS8706_UndefinedType objExpr.Range $"Cannot resolve field '{fieldName}' on '{formatType objNode.Type}'" env
    builder.Create(
        SemanticKind.FieldSet(objNode.Id, fieldName, valueNode.Id),
        Types.unitType,
        range,
        children = [objNode.Id; valueNode.Id])

/// Check LongIdentSet: Module.value <- expr
let checkLongIdentSet
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (longId: Ident list)
    (valueExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let valueNode = checkExpr env builder valueExpr
    let parts = longId |> List.map (fun id -> id.idText)
    let targetName = parts |> String.concat "."
    match tryLookupBinding targetName env with
    | Some binding when binding.IsMutable ->
        addConstraint (Constraint.Equals(binding.Type, valueNode.Type, range)) env
        let targetNode = builder.Create(
            SemanticKind.VarRef(targetName, binding.NodeId),
            binding.Type,
            range)
        builder.Create(
            SemanticKind.Set(targetNode.Id, valueNode.Id),
            Types.unitType,
            range,
            children = [targetNode.Id; valueNode.Id])
    | _ ->
        // `r.Field <- v` (or `Module.r.Field <- v`): the longest proper prefix that names a
        // binding is the record, the remaining parts are a field path. Records are memref-
        // backed, so the store mutates the record in place, parameter or not.
        let rec tryPrefix (k: int) =
            if k < 1 then None
            else
                let prefix = parts |> List.take k |> String.concat "."
                match tryLookupBinding prefix env with
                | Some binding when binding.NativeLiteral.IsNone -> Some (binding, prefix, parts |> List.skip k)
                | _ -> tryPrefix (k - 1)
        match (if parts.Length >= 2 then tryPrefix (parts.Length - 1) else None) with
        | Some (binding, prefix, fieldPath) ->
            let baseNode = builder.Create(
                SemanticKind.VarRef(prefix, binding.NodeId),
                binding.Type,
                range,
                arena = env.CurrentArena)
            // Walk the intermediate fields with FieldGet; the last one is the FieldSet target.
            let middle = fieldPath |> List.take (fieldPath.Length - 1)
            let lastField = List.last fieldPath
            let (objNode, objType) =
                middle |> List.fold (fun (node: SemanticNode, ty: NativeType) fieldName ->
                    let fieldTy = Types.resolveFieldType (applySubst ty) fieldName env range
                    let fieldNode = builder.Create(
                        SemanticKind.FieldGet(node.Id, fieldName),
                        fieldTy,
                        range,
                        children = [node.Id])
                    builder.SetParent(node.Id, fieldNode.Id)
                    (fieldNode, fieldTy)
                ) (baseNode, applySubst binding.Type)
            let lastFieldTy = Types.resolveFieldType (applySubst objType) lastField env range
            addConstraint (Constraint.Equals(lastFieldTy, valueNode.Type, range)) env
            let setNode = builder.Create(
                SemanticKind.FieldSet(objNode.Id, lastField, valueNode.Id),
                Types.unitType,
                range,
                children = [objNode.Id; valueNode.Id])
            builder.SetParent(objNode.Id, setNode.Id)
            builder.SetParent(valueNode.Id, setNode.Id)
            setNode
        | None ->
            addNativeError DiagnosticCodes.CCS8009_UndefinedValue valueExpr.Range $"Cannot assign to '{targetName}' (not found or not mutable)" env
            builder.Create(
                SemanticKind.Error $"Cannot assign to '{targetName}' (not found or not mutable)",
                NativeType.TError "assignment error",
                range)

/// Check DotNamedIndexedPropertySet: obj.Prop[idx] <- value
let checkDotNamedIndexedPropertySet
    (checkExpr: CheckExprFn)
    (env: TypeEnv)
    (builder: NodeBuilder)
    (objExpr: SynExpr)
    (longId: Ident list)
    (indexExpr: SynExpr)
    (valueExpr: SynExpr)
    (range: SourceRange)
    : SemanticNode =
    let objNode = checkExpr env builder objExpr
    let indexNode = checkExpr env builder indexExpr
    let valueNode = checkExpr env builder valueExpr
    let propName = longId |> List.map (fun id -> id.idText) |> String.concat "."

    addConstraint (Constraint.HasMember(objNode.Type, propName, freshTypeVar range, range)) env

    builder.Create(
        SemanticKind.NamedIndexedPropertySet(objNode.Id, propName, indexNode.Id, valueNode.Id),
        Types.unitType,
        range,
        children = [objNode.Id; indexNode.Id; valueNode.Id])
