// SPDX-License-Identifier: MIT
module Clef.Compiler.Baker.Ingredients.Boundaries

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration
open Clef.Compiler.Baker.Ingredients.Obligations

let ownedNode (node: SemanticNode) = node.Metadata.ContainsKey "Baker.BoundaryOwned"
let markOwned (node: SemanticNode) = { node with Metadata = node.Metadata.Add("Baker.BoundaryOwned", MetadataValue.Bool true) }

let platformPremise (platform: PlatformContext option) =
    platform |> Option.map (fun platform ->
        { Id = platform.PlatformId; Description = platform.PlatformDescription; LibraryPath = platform.PlatformLibraryPath
          SourcePaths = platform.PlatformSourcePaths; Architecture = platform.PlatformArchitecture; OS = platform.PlatformOS
          RuntimeClaim = platform.RuntimeModel; Substrate = platform.SubstrateKind; Dimensions = platform.Dimensions
          Representations = platform.Representations; EndpointReturns = platform.EndpointReturns })

/// Closed immutable observations; native types become identities before any
/// later inference-cell mutation can occur. Only settlement calls readers.
let premise (node: SemanticNode) : BoundarySourcePremise =
    let literal = function
        | NativeLiteral.String value -> "string", [value], []
        | NativeLiteral.Int(value, kind) -> "integer", [string kind], [bigint value]
        | NativeLiteral.UInt(value, kind) -> "unsigned-integer", [string kind], [bigint value]
        | NativeLiteral.Bool value -> "boolean", [], [if value then 1I else 0I]
        | NativeLiteral.Char value -> "character", [], [bigint (int value)]
        | NativeLiteral.Float(value, kind) -> "real", [string kind], [bigint (System.BitConverter.DoubleToInt64Bits value)]
        | NativeLiteral.Decimal value -> "decimal", [], System.Decimal.GetBits value |> Array.map bigint |> Array.toList
        | NativeLiteral.ByteArray values -> "bytes", [], values |> Array.map bigint |> Array.toList
        | NativeLiteral.UInt16Array values -> "uint16-array", [], values |> Array.map bigint |> Array.toList
        | NativeLiteral.Unit -> "unit", [], []
    let form, text, numbers =
        match node.Kind with
        | SemanticKind.RecordExpr(fields, copy) -> "record", List.map fst fields, [if copy.IsSome then 1I else 0I]
        | SemanticKind.ArrayExpr _ -> "array", [], []
        | SemanticKind.ArrayAllocate _ -> "array-allocation", [], []
        | SemanticKind.TupleExpr _ -> "tuple", [], []
        | SemanticKind.UnionCase(name, index, _) -> "case", [name], [bigint index]
        | SemanticKind.DUConstruct(name, index, _, _) -> "settled-case", [name], [bigint index]
        | SemanticKind.Literal value -> literal value
        | SemanticKind.VarRef(name, _) -> "reference", [name], []
        | SemanticKind.Binding(name, mutable', recursive', _) -> "binding", [name], [if mutable' then 1I else 0I; if recursive' then 1I else 0I]
        | SemanticKind.TypeAnnotation _ -> "annotation", [], []
        | SemanticKind.Quote _ -> "quotation", [], []
        | SemanticKind.Application _ -> "application", [], []
        | SemanticKind.ContinuationDispatch(_, cases, _) -> "continuation-dispatch", [], cases |> List.map (fst >> bigint)
        | SemanticKind.FieldGet(_, name) -> "field", [name], []
        | SemanticKind.StringByteBorrow _ -> "string-byte-borrow", [], []
        | SemanticKind.CellAddress _ -> "cell-address", [], []
        | SemanticKind.ElementAddress _ -> "element-address", [], []
        | SemanticKind.FieldAddress(_, name) -> "field-address", [name], []
        | SemanticKind.Reborrow _ -> "reborrow", [], []
        | SemanticKind.Intrinsic info -> "intrinsic", [string info.Module; info.Operation], []
        | SemanticKind.Lambda(formals, _, captures, _, context) -> "lambda", string context :: List.map (fun (name, _, _) -> name) formals, [bigint formals.Length; bigint captures.Length]
        | SemanticKind.ModuleDef(name, _) -> "module", [name], []
        | SemanticKind.TypeDef(name, kind, _) ->
            match kind with
            | TypeDefKind.RecordDef fields -> "record-definition", name :: List.map fst fields, [bigint fields.Length]
            | TypeDefKind.UnionDef cases ->
                let names = cases |> List.collect (fun (name, fields) -> name :: (fields |> List.collect (fun (name, _) -> match name with None -> ["unnamed"] | Some name -> ["named"; name])))
                "union-definition", name :: names, cases |> List.map (snd >> List.length >> bigint)
            | TypeDefKind.EnumDef cases ->
                let forms = cases |> List.map (fun (name, value) -> let form, text, numbers = literal value in name :: form :: text, numbers)
                "enum-definition", name :: (forms |> List.collect fst), forms |> List.collect (fun (text, numbers) -> bigint text.Length :: bigint numbers.Length :: numbers)
            | TypeDefKind.AbbreviationDef _ -> "abbreviation-definition", [name], []
            | TypeDefKind.ClassDef -> "class-definition", [name], []
            | TypeDefKind.StructDef -> "struct-definition", [name], []
            | TypeDefKind.InterfaceDef -> "interface-definition", [name], []
        | _ -> "other-incidence", [], []
    let embeddedTypes =
        match node.Kind with
        | SemanticKind.Lambda(formals, _, captures, _, _) -> (formals |> List.map (fun (_, ty, _) -> ty)) @ (captures |> List.map _.Type)
        | SemanticKind.TypeAnnotation(_, ty) -> [ty]
        | SemanticKind.TypeDef(_, TypeDefKind.RecordDef fields, _) -> fields |> List.map snd
        | SemanticKind.TypeDef(_, TypeDefKind.UnionDef cases, _) -> cases |> List.collect (snd >> List.map snd)
        | SemanticKind.TypeDef(_, TypeDefKind.AbbreviationDef target, _) -> [target]
        | _ -> []
    let rec constructors ty =
        let own tc = [Clef.Compiler.NativeTypedTree.TypeIdentities.constructor tc, tc.Layout, tc.FieldCount, tc.CaseCount, tc.Qualifiers, tc.FieldPinAttributes]
        match applySubst ty with
        | NativeType.TApp(tc, arguments) -> own tc @ List.collect constructors arguments
        | NativeType.TNum(carrier, _) -> CarrierRef.tryConstructor carrier |> Option.map own |> Option.defaultValue []
        | NativeType.TTuple(arguments, _) -> List.collect constructors arguments
        | NativeType.TFun(argument, result) | NativeType.TMap(argument, result) -> constructors argument @ constructors result
        | NativeType.TAnon(fields, _) -> fields |> List.collect (snd >> constructors)
        | NativeType.TUnion(tc, cases) -> own tc @ (cases |> List.collect (fun case -> case.Fields |> List.collect (snd >> constructors)))
        | NativeType.TForall(_, ty) | NativeType.TByref(ty, _) | NativeType.TNativePtr ty | NativeType.TLazy ty
        | NativeType.TSeq ty | NativeType.TSeqEnumerator ty | NativeType.TList ty | NativeType.TSet ty -> constructors ty
        | _ -> []
    let stringMetadata name =
        match node.Metadata.TryFind name with Some (MetadataValue.String value) -> Some value | _ -> None
    let metadata = node.Metadata |> Map.fold (fun facts name value ->
        let fact =
            match value with
            | MetadataValue.String value -> Some (["string"; value], [], [], None)
            | MetadataValue.StringList values -> Some ("strings" :: values, [], [], None)
            | MetadataValue.Int value -> Some (["int"], [bigint value], [], None)
            | MetadataValue.Int64 value -> Some (["int64"], [bigint value], [], None)
            | MetadataValue.Bool value -> Some (["bool"], [if value then 1I else 0I], [], None)
            | MetadataValue.NodeId value -> Some (["node"], [], [value], None)
            | MetadataValue.NodeIdList values -> Some (["nodes"], [], values, None)
            | MetadataValue.Type ty -> Some (["type"], [], [], Some (Clef.Compiler.NativeTypedTree.TypeIdentities.ofType ty))
            | _ -> None // No boundary rule reads floating/source-location/specialization metadata.
        match fact with Some value -> Map.add name value facts | None -> facts) Map.empty
    { Shape = { Form = form; Text = text; Numbers = numbers
                References = Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence node |> List.collect _.Sources
                Children = node.Children; Parent = node.Parent
                SourceType = Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type }
      EmbeddedTypes = embeddedTypes |> List.map Clef.Compiler.NativeTypedTree.TypeIdentities.ofType
      ConstructorFacts = (node.Type :: embeddedTypes) |> List.collect constructors
      Reachable = node.IsReachable; Range = node.ValueRange
      ExternLibrary = stringMetadata "FidelityExtern.Library"; ExternSymbol = stringMetadata "FidelityExtern.Symbol"
      HasExtern = node.Metadata.ContainsKey "FidelityExtern.Library" || node.Metadata.ContainsKey "FidelityExtern.Symbol"
      Metadata = metadata }

let premises (graph: SemanticGraph) =
    graph.Nodes |> Map.fold (fun facts id node -> if ownedNode node then facts else Map.add id (premise node) facts) Map.empty

let row role ordinal sources target =
    { Class = EdgeClass.Boundary; Role = role; Ordinal = ordinal; Sources = sources; Target = target }

let importRow (import: BoundaryImport) =
    row (EdgeRole.BoundaryImport import) 0
        (import.Scope :: import.Binding :: import.DeclarationPath @ (import.Parameters |> List.map fst) @ Set.toList import.Participants) import.Identity

let callRow (call: BoundaryCall) =
    row (EdgeRole.BoundaryCall call) 0
        (call.Import :: call.Callee :: (call.Arguments |> List.map _.Actual) @ call.ErasedUnitArguments @ Set.toList call.Participants) call.Site

let operandRows (call: BoundaryCall) =
    let operands = call.Arguments |> List.mapi (fun ordinal operand ->
        let sources = [call.Site; call.Import; call.Callee; operand.Actual; operand.Formal] @ Set.toList call.Participants
        row (EdgeRole.BoundaryOperand operand) ordinal sources call.Site ::
        (operand.Adaptation |> Option.toList |> List.map (fun meet -> row (EdgeRole.BoundaryAdaptation meet) ordinal sources call.Site))) |> List.concat
    let result = call.ResultAdaptation |> Option.toList |> List.map (fun meet ->
        row (EdgeRole.BoundaryAdaptation meet) -1 ([call.Site; call.Import; call.Callee] @ Set.toList call.Participants) call.Site)
    operands @ result

let coverageSources (call: BoundaryCall) _ordinal =
    let ordered = call.Arguments |> List.collect (fun operand -> [operand.Actual; operand.Formal])
    [call.Site; call.Import; call.Callee] @ ordered @ call.ErasedUnitArguments @ Set.toList call.Participants

let coverageBody (coverage: BoundaryCoverage) =
    match coverage.Input, coverage.Destination with
    | ValueRange.Bounded(lower, upper), ValueRange.Bounded(minimum, maximum) ->
        Some (ObligationBody.IntegerRepresentationCoverage(lower, upper, minimum, maximum))
    | _ -> None

/// Exact finite arithmetic is the checked proof rule. Creating an obligation
/// alone proves nothing; its outcome is independently recorded and checked.
let coverageOutcome (coverage: BoundaryCoverage) =
    match coverage.Input, coverage.Destination with
    | ValueRange.Bounded(lower, upper), ValueRange.Bounded(minimum, maximum)
        when minimum <= lower && lower <= upper && upper <= maximum -> BoundaryProofOutcome.Proven
    | _ -> BoundaryProofOutcome.Refuted

let coverageRows (call: BoundaryCall) (coverage: BoundaryCoverage) outcome =
    let sources = coverageSources call coverage.Ordinal
    [ row (EdgeRole.BoundaryCoverage coverage) coverage.Ordinal sources coverage.Obligation
      { Class = EdgeClass.Obligation; Role = EdgeRole.Constrains; Ordinal = coverage.Ordinal; Sources = sources; Target = coverage.Obligation }
      row (EdgeRole.BoundaryProof outcome) coverage.Ordinal (coverage.Obligation :: sources) call.Site
      { Class = EdgeClass.Provenance; Role = EdgeRole.EnrichedWith; Ordinal = coverage.Ordinal; Sources = sources; Target = coverage.Obligation } ]

let coverage enrichId (graph: SemanticGraph) (call: BoundaryCall) ordinal operand input destination =
    let initial = { Site = call.Site; Operand = operand; Ordinal = ordinal; Input = input; Destination = destination; Obligation = NodeId 0 }
    match coverageBody initial with
    | None -> Error "A scalar boundary coverage proof requires observable finite source and destination ranges."
    | Some body ->
        let node = obligationNode graph.Nodes[call.Site] enrichId
                       { Id = $"boundary_{NodeId.value call.Site}_{ordinal}"; Kind = "boundary-range-coverage"; Logic = "QF_LIA"
                         Statement = "the exact source boundary occurrence fits its declared destination range"
                         Source = fmtRange graph.Nodes[call.Site].Range; Refs = []; Body = body } |> markOwned
        let coverage = { initial with Obligation = node.Id }
        let outcome = coverageOutcome coverage
        Ok ({ NewNodes = [node]; Annotated = []; NewEdges = coverageRows call coverage outcome }, coverage, outcome)

/// A graph citizen records this recipe firing even for an empty domain.
let anchor enrichId (graph: SemanticGraph) =
    let sourceRange = graph.Nodes |> Map.toSeq |> Seq.tryHead |> Option.map (snd >> _.Range)
                      |> Option.defaultValue { File = ""; Start = { Line = 0; Column = 0 }; End = { Line = 0; Column = 0 } }
    { Id = NodeId.fresh (); Kind = SemanticKind.Literal NativeLiteral.Unit; Range = sourceRange
      Type = Types.unitType; SRTPResolution = None; ArenaAffinity = ArenaAffinity.CurrentActor
      LayoutHint = None; Children = []; Parent = None; Metadata = Map.empty; IsReachable = false
      EmissionStrategy = EmissionStrategy.Inline; ValueRange = None }
    |> markBaker "BoundarySettlement" enrichId |> markOwned
