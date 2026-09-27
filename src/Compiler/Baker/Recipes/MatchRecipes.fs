// SPDX-License-Identifier: MIT

/// Baker match recipes construct typed decisions and source variable bindings.
/// Pattern tests, guarded extraction and fallthrough are explicit PSG structure;
/// the witness consumes shallow, guard-free CaseElimination nodes.
///
/// See: docs/fidelity/Baker_Saturation_Architecture.md
/// See: clef-lang-spec/spec/patterns.md
module Clef.Compiler.Baker.Recipes.MatchRecipes

open XParsec.Parsers
open XParsec.Combinators
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives

//=============================================================================
// BRIDGE: Convert SaturationParser results to Decomposition.Result
//=============================================================================

/// Convert a Decomposition.Context to a SaturationState
let private toSaturationState (ctx: Context) : SaturationState =
    { EmittedNodes = []
      Bindings = Map.empty
      ExpansionId = ctx.ExpansionId
      OriginalHOF = ctx.OriginalHOF
      SourceRange = ctx.SourceRange
      InspiringNode = ctx.InspiringNode
      Platform = ctx.Platform }

/// Run a saturation parser and convert to Decomposition.Result
let private runSaturation (ctx: Context) (parser: SaturationParser<NodeId>) : Result =
    let initialState = toSaturationState ctx
    let result, nodes = run initialState parser
    match result with
    | Matched resultNodeId ->
        mkResultNoShadow nodes resultNodeId []
    | NoMatch reason ->
        failwithf "Saturation failed: %s" reason

/// Count bindings in a pattern (recursive for nested patterns)
let rec private countPatternBindings (pattern: Pattern) : int =
    match pattern with
    | Pattern.Var _ -> 1
    | Pattern.Union (_, _, Some payload, _) -> countPatternBindings payload
    | Pattern.Union (_, _, None, _) -> 0
    | Pattern.Tuple elements -> elements |> List.sumBy countPatternBindings
    | Pattern.Record (fields, _) ->
        fields |> List.sumBy (fun (_, fieldPattern) -> countPatternBindings fieldPattern)
    | Pattern.Array elements -> elements |> List.sumBy countPatternBindings
    | Pattern.And (left, right) -> countPatternBindings left + countPatternBindings right
    | Pattern.Or (left, _) -> countPatternBindings left  // Or patterns must bind same names
    | Pattern.As (inner, _) -> 1 + countPatternBindings inner  // 1 for the 'as' binding + inner
    | Pattern.Exception (_, bindName) -> if Option.isSome bindName then 1 else 0
    | Pattern.Wildcard | Pattern.Null | Pattern.Const _ | Pattern.IsType _ -> 0

/// Read actual union payload fields, including wildcard positions. A wildcard
/// contains no type; substituting unit would corrupt the physical tuple shape.
let private payloadType (graph: SemanticGraph) unionType tag : Result<NativeType, string> =
    let missing detail = Error (sprintf "%s (%A tag %d)" detail unionType tag)
    let packed fields =
        match fields with
        | [] -> missing "the union case declares no payload field"
        | [field] -> Ok(applySubst field)
        | fields -> Ok(NativeType.TTuple(List.map applySubst fields, false))
    match applySubst unionType with
    | NativeType.TApp(constructor, [element]) when (constructor.Name = "option" || constructor.Name = "voption") && tag = 1 -> Ok element
    | NativeType.TApp(constructor, [ok; error]) when constructor.Name = "Result" || constructor.Name = "result" ->
        match tag with 0 -> Ok ok | 1 -> Ok error | _ -> missing "Result has no case at this tag"
    | NativeType.TUnion(_, cases) ->
        match cases |> List.tryFind (fun case -> case.Index = tag) with
        | Some case -> packed (List.map snd case.Fields)
        | None -> missing "the union type has no case at this tag"
    | NativeType.TApp(constructor, arguments) ->
        let definition = graph.Nodes.Values |> Seq.tryFind (fun node ->
            match node.Kind, applySubst node.Type with
            | SemanticKind.TypeDef(_, TypeDefKind.UnionDef _, _), NativeType.TApp(declared, _) ->
                declared.Name = constructor.Name && declared.Module = constructor.Module
            | _ -> false)
        match definition with
        | None -> missing "no union declaration in the graph matches the constructor"
        | Some node ->
            match node.Kind, canonicalizeVars node.Type with
            | SemanticKind.TypeDef(_, TypeDefKind.UnionDef cases, _), NativeType.TApp(_, parameters) ->
                let parameter = function
                    | NativeType.TVar value | NativeType.TNum(CarrierRef.CVar value, _) -> Ok value
                    | NativeType.TMeasure dimension when dimension.Bases.IsEmpty ->
                        match Map.toList dimension.Vars with
                        | [variable, 1] -> Ok (measureCellOf variable)
                        | _ -> Error "the union declaration has a non-parameter measure"
                    | _ -> Error "the union declaration has a non-parameter type argument"
                let parameters = List.map parameter parameters
                match parameters |> List.tryPick (function Error reason -> Some reason | Ok _ -> None) with
                | Some reason -> missing reason
                | None ->
                    let parameters = parameters |> List.choose (function Ok value -> Some value | Error _ -> None)
                    if parameters.Length <> arguments.Length then missing "the union declaration arity disagrees with the instantiated type" else
                    match cases |> List.tryItem tag with
                    | Some (_, fields) ->
                        fields |> List.map (fun (_, field) -> instantiate parameters arguments (canonicalizeVars field)) |> packed
                    | None -> missing "the union declaration has no case at this tag"
            | _ -> missing "the matching declaration is not a generic union declaration"
    | _ -> missing "the scrutinee type is not a union type"

/// A constructor's argument list wraps a single payload in Pattern.Tuple.
/// That wrapper does not introduce a tuple value in the union representation.
let private singlePayload = function
    | Pattern.Tuple [payload] -> payload
    | payload -> payload

/// A decision consumes only one pattern test. Refutable payload patterns become
/// further decisions in its selected body, never implicit work for the witness.
let private caseDecision (evidence: ResizeArray<Hyperedge>) diagnostic original inputType pattern selected fallback resultType = saturation {
    let arm pattern body : CaseArm =
        { Pattern = pattern; Bindings = []; Guard = None; Body = body }
    let! scrutinee =
        match fallback with
        | Some _ -> preturn original
        | None -> createWithChildren (SemanticKind.TypeAnnotation(original, inputType)) inputType [original]
    let arms = arm pattern selected :: (fallback |> Option.toList |> List.map (arm Pattern.Wildcard))
    let! decision =
        createWithChildren (SemanticKind.CaseElimination(scrutinee, arms)) resultType
            (scrutinee :: (arms |> List.map _.Body))
    match fallback with
    | Some _ -> return decision
    | None ->
        let! yes = boolLit true
        let! no = boolLit false
        let tests = [arm pattern yes; arm Pattern.Wildcard no]
        let! test = createWithChildren (SemanticKind.CaseElimination(scrutinee, tests)) Types.boolType [scrutinee; yes; no]
        let! required = createWithChildren (SemanticKind.Require(test, diagnostic)) Types.unitType [test]
        let! frontier = evaluateBefore [required] decision resultType
        evidence.Add { Class = EdgeClass.Provenance; Role = EdgeRole.MatchRequirement; Ordinal = 0
                       Sources = [required; test; decision; scrutinee; yes; no; selected; original]; Target = frontier }
        return frontier
  }

/// A terminal boolean condition has no result on failure. This is shared by
/// source guards and semantic literal equality; its continuation is already
/// inside the selected pattern scope.
let private requireThen (evidence: ResizeArray<Hyperedge>) diagnostic condition selected resultType = saturation {
    let! required = createWithChildren (SemanticKind.Require(condition, diagnostic)) Types.unitType [condition]
    let! frontier = evaluateBefore [required] selected resultType
    evidence.Add { Class = EdgeClass.Provenance; Role = EdgeRole.MatchRequirement; Ordinal = 1
                   Sources = [required; condition; selected]; Target = frontier }
    return frontier
  }

/// Compile a constructor chain with the original later cases as its failure
/// continuation. Every payload read and source guard remains inside the branch
/// whose pattern facts admit it. Source variable definitions retain their IDs.
let private decisionParser (evidence: ResizeArray<Hyperedge>) (graph: SemanticGraph) (scrutinee: NodeId) (cases: MatchCase list) (resultType: NativeType) =
    let scrutineeType = graph.Nodes[scrutinee].Type
    let range = graph.Nodes[scrutinee].Range
    let diagnostic = sprintf "Pattern match failed at %s:%d:%d" range.File range.Start.Line range.Start.Column
    let rec compile (input: NodeId) (inputType: NativeType) (pattern: Pattern) (bindings: NodeId list) (success: NodeId) (fallback: NodeId option) : SaturationParser<NodeId> =
        if bindings.Length <> countPatternBindings pattern then fail (XParsec.ErrorType.Message (sprintf "CCS source checking did not settle the source bindings for match pattern %A at scrutinee %d: the pattern requires %d exact source bindings, got %d" pattern (NodeId.value scrutinee) (countPatternBindings pattern) bindings.Length)) else
        match pattern with
        | Pattern.Wildcard -> saturation { return success }
        | Pattern.Var(name, ty) ->
            match bindings with
            | [source] -> saturation {
                let! binding = letBindAt source name input ty
                return! evaluateBefore [binding] success resultType
              }
            | _ -> fail (XParsec.ErrorType.Message (sprintf "CCS source checking did not settle the source binding for match variable '%s' at scrutinee %d: expected exactly one, got %d" name (NodeId.value scrutinee) bindings.Length))
        | Pattern.Union(name, tag, payload, unionType) -> saturation {
            let! selected =
                match payload |> Option.map singlePayload with
                | None | Some Pattern.Wildcard -> preturn success
                | Some payloadPattern ->
                    match payloadType graph unionType tag with
                    | Error reason ->
                        fail (XParsec.ErrorType.Message (sprintf "CCS source checking did not settle the instantiated payload type for union pattern '%s' at scrutinee %d: %s" name (NodeId.value scrutinee) reason))
                    | Ok payloadType -> saturation {
                        let! value = duEliminate input name tag payloadType
                        return! compile value payloadType payloadPattern bindings success fallback
                      }
            let shallow = Pattern.Union(name, tag, payload |> Option.map (fun _ -> Pattern.Wildcard), unionType)
            return! caseDecision evidence diagnostic input inputType shallow selected fallback resultType
          }
        | Pattern.Const constant -> saturation {
            // The literal retains the input's checked dimensional type. Its
            // hosted payload kind does not choose a source width or equality
            // algorithm; the ordinary typed operation owns those semantics.
            let! literal = createWithChildren (SemanticKind.Literal constant) inputType []
            let! equal = compareEq input literal inputType
            match fallback with
            | Some later -> return! ifThenElse equal success later resultType
            | None -> return! requireThen evidence diagnostic equal success resultType
          }
        | Pattern.Tuple elements ->
            match applySubst inputType with
            | NativeType.TTuple(types, _) when types.Length = elements.Length ->
                let components = List.zip elements types |> List.mapi (fun index (pattern, ty) ->
                    pattern, ty, fun () -> createWithChildren (SemanticKind.TupleGet(input, index)) ty [input])
                compileComponents components bindings success fallback
            | _ -> fail (XParsec.ErrorType.Message (sprintf "CCS source checking did not settle a tuple input type for tuple pattern at scrutinee %d: the pattern has %d elements, the input type is %A" (NodeId.value scrutinee) elements.Length inputType))
        | Pattern.Record(fields, recordType) ->
            let declared =
                match applySubst recordType with
                | NativeType.TAnon(fields, _) -> Some fields
                | _ -> Clef.Compiler.PSGSaturation.SemanticGraph.RecordInstances.tryFields recordType graph
            match declared with
            | None ->
                fail (XParsec.ErrorType.Message (sprintf "CCS source checking did not settle the instantiated fields for record pattern at scrutinee %d: %A" (NodeId.value scrutinee) recordType))
            | Some declared ->
                match fields |> List.tryFind (fun (name, _) -> declared |> List.exists (fst >> (=) name) |> not) with
                | Some (name, _) ->
                    fail (XParsec.ErrorType.Message (sprintf "CCS source checking did not settle record pattern field '%s' at scrutinee %d: %A declares no such field" name (NodeId.value scrutinee) recordType))
                | None ->
                    let components = fields |> List.map (fun (name, pattern) ->
                        let ty = declared |> List.find (fst >> (=) name) |> snd
                        pattern, ty, fun () -> createWithChildren (SemanticKind.FieldGet(input, name)) ty [input])
                    compileComponents components bindings success fallback
        | unsupported ->
            fail (XParsec.ErrorType.Message (sprintf "Baker Match recipe did not settle a decision for pattern at scrutinee %d: %A requires further source pattern elaboration" (NodeId.value scrutinee) unsupported))
    and compileComponents components bindings success fallback : SaturationParser<NodeId> =
        match components with
        | [] -> preturn success
        | (pattern, ty, project) :: rest -> saturation {
            let own, remaining = List.splitAt (countPatternBindings pattern) bindings
            let! selected = compileComponents rest remaining success fallback
            match pattern with
            | Pattern.Wildcard -> return selected
            | _ ->
                let! value = project ()
                return! compile value ty pattern own selected fallback
          }
    let rec remaining (input: NodeId) (cases: MatchCase list) : SaturationParser<NodeId> =
        match cases with
        | [] -> fail (XParsec.ErrorType.Message (sprintf "CCS source checking did not settle a terminal case for match at scrutinee %d: the match has no cases" (NodeId.value scrutinee)))
        | case :: rest -> saturation {
            let! fallback =
                match rest with
                | [] -> preturn None
                | _ -> saturation {
                    let! later = remaining input rest
                    return Some later
                  }
            let! success =
                match case.Guard, fallback with
                | None, _ -> preturn case.Body
                | Some guard, Some later -> ifThenElse guard case.Body later resultType
                | Some guard, None -> requireThen evidence diagnostic guard case.Body resultType
            return! compile input scrutineeType case.Pattern case.PatternBindings success fallback
          }
    saturation {
        let! expansion = getExpansionId
        let name = sprintf "__match_input_%d" expansion
        let! snapshot = letBind name scrutinee scrutineeType
        let! input = varRef name (Some snapshot) scrutineeType
        let! decision = remaining input cases
        return! evaluateBefore [snapshot] decision resultType
    }

/// Every match uses the same ordered, selected-scope source algorithm.
/// Bindings and guards live in selected bodies, never in arm metadata.
let enrichMatchWithEvidence
    (graph: SemanticGraph)
    (ctx: Context)
    (scrutineeId: NodeId)
    (cases: MatchCase list)
    (resultType: NativeType)
    : Result * Hyperedge list =

    let evidence = ResizeArray<Hyperedge>()
    let parser = decisionParser evidence graph scrutineeId cases resultType
    let result = runSaturation ctx parser
    // Replacing PatternBinding at its source identity also preserves its source
    // range and any existing provenance; generated enrichment labels are added.
    let nodes =
        result.NewNodes |> List.map (fun node ->
            match Map.tryFind node.Id graph.Nodes with
            | Some original ->
                { node with Range = original.Range
                            Metadata = node.Metadata |> Map.fold (fun metadata key value -> Map.add key value metadata) original.Metadata }
            | None -> node)
    { result with NewNodes = nodes }, List.ofSeq evidence

let enrichMatch graph ctx scrutinee cases resultType =
    enrichMatchWithEvidence graph ctx scrutinee cases resultType |> fst

/// Legacy tuple entry point shares the same selected-scope protocol.
let decomposeMatch graph ctx scrutinee cases resultType = enrichMatch graph ctx scrutinee cases resultType
