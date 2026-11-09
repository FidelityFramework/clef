// SPDX-License-Identifier: MIT
/// The source publication seam. Builders run while CCS owns the graph; Alex
/// witnesses the materialized domain projections carried by graph codata.
module Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
module AggregateTypes = Clef.Compiler.Baker.Ingredients.CallableAggregateTypes
module TypeIdentity = Clef.Compiler.NativeTypedTree.TypeIdentities
module Codes = Clef.Compiler.NativeTypedTree.Expressions.Types.DiagnosticCodes
module ProofDispatch = Clef.Compiler.Baker.Recipes.ProofDispatchRecipes
module LiveScopes = Clef.Compiler.Baker.Recipes.WitnessScopeRecipes
module PreparedRows = Clef.Compiler.Baker.Recipes.WitnessForeignDemandRecipes
module LiveRows = Clef.Compiler.Baker.Recipes.WitnessLiveRowsRecipes
module PublishedRows = Clef.Compiler.Baker.Recipes.WitnessPublishedRowsRecipes

type Projection = WitnessEmissionProjection

/// Library retention is not a host-loading contract. Read only each checked
/// public type: native values formed privately inside a body are not exports.
let exportedInterfaceFailures (graph: SemanticGraph) : WitnessProjectionFailure list =
    let descriptors = PlatformResolution.readDescriptors graph
    let authorizedPaths (node: SemanticNode) =
        let rec lambdas parameters body =
            match graph.Nodes.TryFind body with
            | Some { Kind = SemanticKind.Lambda (more, inner, _, _, _) } -> lambdas (parameters @ more) inner
            | _ -> parameters, body
        let typeRefMatches (typeNodeId: NodeId) (ty: NativeType) =
            let ty = applySubst ty
            let isPointerSlot =
                Types.tryGetNTUKind ty = Some NTUKind.NTUptr ||
                Types.tryGetNTUKind ty = Some NTUKind.NTUfnptr ||
                (match ty with
                 | NativeType.TApp (tc, [inner]) when tc.Name = "option" ->
                     let inner = applySubst inner
                     Types.tryGetNTUKind inner = Some NTUKind.NTUptr || Types.tryGetNTUKind inner = Some NTUKind.NTUfnptr
                 | _ -> false)
            match PlatformResolution.caseOf graph typeNodeId with
            | Some (_, "Void", None) -> Types.tryGetNTUKind ty = Some NTUKind.NTUunit
            | Some (_, "Bool", None) -> Types.tryGetNTUKind ty = Some NTUKind.NTUbool
            | Some (_, "Pointer", Some bitsId) ->
                let pointerBits = graph.Platform |> Option.bind (fun ctx -> PlatformContext.pointerSize ctx |> Result.toOption) |> Option.map (fun bytes -> int64 bytes * 8L)
                Option.isSome pointerBits && PlatformResolution.int64Of graph bitsId = pointerBits && isPointerSlot
            | Some (_, "Integer", Some pairId) ->
                let pointerBits = graph.Platform |> Option.bind (fun ctx -> PlatformContext.pointerSize ctx |> Result.toOption) |> Option.map (fun bytes -> int64 bytes * 8L)
                let offered family bits =
                    match graph.Platform with
                    | Some ctx when not ctx.Representations.IsEmpty ->
                        ctx.Representations.Values
                        |> Seq.exists (fun r -> r.Family = family && int64 r.Bits = bits && NumericRepresentation.isOffered r)
                    | _ -> false
                match PlatformResolution.valueOf graph pairId with
                | Some { Kind = SemanticKind.TupleExpr [signId; bitsId] } ->
                    match PlatformResolution.caseOf graph signId, PlatformResolution.int64Of graph bitsId, Types.tryGetNTUKind ty with
                    | Some (_, "Signed", None), Some bits, Some (NTUKind.NTUint (NTUWidth.Fixed w)) -> bits = int64 w && offered "int" bits
                    | Some (_, "Signed", None), Some bits, Some (NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Pointer)) -> Some bits = pointerBits && offered "int" bits
                    | Some (_, "Signed", None), Some bits, Some (NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register)) -> offered "int" bits
                    | Some (_, "Signed", None), Some bits, Some NTUKind.NTUdiff -> Some bits = pointerBits && offered "int" bits
                    | Some (_, "Unsigned", None), Some bits, Some (NTUKind.NTUuint (NTUWidth.Fixed w)) -> bits = int64 w && offered "uint" bits
                    | Some (_, "Unsigned", None), Some bits, Some (NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Pointer)) -> Some bits = pointerBits && offered "uint" bits
                    | Some (_, "Unsigned", None), Some bits, Some (NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Register)) -> offered "uint" bits
                    | Some (_, "Unsigned", None), Some bits, Some (NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register)) -> offered "uint" bits
                    | Some (_, "Unsigned", None), Some bits, Some NTUKind.NTUsize -> Some bits = pointerBits && offered "uint" bits
                    | _ -> false
                | _ -> false
            | Some (_, "Float", Some bitsId) ->
                let offeredFloat bits =
                    match graph.Platform with
                    | Some ctx when not ctx.Representations.IsEmpty ->
                        ctx.Representations.Values
                        |> Seq.exists (fun r -> r.Family = "ieee" && int64 r.Bits = bits && NumericRepresentation.isOffered r)
                    | _ -> false
                match PlatformResolution.int64Of graph bitsId, Types.tryGetNTUKind ty with
                | Some bits, Some (NTUKind.NTUfloat (NTUWidth.Fixed w)) -> bits = int64 w && offeredFloat bits
                | Some bits, Some (NTUKind.NTUfloat (NTUWidth.Resolved WidthDimension.Register)) -> offeredFloat bits
                | _ -> false
            | Some (_, "Named", Some nameId) ->
                match PlatformResolution.stringOf graph nameId, ty with
                | Some name, NativeType.TApp (tc, _) -> tc.Name = name || tc.Name.EndsWith("." + name)
                | _ -> false
            | _ -> false
        let parameterMatches (paramNodeId: NodeId) (ty: NativeType) =
            match PlatformResolution.recordOf graph paramNodeId with
            | Some (paramRecord, paramFields) when PlatformResolution.typeName paramRecord = Some "ParameterInfo" ->
                let passByOk =
                    match PlatformResolution.field "PassBy" paramFields |> Option.bind (PlatformResolution.caseOf graph) with
                    | Some (_, "Value", None) -> true
                    | _ -> false
                let typeOk =
                    PlatformResolution.field "Type" paramFields |> Option.exists (fun typeId -> typeRefMatches typeId ty)
                passByOk && typeOk
            | _ -> false
        let descriptorMatches typeName fieldName fieldTy =
            let rec signature parameters ty =
                match applySubst ty with
                | NativeType.TFun (parameter, result) -> signature (parameter :: parameters) result
                | result ->
                    let parameters = List.rev parameters
                    let parameters =
                        match parameters with
                        | [parameter] when Types.tryGetNTUKind (applySubst parameter) = Some NTUKind.NTUunit -> []
                        | _ -> parameters
                    parameters, result
            let fnSignature =
                match applySubst fieldTy, Types.tryGetNTUKind fieldTy with
                | NativeType.TApp (_, [sigTy]), Some NTUKind.NTUfnptr -> Some (signature [] sigTy)
                | _ -> None
            graph.Nodes.Values |> Seq.exists (fun candidate ->
                match candidate.Kind, candidate.Parent, candidate.Children with
                | SemanticKind.Binding (_, false, _, _), parent, children when parent = node.Parent && not children.IsEmpty ->
                    match PlatformResolution.valuePath graph (List.last children) with
                    | Some (record, path) when PlatformResolution.typeName record = Some "CallbackDescriptor" &&
                                               (path |> List.forall (fun id -> match graph.Nodes.TryFind id with Some { Kind = SemanticKind.Binding (_, true, _, _) } -> false | _ -> true)) &&
                                               (path |> List.exists (fun id -> match graph.Nodes.TryFind id with Some { Kind = SemanticKind.Quote _ } -> true | _ -> false)) ->
                        match PlatformResolution.recordOf graph record.Id with
                        | Some (_, fields) ->
                            let text key = PlatformResolution.field key fields |> Option.bind (PlatformResolution.stringOf graph)
                            match text "Record", text "Field", PlatformResolution.field "Signature" fields |> Option.bind (PlatformResolution.recordOf graph) with
                            | Some recordName, Some field, Some (signature, signatureFields) when recordName = typeName && field = fieldName && PlatformResolution.typeName signature = Some "FunctionDescriptor" ->
                                let name = PlatformResolution.field "CName" signatureFields |> Option.bind (PlatformResolution.stringOf graph)
                                let convention = PlatformResolution.field "CallingConvention" signatureFields |> Option.bind (PlatformResolution.caseOf graph)
                                name |> Option.exists (System.String.IsNullOrWhiteSpace >> not) &&
                                (match convention with Some (_, "CDecl", None) -> true | _ -> false) &&
                                (fnSignature |> Option.exists (fun (fnParams, fnRet) ->
                                    let parameters = PlatformResolution.field "Parameters" signatureFields |> Option.bind (PlatformResolution.elementsOf graph)
                                    (parameters |> Option.exists (fun values -> List.length values = List.length fnParams && List.forall2 parameterMatches values fnParams)) &&
                                    (PlatformResolution.field "ReturnType" signatureFields |> Option.exists (fun retId -> typeRefMatches retId fnRet))))
                            | _ -> false
                        | _ -> false
                    | _ -> false
                | _ -> false)
        let rec application id arguments =
            match graph.Nodes.TryFind id with
            | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> application inner arguments
            | Some { Kind = SemanticKind.Application (target, args) } -> application target (args @ arguments)
            | Some { Kind = SemanticKind.VarRef (_, Some target) } -> Some (target, arguments)
            | _ -> None
        let hasValidLifetime =
            match node.Children with
            | [implementation] ->
                Clef.Compiler.Baker.Ingredients.CompilerOwnedEntries.tryImplementation graph implementation
                |> Option.exists (fun entry -> entry.Lifetime.Binding = node.Id)
            | _ -> false
        match hasValidLifetime, PlatformResolution.lambdaOfBinding graph node.Id with
        | true, Some (parameters, body) ->
            let parameters, body = lambdas parameters body
            match application body [] with
            | Some (targetId, arguments) ->
                match graph.Nodes.TryFind targetId, PlatformResolution.lambdaOfBinding graph targetId with
                | Some target, Some (formals, targetBody) when
                    target.Parent = node.Parent &&
                    Map.containsKey "FidelityExtern.Library" target.Metadata &&
                    List.length parameters = List.length formals &&
                    List.length formals = List.length arguments &&
                    (descriptors.Functions |> List.exists (fun descriptor ->
                        descriptor.Body = Some targetBody &&
                        (descriptor.Parameters |> List.map fst) = (formals |> List.map (fun (_, _, id) -> id)) &&
                        (match PlatformResolution.recordOf graph descriptor.Node with
                         | Some (record, fields) ->
                             let _, findings = PlatformResolution.readFunctionForBinding graph target "" record fields
                             findings.IsEmpty
                         | None -> false))) ->
                    let parameterOutcomes =
                        parameters |> List.mapi (fun ordinal (_, ty, formal) ->
                            let (_, formalTy, _), arg = formals[ordinal], arguments[ordinal]
                            match applySubst ty, AggregateTypes.shape graph ty with
                            | NativeType.TApp (tc, _), Some (AggregateTypes.Shape.Record (_, [fieldName, fieldTy]))
                                when Types.tryGetNTUKind fieldTy = Some NTUKind.NTUfnptr ->
                                let name = tc.Name
                                let shortName = name.Substring(name.LastIndexOf('.') + 1)
                                let identity = NominalTypeIdentity.display (NominalTypeIdentity.ofConstructor tc)
                                let fieldIdentity = TypeIdentity.ofType (applySubst fieldTy)
                                let forwarded =
                                    TypeIdentity.ofType (applySubst formalTy) = fieldIdentity &&
                                    match graph.Nodes.TryFind arg with
                                    | Some { Kind = SemanticKind.FieldGet (receiver, field) } when field = fieldName ->
                                        match graph.Nodes.TryFind receiver with
                                        | Some { Kind = SemanticKind.VarRef (_, Some id) } -> id = formal
                                        | _ -> false
                                    | _ -> false
                                if forwarded && ([name; shortName; identity] |> List.exists (fun n -> descriptorMatches n fieldName fieldTy)) then
                                    Ok (Some (["public interface"] @ List.replicate ordinal "result" @ ["parameter"; fieldName]))
                                else Error ()
                            | _ ->
                                let directForwarded =
                                    TypeIdentity.ofType (applySubst formalTy) = TypeIdentity.ofType (applySubst ty) &&
                                    match graph.Nodes.TryFind arg with
                                    | Some { Kind = SemanticKind.VarRef (_, Some id) } -> id = formal
                                    | _ -> false
                                if directForwarded then Ok None else Error ())
                    if parameterOutcomes |> List.forall Result.isOk then
                        parameterOutcomes |> List.choose (function Ok (Some slot) -> Some slot | _ -> None) |> Set.ofList
                    else Set.empty
                | _ -> Set.empty
            | _ -> Set.empty
        | _ -> Set.empty
    let rec exposed seen participants path ty =
        let ty = applySubst ty

        if Types.tryGetNTUKind ty = Some NTUKind.NTUfnptr then
            [ path, participants ]
        else
            let identity = TypeIdentity.ofType ty

            if Set.contains identity seen then
                []
            else
                let seen = Set.add identity seen

                let child name =
                    exposed seen participants (path @ [ name ])

                match ty with
                | NativeType.TForall(_, body) -> exposed seen participants path body
                | NativeType.TFun(parameter, result) -> child "parameter" parameter @ child "result" result
                | NativeType.TByref(element, _)
                | NativeType.TNativePtr element
                | NativeType.TLazy element
                | NativeType.TSeq element
                | NativeType.TSeqEnumerator element
                | NativeType.TList element
                | NativeType.TSet element -> child "element" element
                | NativeType.TMap(key, value) -> child "key" key @ child "value" value
                | _ ->
                    match AggregateTypes.shape graph ty with
                    | Some(AggregateTypes.Shape.Record(declaration, fields)) ->
                        let participants = Set.union participants (Set.ofList (Option.toList declaration))

                        fields
                        |> List.collect (fun (name, field) -> exposed seen participants (path @ [ name ]) field)
                    | Some(AggregateTypes.Shape.Union(declaration, cases)) ->
                        let participants = Set.union participants (Set.ofList (Option.toList declaration))

                        cases
                        |> List.collect (fun (case, fields) ->
                            fields
                            |> List.mapi (fun ordinal (name, field) ->
                                exposed seen participants (path @ [ case; Option.defaultValue ($"Item{ordinal + 1}") name ]) field)
                            |> List.concat)
                    | None ->
                        // Only collection element positions carry values here.
                        // Opaque phantom arguments, such as CHandle<'Tag>, do not.
                        match ty, Types.tryGetNTUKind ty with
                        | NativeType.TApp(_, [ element ]),
                          Some(NTUKind.NTUarray | NTUKind.NTUborrowedview | NTUKind.NTUlazy | NTUKind.NTUseq | NTUKind.NTUlist | NTUKind.NTUset) ->
                            child "element" element
                        | NativeType.TApp(_, [ key; value ]), Some NTUKind.NTUmap -> child "key" key @ child "value" value
                        | _ -> []

    graph.DeclarationRoots
    |> List.choose (fun (id, root) -> if root = DeclRoot.LibraryExport then Some id else None)
    |> List.distinct
    |> List.collect (fun id ->
        match graph.Nodes.TryFind id with
        | None ->
            [
                {
                    Kind = WitnessProjectionFailureKind.Settlement
                    Occurrence = Some id
                    Participants = Set.singleton id
                    Reason = "A retained library declaration is absent from the current source graph."
                }
            ]
        | Some node ->
            let authorized = authorizedPaths node
            exposed Set.empty (Set.singleton id) [ "public interface" ] node.Type
            |> List.filter (fun (path, _) -> not (Set.contains path authorized))
            |> List.map (fun (path, participants) ->
                let location = String.concat "." path

                {
                    Kind = WitnessProjectionFailureKind.LibraryNativeInterfaceLoading
                    Occurrence = Some id
                    Participants = participants
                    Reason =
                        $"Library native callable exposure at {location} has no admitted host loading contract (L3); source retention and ProgramImageCodeLifetime do not establish host loading."
                }))

let private project graph =
    let exported = exportedInterfaceFailures graph
    let ordinary = OrdinaryDemand.projectValidated graph
    // Callable component positions depend on this exact validated omission
    // proof. Reading an older held mask would publish inconsistent domains.
    let callable =
        match ordinary with
        | Ok demand -> CallableEmission.projectWithDemand graph demand
        | Error failures -> Error failures
    let storage = StorageWitness.project graph
    let boundary = BoundaryEmission.project graph
    let numeric = NumericPublication.project graph
    let memory = MemoryPublication.project graph
    let spatial = SpatialPublication.project graph
    match ordinary, callable, storage, boundary, numeric, memory, spatial with
    | Ok ordinary, Ok callable, Ok storage, Ok boundary, Ok numeric, Ok memory, Ok spatial when exported.IsEmpty ->
        Ok { Ordinary = ordinary; Callable = callable; Storage = storage; Boundary = boundary; Numeric = numeric; Memory = memory; Spatial = spatial }
    | _ ->
        let failures = function Ok _ -> [] | Error failures -> failures
        // Failed demand validation already owns its diagnostic; the dependent
        // callable domain cannot contribute an independent result in that case.
        let callableFailures = match ordinary with Ok _ -> failures callable | Error _ -> []
        Error(
            exported
            @ failures ordinary
            @ callableFailures
            @ failures storage
            @ failures boundary
            @ failures numeric
            @ failures memory
            @ failures spatial
        )

/// Preserve each typed failure's diagnostic meaning and source occurrence.
let diagnostics (graph: SemanticGraph) (failures: WitnessProjectionFailure list) : Diagnostics.Diagnostic list =
    failures |> List.map (fun failure ->
        let code =
            match failure.Kind with
            | WitnessProjectionFailureKind.Settlement -> "CCS8403"
            | WitnessProjectionFailureKind.LibraryNativeInterfaceLoading -> Codes.CCS8416_LibraryNativeInterfaceLoading
        ({ Severity = Diagnostics.NativeDiagnosticSeverity.Error; Code = code
           Message = "Source settlement is required before witnessing: " + failure.Reason
           Range = failure.Occurrence |> Option.bind graph.Nodes.TryFind |> Option.map _.Range |> Option.defaultValue Clef.Compiler.NativeTypedTree.NativeTypes.dummyRange
           RelatedNodes = Set.toList failure.Participants; Reachability = Diagnostics.ReachabilityContext.Reachable } : Diagnostics.Diagnostic))

/// A source edit retains premises for validation but cannot carry publication
/// into witnessing. The original graph retains its own published facts.
let invalidate (graph: SemanticGraph) =
    Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.invalidateWitness graph

let private materialized value =
    let held = lazy value
    held.Force() |> ignore
    held

/// Live CPU union operations require the placement owner's complete byte
/// representation. Resource-option reads retain their own value convention.
let internal unionLayoutFailures (graph: SemanticGraph) (scope: WitnessLiveScopePlan) =
    match graph.Platform with
    | Some platform when PlatformContext.substrateKind platform <> SubstrateKind.FPGA ->
        let resourceOptions =
            (PlatformResolution.readDescriptors graph).Resources
            |> List.map _.ResultType |> Set.ofList
        scope.Occurrences
        |> Map.toList
        |> List.choose (fun (id, occurrence) ->
            let node = occurrence.Body
            let unionType, isTag =
                match node.Kind with
                | SemanticKind.DUConstruct _ -> Some node.Type, false
                | SemanticKind.DUInitialize (destination, _, _, _) ->
                    graph.Nodes.TryFind destination |> Option.map _.Type, false
                | SemanticKind.DUGetTag (_, ty) -> Some ty, true
                | _ -> None, false
            unionType |> Option.bind (fun ty ->
                let reason =
                    if Placement.tryUnionTagBits graph ty |> Option.isNone then
                        Some "A live union operation requires a complete, representable source placement."
                    elif isTag && not (resourceOptions.Contains(TypeIdentity.ofType ty)) &&
                         (node.ValueRange |> Option.exists ValueRange.isNonNegative |> not) then
                        Some "A live union tag read requires its nonnegative source range."
                    else None
                reason |> Option.map (fun message ->
                    { Kind = WitnessProjectionFailureKind.Settlement
                      Occurrence = Some id
                      Participants = Set.singleton id
                      Reason = message })))
    | _ -> []

/// Complete source publication once. The graph returned here owns all current
/// projected facts and eager indices; it is the graph handed to witnessing.
let prepare (graph: SemanticGraph) : Result<SemanticGraph, WitnessProjectionFailure list> =
    match project graph with
    | Error failures -> Error failures
    | Ok projection ->
        match ProofDispatch.materialize graph with
        | Error failures -> Error failures
        | Ok dispatch ->
          match LiveScopes.projectWithEmission projection graph with
          | Error failures -> Error failures
          | Ok liveScope ->
            let preparedRows = PreparedRows.project graph
            let segmentation = WitnessSegmentation.project graph projection liveScope
            let liveRows = LiveRows.project graph projection liveScope preparedRows segmentation
            let publication =
                match unionLayoutFailures graph liveScope @ DeviceAccess.checkSelected graph liveRows.Codata.Mmio with
                | [] -> PublishedRows.project graph liveScope liveRows dispatch
                | failures -> Error failures
            match publication with
            | Error failures -> Error failures
            | Ok publishedRows ->
              let facts = {
                  graph.Codata.Value with OrdinaryDemand = projection.Ordinary
                                          WitnessEmission = Some projection
                                          WitnessSegmentation = Some segmentation
                                          WitnessLiveScope = Some liveScope
                                          WitnessPreparedRows = Some preparedRows
                                          WitnessLiveRows = Some liveRows
                                          WitnessPublishedRows = Some publishedRows
                                          ProofDispatch = Some dispatch }
              // Force semantic lazy computations under their source owner. A consumer
              // must not execute a deferred layout/index/classification computation.
              let settled = {
                  graph with
                      Types = materialized graph.Types.Value
                      ModuleClassifications = materialized graph.ModuleClassifications.Value
                      FieldRanges = materialized graph.FieldRanges.Value
                      ElementRanges = materialized graph.ElementRanges.Value
                      Layouts = materialized graph.Layouts.Value
                      Escaping = materialized graph.Escaping.Value
                      Codata = materialized facts
                      WitnessProvenance = None }
              Ok { settled with WitnessProvenance = Some { PreparedRoots = settled } }

/// The complete identity policy for prepared input roots. Keeping names next
/// to typed accessors lets the maintenance test check this policy against the
/// SemanticGraph record without adding reflection to passive publication.
let internal preparedRootIdentities : (string * (SemanticGraph -> obj | null)) list =
    [ "Nodes", (fun graph -> box graph.Nodes)
      "DeclarationRoots", (fun graph -> box graph.DeclarationRoots)
      "Modules", (fun graph -> box graph.Modules)
      "Types", (fun graph -> box graph.Types)
      "Platform", (fun graph -> box graph.Platform)
      "ModuleClassifications", (fun graph -> box graph.ModuleClassifications)
      "FieldRanges", (fun graph -> box graph.FieldRanges)
      "ElementRanges", (fun graph -> box graph.ElementRanges)
      "Layouts", (fun graph -> box graph.Layouts)
      "StaticStringPool", (fun graph -> box graph.StaticStringPool)
      "LiteralStorage", (fun graph -> box graph.LiteralStorage)
      "Escaping", (fun graph -> box graph.Escaping)
      "Codata", (fun graph -> box graph.Codata)
      "Edges", (fun graph -> box graph.Edges)
      "SequenceRangeProvenance", (fun graph -> box graph.SequenceRangeProvenance)
      // The prepared projection consumed this exact producer receipt. Equal
      // reissued facts still require source preparation, not passive rebasing.
      "RangeContextFacts", (fun graph -> box graph.RangeContextFacts) ]

/// This root supplies the retained inputs being compared. tryRead explicitly
/// requires it; prepare's retained graph intentionally has no self-reference.
let internal preparedRootExceptions =
    [ ("WitnessProvenance", "Required and opened by tryRead; its PreparedRoots are the identity comparison baseline.") ]

/// Compare only the retained input roots. This neither forces lazy source
/// computations nor reconstructs their premises. Every root participates,
/// including relation and declaration membership. Shared checker cells remain
/// a separate immutable-input requirement; this evidence does not freeze them
/// or identify the accepted source revision.
let private samePreparedRoots (prepared: SemanticGraph) (graph: SemanticGraph) =
    preparedRootIdentities |> List.forall (fun (_, read) ->
        obj.ReferenceEquals(read prepared, read graph))

let private isMaterialized (graph: SemanticGraph) =
    graph.Codata.IsValueCreated && graph.Types.IsValueCreated &&
    graph.ModuleClassifications.IsValueCreated && graph.FieldRanges.IsValueCreated &&
    graph.ElementRanges.IsValueCreated && graph.Layouts.IsValueCreated && graph.Escaping.IsValueCreated

/// Passive projection only. Do not force a deferred source computation, scan
/// source relations, infer a missing fact or consult process-global identity.
let tryRead (graph: SemanticGraph) =
    match graph.WitnessProvenance with
    | None -> Error "The current graph has no complete source witness projection."
    | Some provenance when not (samePreparedRoots provenance.PreparedRoots graph) ->
        Error "The current graph differs from its source witness projection input; source republication is required."
    | Some _ when not (isMaterialized graph) ->
        Error "The current graph has no materialized source witness projection."
    | Some _ ->
        match graph.Codata.Value.WitnessEmission with
        | Some _ when graph.Codata.Value.WitnessPreparedRows.IsNone ->
            Error "The current graph has no Baker-prepared foreign, demand and incidence rows."
        | Some _ when graph.Codata.Value.WitnessLiveRows.IsNone ->
            Error "The current graph has no Baker-selected live fact rows."
        | Some _ when graph.Codata.Value.WitnessPublishedRows.IsNone ->
            Error "The current graph has no Baker-frozen publication rows."
        | Some projection when graph.Codata.Value.WitnessLiveScope.IsSome -> Ok projection
        | Some _ -> Error "The current graph has no source-owned live occurrence scope."
        | None -> Error "The current graph has no complete source witness projection."

/// Validate an already prepared graph without altering its facts. Component
/// source fixtures and retained-input owners may use this source operation;
/// witness consumers never call it to repair a missing admission.
let admit (graph: SemanticGraph) : Result<unit, WitnessProjectionFailure list> =
    let facts = graph.Codata.Value
    // Dispatch retains incidence independently of the domain projections. Its
    // precise refusal must survive a broader domain freshness failure.
    match ProofDispatch.materialize graph with
    | Error failures -> Error failures
    | Ok current when facts.ProofDispatch |> Option.exists (fun held -> ProofDispatch.matches held current) |> not ->
        Error [{ Kind = WitnessProjectionFailureKind.Settlement; Occurrence = None; Participants = Set.empty
                 Reason = "Proof dispatch differs from the current source snapshot." }]
    | Ok dispatch ->
      match project graph with
      | Error failures -> Error failures
      | Ok projection ->
        if facts.OrdinaryDemand <> projection.Ordinary || facts.WitnessEmission <> Some projection then
            Error [{ Kind = WitnessProjectionFailureKind.Settlement; Occurrence = None; Participants = Set.empty
                     Reason = "Witness projection differs from the current source snapshot." }]
        elif
            (match LiveScopes.projectWithEmission projection graph with
             | Ok liveScope -> facts.WitnessSegmentation = Some (WitnessSegmentation.project graph projection liveScope)
             | Error _ -> false) |> not then
            Error [{ Kind = WitnessProjectionFailureKind.Settlement; Occurrence = None; Participants = Set.empty
                     Reason = "Witness segmentation differs from the current source snapshot." }]
        elif
            (match LiveScopes.projectWithEmission projection graph, facts.WitnessLiveScope with
             | Ok current, Some held -> LiveScopes.matches held current
             | _ -> false) |> not then
            Error [{ Kind = WitnessProjectionFailureKind.Settlement; Occurrence = None; Participants = Set.empty
                     Reason = "Live occurrence scope differs from the current source snapshot." }]
        elif
            (facts.WitnessPreparedRows |> Option.exists (fun held -> PreparedRows.matches held (PreparedRows.project graph))) |> not then
            Error [{ Kind = WitnessProjectionFailureKind.Settlement; Occurrence = None; Participants = Set.empty
                     Reason = "Baker-prepared foreign, demand and incidence rows differ from the current source snapshot." }]
        elif
            (match facts.WitnessLiveScope, facts.WitnessPreparedRows, facts.WitnessSegmentation, facts.WitnessLiveRows with
             | Some scope, Some prepared, Some segmentation, Some held ->
                 LiveRows.matches held (LiveRows.project graph projection scope prepared segmentation)
             | _ -> false) |> not then
            Error [{ Kind = WitnessProjectionFailureKind.Settlement; Occurrence = None; Participants = Set.empty
                     Reason = "Baker-selected live fact rows differ from the current source snapshot." }]
        else
            match unionLayoutFailures graph facts.WitnessLiveScope.Value @ DeviceAccess.checkSelected graph facts.WitnessLiveRows.Value.Codata.Mmio with
            | _ :: _ as failures -> Error failures
            | [] when not (isMaterialized graph) ->
                Error [{ Kind = WitnessProjectionFailureKind.Settlement; Occurrence = None; Participants = Set.empty
                         Reason = "Witness input contains deferred source computations." }]
            | [] ->
                if
                    (match facts.WitnessLiveScope, facts.WitnessLiveRows, facts.WitnessPublishedRows with
                     | Some scope, Some rows, Some held ->
                         match PublishedRows.project graph scope rows dispatch with
                         | Ok current -> PublishedRows.matches held current
                         | Error _ -> false
                     | _ -> false) |> not then
                    Error [{ Kind = WitnessProjectionFailureKind.Settlement; Occurrence = None; Participants = Set.empty
                             Reason = "Baker-frozen publication rows differ from the current source snapshot." }]
                else Ok ()

let tryOrdinary graph = tryRead graph |> Result.map _.Ordinary
let tryCallable graph = tryRead graph |> Result.map _.Callable
let tryStorage graph = tryRead graph |> Result.map _.Storage
let tryBoundary graph = tryRead graph |> Result.map _.Boundary
let tryNumeric graph = tryRead graph |> Result.map _.Numeric
let tryMemory graph = tryRead graph |> Result.map _.Memory
let trySpatial graph = tryRead graph |> Result.map _.Spatial
