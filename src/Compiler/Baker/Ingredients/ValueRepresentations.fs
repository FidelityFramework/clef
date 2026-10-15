// SPDX-License-Identifier: MIT
/// Source-owned closure of the settled representation inventory. Native type
/// substitution and declaration lookup end here, before witness publication.
module Clef.Compiler.Baker.Ingredients.ValueRepresentations

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph

module Identity = Clef.Compiler.NativeTypedTree.TypeIdentities
module CallableTypes = Clef.Compiler.Baker.Ingredients.CallableAggregateTypes

let settle (graph: SemanticGraph) (carriers: ScalarCarrier list)
           (elements: Map<NodeId, SettledSlot>) (elementTypes: Map<TypeIdentity, SettledSlot>)
           (declared: Map<NTUKind, SettledSlot>) =
    let scalar slot = Ok(ValueRepresentation.Scalar slot)
    let byte = ValueRepresentation.Scalar(SettledSlot.Integer(8, None))
    let bytes count = Ok(ValueRepresentation.Buffer(Some count, byte))
    let fabric = graph.Platform |> Option.exists (fun p -> PlatformContext.substrateKind p = SubstrateKind.FPGA)
    let pointerBytes = graph.Platform |> Option.bind (fun p -> PlatformContext.tryWidth p "Pointer" |> Result.toOption)
                       |> Option.bind (fun bits -> if bits > 0 && bits % 8 = 0 then Some(bits / 8) else None)
    let resources = (PlatformResolution.readDescriptors graph).Resources
    let resourceHandles = resources |> List.map _.HandleType |> Set.ofList
    let resourceOptions = resources |> List.map (fun row -> row.ResultType, row.HandleType) |> Map.ofList
    let mutable types = Map.empty<TypeIdentity, Result<ValueRepresentation, string>>
    let rec represent (visiting: Set<TypeIdentity>) (ty: NativeType) = representAt visiting (Identity.ofType ty) [] ty
    and representAt (visiting: Set<TypeIdentity>) (aggregateIdentity: TypeIdentity) (path: CallableAggregatePathStep list) (ty: NativeType) =
        let key = Identity.ofType ty
        match (if path.IsEmpty then types.TryFind key else None) with
        | Some found -> found
        | None when Set.contains key visiting -> Error "Recursive inline type has no finite settled value representation."
        | None ->
            let next = Set.add key visiting
            let recurse = represent next
            let componentValue (step: CallableAggregatePathStep) (fieldType: NativeType) =
                let fieldPath = path @ [step]
                match CallableTypes.callableKind fieldType with
                | Some _ ->
                    Placement.callableComponent graph aggregateIdentity fieldPath
                    |> Result.bind (fun placement ->
                        match graph.Codata.Value.CallableAggregateSlots.TryFind placement.Identity with
                        | Some slot when slot.SourceType = Identity.ofType fieldType ->
                            Ok(ValueRepresentation.CallableComponent(placement.Identity, placement.Data))
                        | _ -> Error "Callable component declaration path has a different instantiated source type (CCS8414).")
                | None ->
                    match CallableTypes.shape graph fieldType with
                    | Some _ -> representAt next aggregateIdentity fieldPath fieldType
                    | None -> recurse fieldType
            let record (fields: (string * NativeType) list) =
                match graph.Layouts.Value.TryFind key with
                | Some(SettledLayout.Record(placed, size, alignment)) when List.map fst fields = List.map (fun (field: SettledField) -> field.Name) placed ->
                    let representations = List.zip fields placed |> List.mapi (fun ordinal ((name, ty), (field: SettledField)) ->
                        let represented =
                            match field.Slot with
                            | SettledSlot.Integer _ | SettledSlot.Bool | SettledSlot.Char | SettledSlot.Real _ | SettledSlot.Unit -> scalar field.Slot
                            | _ -> componentValue (CallableAggregatePathStep.RecordField ordinal) ty
                        represented |> Result.map (fun value -> name, value))
                    match representations |> List.tryPick (function Error e -> Some e | _ -> None) with
                    | Some reason -> Error reason
                    | None ->
                        let placement =
                            match size, alignment with
                            | Some size, Some align when size >= 0 && align > 0 && (placed |> List.forall (fun f -> f.Offset.IsSome)) ->
                                Some(placed |> List.map (fun f -> f.Offset.Value), size, align)
                            | _ -> None
                        if not fabric && placement.IsNone then Error "Record has no complete source byte placement."
                        else Ok(ValueRepresentation.Record(representations |> List.choose (function Ok v -> Some v | _ -> None), placement))
                | Some _ -> Error "Record fields disagree with the exact settled layout."
                | None -> Error "Record has no source-settled layout."
            let union () =
                match graph.Layouts.Value.TryFind key with
                | Some(SettledLayout.Union(cases, payloadOffset, Some size, Some alignment)) when size > 0 && alignment > 0 ->
                    if resourceOptions.ContainsKey key then
                        let handleType = resourceOptions[key]
                        match cases, payloadOffset, Placement.handleSlot graph handleType with
                        | [("None", None);("Some", Some actual)], Some offset, Ok slot when actual = slot ->
                            Ok(ValueRepresentation.Union(["None", []; "Some", [ValueRepresentation.Scalar slot]], Some(offset, size, alignment)))
                        | _ -> Error "A resource Option requires its exact source cases, opaque handle slot and complete union placement."
                    elif fabric && (cases |> List.forall (snd >> Option.isNone)) then Ok(ValueRepresentation.Tag cases.Length)
                    elif fabric then Error "A payload union requires an admitted fabric representation."
                    else
                        let hasComponents =
                            graph.Codata.Value.CallableAggregateSlots.Values |> Seq.exists (fun slot ->
                                slot.AggregateType = aggregateIdentity && List.length slot.Path >= List.length path &&
                                List.take (List.length path) slot.Path = path)
                        if not hasComponents then bytes size
                        else
                            match CallableTypes.shape graph ty, payloadOffset with
                            | Some(CallableTypes.Shape.Union(_, sourceCases)), Some offset
                                when List.map fst sourceCases = List.map fst cases ->
                                let payloads = sourceCases |> List.mapi (fun caseOrdinal (name, fields) ->
                                    let fields = fields |> List.mapi (fun payloadOrdinal (_, fieldType) ->
                                        componentValue (CallableAggregatePathStep.UnionPayload(caseOrdinal, payloadOrdinal)) fieldType)
                                    name, fields)
                                match payloads |> List.collect snd |> List.tryPick (function Error reason -> Some reason | _ -> None) with
                                | Some reason -> Error reason
                                | None ->
                                    let represented = payloads |> List.map (fun (name, fields) -> name, fields |> List.choose (function Ok field -> Some field | _ -> None))
                                    Ok(ValueRepresentation.Union(represented, Some(offset, size, alignment)))
                            | _ -> Error "Callable union components lack their exact declared cases and payload placement (CCS8414)."
                | _ -> Error "Union has no complete source-settled representation."
            let nominal (tc: TypeConRef) args =
                if resourceHandles.Contains key then Placement.handleSlot graph key |> Result.bind scalar
                else
                    match tc.NTUKind with
                    | Some NTUKind.NTUunit -> scalar SettledSlot.Unit
                    | Some NTUKind.NTUbool -> scalar SettledSlot.Bool
                    | Some NTUKind.NTUchar -> scalar SettledSlot.Char
                    | Some(NTUKind.NTUint(NTUWidth.Resolved WidthDimension.Pointer))
                    | Some(NTUKind.NTUuint(NTUWidth.Resolved WidthDimension.Pointer))
                    | Some(NTUKind.NTUsize | NTUKind.NTUdiff | NTUKind.NTUptr)
                    | Some(NTUKind.NTUlist | NTUKind.NTUmap | NTUKind.NTUset) -> scalar(SettledSlot.Pointer 1)
                    | Some NTUKind.NTUfnptr -> Error "Native callable values require their source-settled entry and callable components (CCS8410)."
                    | Some(NTUKind.NTUint _ | NTUKind.NTUuint _ as kind) ->
                        declared.TryFind kind |> Option.map scalar
                        |> Option.defaultValue (Error "An integer representation requires its exact settled value occurrence.")
                    | Some(NTUKind.NTUfloat(NTUWidth.Fixed (32 | 64 as bits))) -> scalar(SettledSlot.Real bits)
                    | Some(NTUKind.NTUfloat _ | NTUKind.NTUposit _) -> Error "A real representation requires its exact source numeric format."
                    | Some NTUKind.NTUstring -> Ok(ValueRepresentation.Buffer(None, byte))
                    | Some NTUKind.NTUborrowedview ->
                        match BorrowedViews.layout graph ty, pointerBytes with
                        | Ok layout, Some word ->
                            Ok(ValueRepresentation.Record(
                                ["Data", ValueRepresentation.Buffer(None, ValueRepresentation.Scalar(SettledSlot.Integer(layout.ElementBits, None)))
                                 "RowStride", ValueRepresentation.Scalar(SettledSlot.Pointer 1)], Some([0; 5 * word], 6 * word, word)))
                        | Error reason, _ -> Error reason
                        | _ -> Error "Borrowed view has no declared pointer extent."
                    | _ ->
                        match tc.Name, args with
                        | ("byref" | "inref" | "outref" | "list"), _ -> scalar(SettledSlot.Pointer 1)
                        | ("array" | "Array"), [element] ->
                            match elementTypes.TryFind (Identity.ofType element) with
                            | Some slot -> Ok(ValueRepresentation.Buffer(None, ValueRepresentation.Scalar slot))
                            | None ->
                                recurse element |> Result.bind (function
                                    | ValueRepresentation.Record(_, Some(_, size, _)) -> Ok(ValueRepresentation.Buffer(None, ValueRepresentation.Buffer(Some size, byte)))
                                    | (ValueRepresentation.Scalar _ | ValueRepresentation.Buffer _) as element -> Ok(ValueRepresentation.Buffer(None, element))
                                    | _ -> Error "Array element has no settled physical storage representation.")
                        | ("option" | "voption"), [element] when fabric ->
                            recurse element |> Result.map (fun element -> ValueRepresentation.Record(["tag", ValueRepresentation.Scalar SettledSlot.Bool; "value", element], None))
                        | ("option" | "voption"), [_] | ("Result" | "result"), [_; _] -> union ()
                        | _ ->
                            match RecordInstances.tryFields ty graph with
                            | Some fields -> record fields
                            | None ->
                                match RecordInstances.tryUnionCases ty graph with
                                | Some _ -> union ()
                                | None ->
                                    match TypeLayout.baseLayout tc.Layout with
                                    | TypeLayout.PlatformWord -> scalar(SettledSlot.Pointer 1)
                                    | TypeLayout.NTUCompound 1 -> scalar(SettledSlot.Pointer 1)
                                    | TypeLayout.NTUCompound words when words > 1 -> Ok(ValueRepresentation.Buffer(Some words, ValueRepresentation.Scalar(SettledSlot.Pointer 1)))
                                    | TypeLayout.Inline(size, _) when size > 0 && tc.CaseCount = 0 -> scalar(SettledSlot.Integer(size * 8, None))
                                    | TypeLayout.Inline _ when tc.CaseCount > 0 ->
                                        if fabric then Ok(ValueRepresentation.Tag tc.CaseCount) else bytes 1
                                    | _ -> Error "Nominal type has no admitted source value representation."
            let result =
                match applySubst ty with
                | NativeType.TApp(tc, args) -> nominal tc args
                | NativeType.TNum(carrier, _) ->
                    match CarrierRef.tryConstructor carrier with
                    | Some tc -> nominal tc []
                    | None -> Error "Numeric carrier remains unresolved at source publication."
                | NativeType.TTuple(fields, _) -> record (fields |> List.mapi (fun index ty -> $"Item{index + 1}", ty))
                | NativeType.TAnon(fields, _) -> record fields
                | NativeType.TUnion _ -> union ()
                | NativeType.TByref _ | NativeType.TNativePtr _ | NativeType.TList _ | NativeType.TMap _ | NativeType.TSet _ -> scalar(SettledSlot.Pointer 1)
                | NativeType.TForall(_, body) -> recurse body
                | NativeType.TFun _ -> Error "Callable values require their separately published code and environment components."
                | NativeType.TLazy _ -> Error "Lazy values require their separately published thunk and environment components."
                | NativeType.TSeq _ | NativeType.TSeqEnumerator _ -> Error "Sequence values require their exact source occurrence and continuation contract."
                | NativeType.TVar _ -> Error "Type variable remains unresolved at source publication."
                | NativeType.TMeasure _ -> Error "A physical dimension is not a runtime value."
                | NativeType.TError reason -> Error reason
            if path.IsEmpty then types <- types.Add(key, result)
            result
    let scalarValues = carriers |> List.map (fun carrier -> carrier.Site, carrier) |> Map.ofList
    let codata = graph.Codata.Value
    let premises = Clef.Compiler.Baker.Ingredients.NumericValues.premises graph
    let occurrences = graph.Nodes |> Map.filter (fun id _ -> premises.ContainsKey id) |> Map.map (fun id node ->
        // Close every encountered native type under the source owner even when
        // its particular value has a more precise occurrence representation.
        let general = represent Set.empty node.Type
        if resourceHandles.Contains(Identity.ofType node.Type) then general
        else
            match CallableTypes.callableKind node.Type, scalarValues.TryFind id with
            | Some _, _ -> general
            | None, Some carrier -> scalar carrier.Slot
            | None, None ->
                match codata.LazyOrigins.TryFind id, codata.EnvironmentOrigins.TryFind id, codata.SequenceOrigins.TryFind id with
                | Some _, _, _ when (match applySubst node.Type with NativeType.TLazy _ -> true | _ -> false) -> general
                | Some owner, _, _ ->
                    match codata.LazyLayouts.TryFind owner with
                    | Some layout when layout.Bytes > 0 && layout.Alignment > 0 -> bytes layout.Bytes
                    | _ -> Error "Lazy environment has no complete source layout."
                | None, Some owner, _ ->
                    match codata.EnvironmentLayouts.TryFind owner with
                    | Some layout when layout.Bytes >= 0 && layout.Alignment > 0 -> bytes layout.Bytes
                    | _ -> Error "Closure environment has no complete source layout."
                | None, None, Some owner ->
                    match codata.ContinuationFrames.TryFind owner with
                    | Some frame when frame.Bytes > 0 -> bytes frame.Bytes
                    | _ -> Error "Sequence environment has no complete source layout."
                | _ ->
                    match elements.TryFind id with
                    | Some slot -> Ok(ValueRepresentation.Buffer(None, ValueRepresentation.Scalar slot))
                    | None -> general)
    occurrences, types
