// SPDX-License-Identifier: MIT
/// Source operation construction joins actual ordered operands, their held
/// carriers, exact result bounds and the selected platform declaration.
module Clef.Compiler.Baker.Recipes.NumericOperationRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph
open Clef.Compiler.Baker.Ingredients.Obligations
module Operations = Clef.Compiler.Baker.Ingredients.NumericOperations
module Numeric = Clef.Compiler.Baker.Ingredients.NumericValues

exception private MissingOperation of string
let private require condition message = if not condition then raise (MissingOperation message)
let private need message = function Some value -> value | None -> raise (MissingOperation message)
let private width = function
    | SettledSlot.Integer(bits, _) | SettledSlot.Real bits -> Some bits
    | SettledSlot.Bool -> Some 1 | SettledSlot.Char -> Some 32
    | _ -> None
let private bounds = function ValueRange.Bounded(lo, hi) when lo <= hi -> Some(lo, hi) | _ -> None
let private isIntegerSlot = function SettledSlot.Integer _ | SettledSlot.Bool | SettledSlot.Char -> true | _ -> false

let private adaptation consumer operand fromBits intoBits range =
    if fromBits = intoBits then None else
    Some { Consumer = consumer; Operand = operand; From = fromBits; To = intoBits
           Adapt = if fromBits > intoBits then MeetKind.Truncate
                   elif ValueRange.isNonNegative range then MeetKind.ExtendUnsigned else MeetKind.ExtendSigned }

let private integerSlot (graph: SemanticGraph) sourceCore joined minimumBits =
    match graph.Platform with
    | Some context when PlatformContext.substrateKind context = SubstrateKind.FPGA ->
        let bits = ValueRange.width joined |> need "The operation's integer range is unresolved on fabric." |> max minimumBits
        require (bits > 0) "The operation has no positive source-selected width."
        SettledSlot.Integer(bits, None), None, None
    | Some _ ->
        let core: PlatformResolution.DeclaredCore = sourceCore |> need "The operation requires a selected source core representation declaration."
        let family = if ValueRange.isNonNegative joined then "uint" else "int"
        let candidates =
            core.Representations |> List.filter (fun declaration ->
                let rep = declaration.Representation
                rep.Family = family && rep.Bits >= minimumBits && NumericRepresentation.isOffered rep &&
                (Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources.declaredRange rep |> Option.exists (fun capacity -> ValueRange.contains capacity joined)))
            |> List.sortBy (fun declaration -> declaration.Representation.Bits, declaration.Representation.Name)
        let selected = candidates |> List.tryHead |> need "No offered source representation covers the operation and every admitted input carrier."
        SettledSlot.Integer(selected.Representation.Bits, Some selected.Representation.Name), Some selected.Representation, Some selected.Node
    | None -> raise (MissingOperation "The required operation has no selected source platform.")

let private settleCore (graph: SemanticGraph) anchor (values: Map<NodeId, ScalarCarrier>) (runtime: Set<NodeId>) =
    let reading = PlatformResolution.read graph
    let core = if reading.Findings.IsEmpty then reading.Platform |> Option.bind _.Core else None
    let settleOne (node: SemanticNode) (callee: NodeId, kind: NumericOperationKind, actuals: NodeId list, identities: Set<NodeId>) =
        require (actuals.Length = Operations.arity kind) "The intrinsic operation does not have its complete ordered source operands."
        let result = values.TryFind node.Id |> need "The operation result lacks its source-settled scalar carrier."
        let inputTypes = actuals |> List.map (fun id -> Types.tryGetNTUKind graph.Nodes[id].Type)
        let inputCarriers = actuals |> List.map (fun id -> values.TryFind id)
        let allKinds kind = inputTypes |> List.forall ((=) (Some kind))
        let equality = kind = NumericOperationKind.Equal || kind = NumericOperationKind.NotEqual
        let baseParticipants = identities |> Set.union (Set.ofList actuals) |> Set.add node.Id |> Set.add anchor |> Set.union result.Participants
        let participants = inputCarriers |> List.choose id |> List.fold (fun participants carrier -> Set.union participants carrier.Participants) baseParticipants
        let scalarInput = lazy (inputCarriers |> List.map (need "An operation input lacks its source-settled scalar carrier."))
        let make form slot representation declaration range operands resultAdaptation bodies =
            let claims =
                Operations.associateBodies graph (callee, kind, actuals, identities) bodies
                |> need "The operation's concrete proof bodies do not match its required semantic roles."
            let participants = declaration |> Option.map (fun id -> Set.add id participants) |> Option.defaultValue participants
            let expansion = Elaboration.freshId ()
            let proofs = claims |> List.mapi (fun ordinal (role, body) ->
                let citizen = obligationNode node expansion
                                { Id = Operations.claimId node ordinal role
                                  Kind = "numeric-operation-proof"; Logic = "QF_LIA"
                                  Statement = "The exact source operation construction satisfies its capacity or definedness requirement."
                                  Source = fmtRange node.Range; Refs = []; Body = body } |> Numeric.markOwned
                let proof: NumericOperationProof = { Site = node.Id; Obligation = citizen.Id; Body = body; Participants = participants; Proven = Operations.proofOutcome body }
                citizen, proof)
            let operation: NumericOperationWitness =
                { Site = node.Id; Callee = callee; Kind = kind; Form = form; Operands = operands
                  OperationCarrier = slot; Representation = representation; Declaration = declaration
                  Result = result; ResultAdaptation = resultAdaptation; Range = range
                  Obligations = proofs |> List.map (fun (node, _) -> node.Id); Participants = participants }
            let enrichment = { NewNodes = proofs |> List.map fst; Annotated = []
                               NewEdges = Operations.operationRow operation :: (proofs |> List.collect (snd >> Operations.proofRows)) }
            operation, enrichment, proofs |> List.map snd
        if allKinds NTUKind.NTUunit || allKinds NTUKind.NTUptr then
            require equality "Unit values and opaque references admit equality, not numeric ordering."
            let form = if allKinds NTUKind.NTUunit then NumericOperationForm.Unit else NumericOperationForm.OpaqueReference
            make form (Some(if form = NumericOperationForm.Unit then SettledSlot.Unit else SettledSlot.Pointer 1)) None None None
                 (actuals |> List.map (fun id -> { Actual = id; Carrier = None; Adaptation = None })) None []
        elif allKinds NTUKind.NTUstring then
            raise (MissingOperation "String equality requires its source-owned content comparison construction; an invented foreign memcmp is not that contract.")
        elif scalarInput.Value |> List.forall (fun carrier -> isIntegerSlot carrier.Slot) then
            let scalarInput = scalarInput.Value
            let isComparison = Operations.comparison kind
            require (if isComparison || kind = NumericOperationKind.LogicalNot then result.Slot = SettledSlot.Bool else isIntegerSlot result.Slot)
                    "The operation's checked result carrier is incompatible with its source operator."
            let ranges = scalarInput |> List.map _.Range
            let joined = (if isComparison then ranges else result.Range :: ranges) |> List.fold ValueRange.join ValueRange.Empty
            let lo, hi = bounds joined |> need "The operation lacks a finite established enclosure for its inputs and intermediate result."
            let scalarBits = scalarInput |> List.map (fun carrier -> width carrier.Slot |> need "The input has no scalar width.")
            let minimum = (if isComparison then scalarBits else (width result.Slot |> need "The result has no scalar width.") :: scalarBits) |> List.max
            let isBoolean = scalarInput |> List.forall (fun carrier -> carrier.Slot = SettledSlot.Bool)
            let isCharacter = scalarInput |> List.forall (fun carrier -> carrier.Slot = SettledSlot.Char)
            let slot, representation, declaration =
                if isBoolean then
                    require (isComparison || kind = NumericOperationKind.LogicalNot) "Boolean arithmetic is not an admitted numeric operation."
                    SettledSlot.Bool, None, None
                elif isCharacter then
                    require isComparison "Character arithmetic requires its own source construction."
                    SettledSlot.Char, None, None
                else integerSlot graph core joined minimum
            let bits = width slot |> need "The operation has no settled scalar carrier."
            let operands = List.zip actuals scalarInput |> List.map (fun (id, carrier) ->
                { Actual = id; Carrier = Some carrier; Adaptation = adaptation node.Id id (width carrier.Slot |> Option.get) bits carrier.Range })
            let resultAdaptation = if isComparison then None else adaptation node.Id node.Id bits (width result.Slot |> Option.get) result.Range
            let capacity =
                match representation with
                | Some rep -> Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources.declaredRange rep |> need "The declared operation representation has no finite capacity."
                | None -> if ValueRange.isNonNegative joined then ValueRange.unsignedOf bits else ValueRange.twosComplement bits
            let minimum, maximum = bounds capacity |> need "The operation carrier's capacity is not finite."
            let coverage = ObligationBody.IntegerRepresentationCoverage(lo, hi, minimum, maximum)
            let preconditions =
                match kind, scalarInput with
                | (NumericOperationKind.Divide | NumericOperationKind.Remainder), [_; divisor] ->
                    let lower, upper = bounds divisor.Range |> need "The divisor has no established finite range."
                    [ObligationBody.IntegerDivisorNonzero(lower, upper)]
                | (NumericOperationKind.ShiftLeft | NumericOperationKind.ShiftRight), [_; count] ->
                    let lower, upper = bounds count.Range |> need "The shift count has no established finite range."
                    [ObligationBody.IntegerShiftCount(lower, upper, bits)]
                | _ -> []
            let form = if isBoolean then NumericOperationForm.Boolean else NumericOperationForm.Integer(not(ValueRange.isNonNegative joined))
            make form (Some slot) representation declaration (Some joined) operands resultAdaptation (coverage :: preconditions)
        elif Operations.comparison kind && (scalarInput.Value |> List.forall (fun carrier -> match carrier.Slot with SettledSlot.Real _ -> true | _ -> false)) then
            // Comparing two already settled IEEE operands has no real-valued
            // intermediate or rounding adaptation. The selected source format
            // is still required; a width alone cannot authorize IEEE semantics.
            let inputs = scalarInput.Value
            require (result.Slot = SettledSlot.Bool) "A real comparison requires its source Boolean result."
            require (inputTypes |> List.forall (function Some(NTUKind.NTUfloat _) -> true | _ -> false))
                "A real comparison requires IEEE source carriers; posit and fixed-point comparisons need their own construction."
            let slot = inputs.Head.Slot
            let bits = width slot |> Option.get
            require ((bits = 32 || bits = 64) && (inputs |> List.forall (fun carrier -> carrier.Slot = slot)))
                "A real comparison requires identical settled binary32 or binary64 operands; format conversion needs its own fidelity contract."
            let core = core |> need "A real comparison requires its source core representation declaration."
            let declared =
                match core.Representations |> List.filter (fun declaration ->
                    let representation = declaration.Representation
                    representation.Family = "ieee" && representation.Bits = bits && NumericRepresentation.isOffered representation) with
                | [declaration] -> declaration
                | _ -> raise (MissingOperation "A real comparison requires one exact offered IEEE representation declaration for its settled operands.")
            let operands = List.zip actuals inputs |> List.map (fun (id, carrier) -> { Actual = id; Carrier = Some carrier; Adaptation = None })
            make NumericOperationForm.Real (Some slot) (Some declared.Representation) (Some declared.Node) None operands None []
        elif scalarInput.Value |> List.forall (fun carrier -> match carrier.Slot with SettledSlot.Real _ -> true | _ -> false) then
            let reason = "The real operation requires its exact source format, intermediate capacity and arithmetic fidelity contract before witnessing."
            let inputs = scalarInput.Value
            require (Operations.realArithmetic kind && inputs.Length = Operations.arity kind &&
                     (inputTypes |> List.forall (function Some(NTUKind.NTUfloat _) -> true | _ -> false)) &&
                     (match Types.tryGetNTUKind node.Type with Some(NTUKind.NTUfloat _) -> true | _ -> false)) reason
            let bits = match result.Slot with SettledSlot.Real bits when bits = 32 || bits = 64 -> bits | _ -> raise (MissingOperation reason)
            require (inputs |> List.forall (fun carrier -> carrier.Slot = result.Slot)) reason
            let core = core |> need reason
            let declared =
                match core.Representations |> List.filter (fun declaration ->
                    let representation = declaration.Representation
                    representation.Family = "ieee" && representation.Bits = bits && NumericRepresentation.isOffered representation &&
                    not (System.String.IsNullOrWhiteSpace representation.Boundary) &&
                    not (System.String.IsNullOrWhiteSpace representation.MinMagnitude) &&
                    not (System.String.IsNullOrWhiteSpace representation.MaxMagnitude)) with
                | [declared] -> declared
                | _ -> raise (MissingOperation reason)
            let operands = List.zip actuals inputs |> List.map (fun (id, carrier) -> { Actual = id; Carrier = Some carrier; Adaptation = None })
            make NumericOperationForm.Real (Some result.Slot) (Some declared.Representation) (Some declared.Node) None operands None []
        else
            raise (MissingOperation "The real operation requires its exact source format, intermediate capacity and arithmetic fidelity contract before witnessing.")
    graph.Nodes |> Map.fold (fun (enrichment, operations, unresolved, required, proofs) id node ->
        if not(runtime.Contains id) then enrichment, operations, unresolved, required, proofs else
        match Operations.operation graph node with
        | None -> enrichment, operations, unresolved, required, proofs
        | Some recipe ->
            let required = Set.add id required
            try
                let operation, added, ownProofs = settleOne node recipe
                let unresolved = if ownProofs |> List.forall _.Proven then unresolved else Map.add id "The operation's capacity or definedness obligation is refuted under its retained source ranges." unresolved
                Enrichment.combine enrichment added, operation :: operations, unresolved, required, ownProofs @ proofs
            with MissingOperation reason ->
                let expansion = Elaboration.freshId ()
                let pending = Operations.obligationRoles graph recipe |> List.mapi (fun ordinal role ->
                    obligationNode node expansion
                        { Id = Operations.claimId node ordinal role; Kind = "numeric-operation-proof"; Logic = "QF_LIA"
                          Statement = "The exact source operation construction satisfies its capacity or definedness requirement."
                          Source = fmtRange node.Range; Refs = []; Body = ObligationBody.Pending [reason] } |> Numeric.markOwned)
                let own = { NewNodes = pending; Annotated = []; NewEdges = pending |> List.map (constrains [id; anchor]) }
                Enrichment.combine enrichment own, operations, Map.add id reason unresolved, required, proofs)
        (Enrichment.empty, [], Map.empty, Set.empty, [])

let settle graph anchor values runtime =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> settleCore graph anchor values runtime)
