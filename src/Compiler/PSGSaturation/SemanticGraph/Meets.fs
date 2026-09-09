// Copyright (c) 2025-2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Meets: every place a value meets a slot held at another width (Dimensional_Range_Design.md
/// §3.1, §8.3; rulings 1 and 3). A meet is an extension by the sign of the operand's range where
/// the slot is wider, or a truncation where a refined read is narrower than its cell (lossless
/// by construction; the truncation carries the refined range as its obligation). Both widths are
/// reads of the graph's own selection (`RangeAnalysis.heldWidth`, the settled layouts, the
/// element ranges, the declared Register width); nothing is decided here, and the value a meet
/// produces is emission's to name. The fabric leg has no meets here: its harmonisations are the
/// per-pattern extensions of the CS-10 rules, and it reads no Register width.
///
/// The derivation table, by consumer kind (the operand in order):
///   Application, direct call to a lambda    each argument -> the parameter node's width; the
///                                             result read from the callee's body width to the
///                                             call node's own (keyed with the call as operand)
///   Application, through a value / to an    each argument -> the declared Register width (the
///     escaping lambda, and a closure call     value-call boundary, ruling 1)
///   Application, the syscall ABI             the descriptor -> the Register width; Array.blit's
///     (Sys.write, read, readline)              indices likewise
///   Application, Array.set / Array.create    the value -> the element's settled width
///   Set / Binding                            the value -> the binding or cell's held width
///   RecordExpr / TupleExpr                   each field value -> the field's settled representation
///   IfThenElse / CaseElimination / Match     each arm's value -> the join's width (the node's)
///   Lambda (the return, `returns`)           the body's last value -> the body node's width
///   VarRef / FieldGet / TupleGet /           the slot's width -> the read's width (ruling 3),
///     IndexGet / Array.get / DUEliminate       keyed with the consumer as its own operand
///   IndexSet / ArrayExpr                     each value -> the element's settled width
///   DUConstruct / Option.Some                the payload -> the payload slot's width
module Clef.Compiler.PSGSaturation.SemanticGraph.Meets

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core

type private Ctx = { Graph: SemanticGraph; Word: int option; Curry: CurryInfo }

let private isWordInteger (kind: NTUKind) : bool =
    match kind with
    | NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register) | NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Register)
    | NTUKind.NTUint (NTUWidth.Fixed _) | NTUKind.NTUuint (NTUWidth.Fixed _) -> true
    | _ -> false

/// The width a word-integer node is held at; None for any other node.
let private nodeWidth (graph: SemanticGraph) (nodeId: NodeId) : int option =
    match SemanticGraph.tryGetNode nodeId graph with
    | Some node when Types.tryGetNTUKind node.Type |> Option.exists isWordInteger -> RangeAnalysis.heldWidth graph nodeId
    | _ -> None

let private layoutKey (ty: NativeType) : string = formatType (applySubst ty)

/// The settled layout of an aggregate type: a record or union by its constructor's name, a
/// tuple, an option or a Result by its rendered form.
let private settledLayout (graph: SemanticGraph) (ty: NativeType) : SettledLayout option =
    match applySubst ty with
    | NativeType.TApp (tycon, _) as t when tycon.Name = "option" || tycon.Name = "voption" || tycon.Name = "Result" || tycon.Name = "result" ->
        Map.tryFind (layoutKey t) graph.Layouts.Value
    | NativeType.TApp (tycon, _) as t ->
        match Map.tryFind tycon.Name graph.Layouts.Value with
        | Some layout -> Some layout
        | None -> Map.tryFind (layoutKey t) graph.Layouts.Value
    | NativeType.TUnion (tycon, _) -> Map.tryFind tycon.Name graph.Layouts.Value
    | t -> Map.tryFind (layoutKey t) graph.Layouts.Value

/// The width an array's word-integer elements are held at.
let private elementWidth (graph: SemanticGraph) (elemTy: NativeType) : int =
    let range = Map.tryFind (layoutKey elemTy) graph.ElementRanges.Value |> Option.defaultValue ValueRange.Unbounded
    match RangeAnalysis.heldWidthOf graph range with
    | Some bits -> bits
    | None -> failwithf "Meets: the element type %s has the range %s, which has no width on this substrate (CCS8011)" (layoutKey elemTy) (ValueRange.render range)

/// The last value a node evaluates to, through a block's last child and an annotation.
let rec private lastValueOf (graph: SemanticGraph) (id: NodeId) : NodeId =
    match SemanticGraph.tryGetNode id graph with
    | Some { Kind = SemanticKind.Sequential ids } ->
        match List.tryLast ids with
        | Some last -> lastValueOf graph last
        | None -> id
    | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> lastValueOf graph inner
    | _ -> id

let private functionNodeOf (graph: SemanticGraph) (funcId: NodeId) : SemanticNode option =
    match SemanticGraph.tryGetNode funcId graph with
    | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } -> SemanticGraph.tryGetNode inner graph
    | other -> other

let private lambdaOfBinding (graph: SemanticGraph) (bindingId: NodeId) : SemanticNode option =
    match SemanticGraph.tryGetNode bindingId graph with
    | Some ({ Kind = SemanticKind.Binding _ } as binding) ->
        binding.Children |> List.tryPick (fun childId ->
            match SemanticGraph.tryGetNode childId graph with
            | Some ({ Kind = SemanticKind.Lambda _ } as l) -> Some l
            | Some { Kind = SemanticKind.TypeAnnotation (inner, _) } ->
                match SemanticGraph.tryGetNode inner graph with
                | Some ({ Kind = SemanticKind.Lambda _ } as l) -> Some l
                | _ -> None
            | _ -> None)
    | _ -> None

/// The meet that brings `operand` from `from` bits to `target` bits, if they differ.
let private meet (graph: SemanticGraph) (consumer: NodeId) (operand: NodeId) (from: int) (target: int) : Meet option =
    if from = target then None
    elif from < target then
        let sign =
            match SemanticGraph.tryGetNode operand graph |> Option.bind (fun n -> n.ValueRange) with
            | Some r when ValueRange.isNonNegative r -> MeetKind.ExtendUnsigned
            | Some _ -> MeetKind.ExtendSigned
            | None -> failwithf "Meets: node %d is extended to a wider slot but has no analysed range to read the extension's sign from" (NodeId.value operand)
        Some { Consumer = consumer; Operand = operand; From = from; To = target; Adapt = sign }
    else Some { Consumer = consumer; Operand = operand; From = from; To = target; Adapt = MeetKind.Truncate }

/// A value node into a slot of the given width: read at its last value.
let private meetInto (graph: SemanticGraph) (consumer: NodeId) (valueId: NodeId) (slot: int option) : Meet option =
    let valueId = lastValueOf graph valueId
    match nodeWidth graph valueId, slot with
    | Some from, Some target -> meet graph consumer valueId from target
    | _ -> None

let private fieldSlotWidth (graph: SemanticGraph) (recordTy: NativeType) (field: string) : int option =
    match settledLayout graph recordTy with
    | Some (SettledLayout.Record (fields, _, _)) ->
        fields |> List.tryFind (fun f -> f.Name = field) |> Option.bind (fun f ->
            match f.Slot with
            | SettledSlot.Integer (bits, _) -> Some bits
            | _ -> None)
    | _ -> None

let private payloadSlotWidth (graph: SemanticGraph) (unionTy: NativeType) (caseIndex: int) : int option =
    match settledLayout graph unionTy with
    | Some (SettledLayout.Union (cases, _, _, _)) ->
        List.tryItem caseIndex cases |> Option.bind snd |> Option.bind (fun slot ->
            match slot with
            | SettledSlot.Integer (bits, _) -> Some bits
            | _ -> None)
    | _ -> None

let private elementSlotWidth (graph: SemanticGraph) (arrayId: NodeId) : int option =
    match SemanticGraph.tryGetNode arrayId graph |> Option.map (fun n -> applySubst n.Type) with
    | Some (NativeType.TApp (tycon, [ elemTy ])) when tycon.Name = "array" || tycon.Name = "Array" ->
        if Types.tryGetNTUKind elemTy |> Option.exists isWordInteger then Some (elementWidth graph elemTy) else None
    | _ -> None

/// A direct call's result read from the callee's body width to the call node's own.
let private callResultMeet (graph: SemanticGraph) (node: SemanticNode) (lambda: SemanticNode) : Meet list =
    match lambda.Kind with
    | SemanticKind.Lambda (_, bodyId, _, _, _) ->
        match nodeWidth graph bodyId, nodeWidth graph node.Id with
        | Some from, Some target -> Option.toList (meet graph node.Id node.Id from target)
        | _ -> []
    | _ -> []

let private applicationMeets (ctx: Ctx) (node: SemanticNode) (funcId: NodeId) (args: NodeId list) : Meet list =
    let graph = ctx.Graph
    let toWord (argId: NodeId) = meetInto graph node.Id argId ctx.Word
    let toParameters (lambda: SemanticNode) (parameters: (string * NativeType * NodeId) list) (args: NodeId list) =
        let n = min parameters.Length args.Length
        (List.zip (List.truncate n parameters) (List.truncate n args)
         |> List.choose (fun ((_, _, paramId), argId) -> meetInto graph node.Id argId (nodeWidth graph paramId)))
        @ callResultMeet graph node lambda
    match functionNodeOf graph funcId with
    | Some { Kind = SemanticKind.Intrinsic info } ->
        match info.Module, info.Operation, args with
        | IntrinsicModule.FnPtr, "invoke", pointer :: values ->
            let rec parameters ty =
                match applySubst ty with
                | NativeType.TFun (arg, rest) -> arg :: parameters rest
                | _ -> []
            match SemanticGraph.tryGetNode pointer graph |> Option.map (fun p -> applySubst p.Type) with
            | Some (NativeType.TApp (tc, [signature])) when tc.NTUKind = Some NTUKind.NTUfnptr ->
                let slots = parameters signature
                if slots.Length <> values.Length then [] // FunctionPointers reports incomplete calls.
                else
                    let callback = CallbackDeclarations.forPointer graph pointer
                    List.zip slots values
                    |> List.mapi (fun index (slot, value) ->
                        let declared = callback |> Option.bind (fun c -> List.tryItem index c.Function.Parameters) |> Option.bind snd
                        match declared with
                        | Some parameter -> meetInto graph node.Id value (Some parameter.Bits)
                        | None ->
                            match Types.tryGetNTUKind slot with
                            | Some (NTUKind.NTUint (NTUWidth.Resolved WidthDimension.Register))
                            | Some (NTUKind.NTUuint (NTUWidth.Resolved WidthDimension.Register)) -> toWord value
                            | Some (NTUKind.NTUint (NTUWidth.Fixed bits))
                            | Some (NTUKind.NTUuint (NTUWidth.Fixed bits)) -> meetInto graph node.Id value (Some bits)
                            | _ -> None)
                    |> List.choose id
            | _ -> []
        | IntrinsicModule.Sys, ("write" | "read" | "readline"), fd :: _ -> Option.toList (toWord fd)
        | IntrinsicModule.Array, "set", [ arr; _; value ] -> Option.toList (meetInto graph node.Id value (elementSlotWidth graph arr))
        | IntrinsicModule.Array, "create", [ _; seed ] -> Option.toList (meetInto graph node.Id seed (elementSlotWidth graph node.Id))
        | IntrinsicModule.Array, "blit", [ _; srcIdx; _; dstIdx; count ] -> [ srcIdx; dstIdx; count ] |> List.choose toWord
        | _ -> []
    | Some funcNode ->
        match Map.tryFind node.Id ctx.Curry.SaturatedCalls with
        | Some info ->
            match lambdaOfBinding graph info.TargetBindingId with
            | Some ({ Kind = SemanticKind.Lambda (parameters, _, _, _, _) } as lambda) -> toParameters lambda parameters info.AllArgNodes
            | _ -> info.AllArgNodes |> List.choose toWord
        | None when Map.containsKey node.Id ctx.Curry.PartialApplications -> []
        | None ->
            match funcNode.Kind with
            | SemanticKind.VarRef (_, Some defId) ->
                match lambdaOfBinding graph defId with
                | Some ({ Kind = SemanticKind.Lambda (parameters, _, _, _, _) } as lambda) when args.Length <= parameters.Length ->
                    toParameters lambda parameters args
                | _ -> args |> List.choose toWord
            | SemanticKind.Lambda (parameters, _, _, _, _) when args.Length <= parameters.Length -> toParameters funcNode parameters args
            | _ -> args |> List.choose toWord
    | None -> []

/// The read of a slot into a node held at another width, keyed with the node as its own operand.
let private readMeet (graph: SemanticGraph) (node: SemanticNode) (slot: int option) : Meet list =
    match slot, nodeWidth graph node.Id with
    | Some from, Some target -> Option.toList (meet graph node.Id node.Id from target)
    | _ -> []

/// Floating fields at a foreign representation boundary retain their declared
/// storage precision; source float values convert at construction and readback.
let private realWidth (graph: SemanticGraph) (node: SemanticNode) =
    match Types.tryGetNTUKind node.Type with
    | Some (NTUKind.NTUfloat (NTUWidth.Fixed bits)) -> Some bits
    | Some (NTUKind.NTUfloat (NTUWidth.Resolved dim)) ->
        graph.Platform |> Option.bind (fun p -> PlatformContext.tryWidth p (WidthDimension.name dim) |> Result.toOption)
    | _ -> None

let private realFieldWidth graph recordTy field =
    match settledLayout graph recordTy with
    | Some (SettledLayout.Record (fields, _, _)) -> fields |> List.tryPick (fun f ->
        match f.Name = field, f.Slot with true, SettledSlot.Real bits -> Some bits | _ -> None)
    | _ -> None

let private realMeet consumer operand fromWidth toWidth =
    match fromWidth, toWidth with
    | Some a, Some b when a <> b -> Some { Consumer = consumer; Operand = operand; From = a; To = b; Adapt = if a < b then MeetKind.ExtendFloat else MeetKind.TruncateFloat }
    | _ -> None

let private nodeMeets (ctx: Ctx) (node: SemanticNode) : Meet list =
    let graph = ctx.Graph
    let into valueId slot = meetInto graph node.Id valueId slot
    match node.Kind with
    | SemanticKind.Application (funcId, args) ->
        applicationMeets ctx node funcId args
        @ (match args, functionNodeOf graph funcId with
           | [ arr; _ ], Some { Kind = SemanticKind.Intrinsic { Module = IntrinsicModule.Array; Operation = "get" } } ->
               readMeet graph node (elementSlotWidth graph arr)
           | _ -> [])
    | SemanticKind.Intrinsic { Module = IntrinsicModule.Option; Operation = "Some" } ->
        match node.Children with
        | [ payloadId ] -> Option.toList (into payloadId (payloadSlotWidth graph node.Type 1))
        | _ -> []
    | SemanticKind.DUConstruct (_, caseIndex, Some payloadId, _) -> Option.toList (into payloadId (payloadSlotWidth graph node.Type caseIndex))
    | SemanticKind.Set (targetId, valueId) ->
        match SemanticGraph.tryGetNode targetId graph with
        | Some { Kind = SemanticKind.VarRef (_, Some defId) } -> Option.toList (into valueId (nodeWidth graph defId))
        | _ -> []
    | SemanticKind.Binding _ ->
        // An immutable alias can select a narrower range than its value's ABI
        // carrier (for example a closure call returns a Register-sized zero).
        // BindingWitness consumes this meet before later references read the
        // binding's held width, just as a mutable initializer meets its cell.
        match node.Children with
        | [ valueId ] -> Option.toList (into valueId (nodeWidth graph node.Id))
        | _ -> []
    | SemanticKind.RecordExpr (fields, _) ->
        fields |> List.choose (fun (field, valueId) ->
            match into valueId (fieldSlotWidth graph node.Type field) with
            | Some m -> Some m
            | None ->
                let value = lastValueOf graph valueId
                let fromWidth = SemanticGraph.tryGetNode value graph |> Option.bind (realWidth graph)
                realMeet node.Id value fromWidth (realFieldWidth graph node.Type field))
    | SemanticKind.TupleExpr elements ->
        elements |> List.mapi (fun i e -> into e (fieldSlotWidth graph node.Type (sprintf "Item%d" (i + 1)))) |> List.choose id
    | SemanticKind.IfThenElse (_, thenId, elseId) ->
        (thenId :: Option.toList elseId) |> List.choose (fun armId -> into armId (nodeWidth graph node.Id))
    | SemanticKind.CaseElimination (_, arms) -> arms |> List.choose (fun arm -> into arm.Body (nodeWidth graph node.Id))
    | SemanticKind.Match (_, cases) -> cases |> List.choose (fun c -> into c.Body (nodeWidth graph node.Id))
    | SemanticKind.IndexSet (arrId, _, valueId) -> Option.toList (into valueId (elementSlotWidth graph arrId))
    | SemanticKind.ArrayExpr elements -> elements |> List.choose (fun e -> into e (elementSlotWidth graph node.Id))
    | SemanticKind.VarRef (_, Some defId) ->
        match SemanticGraph.tryGetNode defId graph with
        | Some { Kind = SemanticKind.Binding _ } -> readMeet graph node (nodeWidth graph defId)
        | Some ({ Kind = SemanticKind.PatternBinding _ } as def) ->
            match def.Parent |> Option.bind (fun p -> SemanticGraph.tryGetNode p graph) with
            | Some { Kind = SemanticKind.Lambda _ } -> readMeet graph node (nodeWidth graph defId)
            | _ -> []
        | _ -> []
    | SemanticKind.FieldGet (exprId, field) ->
        match SemanticGraph.tryGetNode exprId graph with
        | Some expr ->
            readMeet graph node (fieldSlotWidth graph expr.Type field)
            @ (realMeet node.Id node.Id (realFieldWidth graph expr.Type field) (realWidth graph node) |> Option.toList)
        | None -> []
    | SemanticKind.TupleGet (tupleId, index) ->
        match SemanticGraph.tryGetNode tupleId graph with
        | Some { Kind = SemanticKind.TupleExpr elements } when index < elements.Length -> readMeet graph node (nodeWidth graph elements.[index])
        | Some tuple -> readMeet graph node (fieldSlotWidth graph tuple.Type (sprintf "Item%d" (index + 1)))
        | None -> []
    | SemanticKind.IndexGet (arrId, _) -> readMeet graph node (elementSlotWidth graph arrId)
    | SemanticKind.DUEliminate (duId, caseIndex, _, _) ->
        match SemanticGraph.tryGetNode duId graph with
        | Some du -> readMeet graph node (payloadSlotWidth graph du.Type caseIndex)
        | None -> []
    | _ -> []

let private onFabric (context: PlatformContext option) : bool =
    context |> Option.exists (fun ctx -> PlatformContext.substrateKind ctx = SubstrateKind.FPGA)

let private wordOf (context: PlatformContext option) : int option =
    context |> Option.bind (fun ctx -> PlatformContext.tryWidth ctx (WidthDimension.name WidthDimension.Register) |> Result.toOption)

/// The meets of every reachable consumer, keyed by the consumer.
let derive (context: PlatformContext option) (graph: SemanticGraph) (curry: CurryInfo) : Map<NodeId, Meet list> =
    if onFabric context then Map.empty
    else
        let ctx = { Graph = graph; Word = wordOf context; Curry = curry }
        graph.Nodes
        |> Map.toList
        |> List.choose (fun (_, node) ->
            if not node.IsReachable then None
            else
                match nodeMeets ctx node with
                | [] -> None
                | meets -> Some (node.Id, meets))
        |> Map.ofList

/// The return meet of every reachable lambda whose body's last value is held at another width
/// than the body's result.
let returns (context: PlatformContext option) (graph: SemanticGraph) : Map<NodeId, Meet> =
    if onFabric context then Map.empty
    else
        graph.Nodes
        |> Map.toList
        |> List.choose (fun (_, node) ->
            match node.Kind with
            | SemanticKind.Lambda (_, bodyId, _, _, _) when node.IsReachable ->
                let lastValue = lastValueOf graph bodyId
                let bodyReachable = SemanticGraph.tryGetNode bodyId graph |> Option.exists (fun b -> b.IsReachable)
                if lastValue = bodyId || not bodyReachable then None
                else meetInto graph bodyId lastValue (nodeWidth graph bodyId) |> Option.map (fun m -> node.Id, m)
            | _ -> None)
        |> Map.ofList
