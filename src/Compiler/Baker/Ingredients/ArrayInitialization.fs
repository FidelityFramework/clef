// SPDX-License-Identifier: MIT
/// Source initialization incidence, shared by scalar analysis and late memory
/// settlement. This does not select carriers, storage layout or residence.
module Clef.Compiler.Baker.Ingredients.ArrayInitialization

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Requirements = Clef.Compiler.PSGSaturation.SemanticGraph.Requirements

exception private MissingInitialization of string

/// Establish the complete current zeroCreate initialization, including its
/// guarded write rewrite. Copy initialization belongs to its separate rule.
let tryInitialization (graph: SemanticGraph) (allocation: NodeId) : Result<NodeId list, string> =
    let mutable support = Set.empty
    let demand condition reason = if not condition then raise (MissingInitialization reason)
    let needed reason = function Some value -> value | None -> raise (MissingInitialization reason)
    let live id =
        support <- Set.add id support
        graph.Nodes.TryFind id |> Option.filter _.IsReachable
        |> needed "An array initialization participant is not a live source occurrence."
    let integer expected id =
        match (live id).Kind with
        | SemanticKind.Literal(NativeLiteral.Int(value, _)) -> bigint value = expected
        | SemanticKind.Literal(NativeLiteral.UInt(value, _)) -> bigint value = expected
        | _ -> false
    let reference binding id =
        match (live id).Kind, (live id).Children with
        | SemanticKind.VarRef(_, Some actual), [] -> actual = binding
        | _ -> false
    let rec zeroCount seen id =
        demand (not (Set.contains id seen)) "The allocation count alias path is cyclic."
        let seen = Set.add id seen
        match (live id).Kind, (live id).Children with
        | SemanticKind.Binding(_, false, _, _), [value] -> zeroCount seen value
        | SemanticKind.VarRef(_, Some value), [] -> zeroCount seen value
        | SemanticKind.TypeAnnotation(value, _), [actual] when value = actual -> zeroCount seen value
        | SemanticKind.Sequential items, children when items = children && not items.IsEmpty -> zeroCount seen (List.last items)
        | _ -> integer 0I id
    let sequence id =
        match (live id).Kind with
        | SemanticKind.Sequential items when (live id).Children = items -> items
        | _ -> raise (MissingInitialization "Array construction lost its exact ordered source continuation.")
    let call modl operation id =
        demand (match (live id).Kind with
                | SemanticKind.Application(callee, arguments) -> (live id).Children = callee :: arguments
                | _ -> false) "An array initialization operation lost its executable source incidence."
        match ArrayShapes.intrinsicApplication graph id with
        | Some(info, arguments, participants) when info.Module = modl && info.Operation = operation ->
            participants |> Set.iter (live >> ignore)
            arguments |> List.iter (live >> ignore)
            if modl = IntrinsicModule.Operators then
                demand (arguments |> List.forall (fun actual -> Types.isIntegerType (live actual).Type))
                       "An array initialization operation lacks its checked integer operands."
            arguments
        | _ -> raise (MissingInitialization "An array initialization operation changed its exact source intrinsic.")
    let operation name actuals id =
        demand (call IntrinsicModule.Operators name id = actuals)
               "An array initialization operation changed its exact ordered operands."
    let conjunction left right id =
        demand (match (live id).Kind, (live id).Children with
                | SemanticKind.IfThenElse(condition, yes, Some no), children when condition = left && yes = right && children = [left; right; no] ->
                    match (live no).Kind with SemanticKind.Literal(NativeLiteral.Bool false) -> true | _ -> false
                | _ -> false) "An array range guard lost its exact short-circuit conjunction."
    let requirement required predicate frontier continuation =
        let fact = Requirements.tryRequirement graph required
                   |> needed "An array construction lacks its actual always-active Require frontier."
        demand (fact.Condition = predicate && fact.Frontier = frontier && fact.Continuation = continuation && fact.PatternTest.IsNone)
               "The array requirement no longer guards its exact construction continuation."
        fact.Participants |> List.iter (live >> ignore)
    let rec allocationTarget seen id =
        demand (not (Set.contains id seen)) "The allocation alias path is cyclic."
        let seen = Set.add id seen
        match (live id).Kind, (live id).Children with
        | SemanticKind.ArrayAllocate count, [actual] when count = actual -> id
        | SemanticKind.Binding(_, false, _, _), [value] -> allocationTarget seen value
        | SemanticKind.VarRef(_, Some value), [] -> allocationTarget seen value
        | SemanticKind.TypeAnnotation(value, _), [actual] when value = actual -> allocationTarget seen value
        | SemanticKind.Sequential items, children when items = children && not items.IsEmpty -> allocationTarget seen (List.last items)
        | _ -> raise (MissingInitialization "A constructed destination has no exact allocation provenance.")
    let initializedBlock output actions block =
        match sequence block with
        | stored :: tail ->
            demand (match (live stored).Kind, (live stored).Children with
                    | SemanticKind.Binding(_, false, _, _), [actual] -> actual = allocation
                    | _ -> false) "Array storage is not bound before its initializer."
            demand (reference stored output && tail = actions @ [output])
                   "The initialized array escapes before its complete ordered writes."
        | _ -> raise (MissingInitialization "An array initializer has no storage continuation.")
    try
        let rows = graph.Edges |> List.filter (fun edge ->
            match edge.Role with EdgeRole.ArrayAllocationConstruction item -> item.Site = allocation | _ -> false)
        let construction =
            match rows with
            | [{ Role = EdgeRole.ArrayAllocationConstruction item }] when NumericValues.sameRows [MemoryValues.allocationConstructionRow item] rows -> item
            | _ -> raise (MissingInitialization "An array allocation construction row is absent, duplicated or inconsistent.")
        let node = live allocation
        let count = construction.Count
        demand (node.Kind = SemanticKind.ArrayAllocate count.Reference && node.Children = [count.Reference])
               "An array allocation changed its exact source count operand."
        live count.Actual |> ignore
        demand (Types.isIntegerType (live count.Actual).Type && Types.isIntegerType (live count.Reference).Type)
               "An array allocation count lacks its checked integer type."
        demand (match (live count.Binding).Kind, (live count.Binding).Children with
                | SemanticKind.Binding(_, false, _, _), [actual] -> actual = count.Actual
                | _ -> false) "An array operand is not bound exactly once to its declared actual."
        demand (reference count.Binding count.Reference) "An array operand reference no longer names its exact source binding."
        let value = construction.Default |> needed "This allocation requires its complete source copy initialization rule."
        let element =
            match applySubst node.Type with
            | NativeType.TApp(tc, [element]) when tc.NTUKind = Some NTUKind.NTUarray -> applySubst element
            | _ -> raise (MissingInitialization "The array constructor lacks its checked element type.")
        let defaultNode = live value
        demand (applySubst defaultNode.Type = element &&
                (match defaultNode.Kind with
                 | SemanticKind.Literal(NativeLiteral.Bool false) -> element = Types.boolType
                 | SemanticKind.Literal(NativeLiteral.Char '\000') -> element = Types.charType
                 | _ -> Types.isIntegerType element && integer 0I value))
               "Array.zeroCreate no longer carries the exact source default value for its element."
        let guard = construction.Guard
        demand (sequence construction.Owner = [count.Binding; value; guard.Frontier])
               "Array.zeroCreate lost its exact count/default binding and Require execution prefix."
        demand (guard.Count = count.Reference && guard.Offset.IsNone && guard.Buffer.IsNone && guard.Length.IsNone &&
                guard.NonnegativeOffset.IsNone && guard.End.IsNone && guard.Within.IsNone && guard.Predicate = guard.NonnegativeCount)
               "The allocation requirement is not its declared nonnegative count guard."
        demand (integer 0I guard.Zero) "An array range guard has no exact zero endpoint."
        operation "op_GreaterThanOrEqual" [count.Reference; guard.Zero] guard.NonnegativeCount
        requirement guard.Requirement guard.Predicate guard.Frontier guard.Continuation
        match construction.Initialization with
        | None ->
            // A cached range is not authority for omitting executable writes.
            demand (zeroCount Set.empty count.Actual) "A nonempty zeroCreate allocation has no complete initialization loop."
            match sequence guard.Continuation with
            | [_; output] -> initializedBlock output [] guard.Continuation
            | _ -> raise (MissingInitialization "An empty zeroCreate changed its storage continuation.")
        | Some init ->
            demand (integer 0I init.Initial) "An array construction loop must begin at its exact zero index."
            demand (match (live init.Index).Kind, (live init.Index).Children with
                    | SemanticKind.Binding(_, true, _, _), [initial] -> initial = init.Initial
                    | _ -> false) "An array construction loop lost its actual mutable induction binding."
            demand (reference init.Index init.Current) "An array construction loop reads another induction binding."
            match call IntrinsicModule.Operators "op_LessThan" init.Guard with
            | [atGuard; actualCount] ->
                demand (reference init.Index atGuard && actualCount = count.Reference) "An array loop guard reads another induction binding or count."
            | _ -> raise (MissingInitialization "An array loop guard changed arity.")
            match call IntrinsicModule.Operators "op_Addition" init.Step with
            | [current; one] ->
                demand (current = init.Current && integer 1I one) "An array construction loop does not advance by exactly one."
            | _ -> raise (MissingInitialization "An array loop step changed its operands.")
            demand (match (live init.Advance).Kind, (live init.Advance).Children with
                    | SemanticKind.Set(target, step), children -> reference init.Index target && step = init.Step && children = [target; step]
                    | _ -> false) "An array loop does not assign its exact next index to its induction binding."
            demand (match (live init.Loop).Kind, (live init.Loop).Children with
                    | SemanticKind.WhileLoop(predicate, body), children ->
                        predicate = init.Guard && children = [predicate; body] && sequence body = [init.Write; init.Advance]
                    | _ -> false) "An array construction lost its complete ordered loop body."
            let writes = graph.Edges |> List.filter (fun edge ->
                edge.Role = EdgeRole.MemoryAccessGuard && List.tryLast edge.Sources = Some init.Write)
            match writes with
            | [{ Class = EdgeClass.Provenance; Ordinal = 0; Target = site
                 Sources = [buffer; index; length; zero; lower; upper; predicate; required; frontier] }] ->
                let actualRows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.MemoryAccessGuard && edge.Target = site)
                demand (NumericValues.sameRows writes actualRows) "An initialization write has inconsistent source bounds-guard incidence."
                demand (buffer = init.Buffer && index = init.Current && allocationTarget Set.empty buffer = allocation)
                       "Array.zeroCreate lost its complete count-correlated default writes."
                demand (match (live site).Kind, (live site).Children with
                        | SemanticKind.IndexSet(actualBuffer, actualIndex, stored), children ->
                            actualBuffer = buffer && actualIndex = index && stored = value && children = [buffer; index; value]
                        | _ -> false) "Array.zeroCreate lost its actual guarded default write."
                demand (call IntrinsicModule.Array "length" length = [buffer]) "An initialization write guards another buffer's extent."
                demand (integer 0I zero) "An initialization write lost its exact zero endpoint."
                operation "op_GreaterThanOrEqual" [index; zero] lower
                operation "op_LessThan" [index; length] upper
                conjunction lower upper predicate
                requirement required predicate frontier site
            | _ -> raise (MissingInitialization "An initialization write lost its unique source bounds-guard rewrite.")
            initializedBlock init.Buffer [init.Index; init.Loop] guard.Continuation
        Ok (Set.toList support)
    with MissingInitialization reason -> Error reason
