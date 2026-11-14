// SPDX-License-Identifier: MIT
/// Source initialization incidence, shared by scalar analysis and late memory
/// settlement. This does not select carriers, storage layout or residence.
module Clef.Compiler.Baker.Ingredients.ArrayInitialization

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Requirements = Clef.Compiler.PSGSaturation.SemanticGraph.Requirements

type private ResultBuilder() =
    member _.Return(value) = Ok value
    member _.ReturnFrom(result: Result<_, _>) = result
    member _.Bind(result, binder) = Result.bind binder result
    member _.Zero() = Ok ()
    member _.Delay(f) = f
    member _.Run(f) = f ()
    member this.Combine(first, second) = this.Bind(first, fun () -> second ())

let private checked' = ResultBuilder()

let tryInitialization (graph: SemanticGraph) (allocation: NodeId) : Result<NodeId list, string> =
    let mutable support = Set.empty
    let demand condition reason = if condition then Ok () else Error reason
    let needed reason = function Some value -> Ok value | None -> Error reason
    let live id =
        support <- Set.add id support
        graph.Nodes.TryFind id |> Option.filter _.IsReachable
        |> needed "An array initialization participant is not a live source occurrence."
    let integer expected id =
        match live id with
        | Ok { Kind = SemanticKind.Literal(NativeLiteral.Int(value, _)) } -> Ok (bigint value = expected)
        | Ok { Kind = SemanticKind.Literal(NativeLiteral.UInt(value, _)) } -> Ok (bigint value = expected)
        | Ok _ -> Ok false
        | Error reason -> Error reason
    let reference binding id =
        match live id with
        | Ok { Kind = SemanticKind.VarRef(_, Some actual); Children = [] } -> Ok (actual = binding)
        | Ok _ -> Ok false
        | Error reason -> Error reason
    let rec zeroCount seen id = checked' {
        do! demand (not (Set.contains id seen)) "The allocation count alias path is cyclic."
        let seen = Set.add id seen
        let! node = live id
        match node.Kind, node.Children with
        | SemanticKind.Binding(_, false, _, _), [value] -> return! zeroCount seen value
        | SemanticKind.VarRef(_, Some value), [] -> return! zeroCount seen value
        | SemanticKind.TypeAnnotation(value, _), [actual] when value = actual -> return! zeroCount seen value
        | SemanticKind.Sequential items, children when items = children && not items.IsEmpty -> return! zeroCount seen (List.last items)
        | _ -> return! integer 0I id
    }
    let sequence id = checked' {
        let! node = live id
        match node.Kind with
        | SemanticKind.Sequential items when node.Children = items -> return items
        | _ -> return! Error "Array construction lost its exact ordered source continuation."
    }
    let call modl operation id = checked' {
        let! node = live id
        do! demand (match node.Kind with
                    | SemanticKind.Application(callee, arguments) -> node.Children = callee :: arguments
                    | _ -> false) "An array initialization operation lost its executable source incidence."
        match ArrayShapes.intrinsicApplication graph id with
        | Some(info, arguments, participants) when info.Module = modl && info.Operation = operation ->
            let rec touchAll = function
                | [] -> Ok ()
                | item :: rest -> live item |> Result.bind (fun _ -> touchAll rest)
            do! touchAll (Set.toList participants)
            do! touchAll arguments
            if modl = IntrinsicModule.Operators then
                let rec checkInt = function
                    | [] -> Ok true
                    | actual :: rest ->
                        live actual |> Result.bind (fun n ->
                            if Types.isIntegerType n.Type then checkInt rest else Ok false)
                let! allInt = checkInt arguments
                do! demand allInt "An array initialization operation lacks its checked integer operands."
            return arguments
        | _ -> return! Error "An array initialization operation changed its exact source intrinsic."
    }
    let operation name actuals id = checked' {
        let! args = call IntrinsicModule.Operators name id
        do! demand (args = actuals) "An array initialization operation changed its exact ordered operands."
    }
    let conjunction left right id = checked' {
        let! node = live id
        let! valid =
            match node.Kind, node.Children with
            | SemanticKind.IfThenElse(condition, yes, Some no), children when condition = left && yes = right && children = [left; right; no] ->
                live no |> Result.map (fun noNode -> match noNode.Kind with SemanticKind.Literal(NativeLiteral.Bool false) -> true | _ -> false)
            | _ -> Ok false
        do! demand valid "An array range guard lost its exact short-circuit conjunction."
    }
    let requirement required predicate frontier continuation = checked' {
        let! fact =
            Requirements.tryRequirement graph required
            |> needed "An array construction lacks its actual always-active Require frontier."
        do! demand (fact.Condition = predicate && fact.Frontier = frontier && fact.Continuation = continuation && fact.PatternTest.IsNone)
                   "The array requirement no longer guards its exact construction continuation."
        let rec touchAll = function
            | [] -> Ok ()
            | item :: rest -> live item |> Result.bind (fun _ -> touchAll rest)
        do! touchAll fact.Participants
    }
    let rec allocationTarget seen id = checked' {
        do! demand (not (Set.contains id seen)) "The allocation alias path is cyclic."
        let seen = Set.add id seen
        let! node = live id
        match node.Kind, node.Children with
        | SemanticKind.ArrayAllocate count, [actual] when count = actual -> return id
        | SemanticKind.Binding(_, false, _, _), [value] -> return! allocationTarget seen value
        | SemanticKind.VarRef(_, Some value), [] -> return! allocationTarget seen value
        | SemanticKind.TypeAnnotation(value, _), [actual] when value = actual -> return! allocationTarget seen value
        | SemanticKind.Sequential items, children when items = children && not items.IsEmpty -> return! allocationTarget seen (List.last items)
        | _ -> return! Error "A constructed destination has no exact allocation provenance."
    }
    let initializedBlock output actions block = checked' {
        let! items = sequence block
        match items with
        | stored :: tail ->
            let! storedNode = live stored
            do! demand (match storedNode.Kind, storedNode.Children with
                        | SemanticKind.Binding(_, false, _, _), [actual] -> actual = allocation
                        | _ -> false) "Array storage is not bound before its initializer."
            let! refOk = reference stored output
            do! demand (refOk && tail = actions @ [output])
                       "The initialized array escapes before its complete ordered writes."
        | _ -> return! Error "An array initializer has no storage continuation."
    }
    checked' {
        let rows = graph.Edges |> List.filter (fun edge ->
            match edge.Role with EdgeRole.ArrayAllocationConstruction item -> item.Site = allocation | _ -> false)
        let! construction =
            match rows with
            | [{ Role = EdgeRole.ArrayAllocationConstruction item }] when NumericValues.sameRows [MemoryValues.allocationConstructionRow item] rows -> Ok item
            | _ -> Error "An array allocation construction row is absent, duplicated or inconsistent."
        let! node = live allocation
        let count = construction.Count
        do! demand (node.Kind = SemanticKind.ArrayAllocate count.Reference && node.Children = [count.Reference])
                   "An array allocation changed its exact source count operand."
        let! actualNode = live count.Actual
        let! refNode = live count.Reference
        do! demand (Types.isIntegerType actualNode.Type && Types.isIntegerType refNode.Type)
                   "An array allocation count lacks its checked integer type."
        let! bindingNode = live count.Binding
        do! demand (match bindingNode.Kind, bindingNode.Children with
                    | SemanticKind.Binding(_, false, _, _), [actual] -> actual = count.Actual
                    | _ -> false) "An array operand is not bound exactly once to its declared actual."
        let! countRefOk = reference count.Binding count.Reference
        do! demand countRefOk "An array operand reference no longer names its exact source binding."
        let! value = construction.Default |> needed "This allocation requires its complete source copy initialization rule."
        let! element =
            match applySubst node.Type with
            | NativeType.TApp(tc, [element]) when tc.NTUKind = Some NTUKind.NTUarray -> Ok (applySubst element)
            | _ -> Error "The array constructor lacks its checked element type."
        let! defaultNode = live value
        let! defaultValid =
            match defaultNode.Kind with
            | SemanticKind.Literal(NativeLiteral.Bool false) -> Ok (element = Types.boolType)
            | SemanticKind.Literal(NativeLiteral.Char '\000') -> Ok (element = Types.charType)
            | _ when Types.isIntegerType element -> integer 0I value
            | _ -> Ok false
        do! demand (applySubst defaultNode.Type = element && defaultValid)
                   "Array.zeroCreate no longer carries the exact source default value for its element."
        let guard = construction.Guard
        let! ownerItems = sequence construction.Owner
        do! demand (ownerItems = [count.Binding; value; guard.Frontier])
                   "Array.zeroCreate lost its exact count/default binding and Require execution prefix."
        do! demand (guard.Count = count.Reference && guard.Offset.IsNone && guard.Buffer.IsNone && guard.Length.IsNone &&
                    guard.NonnegativeOffset.IsNone && guard.End.IsNone && guard.Within.IsNone && guard.Predicate = guard.NonnegativeCount)
                   "The allocation requirement is not its declared nonnegative count guard."
        let! zeroOk = integer 0I guard.Zero
        do! demand zeroOk "An array range guard has no exact zero endpoint."
        do! operation "op_GreaterThanOrEqual" [count.Reference; guard.Zero] guard.NonnegativeCount
        do! requirement guard.Requirement guard.Predicate guard.Frontier guard.Continuation
        do!
            match construction.Initialization with
            | None ->
                checked' {
                    let! isZero = zeroCount Set.empty count.Actual
                    do! demand isZero "A nonempty zeroCreate allocation has no complete initialization loop."
                    let! contItems = sequence guard.Continuation
                    match contItems with
                    | [_; output] -> do! initializedBlock output [] guard.Continuation
                    | _ -> return! Error "An empty zeroCreate changed its storage continuation."
                }
            | Some init ->
                checked' {
                    let! initZero = integer 0I init.Initial
                    do! demand initZero "An array construction loop must begin at its exact zero index."
                    let! indexNode = live init.Index
                    do! demand (match indexNode.Kind, indexNode.Children with
                                | SemanticKind.Binding(_, true, _, _), [initial] -> initial = init.Initial
                                | _ -> false) "An array construction loop lost its actual mutable induction binding."
                    let! currentRefOk = reference init.Index init.Current
                    do! demand currentRefOk "An array construction loop reads another induction binding."
                    let! guardArgs = call IntrinsicModule.Operators "op_LessThan" init.Guard
                    do!
                        match guardArgs with
                        | [atGuard; actualCount] ->
                            checked' {
                                let! guardRefOk = reference init.Index atGuard
                                do! demand (guardRefOk && actualCount = count.Reference) "An array loop guard reads another induction binding or count."
                            }
                        | _ -> Error "An array loop guard changed arity."
                    let! stepArgs = call IntrinsicModule.Operators "op_Addition" init.Step
                    do!
                        match stepArgs with
                        | [current; one] ->
                            checked' {
                                let! isOne = integer 1I one
                                do! demand (current = init.Current && isOne) "An array construction loop does not advance by exactly one."
                            }
                        | _ -> Error "An array loop step changed its operands."
                    let! advanceNode = live init.Advance
                    let! advanceOk =
                        match advanceNode.Kind, advanceNode.Children with
                        | SemanticKind.Set(target, step), children ->
                            reference init.Index target |> Result.map (fun r -> r && step = init.Step && children = [target; step])
                        | _ -> Ok false
                    do! demand advanceOk "An array loop does not assign its exact next index to its induction binding."
                    let! loopNode = live init.Loop
                    let! loopOk =
                        match loopNode.Kind, loopNode.Children with
                        | SemanticKind.WhileLoop(predicate, body), children when predicate = init.Guard && children = [predicate; body] ->
                            sequence body |> Result.map (fun items -> items = [init.Write; init.Advance])
                        | _ -> Ok false
                    do! demand loopOk "An array construction lost its complete ordered loop body."
                    let writes = graph.Edges |> List.filter (fun edge ->
                        edge.Role = EdgeRole.MemoryAccessGuard && List.tryLast edge.Sources = Some init.Write)
                    do!
                        match writes with
                        | [{ Class = EdgeClass.Provenance; Ordinal = 0; Target = site
                             Sources = [buffer; index; length; zero; lower; upper; predicate; required; frontier] }] ->
                            checked' {
                                let actualRows = graph.Edges |> List.filter (fun edge -> edge.Role = EdgeRole.MemoryAccessGuard && edge.Target = site)
                                do! demand (NumericValues.sameRows writes actualRows) "An initialization write has inconsistent source bounds-guard incidence."
                                let! allocTarget = allocationTarget Set.empty buffer
                                do! demand (buffer = init.Buffer && index = init.Current && allocTarget = allocation)
                                           "Array.zeroCreate lost its complete count-correlated default writes."
                                let! siteNode = live site
                                do! demand (match siteNode.Kind, siteNode.Children with
                                            | SemanticKind.IndexSet(actualBuffer, actualIndex, stored), children ->
                                                actualBuffer = buffer && actualIndex = index && stored = value && children = [buffer; index; value]
                                            | _ -> false) "Array.zeroCreate lost its actual guarded default write."
                                let! lenArgs = call IntrinsicModule.Array "length" length
                                do! demand (lenArgs = [buffer]) "An initialization write guards another buffer's extent."
                                let! zeroWriteOk = integer 0I zero
                                do! demand zeroWriteOk "An initialization write lost its exact zero endpoint."
                                do! operation "op_GreaterThanOrEqual" [index; zero] lower
                                do! operation "op_LessThan" [index; length] upper
                                do! conjunction lower upper predicate
                                do! requirement required predicate frontier site
                            }
                        | _ -> Error "An initialization write lost its unique source bounds-guard rewrite."
                    do! initializedBlock init.Buffer [init.Index; init.Loop] guard.Continuation
                }
        return Set.toList support
    }
