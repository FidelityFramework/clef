// SPDX-License-Identifier: MIT
// Late source settlement of array construction, residence and ordered copies.
// Construction receipts cite the actual guarded program; they do not replace it.
module Clef.Compiler.Baker.Recipes.ArrayMemoryRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module Memory = Clef.Compiler.Baker.Ingredients.MemoryValues
module Placement = Clef.Compiler.PSGSaturation.SemanticGraph.Placement
module Platform = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
module Requirements = Clef.Compiler.PSGSaturation.SemanticGraph.Requirements

type private ResultBuilder() =
    member _.Bind(value, next) = Result.bind next value
    member _.Return(value) = Ok value
    member _.ReturnFrom(value: Result<'T, 'E>) = value
    member _.Zero() = Ok ()
    member _.Delay(f: unit -> Result<'T, 'E>) = f
    member _.Run(f: unit -> Result<'T, 'E>) = f ()
    member _.Combine(first: Result<unit, 'E>, second: unit -> Result<'T, 'E>) =
        match first with
        | Ok () -> second ()
        | Error err -> Error err
    member _.For(items: seq<'T>, body: 'T -> Result<unit, 'E>) =
        use enumerator = items.GetEnumerator()
        let rec loop () =
            if not (enumerator.MoveNext()) then Ok ()
            else
                match body enumerator.Current with
                | Ok () -> loop ()
                | Error err -> Error err
        loop ()

let private result = ResultBuilder()

let private mapResult (fn: 'T -> Result<'U, 'E>) (items: 'T list) : Result<'U list, 'E> =
    let rec loop acc remaining =
        match remaining with
        | [] -> Ok (List.rev acc)
        | head :: tail ->
            match fn head with
            | Ok value -> loop (value :: acc) tail
            | Error err -> Error err
    loop [] items

let private demand condition reason = if condition then Ok () else Error reason
let private needed reason = function Some value -> Ok value | None -> Error reason
let private live (graph:SemanticGraph) id =
    graph.Nodes.TryFind id |> Option.filter _.IsReachable |> needed "An array construction participant is not a live source occurrence."
let private scalar (numeric:NumericWitnessProjection) id =
    numeric.Values.TryFind id |> needed "An array construction scalar has no source-settled carrier."
let private element (numeric:NumericWitnessProjection) id =
    numeric.Elements.TryFind id |> needed "An array construction lacks its complete-write element slot."
let private elementIdentity (numeric:NumericWitnessProjection) id =
    match numeric.SourceTypes.TryFind id with
    | Some(TypeIdentity.Application((constructor: ConstructorIdentity),[element])) when constructor.NativeKind=Some NTUKind.NTUarray -> Ok element
    | _ -> Error "An array copy operand lacks its exact source array element identity."
let private integer graph expected id =
    result {
        let! node = live graph id
        match node.Kind with
        | SemanticKind.Literal(NativeLiteral.Int(value,_)) -> return bigint value = expected
        | SemanticKind.Literal(NativeLiteral.UInt(value,_)) -> return bigint value = expected
        | _ -> return false
    }
let private reference graph binding id =
    result {
        let! node = live graph id
        match node.Kind with
        | SemanticKind.VarRef(_,Some actual) -> return actual=binding
        | _ -> return false
    }
let private sequence graph id =
    result {
        let! node = live graph id
        match node.Kind with
        | SemanticKind.Sequential items when node.Children=items -> return items
        | _ -> return! Error "Array construction lost its exact ordered source continuation."
    }
let private bound graph (operand:ArrayBoundOperand) =
    result {
        if operand.Actual=operand.Binding && operand.Binding=operand.Reference then
            let! isZero = integer graph 0I operand.Actual
            do! demand isZero "An unbound array offset must be the exact source zero literal."
        else
            let! bindingNode = live graph operand.Binding
            do! demand (match bindingNode.Kind,bindingNode.Children with
                        | SemanticKind.Binding(_,false,_,_),[actual] -> actual=operand.Actual
                        | _ -> false) "An array operand is not bound exactly once to its declared actual."
            let! isRef = reference graph operand.Binding operand.Reference
            do! demand isRef "An array operand reference no longer names its exact source binding."
    }

let private operation (graph:SemanticGraph) (numeric:NumericWitnessProjection) kind actuals id =
    result {
        let! settled = numeric.Operations.TryFind id |> needed "An array guard or loop term lacks its source numeric operation contract."
        do! demand (settled.Site=id && settled.Kind=kind && (settled.Operands |> List.map _.Actual)=actuals)
               "An array guard or loop term changed its exact ordered operands."
        let! node = live graph id
        do! demand (match node.Kind with
                    | SemanticKind.Application(callee,arguments) -> callee=settled.Callee && arguments=actuals
                    | _ -> false) "An array numeric operation no longer describes its executable source occurrence."
    }

let private conjunction graph left right id =
    result {
        let! node = live graph id
        let! isValid =
            match node.Kind with
            | SemanticKind.IfThenElse(condition,yes,Some no) when condition=left && yes=right ->
                result {
                    let! noNode = live graph no
                    match noNode.Kind with
                    | SemanticKind.Literal(NativeLiteral.Bool false) -> return true
                    | _ -> return false
                }
            | _ -> Ok false
        do! demand isValid "An array range guard lost its exact short-circuit conjunction."
    }

let private guard graph numeric (operations:Map<NodeId,MemoryWitnessOperation>) (fact:ArrayRangeGuard) : Result<RequirementWitness, string> =
    result {
        let! isZero = integer graph 0I fact.Zero
        do! demand isZero "An array range guard has no exact zero endpoint."
        do! operation graph numeric NumericOperationKind.GreaterOrEqual [fact.Count;fact.Zero] fact.NonnegativeCount
        do! match fact.Buffer,fact.Offset,fact.Length,fact.NonnegativeOffset,fact.End,fact.Within with
            | None,None,None,None,None,None ->
                demand (fact.Predicate=fact.NonnegativeCount) "The allocation requirement is not its declared nonnegative count guard."
            | Some buffer,Some offset,Some length,Some nonnegative,Some finish,Some within ->
                result {
                    do! demand (match operations.TryFind length with
                                | Some(MemoryWitnessOperation.ArrayExtent extent) -> extent.Site=length && extent.Source=buffer
                                | Some(MemoryWitnessOperation.BufferExtent extent) -> extent.Site=length && extent.Source=buffer
                                | _ -> false) "An array slice guard does not read its exact buffer extent."
                    do! operation graph numeric NumericOperationKind.GreaterOrEqual [offset;fact.Zero] nonnegative
                    do! operation graph numeric NumericOperationKind.Add [offset;fact.Count] finish
                    do! operation graph numeric NumericOperationKind.LessOrEqual [finish;length] within
                    let! predNode = live graph fact.Predicate
                    let! remaining =
                        match predNode.Kind with
                        | SemanticKind.IfThenElse(condition,yes,Some _) when condition=fact.NonnegativeCount -> Ok yes
                        | _ -> Error "An array slice requirement lacks its count-first conjunction."
                    do! conjunction graph nonnegative within remaining
                    do! conjunction graph fact.NonnegativeCount remaining fact.Predicate
                }
            | _ -> Error "An array slice guard has an incomplete buffer/offset/extent premise set."
        let! required = Requirements.tryRequirement graph fact.Requirement |> needed "An array construction lacks its actual always-active Require frontier."
        do! demand (required.Condition=fact.Predicate && required.Frontier=fact.Frontier && required.Continuation=fact.Continuation)
               "The array requirement no longer guards its exact construction continuation."
        return { Site=required.Site;Condition=required.Condition;Diagnostic=required.Diagnostic;Frontier=required.Frontier
                 Continuation=required.Continuation;PatternTest=required.PatternTest;Participants=required.Participants }
    }

let private allocationTarget graph id =
    let rec resolve seen current =
        result {
            do! demand (not(Set.contains current seen)) "The allocation alias path is cyclic."
            let seen = Set.add current seen
            let! node = live graph current
            match node.Kind,node.Children with
            | SemanticKind.ArrayAllocate _,_ -> return current
            | SemanticKind.Binding(_,false,_,_),[value] -> return! resolve seen value
            | SemanticKind.VarRef(_,Some value),_ | SemanticKind.TypeAnnotation(value,_),_ -> return! resolve seen value
            | SemanticKind.Sequential items,_ when not items.IsEmpty -> return! resolve seen (List.last items)
            | _ -> return! Error "A constructed destination has no exact allocation provenance."
        }
    resolve Set.empty id

let private access graph (operations:Map<NodeId,MemoryWitnessOperation>) frontier =
    let rows=graph.Edges |> List.filter(fun edge ->
        edge.Role=EdgeRole.MemoryAccessGuard &&
        (match edge.Sources with [_;_;_;_;_;_;_;_;actual] -> actual=frontier | _ -> false))
    match rows with
    | [{Class=EdgeClass.Provenance;Ordinal=0;Target=site}] ->
        match operations.TryFind site with
        | Some(MemoryWitnessOperation.ArrayAccess value) when value.Site=site && value.Bounds.Requirement.Frontier=frontier -> Ok value
        | _ -> Error "A constructed copy access has no settled guarded memory operation."
    | _ -> Error "A constructed copy access lost its unique source bounds-guard rewrite."

let private loop (graph:SemanticGraph) (numeric:NumericWitnessProjection) index initial loopId predicate current step advance body =
    result {
        let! isInitZero = integer graph 0I initial
        do! demand isInitZero "An array construction loop must begin at its exact zero index."
        let! indexNode = live graph index
        do! demand (match indexNode.Kind,indexNode.Children with
                    | SemanticKind.Binding(_,true,_,_),[value] -> value=initial
                    | _ -> false) "An array construction loop lost its actual mutable induction binding."
        let! isCurrentRef = reference graph index current
        do! demand isCurrentRef "An array construction loop reads another induction binding."
        let! guardIndex,count =
            match numeric.Operations.TryFind predicate with
            | Some fact when fact.Kind=NumericOperationKind.Less ->
                match fact.Operands with
                | [atGuard;count] -> Ok(atGuard.Actual,count.Actual)
                | _ -> Error "An array loop guard changed arity."
            | _ -> Error "An array loop lacks its source-settled strict count bound."
        let! isGuardRef = reference graph index guardIndex
        do! demand isGuardRef "An array loop guard reads another induction binding."
        do! operation graph numeric NumericOperationKind.Less [guardIndex;count] predicate
        let! one =
            match numeric.Operations.TryFind step with
            | Some fact ->
                match fact.Operands with
                | [atStep;one] when atStep.Actual=current -> Ok one.Actual
                | _ -> Error "An array loop step changed its operands."
            | None -> Error "An array loop step lacks source numeric settlement."
        let! isOne = integer graph 1I one
        do! demand isOne "An array construction loop does not advance by exactly one."
        do! operation graph numeric NumericOperationKind.Add [current;one] step
        let! advanceNode = live graph advance
        let! isAdvanceValid =
            match advanceNode.Kind with
            | SemanticKind.Set(target,value) ->
                result {
                    let! isTargetRef = reference graph index target
                    return (isTargetRef && value=step)
                }
            | _ -> Ok false
        do! demand isAdvanceValid "An array loop does not assign its exact next index to its induction binding."
        let! loopNode = live graph loopId
        let! isLoopValid =
            match loopNode.Kind with
            | SemanticKind.WhileLoop(condition,actions) when condition=predicate ->
                result {
                    let! actionSeq = sequence graph actions
                    return (actionSeq = body)
                }
            | _ -> Ok false
        do! demand isLoopValid "An array construction lost its complete ordered loop body."
        return count
    }

let private allocationRow (graph:SemanticGraph) (construction:ArrayAllocationConstruction) =
    let rows=graph.Edges |> List.filter(fun edge -> match edge.Role with EdgeRole.ArrayAllocationConstruction item -> item.Site=construction.Site | _ -> false)
    demand (Clef.Compiler.Baker.Ingredients.NumericValues.sameRows [Memory.allocationConstructionRow construction] rows)
           "An array allocation construction row is absent, duplicated or inconsistent."

let private copyRow (graph:SemanticGraph) (construction:ArrayCopyConstruction) =
    let rows=graph.Edges |> List.filter(fun edge -> match edge.Role with EdgeRole.ArrayCopyConstruction item -> item.Site=construction.Site | _ -> false)
    demand (Clef.Compiler.Baker.Ingredients.NumericValues.sameRows [Memory.copyConstructionRow construction] rows)
           "An array copy construction row is absent, duplicated or inconsistent."

let private initializedBlock graph allocation output prefix actions block =
    result {
        let! items = sequence graph block
        match items with
        | stored::tail ->
            let! storedNode = live graph stored
            do! demand (match storedNode.Kind,storedNode.Children with
                        | SemanticKind.Binding(_,false,_,_),[actual] -> actual=allocation
                        | _ -> false) "Array storage is not bound before its initializer."
            let! isOutputRef = reference graph stored output
            do! demand (isOutputRef && tail=prefix@actions@[output])
                   "The initialized array escapes before its complete ordered writes."
        | _ -> do! Error "An array initializer has no storage continuation."
    }

// No operation is admitted from a known subset of construction participants.
// Every allocation and copy receipt validates its complete executable recipe.
let private settleCore (graph:SemanticGraph) (numeric:NumericWitnessProjection) (existing:(NodeId*MemoryWitnessOperation) list)
    : Enrichment * (NodeId*MemoryWitnessOperation) list * MemoryArrayCopyWitness list * Map<NodeId,string> * Set<NodeId> =
    let operations=Map.ofList existing
    let excluded=Memory.excluded graph
    let executable=Memory.executable graph excluded
    let allocations=Memory.allocationConstructions graph |> List.filter(fun item -> executable item.Site)
    let constructions=Memory.copyConstructions graph |> List.filter(fun item -> executable item.Site)
    let mutable enrichment=Enrichment.empty
    let mutable admitted=[]
    let mutable copies=[]
    let mutable failures=Map.empty
    let mutable required=Set.empty
    let getPlatform () = Platform.resolve graph |> needed "An array allocation needs the selected source platform declaration."
    let countRange (count:ScalarCarrier) =
        result {
            do! demand (match count.Slot with SettledSlot.Integer _ -> true | _ -> false) "An array count needs a source-settled integer carrier."
            match count.Range with
            | ValueRange.Bounded(lo,hi) when lo<=hi && hi>=0I -> return (max 0I lo,hi)
            | _ -> return! Error "An array count has no finite nonnegative successful allocation range."
        }
    let asyncInitialization (construction:ArrayAllocationConstruction) count slot bytes =
        result {
            let! row =
                graph.Codata.Value.AsyncOrchestrations |> Map.toList |> List.choose (fun (_,row) ->
                    if row.ResultStorage=construction.Site then Some row else None)
                |> function
                   | [row] -> Ok row
                   | _ -> Error "An uninitialized array lacks a unique complete source orchestration or copy construction."
            let countText =
                match count with
                | ValueRange.Empty -> "empty"
                | ValueRange.Bounded(lo,hi) -> sprintf "[%s..%s]" (string lo) (string hi)
                | ValueRange.Above lo -> sprintf "[%s..+infinity)" (string lo)
                | ValueRange.Below hi -> sprintf "(-infinity..%s]" (string hi)
                | ValueRange.Unbounded -> "unbounded"
            do! demand (row.Site=construction.Owner && row.ResultCapacity>0 && row.ResultCapacity=row.Children.Length
                        && Set.count(Set.ofList row.Children)=row.Children.Length
                        && row.ResultOrdering=(row.Children |> List.mapi(fun ordinal child -> ordinal,child))
                        && count=ValueRange.point(bigint row.ResultCapacity) && row.ElementStride=bytes)
                   (sprintf "The orchestration result allocation disagrees with its settled child ordering or capacity (owner %d/%d, capacity %d/%d, count %s, stride %d/%d)."
                       (NodeId.value row.Site) (NodeId.value construction.Owner) row.ResultCapacity row.Children.Length countText row.ElementStride bytes)
            let writes =
                operations |> Map.toList |> List.choose(fun (_,operation) ->
                    match operation with
                    | MemoryWitnessOperation.ArrayAccess access when access.Value.IsSome && allocationTarget graph access.Buffer=Ok construction.Site -> Some access
                    | _ -> None)
            do! demand (writes.Length=row.Children.Length) "The orchestration result array does not have exactly one write per child."
            let! ordered = row.ResultOrdering |> mapResult(fun (ordinal,child) ->
                result {
                    let! write = writes |> List.filter(fun write -> write.Value=Some child) |> function
                                 | [write] -> Ok write
                                 | _ -> Error "An orchestration child has no unique result delivery."
                    let! index = scalar numeric write.Index
                    do! demand (index.Range=ValueRange.point(bigint ordinal) && write.Element=slot)
                           "An orchestration child delivers to another ordinal or element carrier."
                    return write.Bounds.Requirement.Frontier
                })
            let blocks = graph.Nodes.Values |> Seq.choose(fun node ->
                match node.Kind with
                | SemanticKind.Sequential(stored::tail) when tail.Length=ordered.Length+1 && allocationTarget graph stored=Ok construction.Site ->
                    let output=List.last tail
                    if reference graph stored output=Ok true && tail=ordered@[output] then Some node.Id else None
                | _ -> None) |> Seq.toList
            do! demand (blocks.Length=1) "The orchestration result escapes before its complete ordered child deliveries."
            return Set.ofList(row.Site::construction.Site::(blocks@ordered@row.Children))
        }
    let validateCopy (construction:ArrayCopyConstruction) =
        result {
            do! copyRow graph construction
            for op in [construction.Source;construction.SourceOffset;construction.DestinationOffset;construction.Count] do
                do! bound graph op
            let! count = scalar numeric construction.Count.Reference
            let! _,maximum = countRange count
            let! requirements = construction.Requirements |> mapResult (guard graph numeric operations)
            do! demand (not requirements.IsEmpty && (construction.Requirements |> List.forall(fun item -> item.Count=construction.Count.Reference)))
                   "An array copy lacks its count-correlated range requirements."
            for outer,inner in List.pairwise construction.Requirements do
                do! demand (outer.Continuation=inner.Frontier) "Array copy requirements no longer execute in their declared order."
            let! read,write,actions =
                match construction.Index,construction.IndexInitial,construction.Loop,construction.Guard,construction.Current,
                      construction.SourceIndex,construction.DestinationIndex,construction.Read,construction.Write,construction.Step,construction.Advance with
                | Some index,Some initial,Some loopId,Some predicate,Some current,Some sourceIndex,Some destinationIndex,Some read,Some write,Some step,Some advance ->
                    result {
                        let! loopCount = loop graph numeric index initial loopId predicate current step advance [read;write;advance]
                        do! demand (loopCount=construction.Count.Reference) "An array copy loop uses another count."
                        do! operation graph numeric NumericOperationKind.Add [construction.SourceOffset.Reference;current] sourceIndex
                        do! operation graph numeric NumericOperationKind.Add [construction.DestinationOffset.Reference;current] destinationIndex
                        let! source = access graph operations read
                        let! target = access graph operations write
                        let! targetNode = live graph target.Site
                        let! srcElemId = elementIdentity numeric source.Buffer
                        let! dstElemId = elementIdentity numeric target.Buffer
                        do! demand (source.Buffer=construction.Source.Reference && source.Index=sourceIndex && source.Value.IsNone &&
                                    target.Buffer=construction.Destination && target.Index=destinationIndex && target.Value=Some source.Site &&
                                    (match targetNode.Kind with
                                     | SemanticKind.IndexSet(_,_,evaluation) -> evaluation=read
                                     | _ -> false) &&
                                    srcElemId=dstElemId)
                               "An array copy's read/write pair does not preserve its exact ordered element transfer."
                        return (Some source,Some target,[index;loopId])
                    }
                | None,None,None,None,None,None,None,None,None,None,None when maximum=0I && count.Range=ValueRange.point 0I ->
                    Ok(None,None,[])
                | _ -> Error "An array copy lacks its complete index/read/write/advance loop construction."
            do! match construction.Allocation with
                | Some allocation ->
                    result {
                        let! dstTarget = allocationTarget graph construction.Destination
                        let! isDstOffsetZero = integer graph 0I construction.DestinationOffset.Reference
                        do! demand (dstTarget=allocation && isDstOffsetZero)
                               "A fresh snapshot copy no longer targets its own zero-based allocation."
                        let owner=allocations |> List.filter(fun item -> item.Site=allocation)
                        do! demand (match owner with [item] -> item.Owner=construction.Site && item.Count=construction.Count && item.Default.IsNone | _ -> false)
                               "A snapshot allocation does not have this exact source copy owner and count."
                        do! demand (construction.Requirements |> List.exists(fun item -> item.Buffer=Some construction.Source.Reference && item.Offset=Some construction.SourceOffset.Reference))
                               "A snapshot copy lacks the range guard for its exact source window."
                        let finalGuard=List.last construction.Requirements
                        let! block =
                            match construction.Requirements with
                            | [singleGuard] ->
                                result {
                                    let! siteSeq = sequence graph construction.Site
                                    do! demand (siteSeq=[construction.Source.Binding;construction.SourceOffset.Binding;construction.Count.Binding;singleGuard.Frontier])
                                           "Array.sub lost its exact actual-binding and Require execution prefix."
                                    return finalGuard.Continuation
                                }
                            | [_;_] -> Ok construction.Site
                            | _ -> Error "A source snapshot has an unsupported requirement frontier composition."
                        do! initializedBlock graph allocation construction.Destination [construction.DestinationOffset.Reference] actions block
                    }
                | None ->
                    result {
                        let snapshotCandidates=constructions |> List.filter(fun item -> item.Site=construction.Source.Actual && item.Allocation.IsSome)
                        let! snapshot =
                            match snapshotCandidates with
                            | [item] -> Ok item
                            | _ -> Error "An array blit requires one complete preceding source snapshot."
                        let! isSrcOffsetZero = integer graph 0I construction.SourceOffset.Reference
                        do! demand (snapshot.Count=construction.Count && snapshot.Requirements=construction.Requirements && isSrcOffsetZero)
                               "An array blit writeback no longer reads its complete count-correlated snapshot."
                        do! demand (construction.Requirements |> List.exists(fun item -> item.Buffer=Some construction.Destination && item.Offset=Some construction.DestinationOffset.Reference))
                               "An array blit lacks its exact destination range guard."
                        let! dstNode = live graph construction.Destination
                        let! destinationBinding =
                            match dstNode.Kind with
                            | SemanticKind.VarRef(_,Some binding) ->
                                result {
                                    let! bindNode = live graph binding
                                    do! demand (match bindNode.Kind,bindNode.Children with
                                                | SemanticKind.Binding(_,false,_,_),[_] -> true | _ -> false)
                                           "An array blit destination lost its single immutable actual binding."
                                    return binding
                                }
                            | _ -> Error "An array blit destination is not its bound source operand."
                        let! siteSeq = sequence graph construction.Site
                        do! demand (construction.Requirements.Length=2 &&
                                    siteSeq=[snapshot.Source.Binding;snapshot.SourceOffset.Binding;destinationBinding;
                                             construction.DestinationOffset.Binding;construction.Count.Binding;
                                             (List.head construction.Requirements).Frontier])
                               "Array.blit lost its exact ordered actual bindings and range-failure frontier."
                        let! body = sequence graph (List.last construction.Requirements).Continuation
                        match body with
                        | first::tail ->
                            do! demand (first=construction.Source.Binding && tail.Length=actions.Length+1 && List.take actions.Length tail=actions)
                                   "An array blit writes before the complete snapshot has been bound."
                            let! lastNode = live graph (List.last tail)
                            do! demand (match lastNode.Kind with SemanticKind.Literal NativeLiteral.Unit -> true | _ -> false)
                                   "An array blit has no exact unit completion."
                        | _ -> do! Error "An array blit has no ordered snapshot/writeback continuation."
                    }
            let! actualCount = scalar numeric construction.Count.Actual
            let participants=construction.Participants |> Set.union count.Participants |> Set.union actualCount.Participants
            let participants=List.fold(fun found (item:RequirementWitness) -> Set.union found (Set.ofList item.Participants)) participants requirements
            let participants=[read;write] |> List.choose id |> List.fold(fun found (item:MemoryArrayAccessWitness) -> Set.union found item.Participants) participants
            return { Site=construction.Site;Source=construction.Source.Actual;SourceOffset=construction.SourceOffset.Actual
                     Destination=construction.Destination;DestinationOffset=construction.DestinationOffset.Actual
                     Count=construction.Count.Actual;CountCarrier=actualCount;CountOperand=construction.Count;Allocation=construction.Allocation;Loop=construction.Loop
                     Read=read;Write=write;Requirements=requirements;Participants=participants }
        }
    for construction in allocations do
        required<-Set.add construction.Site required
        let outcome =
            result {
                do! allocationRow graph construction
                let! initializationParticipants =
                    match construction.Default with
                    | Some _ ->
                        match Clef.Compiler.Baker.Ingredients.ArrayInitialization.tryInitialization graph construction.Site with
                        | Ok participants -> Ok (Set.ofList participants)
                        | Error reason -> Error reason
                    | None -> Ok Set.empty
                do! bound graph construction.Count
                let! node = live graph construction.Site
                do! demand (node.Kind=SemanticKind.ArrayAllocate construction.Count.Reference && node.Children=[construction.Count.Reference])
                       "An array allocation changed its exact source count operand."
                let! requirement = guard graph numeric operations construction.Guard
                do! demand (construction.Guard.Count=construction.Count.Reference) "An array allocation requirement guards another count."
                let! count = scalar numeric construction.Count.Reference
                let! minimum,maximum = countRange count
                let! slot = element numeric construction.Site
                let! bytes,alignment = Placement.extentOfSlot graph slot |> needed "An array element lacks a settled physical extent."
                do! demand (bytes>0 && alignment>0 && bytes%alignment=0) "An array element has no admitted contiguous aligned stride."
                let! asyncParticipants =
                    if construction.Default.IsNone && construction.Initialization.IsNone &&
                       not(constructions |> List.exists(fun copy -> copy.Allocation=Some construction.Site && copy.Count=construction.Count)) then
                        asyncInitialization construction count.Range slot bytes
                    else Ok Set.empty
                do! match construction.Default,construction.Initialization with
                    | Some value,initialization ->
                        result {
                            let! valNode = live graph value
                            let! isDefaultValid =
                                match valNode.Kind with
                                | SemanticKind.Literal(NativeLiteral.Bool false) when slot=SettledSlot.Bool -> Ok true
                                | SemanticKind.Literal(NativeLiteral.Char '\000') when slot=SettledSlot.Char -> Ok true
                                | _ ->
                                    result {
                                        let! isZeroVal = integer graph 0I value
                                        return (isZeroVal && (match slot with SettledSlot.Integer _ -> true | _ -> false))
                                    }
                            do! demand isDefaultValid
                                   "Array.zeroCreate no longer carries the exact source default value for its element."
                            match initialization with
                            | Some init ->
                                let! loopCount = loop graph numeric init.Index init.Initial init.Loop init.Guard init.Current init.Step init.Advance [init.Write;init.Advance]
                                let! write = access graph operations init.Write
                                let! bufTarget = allocationTarget graph init.Buffer
                                do! demand (loopCount=construction.Count.Reference && write.Buffer=init.Buffer && write.Index=init.Current && write.Value=Some value && write.Element=slot && bufTarget=construction.Site)
                                       "Array.zeroCreate lost its complete count-correlated default writes."
                            | None ->
                                do! demand (maximum=0I && count.Range=ValueRange.point 0I) "A nonempty zeroCreate allocation has no complete initialization loop."
                        }
                    | None,None ->
                        demand (not asyncParticipants.IsEmpty || (constructions |> List.exists(fun copy -> copy.Allocation=Some construction.Site && copy.Count=construction.Count)))
                               "An uninitialized array allocation lacks its complete source copy construction."
                    | None,Some _ -> Error "An array initializer has no source default-value authority."
                let! declared = getPlatform ()
                let! returnedConstruction =
                    graph.Edges |> List.choose(fun edge->
                        match edge.Role with
                        | EdgeRole.StringCheckedConstruction row when row.Snapshot=construction.Owner && row.Returned.IsSome -> Some row
                        | _ -> None)
                    |> function
                       | [] -> Ok None
                       | [row] -> Ok (Some row)
                       | _ -> Error "The returned snapshot has ambiguous lifetime accounts."
                let! returned =
                    match returnedConstruction with
                    | Some row -> StringByteStorageRecipes.returnedLifetime graph row
                    | None -> Ok None
                let! empty =
                    match returnedConstruction,returned with
                    | Some checkedConstruction,Some _ when count.Range=ValueRange.point 0I ->
                        result {
                            let! representation,declaration =
                                Clef.Compiler.Baker.Ingredients.StringBytes.byteRepresentation graph
                                |> needed "An empty checked snapshot lacks its declared octet representation."
                            do! demand (minimum=0I && maximum=0I && slot=SettledSlot.Integer(8,Some representation.Name))
                                    "An empty checked snapshot lacks its exact zero count and octet element."
                            return Some {Site=node.Id;Snapshot=construction.Owner;Owner=checkedConstruction.Owner;Count=construction.Count.Reference
                                         SourceType=Clef.Compiler.NativeTypedTree.TypeIdentities.ofType node.Type;Declaration=declaration}
                        }
                    | _ -> Ok None
                match empty with
                | Some empty -> admitted<-(node.Id,MemoryWitnessOperation.EmptySnapshot empty)::admitted
                | None ->
                    let _,closed,uses=MemoryAccessRecipes.arrayUses graph construction.Site
                    let! scope,space,residence,uses =
                        match returned with
                        | Some(life,space) ->
                            Ok(life.Application,space,MemoryResidence.Heap(life.Application,space.Node),Set.union uses (Memory.resultIds life))
                        | None ->
                            result {
                                do! demand closed "The dynamic array's complete use family has no admitted local storage lifetime."
                                let! scope = MemoryAccessRecipes.nearestLambda graph construction.Site |> needed "A dynamic array lacks a lexical activation scope."
                                for useId in uses do
                                    let! useNode = live graph useId
                                    let inScope =
                                        match useNode.Kind with
                                        | SemanticKind.ModuleDef _ -> true
                                        | _ -> MemoryAccessRecipes.nearestLambda graph useId = Some scope
                                    do! demand inScope "A dynamic array alias or access escapes its stack activation."
                                let! space =
                                    match declared.Spaces |> List.filter(fun space -> space.Kind="stack" && space.Access.Contains("w")) with
                                    | [space] -> Ok space
                                    | _ -> Error "A dynamic array requires exactly one declared writable stack space."
                                return (scope,space,MemoryResidence.Stack(scope,space.Node),uses)
                            }
                    do! demand (space.Alignment>=alignment && space.Alignment%alignment=0) "The declared stack cannot satisfy the array element alignment."
                    let! core = declared.Core |> needed "An array allocation needs the selected core's declared Pointer dimension."
                    let! pointer =
                        match core.Widths |> List.filter(fun width -> width.Name="Pointer" && width.Bits>0) with
                        | [width] -> Ok width
                        | _ -> Error "Array storage has no unique positive declared Pointer dimension."
                    let capacity=ValueRange.unsignedOf pointer.Bits
                    let! indexMaximum =
                        match capacity with
                        | ValueRange.Bounded(_,hi) -> Ok hi
                        | _ -> Error "A finite declared pointer capacity was expected."
                    let unsigned=ValueRange.isNonNegative count.Range
                    let countCapacity=if unsigned then capacity else ValueRange.twosComplement pointer.Bits
                    let! countMinimum,countMaximum =
                        match countCapacity with
                        | ValueRange.Bounded(lo,hi) -> Ok(lo,hi)
                        | _ -> Error "A finite declared count capacity was expected."
                    let extent=maximum*bigint bytes
                    do! demand (extent<=bigint System.Int64.MaxValue && extent<=indexMaximum && maximum<=countMaximum)
                           "The array's maximum byte extent exceeds the declared index/address domain."
                    do! demand (extent<=bigint space.Capacity) "The array's complete maximum byte extent exceeds its declared stack capacity."
                    let participants=construction.Participants |> Set.union initializationParticipants |> Set.union asyncParticipants |> Set.union uses |> Set.union count.Participants
                                     |> Set.union(Set.ofList(requirement.Participants@[declared.Node;space.Node;core.Node;pointer.Node;scope]))
                    let mutable own=Enrichment.empty
                    let proof label body =
                        let info={Id=sprintf "array_%d_%s" (NodeId.value node.Id) label;Kind="array-"+label;Logic="QF_LIA"
                                  Statement="Source array construction extent and layout fit their exact declared storage authority."
                                  Source=fmtRange node.Range;Refs=[];Body=body}
                        let citizen=obligationNode node (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId()) info |> Memory.markOwned
                        let receipt:MemoryProof={Site=node.Id;Obligation=citizen.Id;Body=body;Participants=participants;Proven=true}
                        own<-Enrichment.combine own {NewNodes=[citizen];NewEdges=Memory.proofRows receipt;Annotated=[]}
                        citizen.Id
                    let layout=proof "element_layout" (ObligationBody.ContinuationLayout([0,bytes,alignment],bytes,alignment))
                    let capacityProof=proof "capacity" (ObligationBody.CapacityFits(int64 extent,space.Capacity))
                    let index=proof "index" (ObligationBody.IntegerRepresentationCoverage(minimum,maximum,countMinimum,countMaximum))
                    let address=proof "address" (ObligationBody.IntegerRepresentationCoverage(0I,extent,0I,indexMaximum))
                    let value={Site=node.Id;Count=construction.Count.Reference;CountCarrier=count;IndexUnsigned=unsigned
                               Element=slot;ElementBytes=bytes;Alignment=alignment;Residence=residence
                               MinimumCount=minimum;MaximumCount=maximum;Requirement=requirement;Construction=construction
                               Participants=participants |> Set.add layout |> Set.add capacityProof |> Set.add index |> Set.add address}
                    admitted<-(node.Id,MemoryWitnessOperation.ArrayAllocation value)::admitted
                    enrichment<-Enrichment.combine enrichment own
            }
        match outcome with
        | Ok () -> ()
        | Error reason -> failures<-Map.add construction.Site reason failures
    for construction in constructions do
        match validateCopy construction with
        | Ok copyWitness -> copies<-copyWitness::copies
        | Error reason -> failures<-Map.add construction.Site reason failures
    // A bare ArrayAllocate is never authority for storage, even when no receipt exists.
    for node in graph.Nodes.Values do
        match node.Kind with
        | SemanticKind.ArrayAllocate _ when executable node.Id && not(required.Contains node.Id) ->
            required<-Set.add node.Id required
            failures<-Map.add node.Id "An array allocation lacks its source construction receipt." failures
        | _ -> ()
    enrichment,List.rev admitted,List.rev copies,failures,required

let settle graph numeric existing =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> settleCore graph numeric existing)
