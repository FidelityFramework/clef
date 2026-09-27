// SPDX-License-Identifier: MIT
/// Late source settlement of array construction, residence and ordered copies.
/// Construction receipts cite the actual guarded program; they do not replace it.
module Clef.Compiler.Baker.Recipes.ArrayMemoryRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module Memory = Clef.Compiler.Baker.Ingredients.MemoryValues
module Placement = Clef.Compiler.PSGSaturation.SemanticGraph.Placement
module Platform = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
module Requirements = Clef.Compiler.PSGSaturation.SemanticGraph.Requirements

exception private MissingContract of string
let private demand condition reason = if not condition then raise(MissingContract reason)
let private needed reason = function Some value -> value | None -> raise(MissingContract reason)
let private live (graph:SemanticGraph) id =
    graph.Nodes.TryFind id |> Option.filter _.IsReachable |> needed "An array construction participant is not a live source occurrence."
let private scalar (numeric:NumericWitnessProjection) id =
    numeric.Values.TryFind id |> needed "An array construction scalar has no source-settled carrier."
let private element (numeric:NumericWitnessProjection) id =
    numeric.Elements.TryFind id |> needed "An array construction lacks its complete-write element slot."
let private elementIdentity (numeric:NumericWitnessProjection) id =
    match numeric.SourceTypes.TryFind id with
    | Some(TypeIdentity.Application(constructor,[element])) when constructor.NativeKind=Some NTUKind.NTUarray -> element
    | _ -> raise(MissingContract "An array copy operand lacks its exact source array element identity.")
let private integer graph expected id =
    match (live graph id).Kind with
    | SemanticKind.Literal(NativeLiteral.Int(value,_)) -> bigint value = expected
    | SemanticKind.Literal(NativeLiteral.UInt(value,_)) -> bigint value = expected
    | _ -> false
let private reference graph binding id =
    match (live graph id).Kind with SemanticKind.VarRef(_,Some actual) -> actual=binding | _ -> false
let private sequence graph id =
    match (live graph id).Kind with
    | SemanticKind.Sequential items when (live graph id).Children=items -> items
    | _ -> raise(MissingContract "Array construction lost its exact ordered source continuation.")
let private bound graph (operand:ArrayBoundOperand) =
    if operand.Actual=operand.Binding && operand.Binding=operand.Reference then
        demand (integer graph 0I operand.Actual) "An unbound array offset must be the exact source zero literal."
    else
        demand (match (live graph operand.Binding).Kind,(live graph operand.Binding).Children with
                | SemanticKind.Binding(_,false,_,_),[actual] -> actual=operand.Actual
                | _ -> false) "An array operand is not bound exactly once to its declared actual."
        demand (reference graph operand.Binding operand.Reference) "An array operand reference no longer names its exact source binding."

let private operation (graph:SemanticGraph) (numeric:NumericWitnessProjection) kind actuals id =
    let settled = numeric.Operations.TryFind id |> needed "An array guard or loop term lacks its source numeric operation contract."
    demand (settled.Site=id && settled.Kind=kind && (settled.Operands |> List.map _.Actual)=actuals)
           "An array guard or loop term changed its exact ordered operands."
    demand (match (live graph id).Kind with
            | SemanticKind.Application(callee,arguments) -> callee=settled.Callee && arguments=actuals
            | _ -> false) "An array numeric operation no longer describes its executable source occurrence."

let private conjunction graph left right id =
    demand (match (live graph id).Kind with
            | SemanticKind.IfThenElse(condition,yes,Some no) when condition=left && yes=right ->
                match (live graph no).Kind with SemanticKind.Literal(NativeLiteral.Bool false) -> true | _ -> false
            | _ -> false) "An array range guard lost its exact short-circuit conjunction."

let private guard graph numeric (operations:Map<NodeId,MemoryWitnessOperation>) (fact:ArrayRangeGuard) : RequirementWitness =
    demand (integer graph 0I fact.Zero) "An array range guard has no exact zero endpoint."
    operation graph numeric NumericOperationKind.GreaterOrEqual [fact.Count;fact.Zero] fact.NonnegativeCount
    match fact.Buffer,fact.Offset,fact.Length,fact.NonnegativeOffset,fact.End,fact.Within with
    | None,None,None,None,None,None ->
        demand (fact.Predicate=fact.NonnegativeCount) "The allocation requirement is not its declared nonnegative count guard."
    | Some buffer,Some offset,Some length,Some nonnegative,Some finish,Some within ->
        demand (match operations.TryFind length with
                | Some(MemoryWitnessOperation.ArrayExtent extent) -> extent.Site=length && extent.Source=buffer
                | Some(MemoryWitnessOperation.BufferExtent extent) -> extent.Site=length && extent.Source=buffer
                | _ -> false) "An array slice guard does not read its exact buffer extent."
        operation graph numeric NumericOperationKind.GreaterOrEqual [offset;fact.Zero] nonnegative
        operation graph numeric NumericOperationKind.Add [offset;fact.Count] finish
        operation graph numeric NumericOperationKind.LessOrEqual [finish;length] within
        let remaining =
            match (live graph fact.Predicate).Kind with
            | SemanticKind.IfThenElse(condition,yes,Some _) when condition=fact.NonnegativeCount -> yes
            | _ -> raise(MissingContract "An array slice requirement lacks its count-first conjunction.")
        conjunction graph nonnegative within remaining
        conjunction graph fact.NonnegativeCount remaining fact.Predicate
    | _ -> raise(MissingContract "An array slice guard has an incomplete buffer/offset/extent premise set.")
    let required = Requirements.tryRequirement graph fact.Requirement |> needed "An array construction lacks its actual always-active Require frontier."
    demand (required.Condition=fact.Predicate && required.Frontier=fact.Frontier && required.Continuation=fact.Continuation)
           "The array requirement no longer guards its exact construction continuation."
    { Site=required.Site;Condition=required.Condition;Diagnostic=required.Diagnostic;Frontier=required.Frontier
      Continuation=required.Continuation;PatternTest=required.PatternTest;Participants=required.Participants }

let private allocationTarget graph id =
    let rec resolve seen current =
        demand (not(Set.contains current seen)) "The allocation alias path is cyclic."
        let seen=Set.add current seen
        match (live graph current).Kind,(live graph current).Children with
        | SemanticKind.ArrayAllocate _,_ -> current
        | SemanticKind.Binding(_,false,_,_),[value] -> resolve seen value
        | SemanticKind.VarRef(_,Some value),_ | SemanticKind.TypeAnnotation(value,_),_ -> resolve seen value
        | SemanticKind.Sequential items,_ when not items.IsEmpty -> resolve seen (List.last items)
        | _ -> raise(MissingContract "A constructed destination has no exact allocation provenance.")
    resolve Set.empty id

let private access graph (operations:Map<NodeId,MemoryWitnessOperation>) frontier =
    let rows=graph.Edges |> List.filter(fun edge ->
        edge.Role=EdgeRole.MemoryAccessGuard &&
        (match edge.Sources with [_;_;_;_;_;_;_;_;actual] -> actual=frontier | _ -> false))
    match rows with
    | [{Class=EdgeClass.Provenance;Ordinal=0;Target=site}] ->
        match operations.TryFind site with
        | Some(MemoryWitnessOperation.ArrayAccess value) when value.Site=site && value.Bounds.Requirement.Frontier=frontier -> value
        | _ -> raise(MissingContract "A constructed copy access has no settled guarded memory operation.")
    | _ -> raise(MissingContract "A constructed copy access lost its unique source bounds-guard rewrite.")

let private loop (graph:SemanticGraph) (numeric:NumericWitnessProjection) index initial loopId predicate current step advance body =
    demand (integer graph 0I initial) "An array construction loop must begin at its exact zero index."
    demand (match (live graph index).Kind,(live graph index).Children with
            | SemanticKind.Binding(_,true,_,_),[value] -> value=initial
            | _ -> false) "An array construction loop lost its actual mutable induction binding."
    demand (reference graph index current) "An array construction loop reads another induction binding."
    let guardIndex,count =
        match numeric.Operations.TryFind predicate with
        | Some fact when fact.Kind=NumericOperationKind.Less ->
            match fact.Operands with [atGuard;count] -> atGuard.Actual,count.Actual | _ -> raise(MissingContract "An array loop guard changed arity.")
        | _ -> raise(MissingContract "An array loop lacks its source-settled strict count bound.")
    demand (reference graph index guardIndex) "An array loop guard reads another induction binding."
    operation graph numeric NumericOperationKind.Less [guardIndex;count] predicate
    let one =
        match numeric.Operations.TryFind step with
        | Some fact -> match fact.Operands with [atStep;one] when atStep.Actual=current -> one.Actual | _ -> raise(MissingContract "An array loop step changed its operands.")
        | None -> raise(MissingContract "An array loop step lacks source numeric settlement.")
    demand (integer graph 1I one) "An array construction loop does not advance by exactly one."
    operation graph numeric NumericOperationKind.Add [current;one] step
    demand (match (live graph advance).Kind with
            | SemanticKind.Set(target,value) -> reference graph index target && value=step
            | _ -> false) "An array loop does not assign its exact next index to its induction binding."
    demand (match (live graph loopId).Kind with
            | SemanticKind.WhileLoop(condition,actions) -> condition=predicate && sequence graph actions=body
            | _ -> false) "An array construction lost its complete ordered loop body."
    count

let private allocationRow (graph:SemanticGraph) (construction:ArrayAllocationConstruction) =
    let rows=graph.Edges |> List.filter(fun edge -> match edge.Role with EdgeRole.ArrayAllocationConstruction item -> item.Site=construction.Site | _ -> false)
    demand (Clef.Compiler.Baker.Ingredients.NumericValues.sameRows [Memory.allocationConstructionRow construction] rows)
           "An array allocation construction row is absent, duplicated or inconsistent."

let private copyRow (graph:SemanticGraph) (construction:ArrayCopyConstruction) =
    let rows=graph.Edges |> List.filter(fun edge -> match edge.Role with EdgeRole.ArrayCopyConstruction item -> item.Site=construction.Site | _ -> false)
    demand (Clef.Compiler.Baker.Ingredients.NumericValues.sameRows [Memory.copyConstructionRow construction] rows)
           "An array copy construction row is absent, duplicated or inconsistent."

let private initializedBlock graph allocation output prefix actions block =
    let items=sequence graph block
    match items with
    | stored::tail ->
        demand (match (live graph stored).Kind,(live graph stored).Children with
                | SemanticKind.Binding(_,false,_,_),[actual] -> actual=allocation
                | _ -> false) "Array storage is not bound before its initializer."
        demand (reference graph stored output && tail=prefix@actions@[output])
               "The initialized array escapes before its complete ordered writes."
    | _ -> raise(MissingContract "An array initializer has no storage continuation.")

/// No operation is admitted from a known subset of construction participants.
/// Every allocation and copy receipt validates its complete executable recipe.
let settle (graph:SemanticGraph) (numeric:NumericWitnessProjection) (existing:(NodeId*MemoryWitnessOperation) list)
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
    let platform=lazy(Platform.resolve graph |> needed "An array allocation needs the selected source platform declaration.")
    let countRange (count:ScalarCarrier) =
        demand (match count.Slot with SettledSlot.Integer _ -> true | _ -> false) "An array count needs a source-settled integer carrier."
        match count.Range with
        | ValueRange.Bounded(lo,hi) when lo<=hi && hi>=0I -> max 0I lo,hi
        | _ -> raise(MissingContract "An array count has no finite nonnegative successful allocation range.")
    let validateCopy (construction:ArrayCopyConstruction) =
        copyRow graph construction
        [construction.Source;construction.SourceOffset;construction.DestinationOffset;construction.Count] |> List.iter(bound graph)
        let count=scalar numeric construction.Count.Reference
        let _,maximum=countRange count
        let requirements=construction.Requirements |> List.map(guard graph numeric operations)
        demand (not requirements.IsEmpty && (construction.Requirements |> List.forall(fun item -> item.Count=construction.Count.Reference)))
               "An array copy lacks its count-correlated range requirements."
        construction.Requirements |> List.pairwise |> List.iter(fun (outer,inner) ->
            demand (outer.Continuation=inner.Frontier) "Array copy requirements no longer execute in their declared order.")
        let read,write,actions =
            match construction.Index,construction.IndexInitial,construction.Loop,construction.Guard,construction.Current,
                  construction.SourceIndex,construction.DestinationIndex,construction.Read,construction.Write,construction.Step,construction.Advance with
            | Some index,Some initial,Some loopId,Some predicate,Some current,Some sourceIndex,Some destinationIndex,Some read,Some write,Some step,Some advance ->
                let loopCount=loop graph numeric index initial loopId predicate current step advance [read;write;advance]
                demand (loopCount=construction.Count.Reference) "An array copy loop uses another count."
                operation graph numeric NumericOperationKind.Add [construction.SourceOffset.Reference;current] sourceIndex
                operation graph numeric NumericOperationKind.Add [construction.DestinationOffset.Reference;current] destinationIndex
                let source,target=access graph operations read,access graph operations write
                demand (source.Buffer=construction.Source.Reference && source.Index=sourceIndex && source.Value.IsNone &&
                        target.Buffer=construction.Destination && target.Index=destinationIndex && target.Value=Some read &&
                        elementIdentity numeric source.Buffer=elementIdentity numeric target.Buffer)
                       "An array copy's read/write pair does not preserve its exact ordered element transfer."
                Some source,Some target,[index;loopId]
            | None,None,None,None,None,None,None,None,None,None,None when maximum=0I && count.Range=ValueRange.point 0I -> None,None,[]
            | _ -> raise(MissingContract "An array copy lacks its complete index/read/write/advance loop construction.")
        match construction.Allocation with
        | Some allocation ->
            demand (allocationTarget graph construction.Destination=allocation && integer graph 0I construction.DestinationOffset.Reference)
                   "A fresh snapshot copy no longer targets its own zero-based allocation."
            let owner=allocations |> List.filter(fun item -> item.Site=allocation)
            demand (match owner with [item] -> item.Owner=construction.Site && item.Count=construction.Count && item.Default.IsNone | _ -> false)
                   "A snapshot allocation does not have this exact source copy owner and count."
            demand (construction.Requirements |> List.exists(fun item -> item.Buffer=Some construction.Source.Reference && item.Offset=Some construction.SourceOffset.Reference))
                   "A snapshot copy lacks the range guard for its exact source window."
            let finalGuard=List.last construction.Requirements
            // A sub's root binds the actuals before its guarded initialized block;
            // a blit snapshot is itself that initialized block.
            let block=
                match construction.Requirements with
                | [guard] ->
                    demand (sequence graph construction.Site=[construction.Source.Binding;construction.SourceOffset.Binding;construction.Count.Binding;guard.Frontier])
                           "Array.sub lost its exact actual-binding and Require execution prefix."
                    finalGuard.Continuation
                | [_;_] -> construction.Site
                | _ -> raise(MissingContract "A source snapshot has an unsupported requirement frontier composition.")
            initializedBlock graph allocation construction.Destination [construction.DestinationOffset.Reference] actions block
        | None ->
            let snapshot=constructions |> List.filter(fun item -> item.Site=construction.Source.Actual && item.Allocation.IsSome)
            let snapshot=match snapshot with [item] -> item | _ -> raise(MissingContract "An array blit requires one complete preceding source snapshot.")
            demand (snapshot.Count=construction.Count && snapshot.Requirements=construction.Requirements &&
                    integer graph 0I construction.SourceOffset.Reference)
                   "An array blit writeback no longer reads its complete count-correlated snapshot."
            demand (construction.Requirements |> List.exists(fun item -> item.Buffer=Some construction.Destination && item.Offset=Some construction.DestinationOffset.Reference))
                   "An array blit lacks its exact destination range guard."
            let destinationBinding=
                match (live graph construction.Destination).Kind with
                | SemanticKind.VarRef(_,Some binding) ->
                    demand (match (live graph binding).Kind,(live graph binding).Children with
                            | SemanticKind.Binding(_,false,_,_),[_] -> true | _ -> false)
                           "An array blit destination lost its single immutable actual binding."
                    binding
                | _ -> raise(MissingContract "An array blit destination is not its bound source operand.")
            demand (construction.Requirements.Length=2 &&
                    sequence graph construction.Site=[snapshot.Source.Binding;snapshot.SourceOffset.Binding;destinationBinding;
                                                       construction.DestinationOffset.Binding;construction.Count.Binding;
                                                       (List.head construction.Requirements).Frontier])
                   "Array.blit lost its exact ordered actual bindings and range-failure frontier."
            let body=sequence graph (List.last construction.Requirements).Continuation
            match body with
            | first::tail ->
                demand (first=construction.Source.Binding && tail.Length=actions.Length+1 && List.take actions.Length tail=actions)
                       "An array blit writes before the complete snapshot has been bound."
                demand (match (live graph (List.last tail)).Kind with SemanticKind.Literal NativeLiteral.Unit -> true | _ -> false)
                       "An array blit has no exact unit completion."
            | _ -> raise(MissingContract "An array blit has no ordered snapshot/writeback continuation.")
        let actualCount=scalar numeric construction.Count.Actual
        let participants=construction.Participants |> Set.union count.Participants |> Set.union actualCount.Participants
        let participants=List.fold(fun found (item:RequirementWitness) -> Set.union found (Set.ofList item.Participants)) participants requirements
        let participants=[read;write] |> List.choose id |> List.fold(fun found (item:MemoryArrayAccessWitness) -> Set.union found item.Participants) participants
        { Site=construction.Site;Source=construction.Source.Actual;SourceOffset=construction.SourceOffset.Actual
          Destination=construction.Destination;DestinationOffset=construction.DestinationOffset.Actual
          Count=construction.Count.Actual;CountCarrier=actualCount;Allocation=construction.Allocation;Loop=construction.Loop
          Read=read;Write=write;Requirements=requirements;Participants=participants }
    for construction in allocations do
        required<-Set.add construction.Site required
        try
            allocationRow graph construction
            bound graph construction.Count
            let node=live graph construction.Site
            demand (node.Kind=SemanticKind.ArrayAllocate construction.Count.Reference && node.Children=[construction.Count.Reference])
                   "An array allocation changed its exact source count operand."
            let requirement=guard graph numeric operations construction.Guard
            demand (construction.Guard.Count=construction.Count.Reference) "An array allocation requirement guards another count."
            let count=scalar numeric construction.Count.Reference
            let minimum,maximum=countRange count
            let slot=element numeric construction.Site
            let bytes,alignment=Placement.extentOfSlot graph slot |> needed "An array element lacks a settled physical extent."
            demand (bytes>0 && alignment>0 && bytes%alignment=0) "An array element has no admitted contiguous aligned stride."
            match construction.Default,construction.Initialization with
            | Some value,initialization ->
                demand (sequence graph construction.Owner=[construction.Count.Binding;value;construction.Guard.Frontier])
                       "Array.zeroCreate lost its exact count/default binding and Require execution prefix."
                demand (match (live graph value).Kind with
                        | SemanticKind.Literal(NativeLiteral.Bool false) when slot=SettledSlot.Bool -> true
                        | SemanticKind.Literal(NativeLiteral.Char '\000') when slot=SettledSlot.Char -> true
                        | _ -> integer graph 0I value && (match slot with SettledSlot.Integer _ -> true | _ -> false))
                       "Array.zeroCreate no longer carries the exact source default value for its element."
                match initialization with
                | Some init ->
                    let loopCount=loop graph numeric init.Index init.Initial init.Loop init.Guard init.Current init.Step init.Advance [init.Write;init.Advance]
                    let write=access graph operations init.Write
                    demand (loopCount=construction.Count.Reference && write.Buffer=init.Buffer && write.Index=init.Current && write.Value=Some value && write.Element=slot && allocationTarget graph init.Buffer=construction.Site)
                           "Array.zeroCreate lost its complete count-correlated default writes."
                    initializedBlock graph construction.Site init.Buffer [] [init.Index;init.Loop] construction.Guard.Continuation
                | None ->
                    demand (maximum=0I && count.Range=ValueRange.point 0I) "A nonempty zeroCreate allocation has no complete initialization loop."
                    let body=sequence graph construction.Guard.Continuation
                    demand (body.Length=2) "An empty zeroCreate changed its storage continuation."
                    initializedBlock graph construction.Site (List.last body) [] [] construction.Guard.Continuation
            | None,None ->
                demand (constructions |> List.exists(fun copy -> copy.Allocation=Some construction.Site && copy.Count=construction.Count))
                       "An uninitialized array allocation lacks its complete source copy construction."
            | None,Some _ -> raise(MissingContract "An array initializer has no source default-value authority.")
            let _,closed,uses=MemoryAccessRecipes.arrayUses graph construction.Site
            demand closed "The dynamic array's complete use family has no admitted local storage lifetime."
            let scope=MemoryAccessRecipes.nearestLambda graph construction.Site |> needed "A dynamic array lacks a lexical activation scope."
            demand (uses |> Set.forall(fun id -> match (live graph id).Kind with SemanticKind.ModuleDef _ -> true | _ -> MemoryAccessRecipes.nearestLambda graph id=Some scope))
                   "A dynamic array alias or access escapes its stack activation."
            let declared=platform.Value
            let space=match declared.Spaces |> List.filter(fun space -> space.Kind="stack" && space.Access.Contains("w")) with
                      | [space] -> space | _ -> raise(MissingContract "A dynamic array requires exactly one declared writable stack space.")
            demand (space.Alignment>=alignment && space.Alignment%alignment=0) "The declared stack cannot satisfy the array element alignment."
            let core=declared.Core |> needed "An array allocation needs the selected core's declared Pointer dimension."
            let pointer=match core.Widths |> List.filter(fun width -> width.Name="Pointer" && width.Bits>0) with
                        | [width] -> width | _ -> raise(MissingContract "Array storage has no unique positive declared Pointer dimension.")
            let capacity=ValueRange.unsignedOf pointer.Bits
            let indexMaximum=match capacity with ValueRange.Bounded(_,hi) -> hi | _ -> invalidOp "A finite declared pointer capacity was expected."
            let unsigned=ValueRange.isNonNegative count.Range
            let countCapacity=if unsigned then capacity else ValueRange.twosComplement pointer.Bits
            let countMinimum,countMaximum=match countCapacity with ValueRange.Bounded(lo,hi) -> lo,hi | _ -> invalidOp "A finite declared count capacity was expected."
            let extent=maximum*bigint bytes
            demand (extent<=bigint System.Int64.MaxValue && extent<=indexMaximum && maximum<=countMaximum)
                   "The array's maximum byte extent exceeds the declared index/address domain."
            demand (extent<=bigint space.Capacity) "The array's complete maximum byte extent exceeds its declared stack capacity."
            let participants=construction.Participants |> Set.union uses |> Set.union count.Participants
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
            let capacity=proof "capacity" (ObligationBody.CapacityFits(int64 extent,space.Capacity))
            let index=proof "index" (ObligationBody.IntegerRepresentationCoverage(minimum,maximum,countMinimum,countMaximum))
            let address=proof "address" (ObligationBody.IntegerRepresentationCoverage(0I,extent,0I,indexMaximum))
            let value={Site=node.Id;Count=construction.Count.Reference;CountCarrier=count;IndexUnsigned=unsigned
                       Element=slot;ElementBytes=bytes;Alignment=alignment;Residence=MemoryResidence.Stack(scope,space.Node)
                       MinimumCount=minimum;MaximumCount=maximum;Requirement=requirement
                       Participants=participants |> Set.add layout |> Set.add capacity |> Set.add index |> Set.add address}
            admitted<-(node.Id,MemoryWitnessOperation.ArrayAllocation value)::admitted
            enrichment<-Enrichment.combine enrichment own
        with MissingContract reason -> failures<-Map.add construction.Site reason failures
    for construction in constructions do
        try copies<-validateCopy construction::copies
        with MissingContract reason -> failures<-Map.add construction.Site reason failures
    // A bare ArrayAllocate is never authority for storage, even when no receipt exists.
    for node in graph.Nodes.Values do
        match node.Kind with
        | SemanticKind.ArrayAllocate _ when executable node.Id && not(required.Contains node.Id) ->
            required<-Set.add node.Id required
            failures<-Map.add node.Id "An array allocation lacks its source construction receipt." failures
        | _ -> ()
    enrichment,List.rev admitted,List.rev copies,failures,required
