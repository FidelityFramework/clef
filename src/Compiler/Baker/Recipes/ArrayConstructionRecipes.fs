// SPDX-License-Identifier: MIT
/// Array construction is a source allocation, requirements and ordered writes.
/// Target witnesses only consume the settled storage operation.
module Clef.Compiler.Baker.Recipes.ArrayConstructionRecipes

open XParsec.Parsers
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.SaturationCombinators
open Clef.Compiler.Baker.Ingredients.Primitives
open Clef.Compiler.Baker.Ingredients.Closures
open Clef.Compiler.Baker.Recipes.Decomposition
module C = Clef.Compiler.Baker.Ingredients.Continuations
module Memory = Clef.Compiler.Baker.Ingredients.MemoryValues
module Shapes = Clef.Compiler.Baker.Ingredients.ArrayShapes

exception MissingConstruction of string

let private selected (graph: SemanticGraph) (node: SemanticNode) =
    match node.Kind with
    | SemanticKind.Application _ ->
        match Shapes.intrinsicApplication graph node.Id with
        | Some({ Module = IntrinsicModule.Array; Operation = operation }, arguments, _)
            when (operation = "zeroCreate" && arguments.Length = 1) ||
                 (operation = "sub" && arguments.Length = 3) ||
                 (operation = "blit" && arguments.Length = 5) -> Some(operation, arguments)
        | _ -> None
    | _ -> None

let candidates (graph: SemanticGraph) =
    let excluded=Memory.excluded graph
    graph.Nodes.Values |> Seq.filter (fun node ->
        Memory.executable graph excluded node.Id && not (node.Metadata.ContainsKey "Baker.ArrayConstructionError") && (selected graph node).IsSome) |> Seq.toList

let private arrayElement ty =
    match applySubst ty with
    | NativeType.TApp(tc,[element]) when tc.NTUKind = Some NTUKind.NTUarray -> element
    | _ -> raise(MissingConstruction "The array constructor lacks its checked element type.")

let private defaultValue element =
    match Types.tryGetNTUKind element with
    | Some(NTUKind.NTUint _ | NTUKind.NTUuint _) -> numLit 0L element
    | _ when applySubst element = Types.boolType -> boolLit false
    | _ when applySubst element = Types.charType -> createAndEmit (SemanticKind.Literal(NativeLiteral.Char '\000')) element
    | _ -> raise(MissingConstruction "Array.zeroCreate has no admitted source default-value construction for this element type; CLR/null defaults are not source authority.")

let private bound (graph: SemanticGraph) name actual = saturation {
    let ty = graph.Nodes[actual].Type
    let! binding = letBind name actual ty
    let! reference = varRef name (Some binding) ty
    return { Actual=actual; Binding=binding; Reference=reference }
}

let private extent arrayType buffer = saturation {
    let info = { Module=IntrinsicModule.Array; Operation="length"; Category=IntrinsicCategory.Memory; FullName="Array.length" }
    let! callee = createAndEmit (SemanticKind.Intrinsic info) (NativeType.TFun(arrayType, Types.intType))
    return! app callee [buffer] Types.intType
}

let private requireRange (source: SemanticNode) arrayType buffer offset count continuation resultType = saturation {
    let! zero = intLit 0
    let! nonnegative = ge count zero Types.intType
    let! details =
        match buffer,offset with
        | Some buffer,Some offset -> saturation {
            let! length = extent arrayType buffer
            let! positiveOffset = ge offset zero Types.intType
            let! finish = add offset count Types.intType
            let! within = le finish length Types.intType
            let! remaining = andAlso positiveOffset within
            let! predicate = andAlso nonnegative remaining
            return predicate,Some length,Some positiveOffset,Some finish,Some within }
        | None,None -> preturn(nonnegative,None,None,None,None)
        | _ -> fail (XParsec.ErrorType.Message "An array slice guard requires both its buffer and offset.")
    let predicate,length,positiveOffset,finish,within = details
    let diagnostic = sprintf "Array construction bounds failed at %s:%d:%d" source.Range.File source.Range.Start.Line source.Range.Start.Column
    let! required = createWithChildren (SemanticKind.Require(predicate,diagnostic)) Types.unitType [predicate]
    let! frontier = C.block [required;continuation] resultType
    return { Requirement=required; Predicate=predicate; Frontier=frontier; Continuation=continuation
             Count=count; Offset=offset; Buffer=buffer; Length=length; Zero=zero
             NonnegativeCount=nonnegative; NonnegativeOffset=positiveOffset; End=finish; Within=within }
}

let private requirementRow (guard: ArrayRangeGuard) =
    { Class=EdgeClass.Provenance; Role=EdgeRole.MatchRequirement; Ordinal=1
      Sources=[guard.Requirement;guard.Predicate;guard.Continuation]; Target=guard.Frontier }

let private knownEmpty (graph: SemanticGraph) count =
    graph.Nodes.TryFind count |> Option.bind _.ValueRange = Some(ValueRange.point 0I)

type Expansion = { Nodes:SemanticNode list; Edges:Hyperedge list }

let materialize (graph: SemanticGraph) (source: SemanticNode) : Expansion =
    let operation,actuals = selected graph source |> Option.defaultWith (fun () -> raise(MissingConstruction "No array construction occurrence."))
    let state = SaturationState.create source.Range ("Array."+operation) (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId()) source.Id graph.Platform
    let allocations = ResizeArray<ArrayAllocationConstruction>()
    let copies = ResizeArray<ArrayCopyConstruction>()
    let guards = ResizeArray<ArrayRangeGuard>()
    let zeroLoop output (count:ArrayBoundOperand) value = saturation {
        if knownEmpty graph count.Actual then return None,[] else
        let! zero = intLit 0
        let! index = C.mutableBinding "__array_index" zero Types.intType
        let! atGuard = varRef "__array_index" (Some index) Types.intType
        let! predicate = lt atGuard count.Reference Types.intType
        let! current = varRef "__array_index" (Some index) Types.intType
        let! store = createWithChildren (SemanticKind.IndexSet(output,current,value)) Types.unitType [output;current;value]
        let! one = intLit 1
        let! next = add current one Types.intType
        let! advance = C.assign index "__array_index" Types.intType next
        let! body = C.block [store;advance] Types.unitType
        let! loop = createWithChildren (SemanticKind.WhileLoop(predicate,body)) Types.unitType [predicate;body]
        return Some {Buffer=output;Index=index;Initial=zero;Loop=loop;Guard=predicate
                     Current=current;Write=store;Step=next;Advance=advance},[index;loop]
    }
    let copyLoop owner arrayType (input:ArrayBoundOperand) (sourceOffset:ArrayBoundOperand) destination (destinationOffset:ArrayBoundOperand) (count:ArrayBoundOperand) allocation = saturation {
        if knownEmpty graph count.Actual then
            return { Site=owner; Source=input; SourceOffset=sourceOffset; Destination=destination
                     DestinationOffset=destinationOffset; Count=count; Allocation=allocation
                     Index=None;IndexInitial=None;Loop=None;Guard=None;Current=None;SourceIndex=None;DestinationIndex=None
                     Read=None;Write=None;Step=None;Advance=None;Requirements=[];Participants=Set.empty },[]
        else
        let element = arrayElement arrayType
        let! zero = intLit 0
        let! index = C.mutableBinding "__array_index" zero Types.intType
        let! atGuard = varRef "__array_index" (Some index) Types.intType
        let! predicate = lt atGuard count.Reference Types.intType
        let! current = varRef "__array_index" (Some index) Types.intType
        let! sourceIndex = add sourceOffset.Reference current Types.intType
        let! destinationIndex = add destinationOffset.Reference current Types.intType
        let! read = createWithChildren (SemanticKind.IndexGet(input.Reference,sourceIndex)) element [input.Reference;sourceIndex]
        let! write = createWithChildren (SemanticKind.IndexSet(destination,destinationIndex,read)) Types.unitType [destination;destinationIndex;read]
        let! one = intLit 1
        let! next = add current one Types.intType
        let! advance = C.assign index "__array_index" Types.intType next
        let! body = C.block [read;write;advance] Types.unitType
        let! loop = createWithChildren (SemanticKind.WhileLoop(predicate,body)) Types.unitType [predicate;body]
        return { Site=owner;Source=input;SourceOffset=sourceOffset;Destination=destination;DestinationOffset=destinationOffset
                 Count=count;Allocation=allocation;Index=Some index;IndexInitial=Some zero;Loop=Some loop;Guard=Some predicate
                 Current=Some current;SourceIndex=Some sourceIndex;DestinationIndex=Some destinationIndex
                 Read=Some read;Write=Some write;Step=Some next;Advance=Some advance;Requirements=[];Participants=Set.empty },[index;loop]
    }
    let parser = saturation {
        match operation,actuals with
        | "zeroCreate",[actualCount] ->
            let element = arrayElement source.Type
            let! count = bound graph "__array_count" actualCount
            let! zero = defaultValue element
            let! allocation = createWithChildren (SemanticKind.ArrayAllocate count.Reference) source.Type [count.Reference]
            let! stored = letBind "__array_storage" allocation source.Type
            let! output = varRef "__array_storage" (Some stored) source.Type
            let! initialization,actions = zeroLoop output count zero
            let! initialized = C.block (stored::actions@[output]) source.Type
            let! guard = requireRange source source.Type None None count.Reference initialized source.Type
            guards.Add guard
            allocations.Add { Site=allocation;Owner=source.Id;Count=count;Default=Some zero;Initialization=initialization;Guard=guard;Participants=Set.empty }
            do! enrich source (SemanticKind.Sequential[count.Binding;zero;guard.Frontier]) source.Type [count.Binding;zero;guard.Frontier] source.EmissionStrategy false
        | "sub",[input;offset;actualCount] ->
            let arrayType = graph.Nodes[input].Type
            let! input = bound graph "__array_source" input
            let! offset = bound graph "__array_offset" offset
            let! count = bound graph "__array_count" actualCount
            let! allocation = createWithChildren (SemanticKind.ArrayAllocate count.Reference) arrayType [count.Reference]
            let! stored = letBind "__array_storage" allocation arrayType
            let! output = varRef "__array_storage" (Some stored) arrayType
            let! zero = intLit 0
            let destinationOffset = { Actual=zero;Binding=zero;Reference=zero }
            let! copy,actions = copyLoop source.Id arrayType input offset output destinationOffset count (Some allocation)
            let! initialized = C.block (stored::zero::actions@[output]) arrayType
            let! guard = requireRange source arrayType (Some input.Reference) (Some offset.Reference) count.Reference initialized arrayType
            guards.Add guard
            allocations.Add { Site=allocation;Owner=source.Id;Count=count;Default=None;Initialization=None;Guard=guard;Participants=Set.empty }
            copies.Add { copy with Requirements=[guard] }
            do! enrich source (SemanticKind.Sequential[input.Binding;offset.Binding;count.Binding;guard.Frontier]) source.Type [input.Binding;offset.Binding;count.Binding;guard.Frontier] source.EmissionStrategy false
        | "blit",[input;sourceOffset;destination;destinationOffset;actualCount] ->
            let arrayType = graph.Nodes[input].Type
            let! input = bound graph "__array_source" input
            let! sourceOffset = bound graph "__array_source_offset" sourceOffset
            let! destination = bound graph "__array_destination" destination
            let! destinationOffset = bound graph "__array_destination_offset" destinationOffset
            let! count = bound graph "__array_count" actualCount
            let! snapshotOwner = C.block [] arrayType
            let! allocation = createWithChildren (SemanticKind.ArrayAllocate count.Reference) arrayType [count.Reference]
            let! stored = letBind "__array_snapshot" allocation arrayType
            let! output = varRef "__array_snapshot" (Some stored) arrayType
            let! zero = intLit 0
            let zeroOffset = { Actual=zero;Binding=zero;Reference=zero }
            let! snapshot,first = copyLoop snapshotOwner arrayType input sourceOffset output zeroOffset count (Some allocation)
            let! snapshotState = getUserState
            let snapshotNode = snapshotState.EmittedNodes |> List.find (fun node -> node.Id=snapshotOwner)
            do! enrich snapshotNode (SemanticKind.Sequential(stored::zero::first@[output])) arrayType (stored::zero::first@[output]) snapshotNode.EmissionStrategy false
            let! snapshotBinding = letBind "__array_copied_source" snapshotOwner arrayType
            let! snapshotRef = varRef "__array_copied_source" (Some snapshotBinding) arrayType
            let copied = { Actual=snapshotOwner;Binding=snapshotBinding;Reference=snapshotRef }
            let! writeback,second = copyLoop source.Id arrayType copied zeroOffset destination.Reference destinationOffset count None
            let! result = unitLit
            let! initialized = C.block (snapshotBinding::second@[result]) Types.unitType
            let! targetGuard = requireRange source arrayType (Some destination.Reference) (Some destinationOffset.Reference) count.Reference initialized Types.unitType
            let! sourceGuard = requireRange source arrayType (Some input.Reference) (Some sourceOffset.Reference) count.Reference targetGuard.Frontier Types.unitType
            guards.Add sourceGuard; guards.Add targetGuard
            allocations.Add { Site=allocation;Owner=snapshotOwner;Count=count;Default=None;Initialization=None;Guard=sourceGuard;Participants=Set.empty }
            copies.Add { snapshot with Requirements=[sourceGuard;targetGuard] }
            copies.Add { writeback with Requirements=[sourceGuard;targetGuard] }
            let prefix=[input.Binding;sourceOffset.Binding;destination.Binding;destinationOffset.Binding;count.Binding;sourceGuard.Frontier]
            do! enrich source (SemanticKind.Sequential prefix) source.Type prefix source.EmissionStrategy false
        | _ -> return! fail (XParsec.ErrorType.Message "Array construction does not have its declared ordered operands.")
    }
    let result,created = run state parser
    match result with
    | NoMatch reason -> raise(MissingConstruction reason)
    | Matched () ->
        let participants = Set.ofList(source.Id::actuals @ (created |> List.map _.Id))
        let allocationRows = allocations |> Seq.map (fun construction ->
            let construction={construction with Participants=participants}
            Memory.allocationConstructionRow construction) |> Seq.toList
        let copyRows = copies |> Seq.map (fun construction ->
            let construction={construction with Participants=participants}
            Memory.copyConstructionRow construction) |> Seq.toList
        let storage = graph.Edges |> List.collect (fun edge ->
            match edge.Role with
            | EdgeRole.StringByteStorage _ when edge.Target=source.Id ->
                allocations |> Seq.map (fun construction -> {edge with Target=construction.Site;Sources=source.Id::construction.Site::edge.Sources}) |> Seq.toList
            | _ -> [])
        let oldIncidence = structuralIncidence source |> List.map (fun edge -> edge.Class,edge.Role,edge.Ordinal,edge.Sources,edge.Target) |> Set.ofList
        { Nodes=created
          Edges=(graph.Edges |> List.filter(fun edge -> not(oldIncidence.Contains(edge.Class,edge.Role,edge.Ordinal,edge.Sources,edge.Target))))
                @ (created |> List.collect structuralIncidence) @ (guards |> Seq.map requirementRow |> Seq.toList) @ allocationRows @ copyRows @ storage }
