// SPDX-License-Identifier: MIT
/// A string view follows an already validated source snapshot construction.
/// Neither a byte carrier nor a historical snapshot marker proves a copy.
module Clef.Compiler.Baker.Recipes.StringViewRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Bytes = Clef.Compiler.Baker.Ingredients.StringBytes

exception private MissingContract of string
let private demand condition reason = if not condition then raise (MissingContract reason)
let private needed reason = function Some value -> value | None -> raise (MissingContract reason)
let private only reason = function [value] -> value | _ -> raise (MissingContract reason)
let private live (graph:SemanticGraph) id =
    graph.Nodes.TryFind id |> Option.filter _.IsReachable |> needed "A string snapshot premise is not a live source occurrence."

let private endpoint (graph:SemanticGraph) start =
    let rec walk seen id =
        demand (not(Set.contains id seen)) "A string snapshot alias is cyclic."
        let seen=Set.add id seen
        match (live graph id).Kind with
        | SemanticKind.VarRef(_,Some binding) ->
            match (live graph binding).Kind with
            | SemanticKind.Binding(_,false,_,_) | SemanticKind.PatternBinding _ -> walk seen binding
            | _ -> id
        | SemanticKind.Binding(_,false,_,_) ->
            match (live graph id).Children with [inner] -> walk seen inner | _ -> id
        | SemanticKind.TypeAnnotation(inner,_) -> walk seen inner
        | SemanticKind.Sequential values when not values.IsEmpty -> walk seen (List.last values)
        | _ -> id
    walk Set.empty start

let private application (graph:SemanticGraph) site =
    let rec walk seen id arguments =
        if Set.contains id seen then None else
        let seen=Set.add id seen
        match graph.Nodes.TryFind id with
        | Some {Kind=SemanticKind.Intrinsic info} -> Some(info,arguments)
        | Some {Kind=SemanticKind.Application(callee,actuals)} -> walk seen callee (actuals@arguments)
        | Some {Kind=SemanticKind.TypeAnnotation(inner,_)} -> walk seen inner arguments
        | _ -> None
    walk Set.empty site []

let private view (graph:SemanticGraph) (node:SemanticNode) =
    match node.Kind,application graph node.Id with
    | SemanticKind.Application _,Some(info,[source]) when info.Module=IntrinsicModule.String ->
        match info.Operation with
        | "fromBytes" -> Some(MemoryStringViewDirection.FromBytes,source)
        | "toBytes" -> Some(MemoryStringViewDirection.ToBytes,source)
        | _ -> None
    | _ -> None

let private carrierRepresentation (numeric:NumericWitnessProjection) id =
    match numeric.OccurrenceRepresentations.TryFind id with
    | Some(Ok value) -> value
    | Some(Error reason) -> raise(MissingContract reason)
    | None -> raise(MissingContract "A string view lacks its exact source-settled buffer representation.")

let private zero (graph:SemanticGraph) id =
    match (live graph (endpoint graph id)).Kind with
    | SemanticKind.Literal(NativeLiteral.Int(0L,_)) | SemanticKind.Literal(NativeLiteral.UInt(0UL,_)) -> true
    | _ -> false

let private completeCount graph source count =
    match application graph (endpoint graph count) with
    | Some(info,[buffer]) when info.Module=IntrinsicModule.Array && info.Operation="length" ->
        endpoint graph source=endpoint graph buffer
    | _ -> false

let private excluded (graph:SemanticGraph) =
    let rec collect seen id =
        if Set.contains id seen then seen else
        match graph.Nodes.TryFind id with
        | Some node -> List.fold collect (Set.add id seen) node.Children
        | None -> Set.add id seen
    let declarations=graph.Edges |> List.fold (fun found edge ->
        match edge.Role with EdgeRole.BoundaryDeclaration declaration -> collect found declaration.Binding | _ -> found) Set.empty
    Set.union declarations (Clef.Compiler.PSGSaturation.SemanticGraph.OrdinaryDemand.project graph).DeferredOnly

/// Basic memory access and array-copy owners run first. Their immutable rows
/// authorize this final view; this recipe never reconstructs a missing copy.
let settle (graph:SemanticGraph) (numeric:NumericWitnessProjection)
           (operations:Map<NodeId,MemoryWitnessOperation>) (copies:Map<NodeId,MemoryArrayCopyWitness>) =
    let mutable admitted=[]
    let mutable failures=Map.empty
    let mutable required=Set.empty
    let excluded=excluded graph
    for node in graph.Nodes.Values do
        if node.IsReachable && not(excluded.Contains node.Id) then
          match view graph node with
          | None -> ()
          | Some(direction,source) ->
            required<-Set.add node.Id required
            try
                let evidence=
                    graph.Edges |> List.choose (fun edge ->
                        match direction,edge.Role,edge.Sources with
                        | MemoryStringViewDirection.FromBytes,EdgeRole.StringByteSnapshot,[input;snapshot]
                            when snapshot=source -> Some(edge,input,snapshot)
                        | MemoryStringViewDirection.ToBytes,EdgeRole.StringToBytesSnapshot,[input;inner;snapshot]
                            when inner=node.Id && endpoint graph input=endpoint graph source -> Some(edge,input,snapshot)
                        | _ -> None)
                    |> only "A string view requires its unique complete source snapshot relation."
                let snapshotRow,input,snapshot=evidence
                demand (snapshotRow.Class=EdgeClass.Provenance && snapshotRow.Ordinal=0)
                    "The string snapshot relation has changed its source role."
                let owner=snapshotRow.Target
                live graph owner |> ignore
                let copySite=snapshot
                let copy=copies.TryFind copySite |> needed "The string snapshot has no validated source array-copy construction."
                demand (copy.Site=copySite && copy.CountCarrier.Site=copy.Count)
                    "The string snapshot copy and extent refer to different source occurrences."
                demand (zero graph copy.SourceOffset && zero graph copy.DestinationOffset && completeCount graph copy.Source copy.Count)
                    "A string snapshot must copy the entire source extent from zero to zero."
                let allocation=copy.Allocation |> needed "A string snapshot copy lacks its independent source allocation."
                let allocationFact=
                    match operations.TryFind allocation with
                    | Some(MemoryWitnessOperation.ArrayAllocation fact) when fact.Site=allocation -> fact
                    | _ -> raise(MissingContract "The string snapshot allocation has no validated source allocation operation.")
                demand (endpoint graph allocationFact.Count=endpoint graph copy.Count &&
                        endpoint graph allocation=endpoint graph copy.Destination &&
                        endpoint graph copy.Source<>endpoint graph copy.Destination)
                    "The string snapshot does not retain an independent allocation for its complete copied extent."
                demand (endpoint graph copy.Destination=endpoint graph snapshot)
                    "The string snapshot relation does not name the copy's actual destination."
                let storageTarget=
                    match direction with
                    | MemoryStringViewDirection.FromBytes ->
                        demand (endpoint graph copy.Source=endpoint graph input)
                            "The constructed string copies a different input than its snapshot relation."
                        source
                    | MemoryStringViewDirection.ToBytes ->
                        demand (copy.Source=node.Id) "The string-to-array copy does not read this exact internal view."
                        node.Id
                let storage=graph.Edges |> List.choose (fun edge ->
                    match edge.Role with
                    | EdgeRole.StringByteStorage(lo,hi,name) when edge.Target=storageTarget -> Some(edge,lo,hi,name)
                    | _ -> None) |> only "A string view needs its exact source byte-storage declaration."
                let storageRow,lo,hi,name=storage
                let representation,declaration=Bytes.byteRepresentation graph |> needed "A string view requires a declared unsigned byte representation."
                demand (storageRow.Class=EdgeClass.Range && storageRow.Ordinal=0 && name=representation.Name &&
                        0I<=lo && lo<=hi && hi<=255I && List.contains declaration storageRow.Sources)
                    "The string view's storage range or representation declaration is inconsistent."
                let textRows=
                    match direction with
                    | MemoryStringViewDirection.ToBytes -> []
                    | MemoryStringViewDirection.FromBytes ->
                        let text=
                            graph.Edges |> List.filter (fun edge ->
                                edge.Target=owner && (match edge.Role with EdgeRole.StringAscii | EdgeRole.StringUtf8Constant _ -> true | _ -> false))
                            |> only "The constructed string lacks its source UTF-8 validity premise."
                        demand (text.Class=EdgeClass.Range && text.Ordinal=0) "The string text-validity relation has changed its source role."
                        match text.Role with
                        | EdgeRole.StringAscii -> demand (hi<=127I) "The source ASCII premise exceeds its encoded character range."
                        | EdgeRole.StringUtf8Constant bytes ->
                            try System.Text.UTF8Encoding(false,true).GetString(List.toArray bytes) |> ignore
                            with :? System.Text.DecoderFallbackException -> raise(MissingContract "The source constant UTF-8 premise is invalid.")
                        | _ -> ()
                        [text]
                let sourceCarrier,resultCarrier=carrierRepresentation numeric source,carrierRepresentation numeric node.Id
                let byteBuffer = function
                    | ValueRepresentation.Buffer(_,ValueRepresentation.Scalar(SettledSlot.Integer(8,selected))) ->
                        selected |> Option.forall ((=) representation.Name)
                    | _ -> false
                demand (byteBuffer sourceCarrier && byteBuffer resultCarrier)
                    "An internal string view requires matching source-selected byte buffer carriers."
                match sourceCarrier,resultCarrier with
                | ValueRepresentation.Buffer(sourceCount,_),ValueRepresentation.Buffer(resultCount,_) ->
                    demand (sourceCount=resultCount || resultCount.IsNone) "A string view cannot invent a fixed descriptor extent."
                | _ -> ()
                let participants=
                    [yield node.Id; yield source; yield owner; yield input; yield snapshot; yield allocation; yield declaration
                     yield! snapshotRow.Sources; yield! storageRow.Sources
                     for row in textRows do yield row.Target; yield! row.Sources]
                    |> Set.ofList |> Set.union copy.Participants |> Set.union copy.CountCarrier.Participants
                    |> Set.union allocationFact.Participants
                let fact:MemoryStringViewWitness=
                    {Site=node.Id;Source=source;Owner=owner;Snapshot=snapshot;Direction=direction
                     SourceCarrier=sourceCarrier;ResultCarrier=resultCarrier
                     Element=SettledSlot.Integer(8,Some representation.Name);Representation=representation;Declaration=declaration
                     Extent=copy.CountCarrier;Participants=participants}
                admitted<-(node.Id,MemoryWitnessOperation.StringView fact)::admitted
            with MissingContract reason -> failures<-Map.add node.Id reason failures
    List.rev admitted,failures,required

/// The shared extent owner enumerates every terminal string value through the
/// complete source flow. A constructed terminal needs the already admitted
/// snapshot and copy; it never acquires program-resident literal authority.
let localLineage (graph:SemanticGraph) (memory:MemoryWitnessProjection) source =
    try
        let extent = Clef.Compiler.Baker.Ingredients.ArrayShapes.reader graph source
                     |> needed "The local string borrow lacks complete source descriptor lineage."
        demand (not extent.StringSources.IsEmpty)
            "The local string borrow has no complete terminal string-source inventory."
        let mutable snapshots=[]
        let mutable copies=[]
        let mutable participants=extent.Participants
        for terminal in extent.StringSources do
            match (live graph terminal).Kind with
            | SemanticKind.Literal(NativeLiteral.String _) -> ()
            | _ ->
                let snapshot =
                    match memory.Operations.TryFind terminal with
                    | Some(MemoryWitnessOperation.StringView fact) when fact.Direction=MemoryStringViewDirection.FromBytes && fact.Site=terminal -> fact
                    | _ -> raise(MissingContract "A constructed string borrow lacks its source-admitted immutable snapshot view.")
                let copy=memory.ArrayCopies.TryFind snapshot.Snapshot
                         |> needed "The constructed string borrow lost its exact source array-copy receipt."
                demand (copy.Site=snapshot.Snapshot && copy.CountCarrier=snapshot.Extent)
                    "The constructed string's view and copied descriptor extent no longer correspond."
                snapshots<-snapshot::snapshots
                copies<-copy::copies
                participants<-Set.unionMany[participants;snapshot.Participants;copy.Participants]
        Ok(List.rev snapshots,List.rev copies,participants)
    with MissingContract reason -> Error reason
