// SPDX-License-Identifier: MIT
// Source construction of the complete scalar kernel and spatial schedule.
module Clef.Compiler.Baker.Recipes.KernelModuleRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module Spatial = Clef.Compiler.Baker.Ingredients.SpatialValues
module Platform = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

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

let private settleOne (graph: SemanticGraph) (numeric: NumericWitnessProjection) (site: SemanticNode) =
    let require condition reason = if condition then Ok () else Error reason
    result {
        let! ingress = Clef.Compiler.Baker.Recipes.KernelDeclarations.read graph site.Id
        let mutable participants = ingress.Participants
        let node id =
            participants <- Set.add id participants
            match graph.Nodes.TryFind id with
            | Some found -> Ok found
            | None -> Error $"Kernel participant {NodeId.value id} is absent."
        let rec resolve seen path id =
            result {
                do! require (not(Set.contains id seen)) "A kernel declaration contains a cyclic source reference."
                let! current = node id
                let seen,path = Set.add id seen,Set.add id path
                match current.Kind,current.Children with
                | SemanticKind.TypeAnnotation(inner,_),_ | SemanticKind.Quote(inner,_),_ -> return! resolve seen path inner
                | SemanticKind.VarRef(_,Some binding),_ -> return! resolve seen path binding
                | SemanticKind.Binding(_,false,_,_),[value] -> return! resolve seen path value
                | _ -> return current,path
            }
        let value id = resolve Set.empty Set.empty id
        let fields id =
            result {
                let! resolved, _ = value id
                match resolved.Kind with
                | SemanticKind.RecordExpr(fields,None) -> return fields
                | _ -> return! Error "A kernel declaration requires a complete source record."
            }
        let field name fields =
            match fields |> List.filter (fst >> (=) name) with
            | [_,id] -> Ok id
            | _ -> Error $"A kernel declaration requires exactly one '{name}' field."
        let integer id =
            result {
                let! current, _ = value id
                match current.Kind with
                | SemanticKind.Literal(NativeLiteral.Int(value,_)) -> return current.Id,bigint value
                | SemanticKind.Literal(NativeLiteral.UInt(value,_)) -> return current.Id,bigint value
                | _ -> return! Error "A kernel shape/schedule field requires an exact source integer literal."
            }
        let boundedInteger (lower: int) id =
            result {
                let! source,value = integer id
                do! require (value >= bigint lower && value <= bigint System.Int32.MaxValue) "A kernel shape/schedule extent is outside its admitted finite domain."
                return source,int value
            }
        let! name,root =
            match site.Kind,site.Children with
            | SemanticKind.Binding(name,false,_,Some DeclRoot.KernelModule),[root] -> Ok(name,root)
            | _ -> Error "A kernel module requires an immutable single-valued declaration."
        let! siteParentOpt =
            match site.Parent with
            | Some parentId -> node parentId |> Result.map Some
            | None -> Ok None
        let! scope,qualified =
            match siteParentOpt with
            | Some {Id=id;Kind=SemanticKind.ModuleDef(moduleName,_)} -> Ok(id,moduleName + "." + name)
            | _ -> Error "A kernel module requires its exact source module scope."
        let! design = fields root
        let! shapeFieldId = field "Shape" design
        let! shape = fields shapeFieldId
        let! elementsFieldId = field "Elements" shape
        let! elementsSite,elements = boundedInteger 1 elementsFieldId
        let! grainFieldId = field "Grain" shape
        let! grainSite,grain = boundedInteger 1 grainFieldId
        do! require (elements % grain = 0) "The source kernel Elements must be an exact multiple of Grain."
        let! computeFieldId = field "Compute" design
        let! implementation,computePath = value computeFieldId
        let! parameters,resultId =
            match implementation.Kind with
            | SemanticKind.Lambda(parameters,resultId,[],_,_) when parameters.Length=2 ->
                Ok(parameters |> List.map (fun (name,_,id) -> name,id),resultId)
            | _ -> Error "The admitted element kernel requires exactly two scalar formals and no captured environment."
        let! implParentOpt =
            match implementation.Parent with
            | Some parentId -> node parentId |> Result.map Some
            | None -> Ok None
        let! computeBinding =
            match implParentOpt with
            | Some {Id=id;Kind=SemanticKind.Binding(_,false,_,_)} when computePath.Contains id -> Ok id
            | _ -> Error "Compute must retain its exact immutable source declaration identity."
        do! require (computeBinding=ingress.ComputeBinding && implementation.Id=ingress.Implementation && parameters=ingress.Parameters && resultId=ingress.Result)
                "The kernel implementation no longer corresponds to its source ingress declaration."
        let carrier id =
            result {
                let! _ = node id
                let! found =
                    match numeric.Values.TryFind id with
                    | Some found -> Ok found
                    | None -> Error $"Kernel scalar {NodeId.value id} lacks its source numeric carrier."
                participants <- Set.union participants found.Participants
                do! require (match found.Slot with SettledSlot.Integer(bits,_) when bits>0 -> true | SettledSlot.Bool | SettledSlot.Char -> true | _ -> false)
                        "The admitted element kernel requires source-settled integer, boolean or character values."
                return found
            }
        let parameterIds = parameters |> List.map snd
        let steps = ResizeArray<KernelScalarStep>()
        let mutable complete = Set.empty
        let rec expression active id =
            result {
                do! require (not(Set.contains id active)) "Kernel Compute has a recursive value dependency."
                if not(complete.Contains id) then
                    let! current = node id
                    let active = Set.add id active
                    let alias source =
                        result {
                            do! expression active source
                            let! actual = carrier source
                            let! destination = carrier id
                            do! require (ValueRange.contains destination.Range actual.Range)
                                    "A kernel alias range does not retain every source value."
                            let matches = graph.Codata.Value.Meets.TryFind id |> Option.defaultValue [] |> List.filter (fun meet -> meet.Consumer=id && meet.Operand=source)
                            let! adaptation =
                                match matches with
                                | [] when actual.Slot=destination.Slot -> Ok None
                                | [meet] ->
                                    result {
                                        let width = function
                                            | SettledSlot.Integer(bits,_) -> Ok bits
                                            | SettledSlot.Bool -> Ok 1
                                            | SettledSlot.Char -> Ok 32
                                            | _ -> Error "A kernel alias lacks an admitted scalar slot."
                                        let! actualWidth = width actual.Slot
                                        let! destWidth = width destination.Slot
                                        do! require (meet.From=actualWidth && meet.To=destWidth)
                                                "A kernel alias adaptation differs from its exact source/destination slots."
                                        let valid =
                                            match meet.Adapt with
                                            | MeetKind.ExtendSigned -> meet.To>meet.From && ValueRange.contains (ValueRange.twosComplement meet.From) actual.Range
                                            | MeetKind.ExtendUnsigned -> meet.To>meet.From && ValueRange.contains (ValueRange.unsignedOf meet.From) actual.Range
                                            | MeetKind.Truncate -> meet.To<meet.From && ValueRange.contains destination.Range actual.Range
                                            | _ -> false
                                        do! require valid "A kernel alias adaptation lacks its exact source range premise."
                                        return Some meet
                                    }
                                | _ -> Error "A kernel alias/result lacks its exact source numeric adaptation."
                            steps.Add(KernelScalarStep.Alias(id,source,destination,adaptation))
                        }
                    match parameterIds |> List.tryFindIndex ((=) id),numeric.Operations.TryFind id with
                    | Some ordinal,_ ->
                        let! paramCarrier = carrier id
                        steps.Add(KernelScalarStep.Parameter(id,ordinal,paramCarrier))
                    | None,Some operation ->
                        for operand in operation.Operands do
                            do! expression active operand.Actual
                        participants <- Set.union participants operation.Participants
                        steps.Add(KernelScalarStep.Operation operation)
                    | None,None ->
                        match current.Kind,current.Children with
                        | SemanticKind.Literal((NativeLiteral.Int _ | NativeLiteral.UInt _ | NativeLiteral.Bool _ | NativeLiteral.Char _) as literal),_ ->
                            let! value =
                                match literal with
                                | NativeLiteral.Int(value,_) -> Ok(KernelScalarLiteral.Integer(bigint value))
                                | NativeLiteral.UInt(value,_) -> Ok(KernelScalarLiteral.Integer(bigint value))
                                | NativeLiteral.Bool value -> Ok(KernelScalarLiteral.Boolean value)
                                | NativeLiteral.Char value -> Ok(KernelScalarLiteral.Character value)
                                | _ -> Error "The scalar literal construction changed its source category."
                            let! litCarrier = carrier id
                            steps.Add(KernelScalarStep.Literal(id,value,litCarrier))
                        | SemanticKind.VarRef(_,Some binding),_ -> do! alias binding
                        | SemanticKind.TypeAnnotation(inner,_),_ -> do! alias inner
                        | SemanticKind.Binding(_,false,_,_),[inner] -> do! alias inner
                        | SemanticKind.Sequential children,_ when not children.IsEmpty ->
                            for child in children do
                                do! expression active child
                            do! alias (List.last children)
                        | _ -> do! Error $"Kernel Compute occurrence {NodeId.value id} requires its source scalar construction contract."
                    complete <- Set.add id complete
            }
        for parameter in parameterIds do
            do! expression Set.empty parameter
        do! expression Set.empty resultId
        let! resultCarrier = carrier resultId
        let resultBits = match resultCarrier.Slot with SettledSlot.Integer(bits,_) -> bits | _ -> 0
        do! require (resultBits=ingress.Output.Representation.Bits && ValueRange.contains ingress.Output.Range resultCarrier.Range)
                "The complete computed result requires its declared kernel output representation and range coverage; no implicit result truncation is admitted."
        // Nominal identity and selected-source membership jointly establish
        // authority. A same-short-name program record grants no target facts.
        let targets = graph.Nodes.Values |> Seq.filter (fun candidate ->
            match candidate.Kind,candidate.Type with
            | SemanticKind.Binding(_,false,_,_),NativeType.TApp(constructor,_) ->
                NominalTypeIdentity.ofConstructor constructor=Clef.Compiler.Baker.Recipes.KernelDeclarations.targetIdentity && Platform.isSelectedPlatformDeclaration graph candidate
            | _ -> false) |> Seq.toList
        let! targetDeclaration =
            match targets with
            | [declaration] -> Ok declaration
            | _ -> Error "Exactly one selected Fidelity.Platform.Contracts.KernelTarget declaration is required."
        do! require (targetDeclaration.Id=ingress.Target) "Kernel scheduling and transport must refer to the same selected source declaration."
        let! targetFields = fields targetDeclaration.Id
        let! deviceFieldId = field "Device" targetFields
        let! deviceNode, _ = value deviceFieldId
        let! device =
            match deviceNode.Kind with
            | SemanticKind.Literal(NativeLiteral.String value) when not(System.String.IsNullOrWhiteSpace value) -> Ok value
            | _ -> Error "The selected kernel target requires an explicit device identity."
        let dimension lower name =
            result {
                let! dimFieldId = field name targetFields
                let! _, dimVal = boundedInteger lower dimFieldId
                return dimVal
            }
        let! columns = dimension 1 "Columns"
        let! shimRow = dimension 0 "ShimRow"
        let! computeRow = dimension 1 "ComputeRow"
        let! depth = dimension 1 "FifoDepth"
        let! iterFieldId = field "Iterations" targetFields
        let! _,iterations = integer iterFieldId
        do! require (iterations>0I) "Kernel iteration count must be explicitly positive."
        do! require (computeRow<>shimRow && elements/grain<=columns) "The kernel partition exceeds the declared topology."
        let target = { Declaration=targetDeclaration.Id; Device=device; Columns=columns; ShimRow=shimRow; ComputeRow=computeRow
                       FifoDepth=depth; Iterations=iterations; Participants=participants }
        let tiles = [for ordinal in 0 .. elements/grain-1 -> { Column=ordinal; ShimRow=shimRow; ComputeRow=computeRow; Offset=ordinal*grain; Elements=grain }]
        let rec metadata pending seen =
            result {
                match pending with
                | [] -> return seen
                | id::rest when Set.contains id seen -> return! metadata rest seen
                | id::rest ->
                    let! current = node id
                    let references = match current.Kind with SemanticKind.VarRef(_,Some target) -> [target] | _ -> []
                    return! metadata (current.Children @ references @ rest) (Set.add id seen)
            }
        let! candidates = metadata [root;targetDeclaration.Id] Set.empty
        let outsideUses = graph.Nodes.Values |> Seq.filter (fun current -> current.IsReachable && current.Id<>site.Id && not(candidates.Contains current.Id))
                          |> Seq.collect (fun current -> match current.Kind with SemanticKind.ModuleDef _ | SemanticKind.TypeDef _ -> [] | _ -> Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence current |> List.collect _.Sources)
                          |> Seq.filter candidates.Contains |> Seq.toList
        let! outsideMetadata = metadata outsideUses Set.empty
        let metadataOnly = Set.difference candidates outsideMetadata
        let body = ObligationBody.SpatialKernelPartition(bigint elements,bigint grain,columns,tiles |> List.map (fun tile -> tile.Column,bigint tile.Offset,bigint tile.Elements),depth,iterations)
        let info = { Id=$"kernel_partition_{NodeId.value site.Id}"; Kind="kernel-partition"; Logic="QF_LIA"
                     Statement="the exact source tile partition covers the declared element domain with bounded FIFO and iteration counts"
                     Source=fmtRange site.Range; Refs=[]; Body=body }
        let proofNode = obligationNode site (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId ()) info |> Spatial.markOwned
        let proof = { Site=site.Id; Obligation=proofNode.Id; Body=body; Participants=participants; Proven=true }
        let! coverage =
            match resultCarrier.Range,ingress.Output.Range with
            | ValueRange.Bounded(lower,upper),ValueRange.Bounded(minimum,maximum) -> Ok(ObligationBody.IntegerRepresentationCoverage(lower,upper,minimum,maximum))
            | _ -> Error "Kernel output coverage requires exact finite source bounds."
        let outputInfo = { info with Id=$"kernel_result_{NodeId.value site.Id}"; Kind="kernel-result"; Body=coverage
                                     Statement="the complete mathematical kernel result fits its declared output transport" }
        let outputNode = obligationNode site (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId ()) outputInfo |> Spatial.markOwned
        let outputProof = { Site=site.Id; Obligation=outputNode.Id; Body=coverage; Participants=participants; Proven=true }
        let plan = { Site=site.Id; Scope=scope; Name=qualified; ComputeBinding=computeBinding; Implementation=implementation.Id
                     Parameters=parameters; Result=resultId; Steps=List.ofSeq steps; Ingress=ingress
                     ElementsSite=elementsSite; GrainSite=grainSite; Elements=elements; Grain=grain
                     Target=target; Tiles=tiles; MetadataOnly=metadataOnly; Participants=participants; Obligations=[proofNode.Id;outputNode.Id] }
        return ({ NewNodes=[proofNode;outputNode]; Annotated=[]; NewEdges=Spatial.proofRows proof @ Spatial.proofRows outputProof },plan)
    }
    |> Result.mapError (fun reason -> "KernelModule source settlement: " + reason)

let private settleCore (graph: SemanticGraph) (numeric: NumericWitnessProjection) =
    graph.Nodes.Values |> Seq.fold (fun (enrichment,plans,failures,required) node ->
        match node.Kind with
        | SemanticKind.Binding(_,_,_,Some DeclRoot.KernelModule) ->
            let required=Set.add node.Id required
            match settleOne graph numeric node with
            | Ok(added,plan) -> Enrichment.combine enrichment added,plan::plans,failures,required
            | Error reason -> enrichment,plans,Map.add node.Id reason failures,required
        | _ -> enrichment,plans,failures,required) (Enrichment.empty,[],Map.empty,Set.empty)

let settle graph numeric =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> settleCore graph numeric)
