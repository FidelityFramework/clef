// SPDX-License-Identifier: MIT
/// Source construction of the complete scalar kernel and spatial schedule.
module Clef.Compiler.Baker.Recipes.KernelModuleRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module Spatial = Clef.Compiler.Baker.Ingredients.SpatialValues
module Platform = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

let private settleOne (graph: SemanticGraph) (numeric: NumericWitnessProjection) (site: SemanticNode) =
    try
        let ingress =
            Clef.Compiler.Baker.Recipes.KernelDeclarations.read graph site.Id
            |> Result.defaultWith failwith
        let mutable participants = ingress.Participants
        let require condition reason = if not condition then failwith reason
        let node id =
            participants <- Set.add id participants
            graph.Nodes.TryFind id |> Option.defaultWith (fun () -> failwith $"Kernel participant {NodeId.value id} is absent.")
        let rec resolve seen path id =
            require (not(Set.contains id seen)) "A kernel declaration contains a cyclic source reference."
            let current = node id
            let seen,path = Set.add id seen,Set.add id path
            match current.Kind,current.Children with
            | SemanticKind.TypeAnnotation(inner,_),_ | SemanticKind.Quote(inner,_),_ -> resolve seen path inner
            | SemanticKind.VarRef(_,Some binding),_ -> resolve seen path binding
            | SemanticKind.Binding(_,false,_,_),[value] -> resolve seen path value
            | _ -> current,path
        let value id = resolve Set.empty Set.empty id
        let fields id =
            match (value id |> fst).Kind with
            | SemanticKind.RecordExpr(fields,None) -> fields
            | _ -> failwith "A kernel declaration requires a complete source record."
        let field name fields =
            match fields |> List.filter (fst >> (=) name) with
            | [_,id] -> id
            | _ -> failwith $"A kernel declaration requires exactly one '{name}' field."
        let integer id =
            let current = value id |> fst
            match current.Kind with
            | SemanticKind.Literal(NativeLiteral.Int(value,_)) -> current.Id,bigint value
            | SemanticKind.Literal(NativeLiteral.UInt(value,_)) -> current.Id,bigint value
            | _ -> failwith "A kernel shape/schedule field requires an exact source integer literal."
        let boundedInteger (lower: int) id =
            let source,value = integer id
            require (value >= bigint lower && value <= bigint System.Int32.MaxValue) "A kernel shape/schedule extent is outside its admitted finite domain."
            source,int value
        let name,root =
            match site.Kind,site.Children with
            | SemanticKind.Binding(name,false,_,Some DeclRoot.KernelModule),[root] -> name,root
            | _ -> failwith "A kernel module requires an immutable single-valued declaration."
        let scope,qualified =
            match site.Parent |> Option.map node with
            | Some {Id=id;Kind=SemanticKind.ModuleDef(moduleName,_)} -> id,moduleName + "." + name
            | _ -> failwith "A kernel module requires its exact source module scope."
        let design = fields root
        let shape = field "Shape" design |> fields
        let elementsSite,elements = field "Elements" shape |> boundedInteger 1
        let grainSite,grain = field "Grain" shape |> boundedInteger 1
        require (elements % grain = 0) "The source kernel Elements must be an exact multiple of Grain."
        let implementation,computePath = field "Compute" design |> value
        let parameters,result =
            match implementation.Kind with
            | SemanticKind.Lambda(parameters,result,[],_,_) when parameters.Length=2 ->
                parameters |> List.map (fun (name,_,id) -> name,id),result
            | _ -> failwith "The admitted element kernel requires exactly two scalar formals and no captured environment."
        let computeBinding =
            match implementation.Parent |> Option.map node with
            | Some {Id=id;Kind=SemanticKind.Binding(_,false,_,_)} when computePath.Contains id -> id
            | _ -> failwith "Compute must retain its exact immutable source declaration identity."
        require (computeBinding=ingress.ComputeBinding && implementation.Id=ingress.Implementation && parameters=ingress.Parameters && result=ingress.Result)
                "The kernel implementation no longer corresponds to its source ingress declaration."
        let carrier id =
            node id |> ignore
            let found = numeric.Values.TryFind id |> Option.defaultWith (fun () -> failwith $"Kernel scalar {NodeId.value id} lacks its source numeric carrier.")
            participants <- Set.union participants found.Participants
            require (match found.Slot with SettledSlot.Integer(bits,_) when bits>0 -> true | SettledSlot.Bool | SettledSlot.Char -> true | _ -> false)
                    "The admitted element kernel requires source-settled integer, boolean or character values."
            found
        let parameterIds = parameters |> List.map snd
        let steps = ResizeArray<KernelScalarStep>()
        let mutable complete = Set.empty
        let rec expression active id =
            require (not(Set.contains id active)) "Kernel Compute has a recursive value dependency."
            if not(complete.Contains id) then
                let current = node id
                let active = Set.add id active
                let alias source =
                    expression active source
                    let actual,destination = carrier source,carrier id
                    require (ValueRange.contains destination.Range actual.Range)
                            "A kernel alias range does not retain every source value."
                    let matches = graph.Codata.Value.Meets.TryFind id |> Option.defaultValue [] |> List.filter (fun meet -> meet.Consumer=id && meet.Operand=source)
                    let adaptation =
                        match matches with
                        | [] when actual.Slot=destination.Slot -> None
                        | [meet] ->
                            let width = function SettledSlot.Integer(bits,_) -> bits | SettledSlot.Bool -> 1 | SettledSlot.Char -> 32 | _ -> failwith "A kernel alias lacks an admitted scalar slot."
                            require (meet.From=width actual.Slot && meet.To=width destination.Slot)
                                    "A kernel alias adaptation differs from its exact source/destination slots."
                            let valid =
                                match meet.Adapt with
                                | MeetKind.ExtendSigned -> meet.To>meet.From && ValueRange.contains (ValueRange.twosComplement meet.From) actual.Range
                                | MeetKind.ExtendUnsigned -> meet.To>meet.From && ValueRange.contains (ValueRange.unsignedOf meet.From) actual.Range
                                | MeetKind.Truncate -> meet.To<meet.From && ValueRange.contains destination.Range actual.Range
                                | _ -> false
                            require valid "A kernel alias adaptation lacks its exact source range premise."
                            Some meet
                        | _ -> failwith "A kernel alias/result lacks its exact source numeric adaptation."
                    steps.Add(KernelScalarStep.Alias(id,source,destination,adaptation))
                match parameterIds |> List.tryFindIndex ((=) id),numeric.Operations.TryFind id with
                | Some ordinal,_ -> steps.Add(KernelScalarStep.Parameter(id,ordinal,carrier id))
                | None,Some operation ->
                    for operand in operation.Operands do expression active operand.Actual
                    participants <- Set.union participants operation.Participants
                    steps.Add(KernelScalarStep.Operation operation)
                | None,None ->
                    match current.Kind,current.Children with
                    | SemanticKind.Literal((NativeLiteral.Int _ | NativeLiteral.UInt _ | NativeLiteral.Bool _ | NativeLiteral.Char _) as literal),_ ->
                        let value =
                            match literal with
                            | NativeLiteral.Int(value,_) -> KernelScalarLiteral.Integer(bigint value)
                            | NativeLiteral.UInt(value,_) -> KernelScalarLiteral.Integer(bigint value)
                            | NativeLiteral.Bool value -> KernelScalarLiteral.Boolean value
                            | NativeLiteral.Char value -> KernelScalarLiteral.Character value
                            | _ -> failwith "The scalar literal construction changed its source category."
                        steps.Add(KernelScalarStep.Literal(id,value,carrier id))
                    | SemanticKind.VarRef(_,Some binding),_ -> alias binding
                    | SemanticKind.TypeAnnotation(inner,_),_ -> alias inner
                    | SemanticKind.Binding(_,false,_,_),[inner] -> alias inner
                    | SemanticKind.Sequential children,_ when not children.IsEmpty ->
                        for child in children do expression active child
                        alias (List.last children)
                    | _ -> failwith $"Kernel Compute occurrence {NodeId.value id} requires its source scalar construction contract."
                complete <- Set.add id complete
        for parameter in parameterIds do expression Set.empty parameter
        expression Set.empty result
        let resultCarrier = carrier result
        let resultBits = match resultCarrier.Slot with SettledSlot.Integer(bits,_) -> bits | _ -> 0
        require (resultBits=ingress.Output.Representation.Bits && ValueRange.contains ingress.Output.Range resultCarrier.Range)
                "The complete computed result requires its declared kernel output representation and range coverage; no implicit result truncation is admitted."
        // Nominal identity and selected-source membership jointly establish
        // authority. A same-short-name program record grants no target facts.
        let targets = graph.Nodes.Values |> Seq.filter (fun candidate ->
            match candidate.Kind,candidate.Type with
            | SemanticKind.Binding(_,false,_,_),NativeType.TApp(constructor,_) ->
                NominalTypeIdentity.ofConstructor constructor=Clef.Compiler.Baker.Recipes.KernelDeclarations.targetIdentity && Platform.isSelectedPlatformDeclaration graph candidate
            | _ -> false) |> Seq.toList
        let targetDeclaration =
            match targets with
            | [declaration] -> declaration
            | _ -> failwith "Exactly one selected Fidelity.Platform.Contracts.KernelTarget declaration is required."
        require (targetDeclaration.Id=ingress.Target) "Kernel scheduling and transport must refer to the same selected source declaration."
        let targetFields = fields targetDeclaration.Id
        let device =
            match (field "Device" targetFields |> value |> fst).Kind with
            | SemanticKind.Literal(NativeLiteral.String value) when not(System.String.IsNullOrWhiteSpace value) -> value
            | _ -> failwith "The selected kernel target requires an explicit device identity."
        let dimension lower name = field name targetFields |> boundedInteger lower |> snd
        let columns = dimension 1 "Columns"
        let shimRow = dimension 0 "ShimRow"
        let computeRow = dimension 1 "ComputeRow"
        let depth = dimension 1 "FifoDepth"
        let _,iterations = field "Iterations" targetFields |> integer
        require (iterations>0I) "Kernel iteration count must be explicitly positive."
        require (computeRow<>shimRow && elements/grain<=columns) "The kernel partition exceeds the declared topology."
        let target = { Declaration=targetDeclaration.Id; Device=device; Columns=columns; ShimRow=shimRow; ComputeRow=computeRow
                       FifoDepth=depth; Iterations=iterations; Participants=participants }
        let tiles = [for ordinal in 0 .. elements/grain-1 -> { Column=ordinal; ShimRow=shimRow; ComputeRow=computeRow; Offset=ordinal*grain; Elements=grain }]
        let rec metadata pending seen =
            match pending with
            | [] -> seen
            | id::rest when Set.contains id seen -> metadata rest seen
            | id::rest ->
                let current = node id
                let references = match current.Kind with SemanticKind.VarRef(_,Some target) -> [target] | _ -> []
                metadata (current.Children @ references @ rest) (Set.add id seen)
        let candidates = metadata [root;targetDeclaration.Id] Set.empty
        let outsideUses = graph.Nodes.Values |> Seq.filter (fun current -> current.IsReachable && current.Id<>site.Id && not(candidates.Contains current.Id))
                          |> Seq.collect (fun current -> match current.Kind with SemanticKind.ModuleDef _ | SemanticKind.TypeDef _ -> [] | _ -> Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence current |> List.collect _.Sources)
                          |> Seq.filter candidates.Contains |> Seq.toList
        let metadataOnly = Set.difference candidates (metadata outsideUses Set.empty)
        let body = ObligationBody.SpatialKernelPartition(bigint elements,bigint grain,columns,tiles |> List.map (fun tile -> tile.Column,bigint tile.Offset,bigint tile.Elements),depth,iterations)
        let info = { Id=$"kernel_partition_{NodeId.value site.Id}"; Kind="kernel-partition"; Logic="QF_LIA"
                     Statement="the exact source tile partition covers the declared element domain with bounded FIFO and iteration counts"
                     Source=fmtRange site.Range; Refs=[]; Body=body }
        let proofNode = obligationNode site (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId ()) info |> Spatial.markOwned
        let proof = { Site=site.Id; Obligation=proofNode.Id; Body=body; Participants=participants; Proven=true }
        let coverage =
            match resultCarrier.Range,ingress.Output.Range with
            | ValueRange.Bounded(lower,upper),ValueRange.Bounded(minimum,maximum) -> ObligationBody.IntegerRepresentationCoverage(lower,upper,minimum,maximum)
            | _ -> failwith "Kernel output coverage requires exact finite source bounds."
        let outputInfo = { info with Id=$"kernel_result_{NodeId.value site.Id}"; Kind="kernel-result"; Body=coverage
                                     Statement="the complete mathematical kernel result fits its declared output transport" }
        let outputNode = obligationNode site (Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId ()) outputInfo |> Spatial.markOwned
        let outputProof = { Site=site.Id; Obligation=outputNode.Id; Body=coverage; Participants=participants; Proven=true }
        let plan = { Site=site.Id; Scope=scope; Name=qualified; ComputeBinding=computeBinding; Implementation=implementation.Id
                     Parameters=parameters; Result=result; Steps=List.ofSeq steps; Ingress=ingress
                     ElementsSite=elementsSite; GrainSite=grainSite; Elements=elements; Grain=grain
                     Target=target; Tiles=tiles; MetadataOnly=metadataOnly; Participants=participants; Obligations=[proofNode.Id;outputNode.Id] }
        Ok ({ NewNodes=[proofNode;outputNode]; Annotated=[]; NewEdges=Spatial.proofRows proof @ Spatial.proofRows outputProof },plan)
    with error -> Error("KernelModule source settlement: " + error.Message)

let settle (graph: SemanticGraph) (numeric: NumericWitnessProjection) =
    graph.Nodes.Values |> Seq.fold (fun (enrichment,plans,failures,required) node ->
        match node.Kind with
        | SemanticKind.Binding(_,_,_,Some DeclRoot.KernelModule) ->
            let required=Set.add node.Id required
            match settleOne graph numeric node with
            | Ok(added,plan) -> Enrichment.combine enrichment added,plan::plans,failures,required
            | Error reason -> enrichment,plans,Map.add node.Id reason failures,required
        | _ -> enrichment,plans,failures,required) (Enrichment.empty,[],Map.empty,Set.empty)
