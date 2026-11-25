// SPDX-License-Identifier: MIT
// Settle the source Mealy declaration before passive witnessing. Clock/reset
// identities, ordered state, ports and reset coverage belong to this recipe.
module Clef.Compiler.Baker.Recipes.HardwareModuleRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
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

let private mapResult (fn: 'T -> Result<'U, 'E>) (items: 'T list) : Result<'U list, 'E> =
    let rec loop acc remaining =
        match remaining with
        | [] -> Ok (List.rev acc)
        | head :: tail ->
            match fn head with
            | Ok value -> loop (value :: acc) tail
            | Error err -> Error err
    loop [] items

let private collectResult (fn: 'T -> Result<'U list, 'E>) (items: 'T list) : Result<'U list, 'E> =
    mapResult fn items |> Result.map List.concat

let private map2Result (fn: 'A -> 'B -> Result<'C, 'E>) (xs: 'A list) (ys: 'B list) : Result<'C list, 'E> =
    List.zip xs ys |> mapResult (fun (a, b) -> fn a b)

let private settleOne (graph: SemanticGraph) (numeric: NumericWitnessProjection) (site: SemanticNode) =
    let mutable participants = Set.singleton site.Id
    let node id =
        participants <- Set.add id participants
        match graph.Nodes.TryFind id with
        | Some found -> Ok found
        | None -> Error $"Source participant {NodeId.value id} is absent."
    let require condition reason = if condition then Ok () else Error reason
    let rec resolve seen path id =
        result {
            do! require (not (Set.contains id seen)) "A hardware declaration has a cyclic metadata reference."
            let! current = node id
            let seen, path = Set.add id seen, Set.add id path
            match current.Kind, current.Children with
            | SemanticKind.TypeAnnotation(inner, _), _ -> return! resolve seen path inner
            | SemanticKind.VarRef(_, Some declaration), _ -> return! resolve seen path declaration
            | SemanticKind.Binding(_, false, _, _), [value] -> return! resolve seen path value
            | _ -> return current, path
        }
    let value id = resolve Set.empty Set.empty id
    let fields id =
        result {
            let! current, path = value id
            match current.Kind with
            | SemanticKind.RecordExpr(fields, None) -> return fields, path
            | _ -> return! Error "Hardware metadata requires a settled, complete record value."
        }
    let field name fields =
        match fields |> List.filter (fst >> (=) name) with
        | [_, id] -> Ok id
        | _ -> Error $"Hardware metadata requires exactly one '{name}' field."
    let text id =
        result {
            let! current, _ = value id
            match current.Kind with
            | SemanticKind.Literal(NativeLiteral.String text) -> return text
            | _ -> return! Error "A hardware endpoint field requires a source string constant."
        }
    let integer id =
        result {
            let! current, _ = value id
            match current.Kind with
            | SemanticKind.Literal(NativeLiteral.Int(value, _)) -> return current.Id, bigint value
            | SemanticKind.Literal(NativeLiteral.UInt(value, _)) -> return current.Id, bigint value
            | SemanticKind.Literal(NativeLiteral.Bool value) -> return current.Id, (if value then 1I else 0I)
            | _ -> return! Error "A state reset requires an exact source integer or boolean constant."
        }
    let representation id =
        result {
            let! _ = node id
            match numeric.OccurrenceRepresentations.TryFind id with
            | Some(Ok representation) -> return representation
            | Some(Error reason) -> return! Error reason
            | None -> return! Error $"Hardware value {NodeId.value id} lacks its source-settled representation."
        }
    let record = function
        | ValueRepresentation.Record(fields, _) -> Ok fields
        | _ -> Error "The hardware state/input must have a settled record representation."
    let shapeName ty =
        match applySubst ty with
        | NativeType.TApp(tc, _) -> tc.Name.Split('.') |> Array.last
        | _ -> ""
    let selectedBindings shape =
        graph.Nodes.Values |> Seq.filter (fun candidate ->
            match candidate.Kind with
            | SemanticKind.Binding _ -> Platform.isSelectedPlatformDeclaration graph candidate && shapeName candidate.Type = shape
            | _ -> false) |> Seq.toList
    let portName (name: string) = name.Replace("[", "_").Replace("]", "")
    result {
        let! name, root =
            match site.Kind, site.Children with
            | SemanticKind.Binding(name, false, _, Some DeclRoot.HardwareModule), [root] -> Ok(name, root)
            | _ -> Error "A hardware module must be an immutable, single-valued source declaration."
        let! siteParentOpt =
            match site.Parent with
            | Some parentId -> node parentId |> Result.map Some
            | None -> Ok None
        let! scope, qualified =
            match siteParentOpt with
            | Some { Id = id; Kind = SemanticKind.ModuleDef(moduleName, _) } -> Ok(id, moduleName + "." + name)
            | _ -> Error "A hardware module requires its exact source module scope."
        let! designFields, _ = fields root
        let! initial = field "InitialState" designFields
        let! step = field "Step" designFields
        let! clockReference = field "Clock" designFields
        let! implementation, stepPath = value step
        let! parameters, resultId =
            match implementation.Kind with
            | SemanticKind.Lambda(parameters, resultId, [], _, _) when parameters.Length = 1 || parameters.Length = 2 ->
                Ok(parameters |> List.map (fun (name, _, id) -> name, id), resultId)
            | _ -> Error "A Mealy Step requires one state formal, at most one input formal and no captured environment."
        let! implParentOpt =
            match implementation.Parent with
            | Some parentId -> node parentId |> Result.map Some
            | None -> Ok None
        let! stepBinding =
            match implParentOpt with
            | Some { Id = id; Kind = SemanticKind.Binding(_, false, _, _) } when stepPath.Contains id -> Ok id
            | _ -> Error "The Step implementation lacks its exact immutable declaration identity."
        let stateParamId = snd parameters.Head
        let! state = representation stateParamId
        let! stateFields = record state
        let! stateParamNode = node stateParamId
        let stateRanges =
            match applySubst stateParamNode.Type with
            | NativeType.TApp(tc, _) -> graph.FieldRanges.Value.TryFind (NominalTypeIdentity.ofConstructor tc)
            | _ -> None
        let! input =
            match parameters |> List.tryItem 1 with
            | Some (_, inputParamId) -> representation inputParamId |> Result.map Some
            | None -> Ok None
        let! resultRepresentation = representation resultId
        let! output =
            match resultRepresentation with
            | ValueRepresentation.Record(["Item1", returned; "Item2", output], _) ->
                result {
                    do! require (returned = state) "The returned state differs from the settled state formal."
                    return Some output
                }
            | returned when returned = state -> Ok None
            | _ -> Error "The Step result must retain exactly the state representation, optionally paired with output."
        let! initialFields, _ = fields initial
        do! require (List.map fst stateFields = List.map fst initialFields)
                "InitialState must name every state field exactly once in declaration order."
        let! resets =
            map2Result (fun (fieldName, rep) (_, id) ->
                result {
                    let! literal, value = integer id
                    let! slot =
                        match rep with
                        | ValueRepresentation.Scalar(SettledSlot.Integer(bits, _) as slot) when bits > 0 -> Ok slot
                        | ValueRepresentation.Scalar SettledSlot.Bool -> Ok SettledSlot.Bool
                        | _ -> Error $"State field '{fieldName}' requires an admitted scalar register representation."
                    return fieldName, literal, value, slot
                }) stateFields initialFields
        let! pins =
            match graph.Codata.Value.Pins with
            | Some pins -> Ok pins
            | None -> Error "The hardware module lacks source-settled clock, reset and pin declarations."
        let! clockFields, clockPath = fields clockReference
        let clockDeclarations = selectedBindings "ClockEndpoint" |> List.filter (fun declaration -> clockPath.Contains declaration.Id)
        let! clockDeclaration =
            match clockDeclarations with
            | [declaration] -> Ok declaration.Id
            | _ -> Error "Clock must resolve to one selected platform ClockEndpoint declaration."
        let! clockNameField = field "Name" clockFields
        let! clockNameRaw = text clockNameField
        let clockName = portName clockNameRaw
        let! freqField = field "FrequencyHz" clockFields
        let! _, frequency = integer freqField
        let! clockPkgField = field "PackagePin" clockFields
        let! clockPkg = text clockPkgField
        let! clockStdField = field "Standard" clockFields
        let! clockStd = text clockStdField
        do! require (clockName = pins.Clock.PortName && frequency = bigint pins.Clock.FrequencyHz && frequency > 0I
                     && clockPkg = pins.Clock.PackagePin
                     && clockStd = pins.Clock.IOStandard)
                "The selected Clock identity and settled pin map disagree."
        let! reset =
            match pins.Reset with
            | Some reset -> Ok reset
            | None -> Error "A hardware module requires an explicit reset declaration; absence does not authorize power-on reset."
        let! resetCandidates =
            selectedBindings "ResetEndpoint"
            |> mapResult (fun declaration ->
                result {
                    let! resetFields, _ = fields declaration.Id
                    let! nameField = field "Name" resetFields
                    let! nameRaw = text nameField
                    return declaration, resetFields, (portName nameRaw = reset.PortName)
                })
        let matchingResets =
            resetCandidates
            |> List.choose (fun (decl, resetFields, matched) -> if matched then Some(decl, resetFields) else None)
        let! resetDeclaration =
            match matchingResets with
            | [declaration, resetFields] ->
                result {
                    let! kindField = field "Kind" resetFields
                    let! kindText = text kindField
                    let! activeField = field "ActiveLevel" resetFields
                    let! activeText = text activeField
                    let! pkgField = field "PackagePin" resetFields
                    let! pkgText = text pkgField
                    let! stdField = field "Standard" resetFields
                    let! stdText = text stdField
                    do! require (kindText = (if reset.IsExternal then "External" else "Internal")
                                 && activeText = (if reset.ActiveHigh then "High" else "Low")
                                 && pkgText = reset.PackagePin
                                 && stdText = reset.IOStandard)
                            "The explicit reset declaration and settled pin map disagree."
                    do! require (reset.IsExternal || reset.ActiveHigh) "The admitted internal power-on reset contract is active high."
                    return declaration.Id
                }
            | _ -> Error "The settled reset must identify exactly one selected platform declaration."
        let port direction path name rep =
            result {
                let! pin =
                    match pins.Pins |> List.filter (fun pin -> pin.PortName = name) with
                    | [pin] when pin.Direction = direction -> Ok pin
                    | _ -> Error $"Port '{name}' lacks exactly one selected {direction} pin."
                do! match rep with
                    | ValueRepresentation.Scalar(SettledSlot.Integer(1, _)) | ValueRepresentation.Scalar SettledSlot.Bool -> Ok ()
                    | _ -> Error $"Physical pin '{name}' requires a source-settled one-bit value."
                let! pinCandidates =
                    selectedBindings "PinEndpoint"
                    |> mapResult (fun declaration ->
                        result {
                            let! pinFields, _ = fields declaration.Id
                            let! logField = field "LogicalName" pinFields
                            let! logText = text logField
                            let! pkgField = field "PackagePin" pinFields
                            let! pkgText = text pkgField
                            let! stdField = field "Standard" pinFields
                            let! stdText = text stdField
                            let! dirField = field "Direction" pinFields
                            let! dirText = text dirField
                            let matches =
                                portName logText = name
                                && pkgText = pin.PackagePin
                                && stdText = pin.IOStandard
                                && dirText = direction
                            return declaration, matches
                        })
                let declarations = pinCandidates |> List.choose (fun (decl, matches) -> if matches then Some decl else None)
                match declarations with
                | [declaration] -> return ({ Name = name; Path = path; Representation = rep; Declaration = declaration.Id } : HardwarePortWitness)
                | _ -> return! Error $"Physical pin '{name}' lacks one exact selected source declaration."
            }
        let rec ports direction path rep =
            result {
                let! recFields = record rep
                return!
                    recFields
                    |> collectResult (fun (fieldName, fieldRep) ->
                        let nextPath = path @ [fieldName]
                        match pins.FieldPinAttrs.TryFind fieldName with
                        | Some [pin] ->
                            port direction nextPath pin fieldRep |> Result.map List.singleton
                        | Some names ->
                            result {
                                let! elements = record fieldRep
                                do! require (not names.IsEmpty && names.Length = elements.Length) $"Pins on field '{fieldName}' do not match its ordered components."
                                return! map2Result (fun pin (subField, subRep) -> port direction (nextPath @ [subField]) pin subRep) names elements
                            }
                        | None ->
                            match fieldRep with
                            | ValueRepresentation.Record _ -> ports direction nextPath fieldRep
                            | _ -> Error $"{direction} field '{fieldName}' has no declared physical pin.")
            }
        let! inputPorts =
            match input with
            | Some inputRep -> ports "Input" [] inputRep
            | None -> Ok []
        let! outputPorts =
            match output with
            | Some outputRep -> ports "Output" [] outputRep
            | None -> Ok []
        let names = (inputPorts @ outputPorts) |> List.map _.Name
        do! require ((Set.ofList names).Count = names.Length && not (List.contains pins.Clock.PortName names)
                     && (not reset.IsExternal || not (List.contains reset.PortName names))) "Hardware ports have overlapping source identities."
        // Declaration data is not executable. Shared constants with an outside
        // executable use remain demanded; their reference closure is retained.
        let rec metadata pending (seen: Set<NodeId>) =
            result {
                match pending with
                | [] -> return seen
                | id :: rest when seen.Contains id || id = stepBinding || id = implementation.Id -> return! metadata rest seen
                | id :: rest ->
                    let! current = node id
                    let references = match current.Kind with SemanticKind.VarRef(_, Some id) -> [id] | _ -> []
                    return! metadata (current.Children @ references @ rest) (Set.add id seen)
            }
        let! candidates = metadata [root; resetDeclaration] Set.empty
        let outsideUses = graph.Nodes.Values |> Seq.filter (fun current -> current.IsReachable && current.Id <> site.Id && not (candidates.Contains current.Id))
                          |> Seq.collect (fun current ->
                              match current.Kind with
                              | SemanticKind.ModuleDef _ | SemanticKind.TypeDef _ -> []
                              | _ -> Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence current |> List.collect _.Sources)
                          |> Seq.filter candidates.Contains |> Seq.toList
        let! outsideMetadata = metadata outsideUses Set.empty
        let metadataOnly = Set.difference candidates outsideMetadata
        let enrichmentId = Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId ()
        let! settledFields =
            resets
            |> mapResult (fun (fieldName, literal, value, slot) ->
                result {
                    let! range =
                        if slot = SettledSlot.Bool then Ok ValueRange.boolean
                        else
                            match stateRanges |> Option.bind (Map.tryFind fieldName) with
                            | Some r -> Ok r
                            | None -> Error $"State field '{fieldName}' lacks its exact settled range."
                    let! lower, upper =
                        match range with
                        | ValueRange.Bounded(lo, hi) when lo <= hi -> Ok(lo, hi)
                        | _ -> Error $"State field '{fieldName}' lacks a nonempty finite register range."
                    let! capacity =
                        match slot with
                        | SettledSlot.Bool -> Ok ValueRange.boolean
                        | SettledSlot.Integer(bits, Some repName) ->
                            match graph.Platform |> Option.bind (fun platform -> platform.Representations.TryFind repName)
                                  |> Option.bind (fun rep ->
                                      if rep.Bits = bits then Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources.declaredRange rep else None) with
                            | Some cap -> Ok cap
                            | None -> Error "The state representation lacks its exact source declaration."
                        | SettledSlot.Integer(bits, None) ->
                            result {
                                do! require (graph.Platform |> Option.exists (fun platform -> PlatformContext.substrateKind platform = SubstrateKind.FPGA))
                                        "An undeclared register representation requires source FPGA fabric authority."
                                return (if lower >= 0I then ValueRange.unsignedOf bits else ValueRange.twosComplement bits)
                            }
                        | _ -> Error "Unsupported register reset representation."
                    let! minimum, maximum =
                        match capacity with
                        | ValueRange.Bounded(lo, hi) -> Ok(lo, hi)
                        | _ -> Error "A register requires a bounded representation."
                    do! require (minimum <= lower && lower <= value && value <= upper && upper <= maximum)
                            "The initial state or complete field range does not fit the settled register."
                    return { Name=fieldName; Literal=literal; Reset=value; Slot=slot; Range=range; Capacity=capacity }
                })
        let! proofsNested =
            settledFields
            |> List.mapi (fun ordinal field -> ordinal, field)
            |> mapResult (fun (ordinal, field) ->
                result {
                    let value, literal = field.Reset, field.Literal
                    let! lower, upper =
                        match field.Range with
                        | ValueRange.Bounded(lo,hi) -> Ok(lo,hi)
                        | _ -> Error "Expected settled state bounds."
                    let! minimum, maximum =
                        match field.Capacity with
                        | ValueRange.Bounded(lo,hi) -> Ok(lo,hi)
                        | _ -> Error "Expected settled register capacity."
                    return
                        ["reset", ObligationBody.IntegerRepresentationCoverage(value, value, lower, upper)
                         "register", ObligationBody.IntegerRepresentationCoverage(lower, upper, minimum, maximum)]
                        |> List.map (fun (role, body) ->
                            let info = { Id = $"hardware_{role}_{NodeId.value site.Id}_{ordinal}"; Kind = "hardware-reset-coverage"; Logic = "QF_LIA"
                                         Statement = "the source reset and complete state range fit the exact register"; Source = fmtRange site.Range; Refs = []; Body = body }
                            let citizen = obligationNode site enrichmentId info |> Spatial.markOwned
                            let proof : SpatialProof = { Site = site.Id; Obligation = citizen.Id; Body = body; Participants = Set.add literal participants; Proven = true }
                            citizen, proof)
                })
        let proofs = List.concat proofsNested
        let plan : HardwareModuleWitness =
            { Site = site.Id; Scope = scope; Name = qualified; StepBinding = stepBinding; Implementation = implementation.Id
              Parameters = parameters; Result = resultId; StateRepresentation = state; InputRepresentation = input; ResultRepresentation = resultRepresentation
              ResetFields = settledFields; ClockReference = clockReference; ClockDeclaration = clockDeclaration; ResetDeclaration = resetDeclaration
              ClockPath = clockPath; Pins = pins; InputPorts = inputPorts; OutputPorts = outputPorts
              MetadataOnly = metadataOnly; Participants = participants; Obligations = proofs |> List.map (fun (node, _) -> node.Id) }
        let enrichment = { NewNodes = proofs |> List.map fst; Annotated = []; NewEdges = proofs |> List.collect (snd >> Spatial.proofRows) }
        return (enrichment, plan)
    }
    |> Result.mapError (fun reason -> "HardwareModule source settlement: " + reason)

let private settleCore (graph: SemanticGraph) (numeric: NumericWitnessProjection) =
    graph.Nodes.Values |> Seq.fold (fun (enrichment, plans, failures, required) node ->
        match node.Kind with
        | SemanticKind.Binding(_, _, _, Some DeclRoot.HardwareModule) when node.IsReachable ->
            let required = Set.add node.Id required
            match settleOne graph numeric node with
            | Ok (added, plan) -> Enrichment.combine enrichment added, plan :: plans, failures, required
            | Error reason -> enrichment, plans, Map.add node.Id reason failures, required
        | _ -> enrichment, plans, failures, required) (Enrichment.empty, [], Map.empty, Set.empty)

let settle graph numeric =
  Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph.withEnrichment graph (fun () -> settleCore graph numeric)
