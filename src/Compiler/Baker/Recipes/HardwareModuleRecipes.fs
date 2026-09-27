// SPDX-License-Identifier: MIT
/// Settle the source Mealy declaration before passive witnessing. Clock/reset
/// identities, ordered state, ports and reset coverage belong to this recipe.
module Clef.Compiler.Baker.Recipes.HardwareModuleRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module Spatial = Clef.Compiler.Baker.Ingredients.SpatialValues
module Platform = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

let private settleOne (graph: SemanticGraph) (numeric: NumericWitnessProjection) (site: SemanticNode) =
    try
        let mutable participants = Set.singleton site.Id
        let node id =
            participants <- Set.add id participants
            graph.Nodes.TryFind id |> Option.defaultWith (fun () -> failwith $"Source participant {NodeId.value id} is absent.")
        let require condition reason = if not condition then failwith reason
        let rec resolve seen path id =
            require (not (Set.contains id seen)) "A hardware declaration has a cyclic metadata reference."
            let current = node id
            let seen, path = Set.add id seen, Set.add id path
            match current.Kind, current.Children with
            | SemanticKind.TypeAnnotation(inner, _), _ -> resolve seen path inner
            | SemanticKind.VarRef(_, Some declaration), _ -> resolve seen path declaration
            | SemanticKind.Binding(_, false, _, _), [value] -> resolve seen path value
            | _ -> current, path
        let value id = resolve Set.empty Set.empty id
        let fields id =
            let current, path = value id
            match current.Kind with
            | SemanticKind.RecordExpr(fields, None) -> fields, path
            | _ -> failwith "Hardware metadata requires a settled, complete record value."
        let field name fields =
            match fields |> List.filter (fst >> (=) name) with
            | [_, id] -> id
            | _ -> failwith $"Hardware metadata requires exactly one '{name}' field."
        let text id =
            match (value id |> fst).Kind with
            | SemanticKind.Literal(NativeLiteral.String text) -> text
            | _ -> failwith "A hardware endpoint field requires a source string constant."
        let integer id =
            let current, _ = value id
            match current.Kind with
            | SemanticKind.Literal(NativeLiteral.Int(value, _)) -> current.Id, bigint value
            | SemanticKind.Literal(NativeLiteral.UInt(value, _)) -> current.Id, bigint value
            | SemanticKind.Literal(NativeLiteral.Bool value) -> current.Id, (if value then 1I else 0I)
            | _ -> failwith "A state reset requires an exact source integer or boolean constant."
        let representation id =
            node id |> ignore
            match numeric.OccurrenceRepresentations.TryFind id with
            | Some(Ok representation) -> representation
            | Some(Error reason) -> failwith reason
            | None -> failwith $"Hardware value {NodeId.value id} lacks its source-settled representation."
        let record = function
            | ValueRepresentation.Record(fields, _) -> fields
            | _ -> failwith "The hardware state/input must have a settled record representation."
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
        let name, root =
            match site.Kind, site.Children with
            | SemanticKind.Binding(name, false, _, Some DeclRoot.HardwareModule), [root] -> name, root
            | _ -> failwith "A hardware module must be an immutable, single-valued source declaration."
        let scope, qualified =
            match site.Parent |> Option.map node with
            | Some { Id = id; Kind = SemanticKind.ModuleDef(moduleName, _) } -> id, moduleName + "." + name
            | _ -> failwith "A hardware module requires its exact source module scope."
        let designFields, _ = fields root
        let initial = field "InitialState" designFields
        let step = field "Step" designFields
        let clockReference = field "Clock" designFields
        let implementation, stepPath = value step
        let parameters, result =
            match implementation.Kind with
            | SemanticKind.Lambda(parameters, result, [], _, _) when parameters.Length = 1 || parameters.Length = 2 ->
                parameters |> List.map (fun (name, _, id) -> name, id), result
            | _ -> failwith "A Mealy Step requires one state formal, at most one input formal and no captured environment."
        let stepBinding =
            match implementation.Parent |> Option.map node with
            | Some { Id = id; Kind = SemanticKind.Binding(_, false, _, _) } when stepPath.Contains id -> id
            | _ -> failwith "The Step implementation lacks its exact immutable declaration identity."
        let state = representation (snd parameters.Head)
        let stateFields = record state
        let stateRanges =
            match applySubst (node (snd parameters.Head)).Type with
            | NativeType.TApp(tc, _) -> graph.FieldRanges.Value.TryFind (NominalTypeIdentity.ofConstructor tc)
            | _ -> None
        let input = parameters |> List.tryItem 1 |> Option.map (snd >> representation)
        let resultRepresentation = representation result
        let output =
            match resultRepresentation with
            | ValueRepresentation.Record(["Item1", returned; "Item2", output], _) ->
                require (returned = state) "The returned state differs from the settled state formal."
                Some output
            | returned when returned = state -> None
            | _ -> failwith "The Step result must retain exactly the state representation, optionally paired with output."
        let initialFields, _ = fields initial
        require (List.map fst stateFields = List.map fst initialFields)
                "InitialState must name every state field exactly once in declaration order."
        let resets = List.map2 (fun (name, representation) (_, id) ->
            let literal, value = integer id
            let slot =
                match representation with
                | ValueRepresentation.Scalar(SettledSlot.Integer(bits, _) as slot) when bits > 0 -> slot
                | ValueRepresentation.Scalar SettledSlot.Bool -> SettledSlot.Bool
                | _ -> failwith $"State field '{name}' requires an admitted scalar register representation."
            name, literal, value, slot) stateFields initialFields
        let pins = graph.Codata.Value.Pins |> Option.defaultWith (fun () -> failwith "The hardware module lacks source-settled clock, reset and pin declarations.")
        let clockFields, clockPath = fields clockReference
        let clockDeclarations = selectedBindings "ClockEndpoint" |> List.filter (fun declaration -> clockPath.Contains declaration.Id)
        let clockDeclaration =
            match clockDeclarations with
            | [declaration] -> declaration.Id
            | _ -> failwith "Clock must resolve to one selected platform ClockEndpoint declaration."
        let clockName = field "Name" clockFields |> text |> portName
        let _, frequency = field "FrequencyHz" clockFields |> integer
        require (clockName = pins.Clock.PortName && frequency = bigint pins.Clock.FrequencyHz && frequency > 0I
                 && (field "PackagePin" clockFields |> text) = pins.Clock.PackagePin
                 && (field "Standard" clockFields |> text) = pins.Clock.IOStandard)
                "The selected Clock identity and settled pin map disagree."
        let reset = pins.Reset |> Option.defaultWith (fun () -> failwith "A hardware module requires an explicit reset declaration; absence does not authorize power-on reset.")
        let resetDeclaration =
            let matches = selectedBindings "ResetEndpoint" |> List.filter (fun declaration ->
                let resetFields, _ = fields declaration.Id
                (field "Name" resetFields |> text |> portName) = reset.PortName)
            match matches with
            | [declaration] ->
                let resetFields, _ = fields declaration.Id
                require ((field "Kind" resetFields |> text) = (if reset.IsExternal then "External" else "Internal")
                         && (field "ActiveLevel" resetFields |> text) = (if reset.ActiveHigh then "High" else "Low")
                         && (field "PackagePin" resetFields |> text) = reset.PackagePin
                         && (field "Standard" resetFields |> text) = reset.IOStandard)
                        "The explicit reset declaration and settled pin map disagree."
                require (reset.IsExternal || reset.ActiveHigh) "The admitted internal power-on reset contract is active high."
                declaration.Id
            | _ -> failwith "The settled reset must identify exactly one selected platform declaration."
        let port direction path name representation : HardwarePortWitness =
            let pin =
                match pins.Pins |> List.filter (fun pin -> pin.PortName = name) with
                | [pin] when pin.Direction = direction -> pin
                | _ -> failwith $"Port '{name}' lacks exactly one selected {direction} pin."
            match representation with
            | ValueRepresentation.Scalar(SettledSlot.Integer(1, _)) | ValueRepresentation.Scalar SettledSlot.Bool -> ()
            | _ -> failwith $"Physical pin '{name}' requires a source-settled one-bit value."
            let declarations = selectedBindings "PinEndpoint" |> List.filter (fun declaration ->
                let pinFields, _ = fields declaration.Id
                (field "LogicalName" pinFields |> text |> portName) = name
                && (field "PackagePin" pinFields |> text) = pin.PackagePin
                && (field "Standard" pinFields |> text) = pin.IOStandard
                && (field "Direction" pinFields |> text) = direction)
            match declarations with
            | [declaration] -> { Name = name; Path = path; Representation = representation; Declaration = declaration.Id }
            | _ -> failwith $"Physical pin '{name}' lacks one exact selected source declaration."
        let rec ports direction path representation =
            record representation |> List.collect (fun (name, representation) ->
                let path = path @ [name]
                match pins.FieldPinAttrs.TryFind name with
                | Some [pin] -> [port direction path pin representation]
                | Some names ->
                    let elements = record representation
                    require (not names.IsEmpty && names.Length = elements.Length) $"Pins on field '{name}' do not match its ordered components."
                    List.map2 (fun pin (field, representation) -> port direction (path @ [field]) pin representation) names elements
                | None ->
                    match representation with
                    | ValueRepresentation.Record _ -> ports direction path representation
                    | _ when direction = "Output" -> []
                    | _ -> failwith $"Input field '{name}' has no declared physical pin.")
        let inputPorts = input |> Option.map (ports "Input" []) |> Option.defaultValue []
        let outputPorts = output |> Option.map (ports "Output" []) |> Option.defaultValue []
        let names = (inputPorts @ outputPorts) |> List.map _.Name
        require ((Set.ofList names).Count = names.Length && not (List.contains pins.Clock.PortName names)
                 && (not reset.IsExternal || not (List.contains reset.PortName names))) "Hardware ports have overlapping source identities."
        // Declaration data is not executable. Shared constants with an outside
        // executable use remain demanded; their reference closure is retained.
        let rec metadata pending (seen: Set<NodeId>) =
            match pending with
            | [] -> seen
            | id :: rest when seen.Contains id || id = stepBinding || id = implementation.Id -> metadata rest seen
            | id :: rest ->
                let current = node id
                let references = match current.Kind with SemanticKind.VarRef(_, Some id) -> [id] | _ -> []
                metadata (current.Children @ references @ rest) (Set.add id seen)
        let candidates = metadata [root; resetDeclaration] Set.empty
        let outsideUses = graph.Nodes.Values |> Seq.filter (fun current -> current.IsReachable && current.Id <> site.Id && not (candidates.Contains current.Id))
                          |> Seq.collect (fun current ->
                              match current.Kind with
                              | SemanticKind.ModuleDef _ | SemanticKind.TypeDef _ -> []
                              | _ -> Clef.Compiler.Baker.Ingredients.Closures.structuralIncidence current |> List.collect _.Sources)
                          |> Seq.filter candidates.Contains |> Seq.toList
        let metadataOnly = Set.difference candidates (metadata outsideUses Set.empty)
        let enrichmentId = Clef.Compiler.PSGSaturation.SemanticGraph.Elaboration.freshId ()
        let settledFields = resets |> List.map (fun (name, literal, value, slot) ->
            let range =
                if slot = SettledSlot.Bool then ValueRange.boolean
                else stateRanges |> Option.bind (Map.tryFind name)
                     |> Option.defaultWith (fun () -> failwith $"State field '{name}' lacks its exact settled range.")
            let lower, upper =
                match range with
                | ValueRange.Bounded(lo, hi) when lo <= hi -> lo, hi
                | _ -> failwith $"State field '{name}' lacks a nonempty finite register range."
            let capacity =
                match slot with
                | SettledSlot.Bool -> ValueRange.boolean
                | SettledSlot.Integer(bits, Some name) ->
                    graph.Platform |> Option.bind (fun platform -> platform.Representations.TryFind name)
                    |> Option.bind (fun representation ->
                        if representation.Bits = bits then Clef.Compiler.NativeTypedTree.Expressions.Intrinsics.RangeSources.declaredRange representation else None)
                    |> Option.defaultWith (fun () -> failwith "The state representation lacks its exact source declaration.")
                | SettledSlot.Integer(bits, None) ->
                    require (graph.Platform |> Option.exists (fun platform -> PlatformContext.substrateKind platform = SubstrateKind.FPGA))
                            "An undeclared register representation requires source FPGA fabric authority."
                    if lower >= 0I then ValueRange.unsignedOf bits else ValueRange.twosComplement bits
                | _ -> failwith "Unsupported register reset representation."
            let minimum, maximum =
                match capacity with ValueRange.Bounded(lo, hi) -> lo, hi | _ -> failwith "A register requires a bounded representation."
            require (minimum <= lower && lower <= value && value <= upper && upper <= maximum)
                    "The initial state or complete field range does not fit the settled register."
            { Name=name; Literal=literal; Reset=value; Slot=slot; Range=range; Capacity=capacity })
        let proofs = settledFields |> List.mapi (fun ordinal field ->
            let value, literal = field.Reset, field.Literal
            let lower, upper = match field.Range with ValueRange.Bounded(lo,hi) -> lo,hi | _ -> failwith "Expected settled state bounds."
            let minimum, maximum = match field.Capacity with ValueRange.Bounded(lo,hi) -> lo,hi | _ -> failwith "Expected settled register capacity."
            ["reset", ObligationBody.IntegerRepresentationCoverage(value, value, lower, upper)
             "register", ObligationBody.IntegerRepresentationCoverage(lower, upper, minimum, maximum)]
            |> List.map (fun (role, body) ->
                let info = { Id = $"hardware_{role}_{NodeId.value site.Id}_{ordinal}"; Kind = "hardware-reset-coverage"; Logic = "QF_LIA"
                             Statement = "the source reset and complete state range fit the exact register"; Source = fmtRange site.Range; Refs = []; Body = body }
                let citizen = obligationNode site enrichmentId info |> Spatial.markOwned
                let proof : SpatialProof = { Site = site.Id; Obligation = citizen.Id; Body = body; Participants = Set.add literal participants; Proven = true }
                citizen, proof)) |> List.concat
        let plan : HardwareModuleWitness =
            { Site = site.Id; Scope = scope; Name = qualified; StepBinding = stepBinding; Implementation = implementation.Id
              Parameters = parameters; Result = result; StateRepresentation = state; InputRepresentation = input; ResultRepresentation = resultRepresentation
              ResetFields = settledFields; ClockReference = clockReference; ClockDeclaration = clockDeclaration; ResetDeclaration = resetDeclaration
              ClockPath = clockPath; Pins = pins; InputPorts = inputPorts; OutputPorts = outputPorts
              MetadataOnly = metadataOnly; Participants = participants; Obligations = proofs |> List.map (fun (node, _) -> node.Id) }
        let enrichment = { NewNodes = proofs |> List.map fst; Annotated = []; NewEdges = proofs |> List.collect (snd >> Spatial.proofRows) }
        Ok (enrichment, plan)
    with error -> Error ("HardwareModule source settlement: " + error.Message)

let settle (graph: SemanticGraph) (numeric: NumericWitnessProjection) =
    graph.Nodes.Values |> Seq.fold (fun (enrichment, plans, failures, required) node ->
        match node.Kind with
        | SemanticKind.Binding(_, _, _, Some DeclRoot.HardwareModule) ->
            let required = Set.add node.Id required
            match settleOne graph numeric node with
            | Ok (added, plan) -> Enrichment.combine enrichment added, plan :: plans, failures, required
            | Error reason -> enrichment, plans, Map.add node.Id reason failures, required
        | _ -> enrichment, plans, failures, required) (Enrichment.empty, [], Map.empty, Set.empty)
