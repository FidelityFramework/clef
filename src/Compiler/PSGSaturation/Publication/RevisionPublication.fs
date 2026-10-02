// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// The only graph exit from CCS. Baker has already selected and frozen every
/// leaf table. This assembly boundary constructs one immutable PSG revision;
/// no source analysis, type freezing, scope selection or repair occurs here.
module Clef.Compiler.PSGSaturation.Publication.RevisionPublication

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types

[<Literal>]
let Producer = "Clef.Compiler.Service"

type PublicationFailure = { Occurrence: NodeId option; Reason: string }

let private refusal reason : PublicationFailure list = [{ Occurrence = None; Reason = reason }]

/// Read stored source admission and copy its immutable rows. Physical target
/// authority comes only from Baker's prepared source, never from a caller.
let publish (graph: SemanticGraph) : Result<Fidelity.PSG.Revision, PublicationFailure list> =
    match Clef.Compiler.PSGSaturation.SemanticGraph.WitnessEmission.tryRead graph with
    | Error reason -> Error (refusal ("Source emission admission: " + reason))
    | Ok _ ->
        match graph.Codata.Value.WitnessPublishedRows with
        | None -> Error (refusal "Baker's frozen publication rows are absent.")
        | Some rows ->
            Ok { Header = { Schema = Fidelity.PSG.Revision.Schema; Producer = Producer }
                 Nodes = rows.Nodes; SourceReadings = rows.SourceReadings; Edges = rows.Edges
                 DeclarationRoots = rows.DeclarationRoots; ModuleClassifications = rows.ModuleClassifications
                 Platform = rows.Platform; StaticStringPool = rows.StaticStringPool; LiteralStorage = rows.LiteralStorage
                 Codata = rows.Codata; Emission = rows.Emission; Foreign = rows.Foreign; Demand = rows.Demand
                 Obligations = rows.Obligations; CurrentClaims = rows.CurrentClaims
                 ObligationSources = rows.ObligationSources; ObligationQuery = rows.ObligationQuery }
