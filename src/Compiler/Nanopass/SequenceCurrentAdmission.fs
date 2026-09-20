// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Fresh current-read certificates for the graph's exact iterator protocols.
/// Consumers fold these facts and publish the set after the relevant rewrites.
module Clef.Compiler.Nanopass.SequenceCurrentAdmission

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Recipes = Clef.Compiler.Baker.Recipes.SequenceCurrentRecipes

let certify (graph: SemanticGraph) : Set<NodeId> * Hyperedge list =
    let consumers = Recipes.structuralConsumers graph
    let evidence = graph.Nodes.Values |> Seq.choose (Recipes.forLoop graph consumers) |> Seq.toList
    evidence |> List.map _.Target |> Set.ofList, evidence
