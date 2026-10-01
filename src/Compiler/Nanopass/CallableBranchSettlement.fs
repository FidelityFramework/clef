// SPDX-License-Identifier: MIT
/// Final callable refinement after all ordinary/range/lifetime/proof owners.
/// Default source resolution remains conservative. No source node, demand,
/// numeric, lifetime, layout or obligation fact is rewritten by this pass.
module Clef.Compiler.Nanopass.CallableBranchSettlement

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Graph = Clef.Compiler.PSGSaturation.SemanticGraph.Core.SemanticGraph
module Origins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins
module Environments = Clef.Compiler.PSGSaturation.SemanticGraph.ClosureEnvironments
module Carriers = Clef.Compiler.PSGSaturation.SemanticGraph.CallableCarriers
module Flows = Clef.Compiler.PSGSaturation.SemanticGraph.CallableFlows
module Recipe = Clef.Compiler.Baker.Recipes.CallableBranchRecipes

let normalize (graph: SemanticGraph) =
    let resolution = Origins.resolveCallableBranches graph
    let codata = graph.Codata.Value
    let carriers, carrierResiduals =
        Carriers.settleWithResolution resolution
            { Layouts = codata.EnvironmentLayouts; Origins = Environments.origins graph
              Known = Environments.knownCallables graph } graph
    // Existing storage/joins are not rewritten after their owning proof pass.
    // CallableEmission independently refuses any refined storage mismatch.
    let flows, flowResiduals =
        Flows.settleWithResolution resolution
            { Carriers = carriers; Joins = codata.CallableJoins; Layouts = codata.EnvironmentLayouts
              SequenceFlows = codata.SequenceFlows; SequenceFamilies = codata.SequenceFamilies } graph
    let graph = Graph.invalidateWitness graph
    let codata =
        { graph.Codata.Value with
            CallableCarriers = carriers; CallableFlows = flows }
    let graph = { graph with Codata = lazy codata }
    let authority = Recipe.settle graph
    { graph with Codata = lazy { codata with CallableBranches = authority } }, carrierResiduals, flowResiduals
