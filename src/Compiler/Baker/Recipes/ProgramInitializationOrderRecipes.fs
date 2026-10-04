// SPDX-License-Identifier: MIT
module Clef.Compiler.Baker.Recipes.ProgramInitializationOrderRecipes

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Baker.Ingredients.Obligations
module Uses = Clef.Compiler.Baker.Ingredients.ProgramValueUses

let info (binding: SemanticNode) body : ObligationInfo =
    { Id = sprintf "program_binding_%d_initialization_order" (NodeId.value binding.Id)
      Kind = "program-initialization-order"; Logic = "QF_LIA"
      Statement = "Every supported read of this runtime callable slot occurs after its initializer completes, within the ordered startup or ordinary source-entry activation. This finite order condition does not establish captured-storage lifetime, strictness, termination or preservation through lowering."
      Source = fmtRange binding.Range; Refs = []; Body = body }

let birth (graph: SemanticGraph) binding =
    let participants = Uses.scope graph binding
    let sources = participants |> List.map (fun (participant: Participant) -> participant.Node)
    let node = obligationNode graph.Nodes[binding] (NodeId.value binding)
                   (info graph.Nodes[binding] (ObligationBody.Pending ["Current complete callable-slot read scopes have not been established."]))
    { NewNodes = [node]
      NewEdges = [constrains sources node
                  { Class = EdgeClass.Provenance; Role = EdgeRole.ProgramInitializationOrder participants
                    Sources = sources; Target = node.Id; Ordinal = 0 }
                  { Class = EdgeClass.Provenance; Role = EdgeRole.ProgramInitializationOrderHistory participants
                    Sources = sources; Target = node.Id; Ordinal = 0 }]
      Annotated = [] }
