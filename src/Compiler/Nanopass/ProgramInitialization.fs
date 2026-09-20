// SPDX-License-Identifier: MIT
/// Program startup is settled before first reachability. Baker places the
/// ordered eager initializer occurrences in one real entry activation; source
/// declarations and the source entry remain stable ordinary graph identities.
module Clef.Compiler.Nanopass.ProgramInitialization

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Diagnostics
open Clef.Compiler.Baker.Recipes.Decomposition
open Clef.Compiler.Nanopass.Recipe
module Facts = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization
module Selection = Clef.Compiler.Baker.Recipes.ProgramInitializationSelection
module Construction = Clef.Compiler.Baker.Recipes.ProgramInitializationRecipes
module Platform = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution

let private residual (graph: SemanticGraph) site message =
    { Severity = NativeDiagnosticSeverity.Error; Code = "CCS8403"
      Message = "Program initialization requires further settlement: " + message
      Range = graph.Nodes[site].Range; RelatedNodes = [site]; Reachability = ReachabilityContext.Unknown }

let private sourceEntries (graph: SemanticGraph) =
    let rec members id =
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.ModuleDef(_, ids) } -> ids |> List.collect members
        | Some ({ Kind = SemanticKind.Binding(name, false, _, root); Children = [_] } as node)
            when root = Some DeclRoot.EntryPoint || (root.IsNone && name = "main") -> [node]
        | _ -> []
    graph.DeclarationRoots |> List.collect (fun (id, root) ->
        if root = DeclRoot.EntryPoint then members id else []) |> List.distinctBy _.Id

/// `orderedRoots` is the source checker's preserved file/module order, never a
/// node-map ordering. The selection reader proves the eager dependency boundary.
let private normalizeUsing select (orderedRoots: NodeId list) (graph: SemanticGraph) : SemanticGraph * Diagnostic list =
    if Facts.read graph |> Option.isSome then graph, [] else
    match sourceEntries graph with
    | [] -> graph, []
    | sources when sources.Length <> 1 -> graph, [residual graph sources.Head.Id "Exactly one CPU source entry must select startup."]
    | [source] ->
        let selection: Selection.Reading = select graph orderedRoots
        let shape =
            match graph.Nodes.TryFind source.Children.Head with
            | Some { Kind = SemanticKind.Lambda(_, _, [], _, LambdaContext.RegularClosure) } -> true
            | _ -> false
        if not selection.Unresolved.IsEmpty then
            let pending = selection.Unresolved |> List.mapi (fun ordinal (site, reason) ->
                { Sources = [source.Id; source.Children.Head]; Target = site
                  Class = EdgeClass.Provenance; Role = EdgeRole.ProgramInitializationPending reason; Ordinal = ordinal })
            let reported = if graph.Platform.IsSome then selection.Unresolved else selection.Contradictions
            { graph with Edges = graph.Edges @ pending }, reported |> List.map (fun (site, reason) -> residual graph site reason)
        elif not shape then graph, [residual graph source.Id "The source entry is not an ordinary captureless Lambda."]
        else
            let startup = graph.Platform |> Option.bind _.FreestandingStartup |> Option.map (fun startup ->
                let nodes, binding = IntrinsicElaboration.buildStartWrapper startup source.Id source.Type { source.Range with End = source.Range.Start }
                let references = nodes |> List.choose (fun node ->
                    match node.Kind with SemanticKind.VarRef(_, Some target) when target = source.Id -> Some node.Id | _ -> None) |> Set.ofList
                let call = nodes |> List.filter (fun node ->
                    match node.Kind with SemanticKind.Application(callee, _) -> references.Contains callee | _ -> false)
                           |> function [node] -> node.Id | _ -> invalidOp "Platform startup did not construct one exact source-entry call."
                ({ Nodes = nodes; Binding = binding; Call = call }: Construction.ExistingStartup))
            let context = mkContext source.Range source.Type graph.Platform "Program.initialization" source.Id
            let expansion = Construction.materialize context graph source selection.Initializers selection.UnitActivations startup
            let create (_: SemanticNode) _ = RecipeCreated {
                OriginalNodeId = source.Id; NewNodes = expansion.Nodes; NewEdges = expansion.Edges
                ReplacementRootId = source.Id; ElaborationKind = "Baker"; ElaborationSource = "Program.initialization" }
            let folded = FoldIn.foldIn (FanOut.fanOut "Program.initialization" (fun node -> node.Id = source.Id) create graph) graph
            let roots = (expansion.EntryBinding, DeclRoot.EntryPoint) :: (folded.DeclarationRoots |> List.filter (fun (_, root) -> root <> DeclRoot.EntryPoint))
            let folded = { folded with DeclarationRoots = roots }
            if Facts.read folded |> Option.isSome then folded, []
            else folded, [residual folded expansion.EntryBinding "The generated entry, call, ordered spine and declaration incidence disagree."]
    | _ -> graph, []

/// Standalone source checking treats the supplied units as implementations.
let normalize orderedRoots graph = normalizeUsing Selection.select orderedRoots graph

/// Project checking distinguishes owned implementation files from imported
/// declaration context. Dependency activation is closed by the selection pass.
let normalizeOwned ownedFiles orderedRoots graph = normalizeUsing (Selection.selectOwned ownedFiles) orderedRoots graph

/// Dynamic initialization uses the descriptor's writable program space even
/// for a logically immutable source binding. Role authority does not discharge
/// the independent per-value layout, backing residence or capacity obligations.
let settleValueAuthority admitted (graph: SemanticGraph) : SemanticGraph * Diagnostic list =
    if not admitted || graph.Platform.IsNone then graph, [] else
    match Facts.read graph with
    | None ->
        match graph.Edges |> List.tryFind (fun edge -> edge.Role = EdgeRole.ProgramInitialization) with
        | Some edge -> graph, [residual graph edge.Target "The settled entry, call, initializer order and storage intent no longer agree."]
        | None -> graph, []
    | Some plan ->
        let values = plan.Initializers |> List.filter (fun row -> plan.ValueBindings.Contains row.Binding)
        let authority = (Platform.read graph).Platform |> Option.bind (fun platform ->
            platform.ProgramLifetime |> Option.bind (fun designation ->
                designation.Mutable |> Option.map (fun space -> platform.Node, designation.Node, space.Reference, space.Space.Node)))
        match authority with
        | None -> graph, values |> List.map (fun row -> residual graph row.Binding "Runtime value initialization requires the descriptor's explicit writable program space.")
        | Some(descriptor, designation, reference, space) ->
            let evidence = values |> List.map (fun row ->
                { Sources = [plan.EntryLambda; plan.Spine; row.Initializer; descriptor; designation; reference; space]
                  Target = row.Binding; Class = EdgeClass.Provenance; Role = EdgeRole.ProgramValue; Ordinal = row.Ordinal })
            { graph with Edges = (graph.Edges |> List.filter (fun edge -> edge.Role <> EdgeRole.ProgramValue)) @ evidence }, []
