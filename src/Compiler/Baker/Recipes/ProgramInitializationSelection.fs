// SPDX-License-Identifier: MIT
/// Select runtime startup occurrences from ordered source members. Declaration
/// readers supply phase identities; executable demand can also use shared data.
module Clef.Compiler.Baker.Recipes.ProgramInitializationSelection

open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core
open Clef.Compiler.PSGSaturation.SemanticGraph.Reachability
module Platform = Clef.Compiler.PSGSaturation.SemanticGraph.PlatformResolution
module Mappings = Clef.Compiler.PSGSaturation.SemanticGraph.MappedBindings
module Mmio = Clef.Compiler.PSGSaturation.SemanticGraph.Mmio

type Reading = {
    Initializers: NodeId list
    CodeDeclarations: NodeId list
    DeclarationValues: Set<NodeId>
    RuntimeDemand: Set<NodeId>
    Unresolved: (NodeId * string) list
    Contradictions: (NodeId * string) list
    UnitActivations: (NodeId * NodeId list) list
}

let private children (node: SemanticNode) =
    node.Children @ (kindEdges node.Id node.Kind
        |> List.filter Hyperedge.isStructural |> List.collect _.Sources) |> List.distinct

let private quotations (graph: SemanticGraph) =
    let rec held seen id =
        if Set.contains id seen then false else
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.Quote _ } -> true
        | Some { Kind = SemanticKind.TypeAnnotation(value, _) }
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } -> held (Set.add id seen) value
        | _ -> false
    graph.Nodes |> Map.toSeq |> Seq.choose (fun (id, node) ->
        match node.Kind with SemanticKind.Binding _ when held Set.empty id -> Some id | _ -> None) |> Set.ofSeq

let private declarations (graph: SemanticGraph) =
    let platform = Platform.read graph
    let descriptors = Platform.readDescriptors graph
    let mappings = Mappings.read graph
    let roots =
        (platform.Platform |> Option.map _.Node |> Option.toList)
        @ (descriptors.Layouts |> List.map _.Node)
        @ (descriptors.Functions |> List.map _.Node)
        @ (mappings.Mappings |> List.map _.Node)
        @ ((platform.Findings @ descriptors.Findings @ mappings.Findings) |> List.map _.Node)
        @ (graph.Nodes.Values |> Seq.choose (fun node -> match node.Kind with SemanticKind.Quote _ -> Some node.Id | _ -> None) |> Seq.toList)
    // This is declaration-value incidence, not runtime/type/symbol reachability.
    let rec follow seen id =
        if Set.contains id seen then seen else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | None -> seen
        | Some { Kind = SemanticKind.VarRef(_, Some binding) } ->
            match graph.Nodes.TryFind binding with
            | Some { Kind = SemanticKind.Binding(_, false, _, _) } -> follow seen binding
            | _ -> seen
        | Some { Kind = SemanticKind.Binding(_, true, _, _) | SemanticKind.Lambda _ } -> seen
        | Some node -> children node |> List.fold follow seen
    let rec aliases values =
        let next = graph.Nodes.Values |> Seq.fold (fun values node ->
            let value =
                match node.Kind, node.Children with
                | SemanticKind.Binding(_, false, _, _), [value]
                | SemanticKind.TypeAnnotation(value, _), _
                | SemanticKind.VarRef(_, Some value), _ -> Some value
                | _ -> None
            if value |> Option.exists (fun id -> Set.contains id values) then Set.add node.Id values else values) values
        if next = values then values else aliases next
    roots |> List.fold follow Set.empty |> aliases

let private selectUsing (ownedFiles: Set<string> option) (graph: SemanticGraph) (orderedMembers: NodeId list) : Reading =
    let rec members seen ids =
        ids |> List.fold (fun (seen, ordered) id ->
            if Set.contains id seen then seen, ordered else
            let seen = Set.add id seen
            match graph.Nodes.TryFind id with
            | Some { Kind = SemanticKind.ModuleDef(_, nested) } ->
                let seen, nested = members seen nested
                seen, ordered @ nested
            | _ -> seen, ordered @ [id]) (seen, [])
    let ordered = members Set.empty orderedMembers |> snd
    let memberSet = Set.ofList ordered
    let sourceMembers =
        graph.Nodes.Values |> Seq.collect (fun node ->
            match node.Kind with SemanticKind.ModuleDef(_, members) -> members | _ -> [])
        |> Set.ofSeq |> Set.union memberSet
    let quoted = quotations graph
    let declarationValues = declarations graph
    let rec ordinaryCode seen id =
        if Set.contains id seen then false else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.Binding(_, false, _, _); Children = [value] }
        | Some { Kind = SemanticKind.TypeAnnotation(value, _) }
        | Some { Kind = SemanticKind.VarRef(_, Some value) } -> ordinaryCode seen value
        | Some ({ Kind = SemanticKind.Lambda(_, _, [], _, LambdaContext.RegularClosure) } as node) ->
            [ClosureMetadata.LambdaExpression; ClosureMetadata.RequiresClosurePair]
            |> List.forall (fun key -> node.Metadata.TryFind key <> Some (MetadataValue.Bool true))
        | _ -> false
    let code = ordered |> List.filter (ordinaryCode Set.empty)
    let codeSet = sourceMembers |> Set.filter (ordinaryCode Set.empty)
    let candidate id =
        not (quoted.Contains id || codeSet.Contains id)
        && (match graph.Nodes.TryFind id with
            | Some { Kind = SemanticKind.ModuleDef _ | SemanticKind.TypeDef _ | SemanticKind.PatternBinding _ } -> false
            | Some { Kind = SemanticKind.Binding(_, _, _, Some _) } -> false
            | Some _ -> true
            | None -> false)
    // Only structurally inert construction is discarded without demand. Calls,
    // loops, stores and unfamiliar operations are potentially observable. The
    // write-invalidation summaries are deliberately not used as a purity proof.
    let rec observable seen id =
        if Set.contains id seen then true else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.Intrinsic _; Type = NativeType.TFun _; Children = [] } -> false
        | Some { Kind = SemanticKind.Literal _ | SemanticKind.VarRef _ | SemanticKind.PatternBinding _
                      | SemanticKind.TypeDef _ | SemanticKind.Quote _
                      | SemanticKind.Lambda _ | SemanticKind.SeqExpr _ | SemanticKind.LazyExpr _ } -> false
        | Some ({ Kind = SemanticKind.Binding _ | SemanticKind.TypeAnnotation _ | SemanticKind.RecordExpr _
                       | SemanticKind.TupleExpr _ | SemanticKind.ArrayExpr _ | SemanticKind.ListExpr _
                       | SemanticKind.UnionCase _ | SemanticKind.DUConstruct _ | SemanticKind.Sequential _
                       | SemanticKind.IfThenElse _ } as node) -> children node |> List.exists (observable seen)
        | _ -> true
    let effectCandidates = ordered |> List.filter (fun id -> candidate id && not (declarationValues.Contains id) && observable Set.empty id)
    // Before startup settlement a declaration root can be a lexical module.
    // Membership does not demand every value in that module at runtime.
    let rec executableRoots seen root id =
        if Set.contains id seen then [] else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | Some { Kind = SemanticKind.ModuleDef(_, members) } ->
            members |> List.collect (executableRoots seen root)
        | Some { Kind = SemanticKind.Binding(_, _, _, Some actual) } when actual = root -> [id]
        | Some { Kind = SemanticKind.Binding("main", _, _, None) } when root = DeclRoot.EntryPoint -> [id]
        | _ -> []
    let entries = graph.DeclarationRoots |> List.collect (fun (id, root) -> executableRoots Set.empty root id)
    let normalizeFile file =
        if System.String.IsNullOrWhiteSpace file then ""
        else System.IO.Path.GetFullPath(file).Replace('\\', '/')
    let sourceFile id = graph.Nodes.TryFind id |> Option.map (fun node -> normalizeFile node.Range.File) |> Option.defaultValue ""
    let explicitlyOwned =
        match ownedFiles with
        | Some files -> files |> Set.map normalizeFile
        | None -> ordered |> List.map sourceFile |> Set.ofList
    let initialFiles = Set.union explicitlyOwned (entries |> List.map sourceFile |> Set.ofList)
    let mapped = (Mappings.read graph).Mappings |> List.map (fun row -> row.Binding, [row.AcquireBinding; row.ReleaseBinding]) |> Map.ofList
    let symbols = buildQualifiedBindingIndex graph
    // Type retention is not executable demand. In particular a referenced
    // record type cannot activate every initializer in its declaration file.
    let rec demand seen id =
        if Set.contains id seen then seen else
        let seen = Set.add id seen
        match graph.Nodes.TryFind id with
        | None -> seen
        | Some { Kind = SemanticKind.ModuleDef _ | SemanticKind.TypeDef _ | SemanticKind.Quote _ } -> seen
        | Some node ->
            let references =
                match mapped.TryFind id with
                | Some bindings -> bindings
                | None -> getSemanticReferences node
            let references =
                match Mmio.operation graph id, node.Kind with
                | Some(operation, _), SemanticKind.Application(callee, _) when operation.StartsWith("bind") -> [callee]
                | _ -> references
            references @ (getIntrinsicImplementationRef node graph |> Option.toList)
            @ (getStringLiteralBindingRef node symbols |> Option.toList)
            |> List.fold demand seen
    let rec activate activeFiles =
        let effects = effectCandidates |> List.filter (fun id -> activeFiles |> Set.contains (sourceFile id))
        let runtime = entries @ effects |> List.fold demand Set.empty
        let demandedBindings = runtime |> Set.filter (fun id ->
            sourceMembers.Contains id &&
            (match graph.Nodes.TryFind id with Some { Kind = SemanticKind.Binding _ } -> true | _ -> false))
        let next = demandedBindings |> Set.fold (fun files id -> Set.add (sourceFile id) files) activeFiles
        if next = activeFiles then runtime, demandedBindings, activeFiles else activate next
    let runtime, demandedBindings, activeFiles = activate initialFiles
    let modules = graph.Nodes.Values |> Seq.choose (fun node ->
        match node.Kind with SemanticKind.ModuleDef _ -> Some node.Id | _ -> None) |> Seq.toList
    let unitActivations = modules |> List.choose (fun moduleId ->
        let file = sourceFile moduleId
        if not (activeFiles.Contains file) then None else
        let premises =
            if explicitlyOwned.Contains file then modules |> List.filter (fun id -> sourceFile id = file)
            else
                (entries |> List.filter (fun id -> sourceFile id = file))
                @ (demandedBindings |> Set.toList |> List.filter (fun id -> sourceFile id = file))
        Some (moduleId, List.distinct premises))
    let selected = ordered |> List.filter (fun id -> candidate id && runtime.Contains id)
    let selectedSet = Set.ofList selected
    let ordinal = ordered |> List.mapi (fun index id -> id, index) |> Map.ofList
    let residuals = System.Collections.Generic.HashSet<NodeId * string>()
    let contradictions = System.Collections.Generic.HashSet<NodeId * string>()
    let complain owner text = residuals.Add((owner, text)) |> ignore
    let contradict owner text =
        complain owner text
        contradictions.Add((owner, text)) |> ignore
    let dependencies owner =
        let mutable dependencies = Set.empty
        let rec visit seen substitutions id =
            if Set.contains id seen then () else
            let seen = Set.add id seen
            let walk = visit seen substitutions
            match substitutions |> Map.tryFind id with
            | Some actual -> walk actual
            | None ->
            match graph.Nodes.TryFind id with
            | None -> contradict owner "An eager initializer dependency is missing from the graph."
            | Some { Kind = SemanticKind.VarRef(_, Some binding) } ->
                if quoted.Contains binding then contradict owner "An eager initializer references a quotation with no runtime value."
                elif sourceMembers.Contains binding && not (codeSet.Contains binding) then dependencies <- dependencies.Add binding
                elif not (codeSet.Contains binding) then walk binding
            | Some { Kind = SemanticKind.Lambda(_, _, captures, _, _)
                          | SemanticKind.SeqExpr(_, captures) | SemanticKind.LazyExpr(_, captures) } ->
                for capture in captures do
                    match capture.SourceNodeId with
                    | Some source when sourceMembers.Contains source && not (codeSet.Contains source) -> dependencies <- dependencies.Add source
                    | Some source -> walk source
                    | None -> complain owner "An initializer capture lacks its resolved source identity."
            | Some { Kind = SemanticKind.Quote _ | SemanticKind.TypeDef _ | SemanticKind.Intrinsic _ } -> ()
            | Some { Kind = SemanticKind.Application(callee, arguments) } ->
                walk callee
                arguments |> List.iter walk
                invoke seen substitutions callee arguments
            | Some { Kind = SemanticKind.IfThenElse(guard, yes, no) } ->
                walk guard
                match graph.Nodes.TryFind guard with
                | Some { Kind = SemanticKind.Literal(NativeLiteral.Bool true) } -> walk yes
                | Some { Kind = SemanticKind.Literal(NativeLiteral.Bool false) } -> no |> Option.iter walk
                | _ -> walk yes; no |> Option.iter walk
            | Some node -> children node |> List.iter walk
        and invoke seen substitutions callee arguments =
            if Set.contains callee seen then () else
            let seen = Set.add callee seen
            match substitutions |> Map.tryFind callee with
            | Some actual -> invoke (Set.remove callee seen) substitutions actual arguments
            | None ->
            match graph.Nodes.TryFind callee with
            | Some { Kind = SemanticKind.TypeAnnotation(value, _) }
            | Some { Kind = SemanticKind.VarRef(_, Some value) } -> invoke seen substitutions value arguments
            | Some ({ Kind = SemanticKind.Binding(_, false, _, _); Children = [value] } as binding) ->
                if binding.Metadata.ContainsKey "FidelityExtern.Library" then
                    // Foreign callbacks need an explicit dependency contract.
                    if arguments |> List.exists (fun id -> match graph.Nodes.TryFind id with Some { Type = NativeType.TFun _ } -> true | _ -> false) then
                        complain owner "A foreign initializer callback lacks a proved pre-entry dependency boundary."
                else invoke seen substitutions value arguments
            | Some { Kind = SemanticKind.Application(inner, supplied) } -> invoke seen substitutions inner (supplied @ arguments)
            | Some { Kind = SemanticKind.Lambda(parameters, body, _, _, _) } ->
                let arity = max 1 parameters.Length
                if arguments.Length >= arity then
                    let substitutions =
                        parameters |> List.mapi (fun index (_, _, id) -> id, arguments[index])
                        |> List.fold (fun map (formal, actual) -> Map.add formal actual map) substitutions
                    visit seen substitutions body
                    if arguments.Length > arity then invoke seen substitutions body (List.skip arity arguments)
            | Some { Kind = SemanticKind.Intrinsic _ | SemanticKind.PlatformBinding _ } -> ()
            | _ -> complain owner "An indirect initializer call lacks a proved pre-entry dependency boundary."
        match graph.Nodes.TryFind owner with
        | Some { Kind = SemanticKind.Binding _; Children = values } -> values |> List.iter (visit Set.empty Map.empty)
        | Some _ -> visit Set.empty Map.empty owner
        | None -> contradict owner "An ordered initializer is missing from the graph."
        dependencies
    let dependencyMap = selected |> List.map (fun id -> id, dependencies id) |> Map.ofList
    let rec reaches seen target id =
        if id = target then true
        elif Set.contains id seen then false
        else dependencyMap.TryFind id |> Option.exists (Set.exists (reaches (Set.add id seen) target))
    for owner in selected do
        for dependency in dependencyMap[owner] do
            if not (selectedSet.Contains dependency) then
                contradict owner $"Eager dependency {NodeId.value dependency} has no selected startup occurrence."
            elif reaches Set.empty owner dependency then
                contradict owner $"Cyclic eager initialization depends on {NodeId.value dependency}."
            elif ordinal[dependency] >= ordinal[owner] then
                contradict owner $"Eager dependency {NodeId.value dependency} is read before its source-ordered initializer."
    { Initializers = selected; CodeDeclarations = code; DeclarationValues = declarationValues
      RuntimeDemand = runtime; Unresolved = residuals |> Seq.sort |> Seq.toList
      Contradictions = contradictions |> Seq.sort |> Seq.toList; UnitActivations = unitActivations }

/// Standalone checking has no package ownership restriction: all supplied
/// implementation units participate, including otherwise-unused eager effects.
let select graph orderedMembers = selectUsing None graph orderedMembers

/// Project checking supplies exact application-source provenance. A dependency
/// unit participates when actual value/function demand activates its whole file.
let selectOwned ownedFiles graph orderedMembers = selectUsing (Some ownedFiles) graph orderedMembers
