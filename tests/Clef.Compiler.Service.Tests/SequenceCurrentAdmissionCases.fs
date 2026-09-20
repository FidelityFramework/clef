namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.Nanopass.Recipe
module CurrentAdmission = Clef.Compiler.Nanopass.SequenceCurrentAdmission
module CurrentFanOut = Clef.Compiler.Nanopass.FanOut
module CurrentFoldIn = Clef.Compiler.Nanopass.FoldIn

module private CurrentProtocol =
    let check body =
        let source = "module CurrentProtocol\n[<Measure>] type m\n" + body
        match parseAndCheck source "sequence-current.clef" with
        | Success result ->
            DimensionalCases.noErrors result
            result.Graph
        | CheckFailure result -> failwithf "Expected admitted iterator source: %A" result.Diagnostics
        | ParseFailure errors -> failwithf "Expected parsed iterator source: %A" errors

    let ordinary () = check "[<EntryPoint>]\nlet main _ =\n    for value in seq { yield 1<m> } do ignore value\n    0\n"

    let arguments (graph: SemanticGraph) id =
        match graph.Nodes[id].Kind with
        | SemanticKind.Application(_, arguments) -> arguments
        | kind -> failwithf "Expected a call: %A" kind

    let reference (graph: SemanticGraph) id =
        match graph.Nodes[id].Kind with
        | SemanticKind.VarRef(_, Some definition) -> definition
        | kind -> failwithf "Expected a resolved declaration: %A" kind

    let fields (edge: Hyperedge) = edge.Class, edge.Role, edge.Ordinal, edge.Sources, edge.Target

    let protocol graph =
        let _, certificates = CurrentAdmission.certify graph
        let certificate = Assert.Single certificates
        match certificate.Sources with
        | [enumerator; guard; loop] ->
            let body = match graph.Nodes[loop].Kind with SemanticKind.WhileLoop(_, body) -> body | _ -> failwith "Missing loop"
            certificate, enumerator, guard, loop, body
        | sources -> failwithf "Incomplete current evidence: %A" sources

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "SequenceCurrentAdmission")>]
type SequenceCurrentAdmissionCases() =
    [<Theory>]
    [<InlineData("[<EntryPoint>]\nlet main _ =\n    for value in seq { yield 1<m> } do ignore value\n    0\n", 1)>]
    [<InlineData("let selected = Seq.filter (fun value -> value > 0<m>) (seq { yield 1<m> })\n[<EntryPoint>]\nlet main _ = ignore selected; 0\n", 1)>]
    [<InlineData("let selected = Seq.collect (fun value -> seq { yield value }) (seq { yield 1<m> })\n[<EntryPoint>]\nlet main _ = ignore selected; 0\n", 2)>]
    [<InlineData("let selected = Seq.append (seq { yield 1<m> }) (seq { yield 2<m> })\n[<EntryPoint>]\nlet main _ = ignore selected; 0\n", 2)>]
    member _.``Existing iteration protocols certify the exact current site and enumerator identity``(source: string, expected: int) =
        let graph = CurrentProtocol.check source
        let nodes, edges = graph.Nodes, graph.Edges
        let admitted, certificates = CurrentAdmission.certify graph
        Assert.Equal(expected, certificates.Length)
        Assert.Equal(expected, admitted.Count)
        for certificate in certificates do
            Assert.Equal(EdgeClass.Suspension, certificate.Class)
            Assert.Equal(EdgeRole.IteratorCurrentAdmitted, certificate.Role)
            Assert.Equal(0, certificate.Ordinal)
            Assert.Contains(certificate.Target, admitted)
            match certificate.Sources with
            | [enumerator; guard; loop] ->
                Assert.Equal(enumerator, CurrentProtocol.reference graph (Assert.Single(CurrentProtocol.arguments graph guard)))
                Assert.Equal(enumerator, CurrentProtocol.reference graph (Assert.Single(CurrentProtocol.arguments graph certificate.Target)))
                match graph.Nodes[loop].Kind with
                | SemanticKind.WhileLoop(actualGuard, body) ->
                    Assert.Equal(guard, actualGuard)
                    match graph.Nodes[body].Kind with
                    | SemanticKind.Sequential [currentBinding; currentRef; _] ->
                        Assert.Equal<NodeId list>([certificate.Target], graph.Nodes[currentBinding].Children)
                        Assert.Equal(currentBinding, CurrentProtocol.reference graph currentRef)
                    | kind -> failwithf "Current did not precede the action: %A" kind
                | kind -> failwithf "Successful pull evidence lost its loop: %A" kind
            | sources -> failwithf "Unexpected proof participants: %A" sources
            for id in certificate.Target :: certificate.Sources do Assert.True(graph.Nodes.ContainsKey id)
        Assert.Same(nodes, graph.Nodes)
        Assert.Same(edges, graph.Edges)
        let repeated, repeatedEdges = CurrentAdmission.certify graph
        Assert.Equal(admitted, repeated)
        Assert.Equal<_ list>(List.map CurrentProtocol.fields certificates, List.map CurrentProtocol.fields repeatedEdges)

    [<Theory>]
    [<InlineData("unguarded")>]
    [<InlineData("different-instance")>]
    [<InlineData("action-first")>]
    [<InlineData("another-pull-first")>]
    [<InlineData("mutable-instance")>]
    [<InlineData("shared-current-outside")>]
    [<InlineData("shared-body-outside")>]
    member _.``Broken iterator protocols never certify a current read``(defect: string) =
        let graph = CurrentProtocol.ordinary ()
        let certificate, enumerator, guard, loop, body = CurrentProtocol.protocol graph
        let update id kind children nodes =
            let original = graph.Nodes[id]
            Map.add id { original with Kind = kind; Children = children } nodes
        let changed =
            match defect with
            | "unguarded" -> update guard (SemanticKind.Literal(NativeLiteral.Bool true)) [] graph.Nodes
            | "different-instance" ->
                let other = { graph.Nodes[enumerator] with Id = NodeId.fresh() }
                let argument = Assert.Single(CurrentProtocol.arguments graph certificate.Target)
                let name = match graph.Nodes[argument].Kind with SemanticKind.VarRef(name, _) -> name | _ -> failwith "Missing reference"
                graph.Nodes |> Map.add other.Id other |> update argument (SemanticKind.VarRef(name, Some other.Id)) []
            | "mutable-instance" ->
                match graph.Nodes[enumerator].Kind with
                | SemanticKind.Binding(name, _, recursive, signature) ->
                    update enumerator (SemanticKind.Binding(name, true, recursive, signature)) graph.Nodes[enumerator].Children graph.Nodes
                | _ -> failwith "Missing enumerator binding"
            | "shared-current-outside" | "shared-body-outside" ->
                let shared = if defect = "shared-current-outside" then certificate.Target else body
                let escape =
                    { graph.Nodes[shared] with
                        Id = NodeId.fresh(); Parent = None
                        Kind = SemanticKind.Sequential [shared]; Children = [shared] }
                graph.Nodes.Add(escape.Id, escape)
            | "action-first" | "another-pull-first" ->
                match graph.Nodes[body].Kind with
                | SemanticKind.Sequential [binding; current; action] ->
                    let reordered = if defect = "action-first" then [action; binding; current] else [guard; binding; current; action]
                    update body (SemanticKind.Sequential reordered) reordered graph.Nodes
                | _ -> failwith "Missing iterator body"
            | _ -> failwith "Unknown protocol defect"
        let admitted, evidence = CurrentAdmission.certify { graph with Nodes = changed }
        Assert.DoesNotContain(certificate.Target, admitted)
        Assert.DoesNotContain(evidence, fun edge -> edge.Target = certificate.Target)
        Assert.Equal(SemanticKind.WhileLoop(guard, body), graph.Nodes[loop].Kind)

    [<Fact>]
    member _.``Current evidence follows all replaced participants through ordinary fan out and fold in``() =
        let original = CurrentProtocol.ordinary ()
        let certificate, _, _, _, _ = CurrentProtocol.protocol original
        let unrelated = original.Edges |> List.filter (fun edge ->
            not (edge.Class = EdgeClass.Suspension && edge.Role = EdgeRole.IteratorCurrentAdmitted))
        let graph = { original with Edges = certificate :: unrelated }
        let replaced = certificate.Target :: certificate.Sources |> Set.ofList
        let creator (node: SemanticNode) _ =
            let replacement = { node with Id = NodeId.fresh() }
            RecipeCreated {
                OriginalNodeId = node.Id; ReplacementRootId = replacement.Id
                NewNodes = [replacement]; ElaborationKind = "Baker"; NewEdges = []; ElaborationSource = "Current identity fixture" }
        let recipes = CurrentFanOut.fanOut "Baker" (fun node -> Set.contains node.Id replaced) creator graph
        let folded = CurrentFoldIn.foldIn recipes graph
        let remap id = recipes.ReplacementMap.TryFind id |> Option.defaultValue id
        let retained = folded.Edges |> List.filter (fun edge ->
            edge.Class = EdgeClass.Suspension && edge.Role = EdgeRole.IteratorCurrentAdmitted) |> Assert.Single
        Assert.Equal<NodeId list>(List.map remap certificate.Sources, retained.Sources)
        Assert.Equal(remap certificate.Target, retained.Target)
        let admitted, fresh = CurrentAdmission.certify folded
        Assert.Contains(retained.Target, admitted)
        Assert.Equal(CurrentProtocol.fields retained, CurrentProtocol.fields (Assert.Single fresh))
        for id in retained.Target :: retained.Sources do Assert.True(folded.Nodes.ContainsKey id)
        Assert.Equal<NodeId list>(certificate.Sources, (Assert.Single(graph.Edges |> List.filter (fun edge ->
            edge.Class = EdgeClass.Suspension && edge.Role = EdgeRole.IteratorCurrentAdmitted))).Sources)
