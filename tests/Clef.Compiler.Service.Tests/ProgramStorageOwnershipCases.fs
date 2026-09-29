namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Ownership = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramStorageAuthority

module private OwnershipFixture =
    let create () =
        let source = """
module ProgramOwnership
let make (flag: bool) = fun (value: bool) -> if flag then value else not value
let first = make true
let second = make false
[<EntryPoint>]
let main _ = if first true && second false then 0 else 1
"""
        let graph = LazyResidenceFixture.programWith (Some source)
        let binding = LazyResidenceFixture.binding "first" graph
        let plan = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read graph |> Option.get
        let initializer = plan.Initializers |> List.find (fun row -> row.Binding = binding) |> _.Initializer
        let instance = Clef.Compiler.Nanopass.ClosureEnvironmentSettlement.programInstance graph binding |> Option.get
        graph, binding, initializer, instance.Allocation.Value

    /// Real diamonds have two distinct parents, not two duplicate edges to one
    /// parent (the ownership index already collapses the latter).
    let diamonds depth (graph: SemanticGraph) initializer =
        let root = graph.Nodes[initializer]
        let leaf = { root with Id = NodeId.fresh(); Parent = None }
        let guard = graph.Nodes.Values |> Seq.find (fun node -> node.Kind = SemanticKind.Literal(NativeLiteral.Bool true)) |> _.Id
        let extend (previous, nodes: Map<NodeId, SemanticNode>, added) _ =
            let left = { root with Id = NodeId.fresh(); Kind = SemanticKind.Sequential [previous]; Children = [previous]; Parent = None }
            let right = { left with Id = NodeId.fresh() }
            let merge = { root with Id = NodeId.fresh(); Kind = SemanticKind.IfThenElse(guard,left.Id,Some right.Id); Children = [guard;left.Id;right.Id]; Parent = None }
            merge.Id, nodes.Add(left.Id,left).Add(right.Id,right).Add(merge.Id,merge), left.Id :: right.Id :: merge.Id :: added
        let top, nodes, added = List.fold extend (leaf.Id, graph.Nodes.Add(leaf.Id,leaf), [leaf.Id]) [1 .. depth]
        let root = { root with Kind = SemanticKind.Sequential [top]; Children = [top] }
        { graph with Nodes = nodes.Add(initializer,root); Codata = lazy (failwith "Ownership forced codata") }, added

    let extraParent (graph: SemanticGraph) site reachable cyclic =
        let parent = { graph.Nodes[site] with Id = NodeId.fresh(); Kind = SemanticKind.Sequential [site]; Children = [site]; Parent = None; IsReachable = reachable }
        let parent = if cyclic then { parent with Kind = SemanticKind.Sequential [site;parent.Id]; Children = [site;parent.Id] } else parent
        { graph with Nodes = graph.Nodes.Add(parent.Id,parent) }, parent.Id

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ProgramStorageOwnership")>]
type ProgramStorageOwnershipCases() =
    [<Fact>]
    member _.``Shared ancestry records each ownership premise once`` () =
        let graph, binding, initializer, site = OwnershipFixture.create ()
        let changed, added = OwnershipFixture.diamonds 12 graph initializer
        let actualBinding, participants = Ownership.candidates changed site |> Assert.Single
        Assert.Equal(binding, actualBinding)
        Assert.Equal((Set.ofList participants).Count, participants.Length)
        for node in site :: initializer :: added do Assert.Contains(node, participants)
        let _, original = Ownership.candidates graph site |> Assert.Single
        Assert.Equal(original.Length + added.Length, participants.Length)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``A good initializer route cannot hide an orphan or a cycle`` cyclic =
        let graph, _, _, site = OwnershipFixture.create ()
        let changed, _ = OwnershipFixture.extraParent graph site true cyclic
        Assert.NotEmpty(Ownership.candidates graph site)
        Assert.Empty(Ownership.candidates changed site)
        Assert.NotEmpty(Ownership.candidates graph site)

    [<Fact>]
    member _.``Retired structural parents are excluded from current ownership`` () =
        let graph, _, _, site = OwnershipFixture.create ()
        let changed, parent = OwnershipFixture.extraParent graph site false true
        let expected = Ownership.candidates graph site
        let actual = Ownership.candidates changed site
        Assert.Equal<(NodeId * NodeId list) list>(expected, actual)
        Assert.DoesNotContain(parent, actual.Head |> snd)

    [<Fact>]
    member _.``Deep branch sharing retains bounded evidence without path expansion`` () =
        let graph, _, initializer, site = OwnershipFixture.create ()
        let changed, added = OwnershipFixture.diamonds 128 graph initializer
        let _, participants = Ownership.candidates changed site |> Assert.Single
        let _, original = Ownership.candidates graph site |> Assert.Single
        Assert.Equal(original.Length + added.Length, participants.Length)
        Assert.Equal((Set.ofList participants).Count, participants.Length)

    [<Fact>]
    member _.``Shared suffix completion preserves first occurrence dependency order`` () =
        let graph, _, initializer, site = OwnershipFixture.create ()
        let _, original = Ownership.candidates graph site |> Assert.Single
        let changed, added = OwnershipFixture.diamonds 2 graph initializer
        let _, participants = Ownership.candidates changed site |> Assert.Single
        match added with
        | [left2; right2; merge2; left1; right1; merge1; leaf] ->
            Assert.Equal(initializer, List.last original)
            let prefix = original |> List.take (original.Length - 1)
            Assert.Equal<NodeId list>(prefix @ [leaf; left1; merge1; left2; merge2; initializer; right2; right1], participants)
        | _ -> failwith "Expected two explicit branch diamonds"

    [<Theory>]
    [<InlineData("lambda", false)>]
    [<InlineData("lambda", true)>]
    [<InlineData("loop", false)>]
    [<InlineData("loop", true)>]
    member _.``Execution barriers reject even when they are the initializer target`` (barrier: string, atTarget: bool) =
        let graph, _, initializer, site = OwnershipFixture.create ()
        let root = graph.Nodes[initializer]
        let body = { root with Id = NodeId.fresh(); Parent = None }
        let guard = graph.Nodes.Values |> Seq.find (fun node -> node.Kind = SemanticKind.Literal(NativeLiteral.Bool true)) |> _.Id
        let kind, children =
            if barrier = "lambda" then SemanticKind.Lambda([],body.Id,[],None,LambdaContext.RegularClosure), [body.Id]
            else SemanticKind.WhileLoop(guard,body.Id), [guard;body.Id]
        let barrierNode = { root with Id = (if atTarget then initializer else NodeId.fresh()); Kind = kind; Children = children; Parent = None }
        let nodes = graph.Nodes.Add(body.Id,body).Add(barrierNode.Id,barrierNode)
        let nodes =
            if atTarget then nodes else
            nodes.Add(initializer,{ root with Kind = SemanticKind.Sequential [barrierNode.Id]; Children = [barrierNode.Id] })
        let changed = { graph with Nodes = nodes }
        Assert.True((Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read changed).IsSome)
        Assert.Empty(Ownership.candidates changed site)

    [<Theory>]
    [<InlineData(false)>]
    [<InlineData(true)>]
    member _.``Completed ancestry cannot hide a later delayed body edge`` delayed =
        let graph, _, initializer, site = OwnershipFixture.create ()
        let root = graph.Nodes[initializer]
        let left = { root with Id = NodeId.fresh(); Kind = SemanticKind.Sequential [site]; Children = [site]; Parent = None }
        let right = { left with Id = NodeId.fresh() }
        let guard = graph.Nodes.Values |> Seq.find (fun node -> node.Kind = SemanticKind.Literal(NativeLiteral.Bool true)) |> _.Id
        let thunk = { root with Id = NodeId.fresh(); Kind = SemanticKind.Lambda([],guard,[],None,LambdaContext.RegularClosure); Children = [guard]; Parent = None }
        let body = if delayed then right.Id else thunk.Id
        let parent = { root with Id = NodeId.fresh(); Kind = SemanticKind.LazyExpr(body,[]); Children = [body;left.Id;right.Id]; Parent = None }
        let values = parent.Id :: root.Children
        let root = { root with Kind = SemanticKind.Sequential values; Children = values }
        let changed = { graph with Nodes = graph.Nodes.Add(left.Id,left).Add(right.Id,right).Add(thunk.Id,thunk).Add(parent.Id,parent).Add(root.Id,root) }
        let actual = Ownership.candidates changed site
        if delayed then Assert.Empty actual else
            let _, participants = actual |> Assert.Single
            Assert.Contains(left.Id, participants)
            Assert.Contains(right.Id, participants)
            Assert.Contains(parent.Id, participants)

    [<Fact>]
    member _.``Two initializer owners do not acquire a singleton authority`` () =
        let graph, _, _, site = OwnershipFixture.create ()
        let second = LazyResidenceFixture.binding "second" graph
        let plan = Clef.Compiler.PSGSaturation.SemanticGraph.ProgramInitialization.read graph |> Option.get
        let initializer = plan.Initializers |> List.find (fun row -> row.Binding = second) |> _.Initializer
        let root = graph.Nodes[initializer]
        let values = site :: root.Children
        let changed = { graph with Nodes = graph.Nodes.Add(initializer,{ root with Kind = SemanticKind.Sequential values; Children = values }) }
        Assert.Empty(Ownership.candidates changed site)
