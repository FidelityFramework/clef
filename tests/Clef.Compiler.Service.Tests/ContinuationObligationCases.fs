namespace Clef.Compiler.Service.Tests

open System.Diagnostics
open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module ContinuationObligations = Clef.Compiler.Baker.Recipes.ContinuationObligationRecipes
module ContinuationDischarge = Clef.Compiler.Nanopass.ObligationDischarge

module private ContinuationLayoutEvidence =
    let cases = [
        [0, 1, 1; 1, 1, 1; 2, 2, 2], 4, 2, "unsat"
        [0, 1, 1; 1, 1, 1; 8, 40, 8], 48, 8, "unsat"
        [], 0, 1, "unsat"
        [0, 1, 1; 3, 1, 1], 4, 1, "sat" // Unjustified interior padding.
        [0, 2, 2; 0, 2, 2], 2, 2, "sat" // Overlap.
        [0, 1, 1; 2, 2, 2], 3, 2, "sat" // Truncated extent.
        [0, 1, 1; 2, 2, 2], 6, 2, "sat" // Excess terminal padding.
        [0, 1, 1; 2, 2, 2], 4, 1, "sat" // Under-aligned frame.
        [0, 3, 3], 3, 3, "sat"          // Non-power-of-two alignment.
        [0, 1, 0], 1, 1, "sat"
        [-1, 1, 1], 0, 1, "sat"
        [0, 0, 1], 0, 1, "sat"
        [0, System.Int32.MaxValue, 1; System.Int32.MaxValue, 1, 1], System.Int32.MaxValue, 1, "sat"
        [], 1, 1, "sat"
        [], 0, 2, "sat"
    ]

    let solve obligation =
        let start = ProcessStartInfo("cvc5")
        start.ArgumentList.Add "--lang=smt2"
        start.ArgumentList.Add "--tlimit-per=2000"
        start.RedirectStandardInput <- true
        start.RedirectStandardOutput <- true
        start.RedirectStandardError <- true
        start.UseShellExecute <- false
        use solver = new Process(StartInfo = start)
        Assert.True(solver.Start())
        let output, errors = solver.StandardOutput.ReadToEndAsync(), solver.StandardError.ReadToEndAsync()
        solver.StandardInput.Write(ContinuationDischarge.smtLib [obligation])
        solver.StandardInput.Close()
        if not (solver.WaitForExit 5000) then
            solver.Kill(true)
            failwith "Continuation layout solver timed out"
        Assert.True(solver.ExitCode = 0, errors.GetAwaiter().GetResult())
        output.GetAwaiter().GetResult().Trim()

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ContinuationObligations")>]
type ContinuationObligationCases() =
    [<Fact>]
    member _.``Concrete layouts prove exact tiling while malformed placement remains refutable``() =
        for index, (slots, extent, alignment, expected) in List.indexed ContinuationLayoutEvidence.cases do
            let obligation =
                { Id = "continuation_layout_check"; Kind = "continuation-layout"; Logic = "QF_LIA"
                  Statement = "placement counterexample"; Source = "test"; Refs = []
                  Body = ObligationBody.ContinuationLayout(slots, extent, alignment) }
            let actual = ContinuationLayoutEvidence.solve obligation
            Assert.True((actual = expected), $"Layout case {index}: expected {expected}, got {actual}")

    [<Fact>]
    member _.``Baker layout obligation cites owner and exact field identities without changing the graph``() =
        let result = DimensionalCases.check "[<EntryPoint>]\nlet main _ =\n    let state = 2\n    let current = true\n    if current then state else 0\n"
        DimensionalCases.noErrors result
        let graph = result.Graph
        let binding name =
            graph.Nodes.Values |> Seq.filter (fun node ->
                match node.Kind with SemanticKind.Binding(actual, _, _, _) -> actual = name | _ -> false)
            |> Assert.Single
        let owner, state, current = binding "main", binding "state", binding "current"
        let slots = [state.Id, 0, 1, 1; current.Id, 1, 1, 1]
        let enrichment = ContinuationObligations.layout 1 "frame_identity" owner slots 2 1
        Assert.Empty enrichment.Annotated
        let node, edge = Assert.Single enrichment.NewNodes, Assert.Single enrichment.NewEdges
        Assert.False node.IsReachable
        Assert.Equal(owner.Range, node.Range)
        Assert.Equal(node.Id, edge.Target)
        Assert.Equal(EdgeRole.Constrains, edge.Role)
        Assert.Equal<EdgeClass>(EdgeClass.Obligation, edge.Class)
        Assert.Equal<NodeId list>([owner.Id; state.Id; current.Id], edge.Sources)
        Assert.False(graph.Nodes.ContainsKey node.Id)
        match node.Kind with
        | SemanticKind.Obligation info ->
            Assert.Equal(ObligationBody.ContinuationLayout([0, 1, 1; 1, 1, 1], 2, 1), info.Body)
            Assert.Equal("unsat", ContinuationLayoutEvidence.solve info)
        | kind -> failwithf "Expected resident obligation: %A" kind
