namespace Clef.Compiler.Service.Tests

open System.Diagnostics
open Xunit
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.NativeTypedTree.DimensionAlgebra
open Clef.Compiler.NativeTypedTree.UnionFind
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module Elaboration = Clef.Compiler.Nanopass.ObligationElaboration
module Discharge = Clef.Compiler.Nanopass.ObligationDischarge

module private ApplicationEvidence =
    let check source =
        let result = DimensionalCases.check source
        DimensionalCases.noErrors result
        result.Graph

    let sample = """let speed (distance: float<m>) (elapsed: float<s>) = distance / elapsed
[<EntryPoint>]
let main _ =
    let velocity = speed 12.0<m> 3.0<s>
    if velocity > 0.0<m/s> then 0 else 1
"""

    let obligations graph =
        (Elaboration.elaborate graph).NewNodes
        |> List.choose (fun node ->
            match node.Kind with
            | SemanticKind.Obligation ({ Body = ObligationBody.ApplicationDimensions _ } as ob) -> Some (node, ob)
            | _ -> None)

    let call name graph =
        // Curried elaboration can retain an unreachable intermediate call.
        // Select the source operation that survives on the saturated spine.
        graph.Nodes.Values |> Seq.filter (fun node -> node.IsReachable) |> Seq.pick (fun node ->
            match node.Kind with
            | SemanticKind.Application (callee, arguments) ->
                match graph.Nodes[callee].Kind with
                | SemanticKind.VarRef (actual, _) when actual = name || actual.EndsWith("." + name) -> Some (node, callee, arguments)
                | _ -> None
            | _ -> None)

    let atCall (site: SemanticNode) graph =
        obligations graph |> List.pick (fun (node, ob) -> if node.Range = site.Range then Some ob else None)

    // Required proof validation uses the same cvc5 executable as CCS.Editor.
    let expectSolver expected obligation =
        let start = ProcessStartInfo("cvc5")
        start.ArgumentList.Add "--lang=smt2"
        start.ArgumentList.Add "--tlimit-per=2000"
        start.RedirectStandardInput <- true
        start.RedirectStandardOutput <- true
        start.RedirectStandardError <- true
        start.UseShellExecute <- false
        use solver = new Process(StartInfo = start)
        if not (solver.Start()) then failwith "Could not start cvc5"
        let output, errors = solver.StandardOutput.ReadToEndAsync(), solver.StandardError.ReadToEndAsync()
        solver.StandardInput.Write(Discharge.smtLib [obligation])
        solver.StandardInput.Close()
        if not (solver.WaitForExit 5000) then
            solver.Kill(true)
            failwith "Application obligation solver timed out"
        let actual = output.GetAwaiter().GetResult().Trim()
        if solver.ExitCode <> 0 || actual <> expected then
            failwithf "Expected %s, got %s (%s)" expected actual (errors.GetAwaiter().GetResult())

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ApplicationObligations")>]
type ApplicationObligationTests() =
    [<Fact>]
    member _.``Calls retain dimensional arguments result and callee provenance``() =
        let graph = ApplicationEvidence.check ApplicationEvidence.sample
        let site, callee, arguments = ApplicationEvidence.call "speed" graph
        let enrichment = Elaboration.elaborate graph
        let node, obligation = ApplicationEvidence.obligations graph |> List.find (fun (node, _) -> node.Range = site.Range)
        match obligation.Body with
        | ObligationBody.ApplicationDimensions comparisons ->
            Assert.Contains(comparisons, fun (path, _, _) -> path = "argument 1.numeric")
            Assert.Contains(comparisons, fun (path, _, _) -> path = "argument 2.numeric")
            Assert.Contains(comparisons, fun (path, _, _) -> path = "result.numeric")
        | _ -> failwith "Missing application dimensional evidence"
        // Read the same enrichment's anchor (fresh node IDs differ across elaborations).
        let target = enrichment.NewNodes |> List.find (fun candidate ->
            match candidate.Kind with SemanticKind.Obligation ob -> ob.Id = obligation.Id | _ -> false)
        let sources = enrichment.NewEdges |> List.find (fun edge -> edge.Target = target.Id) |> fun edge -> edge.Sources
        for source in site.Id :: callee :: arguments do Assert.Contains(source, sources)
        match graph.Nodes[callee].Kind with
        | SemanticKind.VarRef (_, Some definition) -> Assert.Contains(definition, sources)
        | _ -> failwith "Sample call lost its definition reference"
        Assert.Equal(site.Range, node.Range)
        ApplicationEvidence.expectSolver "unsat" obligation

    [<Fact>]
    member _.``Corrupt arguments and results are refutable independently of the callee``() =
        let graph = ApplicationEvidence.check ApplicationEvidence.sample
        let site, _, arguments = ApplicationEvidence.call "speed" graph
        for id, incorrect in [arguments.Head, DimensionalCases.measured DimensionalCases.second;
                              site.Id, DimensionalCases.measured DimensionalCases.metre;
                              arguments.Head, Types.boolType] do
            let changed = { graph with Nodes = graph.Nodes |> Map.add id { graph.Nodes[id] with Type = incorrect } }
            ApplicationEvidence.atCall site changed |> ApplicationEvidence.expectSolver "sat"

    [<Fact>]
    member _.``Polymorphic dimensional calls keep formal axes and independent instances``() =
        let graph = ApplicationEvidence.check """let keep (value: float<'u>) = value
let relay (value: float<'u>) = keep value
[<EntryPoint>]
let main _ = if relay 12.0<m> > 0.0<m> && relay 3.0<s> > 0.0<s> then 0 else 1
"""
        let obligations = ApplicationEvidence.obligations graph |> List.map snd
        Assert.NotEmpty obligations
        Assert.Contains(obligations, fun ob ->
            match ob.Body with
            | ObligationBody.ApplicationDimensions comparisons ->
                comparisons |> List.exists (fun (_, expected, _) -> expected |> Option.exists (fun dim -> not dim.Vars.IsEmpty))
            | _ -> false)
        for obligation in obligations do ApplicationEvidence.expectSolver "unsat" obligation
        let before = obligations |> List.map (fun ob -> ob.Body)
        resetTypeParamCounter ()
        ApplicationEvidence.check "let unrelated = 1.0<m> / 2.0<s>\n" |> ignore
        let after = ApplicationEvidence.obligations graph |> List.map (fun (_, ob) -> ob.Body)
        Assert.True((before = after), "Re-elaboration read another inference session")

    [<Fact>]
    member _.``Partial and higher order calls compare remaining function positions``() =
        let graph = ApplicationEvidence.check """let combine (left: float<'u>) (right: float<'v>) = left * right
let apply f x = f x
[<EntryPoint>]
let main _ =
    let withDistance = combine 12.0<m>
    if apply withDistance 3.0<s> > 0.0<m s> then 0 else 1
"""
        let obligations = ApplicationEvidence.obligations graph |> List.map snd
        Assert.Contains(obligations, fun ob ->
            match ob.Body with
            | ObligationBody.ApplicationDimensions comparisons ->
                comparisons |> List.exists (fun (path, _, _) -> path.StartsWith("result.domain") || path.StartsWith("argument 1.domain"))
            | _ -> false)
        for obligation in obligations do ApplicationEvidence.expectSolver "unsat" obligation

    [<Fact>]
    member _.``Missing evidence cannot become a vacuous application proof``() =
        let graph = ApplicationEvidence.check ApplicationEvidence.sample
        let site, _, _ = ApplicationEvidence.call "speed" graph
        let original = ApplicationEvidence.atCall site graph
        for comparisons in [ []; ["result.numeric", Some DimensionalCases.metre, None] ] do
            { original with Body = ObligationBody.ApplicationDimensions comparisons }
            |> ApplicationEvidence.expectSolver "sat"
        let plain = ApplicationEvidence.check "let identity x = x\n[<EntryPoint>]\nlet main _ = identity 1\n"
        Assert.Empty(ApplicationEvidence.obligations plain)
