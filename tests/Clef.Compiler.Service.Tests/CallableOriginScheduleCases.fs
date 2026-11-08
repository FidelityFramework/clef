namespace Clef.Compiler.Service.Tests

open Xunit
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph.Types
module CallableOrigins = Clef.Compiler.PSGSaturation.SemanticGraph.CallableOrigins

/// clef #131: callable-origin resolution reaches its fixed point by
/// re-evaluating only the readers of changed facts. The whole-graph pass
/// schedule it replaced is retained as the reference; both must reach exactly
/// the same facts, field joins, parameter inputs, branch observations and
/// transport inputs on every graph.
module private OriginSchedules =
    let programs =
        [ "partial-application", """
module PartialApplication
let add (a: int) (b: int) = a + b
let twice (f: int -> int) (x: int) = f (f x)
let makeAdder (n: int) = fun (x: int) -> x + n
let observed =
    let increment = add 1
    let addTwo = makeAdder 2
    twice increment 3 + twice addTwo 4
"""
          "optional-callable", """
module OptionalCallable
let choose (flag: bool) : (int -> int) option = if flag then Some (fun (x: int) -> x + 1) else None
let apply (f: (int -> int) option) (x: int) = match f with Some g -> g x | None -> x
let observed = apply (choose true) 1 + apply (choose false) 2
"""
          "result-callable", """
module ResultCallable
let first (value: bool) = value
let fallback (value: bool) = false
let input () : Result<bool -> bool, bool> = Ok first
let selected = Result.defaultValue fallback (input ()) true
let observed = if selected then 1 else 0
"""
          "field-written-after-read", """
module FieldWrittenAfterRead
type Handler = { mutable Run: int -> int }
let handler = { Run = fun (x: int) -> x + 1 }
let call (x: int) = handler.Run x
let observed =
    handler.Run <- (fun (x: int) -> x + 2)
    call 3
"""
          "result-pipeline", """
module ResultPipeline
let bind (f: int -> Result<int, int>) (r: Result<int, int>) = match r with Ok v -> f v | Error e -> Error e
let check (x: int) = if x > 0 then Ok x else Error 0
let observed =
    match bind check (Ok 3) with
    | Ok v -> v
    | Error e -> e
"""
          "disjunctive-results", """
module DisjunctiveResults
let pair (left: int) (right: int) : Result<int, int> * Result<int, int> =
    ((if left > 0 then Ok left else Error left), (if right > 0 then Ok right else Error right))
let observed =
    match pair 1 -2 with
    | Error errors, _ | _, Error errors -> errors
    | Ok left, Ok right -> left + right
""" ]

    let graph (name: string, source: string) =
        let text = source + "\n[<EntryPoint>]\nlet main _ = ignore observed; 0\n"
        match parseAndCheck text (name + ".clef") with
        | Success result -> DimensionalCases.noErrors result; result.Graph
        | CheckFailure result -> failwithf "%s was rejected: %A" name result.Diagnostics
        | ParseFailure errors -> failwithf "%s did not parse: %A" name errors

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "CallableOrigins")>]
type CallableOriginScheduleCases() =
    static member Programs: obj array seq =
        OriginSchedules.programs |> Seq.map (fun (name, _) -> [| box name |])

    [<Theory>]
    [<MemberData(nameof CallableOriginScheduleCases.Programs)>]
    member _.``The dependency worklist reaches exactly the whole-graph fixed point`` (name: string) =
        let graph = OriginSchedules.programs |> List.find (fst >> (=) name) |> OriginSchedules.graph
        for branchSelections in [false; true] do
            let reference = CallableOrigins.originFixedPoint CallableOrigins.WholeGraphPasses branchSelections graph
            let worklist = CallableOrigins.originFixedPoint CallableOrigins.DependencyWorklist branchSelections graph
            // Non-vacuous: the program has callable origins to propagate.
            Assert.NotEmpty reference.Facts
            Assert.Equal<Map<NodeId, Set<NodeId * int>>>(reference.Facts, worklist.Facts)
            Assert.Equal<Map<NodeId * string, Set<NodeId * int>>>(reference.Fields, worklist.Fields)
            Assert.Equal<Map<NodeId, (NodeId * NodeId) list>>(reference.Inputs, worklist.Inputs)
            Assert.Equal<Map<NodeId, CallableBranchObservation>>(reference.Branches, worklist.Branches)
            Assert.Equal<Map<NodeId, NodeId list>>(reference.TransportInputs, worklist.TransportInputs)
            // Work proportional to the changed facts: never more evaluations
            // than the passes it replaces.
            Assert.True(worklist.Evaluations <= reference.Evaluations,
                        sprintf "%s: worklist evaluated %d node transfers, the whole-graph passes %d" name worklist.Evaluations reference.Evaluations)

    [<Fact>]
    member _.``A field written after its first read reaches the reader's origins`` () =
        let graph = OriginSchedules.programs |> List.find (fst >> (=) "field-written-after-read") |> OriginSchedules.graph
        let worklist = CallableOrigins.originFixedPoint CallableOrigins.DependencyWorklist false graph
        // Both stored functions reach the read in `call`: the initial one and
        // the one written later in node order.
        let read =
            graph.Nodes.Values |> Seq.filter (fun node ->
                node.IsReachable && match node.Kind with SemanticKind.FieldGet(_, "Run") -> true | _ -> false)
            |> Seq.map (fun node -> worklist.Facts.TryFind node.Id |> Option.defaultValue Set.empty)
            |> Seq.maxBy Set.count
        let lambdas =
            read |> Set.filter (fun (origin, offset) ->
                offset = 0 && match graph.Nodes[origin].Kind with SemanticKind.Lambda _ -> true | _ -> false)
        Assert.Equal(2, lambdas.Count)
