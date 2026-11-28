// Negative control, exact reason: CLF004.  A per-region segmentation fold widens
// its accumulator by unioning the whole graph.Nodes.Keys set (recovery wiki section 3.3).
module ClefAnalyzerSegmentationUnionCase

type Graph = { Nodes : Map<int, int>; Edges : list<int * int> }

let regionNodes (graph : Graph) (regions : list<list<int>>) : Set<int> =
    regions
    |> List.fold (fun acc _region ->
        graph.Nodes.Keys |> Seq.fold (fun inner k -> Set.add k inner) acc) Set.empty
