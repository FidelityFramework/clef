// Negative control, exact reason: CLF004 on the edge side.  A per-region
// segmentation fold may not walk the unfiltered graph edge set (clef #165-B
// blocker 7): here the region fold scans every edge of the graph.
module ClefAnalyzerSegmentationEdgeUnionCase

type Graph = { Nodes : Map<int, int>; Edges : list<int * int> }

let regionEdgeSupport (graph : Graph) (regions : list<list<int>>) : Set<int> =
    regions
    |> List.fold (fun acc region ->
        let touched =
            graph.Edges
            |> List.choose (fun (source, target) ->
                if List.exists (fun id -> id = source) region then Some target else None)
        Set.union acc (Set.ofList touched)) Set.empty
