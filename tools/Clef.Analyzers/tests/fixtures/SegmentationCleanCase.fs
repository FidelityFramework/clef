// Positive control for CLF004: the file is named like a segmentation pass, so
// CLF004 runs over it, but it performs only bounded keyed lookups into graph.Nodes
// rather than unioning whole graph.Nodes.Keys or iterating unfiltered graph.Edges.
module ClefAnalyzerSegmentationCleanCase

type CleanGraph = { Nodes : Map<int, int> }

let regionSum (graph : CleanGraph) (regions : list<list<int>>) : int =
    regions
    |> List.fold (fun acc region ->
        region |> List.fold (fun inner id -> inner + (Map.tryFind id graph.Nodes |> Option.defaultValue 0)) acc) 0

let regionMaxima (regions : list<list<int>>) : list<int> =
    regions
    |> List.map (fun region -> region |> List.fold (fun acc value -> if value > acc then value else acc) 0)
