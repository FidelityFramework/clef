// Negative control, exact reason: CLF001 re-invoked publication projection.
// The declaring entity ends with Publication and the invoked value is the
// projection entry point, so the call is refused whatever the local alias
// happens to be called (clef #165-B blocker 7).
module ClefAnalyzerPublicationProjectCase

module WitnessPublication =
    let project (rows : list<int>) : list<int> = rows
    let check (rows : list<int>) : bool = List.isEmpty rows

let pass (rows : list<int>) : list<int> = WitnessPublication.project rows
