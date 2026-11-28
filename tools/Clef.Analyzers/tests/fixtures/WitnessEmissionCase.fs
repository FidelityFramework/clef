// Negative control, exact reason: CLF001 witness projection.  A recipe or a pass
// that calls into WitnessEmission.* re-derives published state instead of
// reading the single topological publication pass (clef #165-B blocker 7).  The
// fixture is not one of the checked-in publication drivers, so it is refused.
module ClefAnalyzerWitnessEmissionCase

module WitnessEmission =
    let prepare (rows : list<int>) : list<int> = rows
    let project (rows : list<int>) : list<int> = rows

let recipe (rows : list<int>) : list<int> = WitnessEmission.prepare rows
