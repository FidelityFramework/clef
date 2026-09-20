// Copyright (c) 2026 Houston Haynes / Braidpoint
// SPDX-License-Identifier: MIT

/// Atomic suspension relations. These facts carry no target representation.
module Clef.Compiler.Baker.Ingredients.Suspensions

open Clef.Compiler.PSGSaturation.SemanticGraph.Types

/// The owner and its generator jointly delimit this suspension site. The
/// site's existing kind distinguishes yielding a value from delegation.
let delimiter owner generator site : Hyperedge =
    { Sources = [owner; generator]; Target = site
      Class = EdgeClass.Suspension; Role = EdgeRole.Delimiter; Ordinal = 0 }

let isDelimiter (edge: Hyperedge) =
    edge.Class = EdgeClass.Suspension && edge.Role = EdgeRole.Delimiter
