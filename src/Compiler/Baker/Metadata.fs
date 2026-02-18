// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Baker: Post-construction enrichment metadata.
///
/// ModuleClassification is now defined in PSG/SemanticGraph.fs and computed
/// lazily from EmissionStrategy. This module re-exports for API stability.
module Clef.Compiler.Baker.Metadata

open Clef.Compiler.PSGSaturation.SemanticGraph.Types
open Clef.Compiler.PSGSaturation.SemanticGraph.Core

// Re-export ModuleClassification from PSG for API stability
type ModuleClassification = Clef.Compiler.PSGSaturation.SemanticGraph.Types.ModuleClassification
