// Copyright (c) 2025-2026 Houston Haynes / SpeakEZ Technologies
// SPDX-License-Identifier: MIT

/// Baker: Post-construction enrichment metadata.
///
/// ModuleClassification is now defined in PSG/SemanticGraph.fs and computed
/// lazily from EmissionStrategy. This module re-exports for API stability.
module FSharp.Native.Compiler.Baker.Metadata

open FSharp.Native.Compiler.PSGSaturation.SemanticGraph

// Re-export ModuleClassification from PSG for API stability
type ModuleClassification = FSharp.Native.Compiler.PSGSaturation.SemanticGraph.ModuleClassification
