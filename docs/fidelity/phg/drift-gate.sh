#!/usr/bin/env bash
# Drift gate for the Design Supersession Register (docs/fidelity/phg/Design_Supersession_Register.md).
#
# The register retires a vocabulary. This gate makes its reappearance a lint failure across the
# design corpus, the two compilers, and the sample applications that express their capabilities.
# A line may still *mention* a retired term if the same line marks it as superseded — a spec
# chapter may say "cont.new … is retired"; it may not say "emit cont.new".
#
# Usage:  drift-gate.sh [--warn-only] [ROOT]        ROOT defaults to the parent of this repo.
# Exit:   0 clean, 1 retired vocabulary found (unless --warn-only).
set -u

WARN_ONLY=0
[[ "${1:-}" == "--warn-only" ]] && { WARN_ONLY=1; shift; }
ROOT="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)}"

# Corpus: design, spec, code, samples. Sample applications are corpus, not exhibits.
CORPUS=(
  "$ROOT/clef/docs" "$ROOT/clef/src" "$ROOT/clef/tests" "$ROOT/clef/samples"
  "$ROOT/clef-lang-spec/spec"
  "$ROOT/Composer/docs" "$ROOT/Composer/src" "$ROOT/Composer/samples" "$ROOT/Composer/tests"
  "$ROOT/BAREWire/docs"
  "$ROOT/ship-of-theseus"
  # agent memory directories are a drift vector like any other doc
  "$ROOT/clef/.serena" "$ROOT/Composer/.serena" "$ROOT/ClefAutoComplete/.serena" "$ROOT/BAREWire/.serena"
  "$ROOT/clef-lang-site/hugo/content"
  "$ROOT/mlir-plugins/README.md"
  # Lattice: the editor witnesses the PSG exactly as Alex does; the forks are corpus, not exhibits
  "$ROOT/lattice-analyzers" "$ROOT/lattice-vim" "$ROOT/lattice-vscode" "$ROOT/lattice-vscode-helpers" "$ROOT/ClefAutoComplete"
  "$ROOT/ionide-native-analyzers" "$ROOT/Ionide-vim-fsnative" "$ROOT/FsNativeAutoComplete"
  # Atelier: the commercial home of the toolchain (native/WREN cross-platform); 100% design today
  "$ROOT/Atelier"
)

# Measurement, never failing: how much of each Lattice fork still addresses the F# Compiler Service
# typed tree as its authority. The canonical position is that Lattice reads the saturated PSG through
# CCS and computes nothing; this count is the size of that migration, reported per repo.
FCS_SURFACE='FSharpChecker|ParseAndCheckFileInProject|FSharpSymbolUse|GetBackgroundCheckResults|FSharp\.Compiler\.(CodeAnalysis|Service|Symbols)'
LATTICE_REPOS=( lattice-analyzers lattice-vim lattice-vscode lattice-vscode-helpers ClefAutoComplete )

# Retired vocabulary. Each entry is an extended regex; the comment is the superseding design.
RETIRED=(
  'cont\.(new|suspend|resume|alloc|store|load|is_done)'   # dcont-representation §1: no op surface above the boundary
  '\b(DCont|dcont|Inet|INet|inet)[ -]dialect'              # Thin_Middle_End §3: the count is zero
  'dcont\.(shift|resume|reset)'                            # ccs-specification §12.6
  'ContStateMachine'                                       # dcont-representation §6: the frame is an environment node
  'resolve-closure-casts'                                  # Closure_Retooling_Plan step 5: plugin retired
  'flattenSequentials|Sequential Flattening|splitAtYield|emitPostYield|WhileBasedMoveNextInfo|WhileBasedYieldInfo'  # seq §6: segments at yield
  'DCont-via-Coroutines|DCont-Native'                      # backend leg vocabulary, not a front-end strategy
  'WAMI dialects'                                          # wasm-targeting/03: WAMI is a backend leg
  'unrealized_conversion_cast'                             # backend-lowering §7.5: SHALL NOT appear in middle-end output
  'memref<2xindex>'                                        # closure-representation §6.3: the index-pair encoding is retired
  'code_ptr'                                               # closure-representation §2.1: no function address stored in an environment
  '`func`, `cf`, `scf`'                                    # backend-lowering §2.1: the witnessed vocabulary is five dialects; cf/builtin are not among them
  'nativeptr<|NativePtr\.|FSharp\.NativeInterop|voidptr'      # ffi-boundary §1: no raw pointer type in interior Clef; TNativePtr is compiler-internal
  '!fidelity\.'                                            # Thin_Middle_End §3: no custom dialect or type above the boundary
  '(^|[^.[:alnum:]_])ptr<'                                 # representation chapters: links are bounded index values, values are memref views; no pointer notation (llvm.ptr</fir.ptr< in below-boundary listings excluded)
  'null pointer|= null :|is a null (pointer )?check'       # map/set/list: the empty collection is the static sentinel; isEmpty is a literal comparison
  'fat pointer|fat ptr|\{ptr: \*|ptr: \*u8|ptr: \*T|\{ptr, len\}'   # strings/arrays are memref views (buffer + dimension); no {ptr, len} header
  'FNCS|F# Native|FSharp\.Native\.|fsnative|FSNAC|FsNative'      # pre-NTU/PSG naming, fully set aside: the product is Clef, the service is CCS, the universe is NTU, the graph is the PSG
  'FSharp\.Quotations'                                    # plan D9: quotations are intrinsic; Expr<'T> is the compiler's, there is no quotations library to open
  '(^|[^A-Za-z])V \([A-Za-z0-9_]+ *[-+*] *[A-Za-z0-9_ +*-]*\)|MLIRTempCounter|freshTemp|ssaCounter|mintSSA'   # SSA is a nanopass derivation (Dimensional_Range_Design.md §8.3): a witness that constructs a name is the push model; no minting, no pools
  '\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'   # plan D10 (Dimensional_Range_Design.md): one int, one float; the width is the range's; no width-named type or suffix
  '\bFirefly\b'                                            # the pre-rename Composer; same family
  '\bKeystone\b|\bkeystone/|\.ks\b'                         # the pre-rename language name and its file extension
  '\bwrendit\b|__wrendit_'                                 # the pre-rename WREN stack name; the built sample (WrenHello) uses `wren`
  '!fir\.'                                                 # a custom type dialect; the witnessed vocabulary is five dialects and a string is memref<?xi8>
  '[Ii]nline-by-default|inlined by default|fsil default|\(fsil\)'   # inline-by-default was tried and reverted (PSG explosion); inline is explicit and semantic
  'resolved by Alex|erased metadata|Alex resolves dimensional'    # dimensions never erase; CCS resolves them at saturation against the platform description; Alex reads
  '\bFS[0-9]{4}\b'                                              # decision D3 (2026-09-04): every FS-prefixed diagnostic retires to the CCS series; the mapping table lands with hardening step 4
  '\b(int8|int16|int32|int64|uint|uint8|uint16|uint32|uint64|nint|unint|float32|posit8|posit16|posit32|posit64)TyCon\b'   # plan D7 interim: per-width numeric carriers; width leaves the type at step 7 (one Int and one Real carrier beside a seal column)
)

# A line that carries one of these markers is talking *about* the retired term, not using it.
SUPERSESSION_MARKERS='retired|retires|superseded|supersession|SHALL NOT|earlier revision|earlier framing|prior art|no longer|not planned|Retired\)|is going away|was written as|dissolved|interim|proposal(.s)? instruction|not denotable|user-denotable|replaces|stripped|NOT null|no null|not a null|never null|non-null|FFI boundary|at the boundary|C boundary|the sentinel|sentinel node|CHandle|no fat|not a fat|not fat|set aside|pre-NTU|formerly|renamed from|supersed|since deleted|-era |re-labeled|relabeled|now Composer|formerly Firefly|renamed|does not exist|no compiler|kept as reference|tried and reverted|never inline-by-default|Firefly, now|renamed to Composer|rename .Firefly|Firefly talk|~~Firefly~~|not user-denotable|no raw pointer|no raw-pointer|compiler-internal|internal-only|pre-strip|below the witness boundary|backend leg'

# Files whose purpose is to record the retirement itself, or history that must stay verbatim.
ALLOW_FILES=(
  # the register and its plans: they name what is retired
  'clef/docs/fidelity/phg/Design_Supersession_Register.md'
  'clef/docs/fidelity/phg/Closure_Retooling_Plan.md'
  'clef/docs/fidelity/phg/PSG_to_PHG_Plan.md'
  'clef/docs/fidelity/phg/drift-gate.sh'
  'clef/docs/fidelity/phg/Lattice_Consumer_Contract.md'
  'clef/docs/fidelity/phg/Dimensional_Vetting_Plan.md'
  'clef/docs/fidelity/phg/Dimensional_Step1_2_Design.md'
  'clef/docs/fidelity/phg/Types_As_Ranges_Position.md'
  'clef/docs/fidelity/phg/Horizon_Requirements.md'
  'clef/docs/fidelity/phg/Dimensional_Steps_1_2_Sequence.md'
  'clef/docs/fidelity/phg/Dimensional_Range_Design.md'
  'Composer/src/MiddleEnd/PSGElaboration/SSAAssignment.fs'
  'ship-of-theseus/scaffold/demo-runbook.md'                      # names the real F# compiler's codes in an F# build runbook
  'Composer/docs/Witness_Boundary_Audit.md'
  # the superseding designs: they quote the retired vocabulary in order to retire it,
  # and they define the one place it may survive (below the boundary, as transliteration)
  'Composer/docs/Delimited_Continuations_Architecture.md'
  'Composer/docs/Thin_Middle_End_Design.md'
  'Composer/docs/Single_Flattening_Design.md'
)

# Code that still carries retired vocabulary because its replacement is scheduled, not landed.
# Each row is a Closure_Retooling_Plan / Phase 3 deliverable. Reported, never failing; remove a
# row when its replacement lands, and the gate becomes an error for that file automatically.
SCHEDULED=(
  'clef/src::TyCon'                                             # hardening step 7 removes the per-width carriers; until then their count is reported here
  'clef/src::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'          # D10: the compiler is F# implementation code; the spellings it admits for Clef go with CS-11, its own use of .NET widths goes at self-hosting
  'Composer/src::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'      # same: F# implementation code
  'Composer/samples::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'  # D10: samples migrate with CS-11 (the dimensional leaves already have)
  'Composer/docs::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'     # D10: Composer's docs migrate with CS-11
  'Composer/tests::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'    # same
  'BAREWire/docs::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'     # D10: BAREWire's wire vocabulary migrates with CS-11 (its widths are schema facts)
  'clef-lang-spec/spec::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'   # D10: the chapters of Dimensional_Range_Design.md §10 are corrected; the rest of the spec migrates with CS-11
  'clef/docs::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'         # D10: clef's docs migrate with CS-11
  'clef/tests::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'        # inherited F# test corpus; moves with CS-11
  'clef/samples::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'      # same
  'ship-of-theseus::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'   # HelloProof's sample and proof trace migrate with CS-11
  'clef-lang-site/hugo/content::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'  # dated posts and docs pages; migrate with CS-11 or stand as history
  'mlir-plugins/README.md::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'      # same
  'Atelier::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'           # same
  'ClefAutoComplete::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'   # F# tooling, not Clef source; its .NET widths are its own until self-hosting
  'lattice-analyzers::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'   # F# tooling, not Clef source; its .NET widths are its own until self-hosting
  'lattice-vim::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'   # F# tooling, not Clef source; its .NET widths are its own until self-hosting
  'lattice-vscode::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'   # F# tooling, not Clef source; its .NET widths are its own until self-hosting
  'lattice-vscode-helpers::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'   # F# tooling, not Clef source; its .NET widths are its own until self-hosting
  'ionide-native-analyzers::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'   # F# tooling, not Clef source; its .NET widths are its own until self-hosting
  'Ionide-vim-fsnative::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'   # F# tooling, not Clef source; its .NET widths are its own until self-hosting
  'FsNativeAutoComplete::\b(u?int(8|16|32|64)|sbyte|unativeint|float32|float64|[Pp]osit(8|16|32|64))\b'   # F# tooling, not Clef source; its .NET widths are its own until self-hosting
  'Composer/src::TyCon'                                         # same
  'BAREWire/docs::FS[0-9]{4}'                               # BAREWire's own FS9xxx analyzer codes retire to CCS with the step-4 table
  'ClefAutoComplete::FS[0-9]{4}'                             # FCS fork: its codes are the F# compiler's; disposition is archive (Lattice_Consumer_Contract.md)
  'ClefAutoComplete::FSharp\.Quotations'                    # FCS fork: the F# compiler's own quotations surface; disposition is archive (same row)
  'clef-lang-spec/spec/lexical-filtering.md::\bFS[0-9]{4}\b'    # the offside example moves with the step-4 table
  'clef/docs/diagnostics.md::\bFS[0-9]{4}\b'                    # step 4
  'Composer/docs/WebView_Build_Integration.md::\bFS[0-9]{4}\b'  # step 4
  # 'path-substring::pattern-substring' — the row applies only to lines matching that retired pattern;
  # an empty pattern applies to every retired pattern in that path.
  'clef/src/Compiler/PSGSaturation/SemanticGraph/Core.fs::'                 # SeqSaturation two-shape recognizer → suspension recipe (spec seq §6)
  'clef/src/Compiler/PSGSaturation/SemanticGraph/Types.fs::code_ptr'        # LambdaContext base indices → closure hyperedge in CCS
  'clef/src/Compiler/Nanopass/BakerSaturation.fs::code_ptr'                 # same
  'Composer/src/MiddleEnd/PSGElaboration/YieldStateIndices.fs::'            # recognizer, Composer side → retired with it
  'Composer/src/MiddleEnd/PSGElaboration/::unrealized_conversion_cast'   # ClosureLayout / closure-pair coeffects → Closure_Retooling_Plan steps 1–3 (narrowed 2026-09-05 from a blanket row that had exempted the whole middle end from every retired pattern)
  'Composer/src/MiddleEnd/PSGElaboration/::memref<2xindex>'   # ClosureLayout / closure-pair coeffects → Closure_Retooling_Plan steps 1–3 (narrowed 2026-09-05 from a blanket row that had exempted the whole middle end from every retired pattern)
  'Composer/src/MiddleEnd/PSGElaboration/::code_ptr'   # ClosureLayout / closure-pair coeffects → Closure_Retooling_Plan steps 1–3 (narrowed 2026-09-05 from a blanket row that had exempted the whole middle end from every retired pattern)
  'Composer/src/MiddleEnd/PSGElaboration/::resolve-closure-casts'   # ClosureLayout / closure-pair coeffects → Closure_Retooling_Plan steps 1–3 (narrowed 2026-09-05 from a blanket row that had exempted the whole middle end from every retired pattern)
  'Composer/src/MiddleEnd/PSGElaboration/::ContStateMachine'   # ClosureLayout / closure-pair coeffects → Closure_Retooling_Plan steps 1–3 (narrowed 2026-09-05 from a blanket row that had exempted the whole middle end from every retired pattern)
  'Composer/src/MiddleEnd/PSGElaboration/::flattenSequentials'   # ClosureLayout / closure-pair coeffects → Closure_Retooling_Plan steps 1–3 (narrowed 2026-09-05 from a blanket row that had exempted the whole middle end from every retired pattern)
  'Composer/src/MiddleEnd/Alex/::unrealized_conversion_cast'   # cast sites and the memref<2xindex> closure pair → steps 4–5 (narrowed 2026-09-05, same reason)
  'Composer/src/MiddleEnd/Alex/::memref<2xindex>'   # cast sites and the memref<2xindex> closure pair → steps 4–5 (narrowed 2026-09-05, same reason)
  'Composer/src/MiddleEnd/Alex/::code_ptr'   # cast sites and the memref<2xindex> closure pair → steps 4–5 (narrowed 2026-09-05, same reason)
  'Composer/src/MiddleEnd/Alex/::resolve-closure-casts'   # cast sites and the memref<2xindex> closure pair → steps 4–5 (narrowed 2026-09-05, same reason)
  'Composer/src/MiddleEnd/Alex/::ContStateMachine'   # cast sites and the memref<2xindex> closure pair → steps 4–5 (narrowed 2026-09-05, same reason)
  'Composer/src/MiddleEnd/Alex/::flattenSequentials'   # cast sites and the memref<2xindex> closure pair → steps 4–5 (narrowed 2026-09-05, same reason)
  'Composer/src/BackEnd/LLVM/Lowering.fs::'                                 # resolve-closure-casts plugin pipeline → step 5
  'Composer/tests/::'                                                       # test expectations that pin the cast form → move with the witness
  'Composer/samples/::'                                                     # sample intermediates/expectations that carry the cast form → move with the witness
  'mlir-plugins/::'                                                         # the plugin itself → retired at step 5
  'Composer/docs/PRDs/::code_ptr'                                           # implementation PRDs carrying the interim layout, each with a banner → move with the code
  'Composer/docs/PRDs/::nativeptr'                                          # implementation PRDs written against the pre-strip pointer surface, each with a surface banner
  'clef/src/Compiler/::nativeptr'                                           # TNativePtr internal-only (commit 8768e536e); remaining NativePtr.* intrinsic recognition is a vestige to confirm
  'clef/tests/::nativeptr'                                                  # inherited F# compiler test corpus exercising the stripped surface; retire with those tests
  'BAREWire/docs/::nativeptr'                                               # BAREWire's .NET-side implementation legitimately uses NativeInterop; the strip governs the cross-compiled Clef surface
  'clef-lang-site/hugo/content/blog/::nativeptr'                            # dated posts, each carrying an editor's note; not rewritten
  'clef-lang-site/hugo/content/docs/internals/farscape/::nativeptr'         # Farscape's generated-code sketches, bannered; move with the generator
  'FsNativeAutoComplete/::'                                                 # superseded by ClefAutoComplete (same tree + 2 housekeeping commits); archive
  'Ionide-vim-fsnative/::'                                                  # superseded by lattice-vim, pending confirmation that its last commit (Multi-LSP docs, MLIR navigation) carried over
  'ClefAutoComplete/src/::FNCS'                                             # the fork's module/project names and HAVE_FNCS: the rename IS the first migration step; counted, not failing
  'ClefAutoComplete/test/::FNCS'                                            # same
  'ClefAutoComplete/benchmarks/::FNCS'                                      # same
  'ClefAutoComplete/build/::FNCS'                                           # same
  'lattice-vscode/src/::FNCS'                                               # client code still addressing the old server name; same migration step
  'lattice-vscode/release/::FNCS'                                           # release notes, history
  # The forks' upstream bodies are slated for retirement/reduction per Lattice_Consumer_Contract §6; their
  # READMEs state the position, and the remainder is counted, not failed, until the reduction lands.
  'ClefAutoComplete/docs/::FNCS' 'ClefAutoComplete/utils/::FNCS' 'ClefAutoComplete/.github/::FNCS'
  'ClefAutoComplete/build.fsx::FNCS' 'ClefAutoComplete/CONTRIBUTING.md::FNCS' 'ClefAutoComplete/CHANGELOG.md::FNCS'
  'ClefAutoComplete/FsNativeAutoComplete.sln::FNCS' 'ClefAutoComplete/Directory.Build.props::FNCS'
  'ClefAutoComplete/paket::FNCS' 'ClefAutoComplete/.devcontainer/::FNCS' 'ClefAutoComplete/.gitpod.yml::FNCS'
  'ClefAutoComplete/.vscode/::FNCS' 'ClefAutoComplete/.config/::FNCS' 'ClefAutoComplete/global.json::FNCS'
  'lattice-vscode/IONIDE_HERITAGE.md::FNCS' 'lattice-vscode/RELEASE_NOTES.md::FNCS' 'lattice-vscode/CONTRIBUTING.md::FNCS'
  'lattice-vscode/paket::FNCS' 'lattice-vscode/build/::FNCS' 'lattice-vscode/.github/::FNCS'
  'lattice-vim/README.mkd::FNCS' 'lattice-vim/IONIDE_HERITAGE.md::FNCS' 'lattice-vim/doc/::FNCS'
  'lattice-analyzers/IONIDE_HERITAGE.md::FNCS' 'lattice-analyzers/docs/::FNCS' 'lattice-analyzers/.github/::FNCS'
  'lattice-vscode-helpers/::FNCS'
  'lattice-vscode/release/::Firefly' 'ClefAutoComplete/test/::Firefly'
  'Composer/docs/PRDs/::FNCS'                                               # implementation PRDs written under the old name; bannered elsewhere; move with the code
  'clef-lang-site/hugo/content/blog/::FNCS'                                 # dated posts
  'Composer/docs/PRDs/::Firefly'                                            # implementation PRDs under the old name
  'ship-of-theseus/::Firefly'                                               # the talk that narrates the rename itself; history
  'clef/tests/::null'                                                       # inherited F# test corpus (null : T annotations)
  'Composer/docs/PRDs/::ptr<'                                               # implementation PRDs, bannered; move with the code
  'Composer/docs/PRDs/::null'                                               # same
  'Composer/docs/PRDs/::fat'                                                # implementation PRDs describing the interim string/array form
  'clef/src/Compiler/NativeTypedTree/::fat'                                 # NTUstring/array layout comments: two words, right size, retired meaning ({ptr,len} → {base index, extent})
  'clef/src/Compiler/NativeTypedTree/::ptr: \*'                             # same
  'clef/tests/::fat'                                                        # SpecDrivenNativeTypeTests pins the retired wording; moves with the layout
  'clef-lang-site/hugo/content/blog/::fat'                                  # dated posts
  'clef-lang-site/hugo/content/blog/::null'                                 # dated posts
  'clef/src/Compiler/Baker/Recipes/::null'                                  # collection recipes still emit a null for empty; the sentinel recipe replaces them (Phase 3 collections)
  'clef/src/Compiler/Baker/Recipes/::ptr<'                                  # same
  'clef/src/Compiler/Baker/Recipes/Decomposition.fs::null'                  # same
)
ALLOW_DIRS=( '/archive/' '/history/' '/proof-trace/' '/net10.0/' '/net9.0/' '/net8.0/' '/bin/' '/obj/' '/intermediates/' '/targets/' '/node_modules/' '/.git/' '/build/' '/target/' )

is_allowed() {
  local f="$1"
  for a in "${ALLOW_FILES[@]}"; do [[ "$f" == *"$a" ]] && return 0; done
  for d in "${ALLOW_DIRS[@]}"; do [[ "$f" == *"$d"* ]] && return 0; done
  return 1
}
is_scheduled() {
  local f="$1" pat="$2"
  for a in "${SCHEDULED[@]}"; do
    local path="${a%%::*}" only="${a#*::}"
    [[ "$f" == *"$path"* ]] || continue
    [[ -z "$only" || "$pat" == *"$only"* ]] && return 0
  done
  return 1
}

hits=0; scheduled=0
for dir in "${CORPUS[@]}"; do
  [[ -d "$dir" ]] || continue
  for pat in "${RETIRED[@]}"; do
    while IFS= read -r line; do
      [[ -z "$line" ]] && continue
      file="${line%%:*}"
      is_allowed "$file" && continue
      rest="${line#*:}"; text="${rest#*:}"
      grep -Eiq "$SUPERSESSION_MARKERS" <<<"$text" && continue
      if is_scheduled "$file" "$pat"; then scheduled=$((scheduled+1)); continue; fi
      printf '%s\n' "$line"
      hits=$((hits+1))
    done < <(grep -rnE --binary-files=without-match \
               --include='*.md' --include='*.fs' --include='*.fsi' --include='*.fsx' --include='*.clef' \
               --include='*.mlir' --include='*.sh' --include='*.toml' --include='*.fidproj' \
               "$pat" "$dir" 2>/dev/null)
  done
done

(( scheduled > 0 )) && echo "drift-gate: $scheduled line(s) in SCHEDULED code (retooling-plan deliverables; not failing)"
for r in "${LATTICE_REPOS[@]}"; do
  [[ -d "$ROOT/$r" ]] || continue
  n=$(grep -rEc --include='*.fs' --include='*.fsi' --include='*.ts' "$FCS_SURFACE" "$ROOT/$r" 2>/dev/null | awk -F: '{s+=$2} END {print s+0}')
  echo "fcs-surface: $r: $n reference(s) to the F# Compiler Service typed tree (migration size; not failing)"
done
if (( hits == 0 )); then
  echo "drift-gate: clean (no retired vocabulary in corpus)"
  exit 0
fi
echo "drift-gate: $hits line(s) of retired vocabulary — see Design_Supersession_Register.md"
(( WARN_ONLY )) && exit 0
exit 1
