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
  "$ROOT/clef-lang-site/hugo/content"
  "$ROOT/mlir-plugins/README.md"
)

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
)

# A line that carries one of these markers is talking *about* the retired term, not using it.
SUPERSESSION_MARKERS='retired|retires|superseded|supersession|SHALL NOT|earlier revision|earlier framing|prior art|no longer|not planned|Retired\)|is going away|was written as|dissolved|interim|proposal(.s)? instruction|not denotable|user-denotable|replaces|stripped|NOT null|no null|not a null|never null|non-null|FFI boundary|at the boundary|C boundary|the sentinel|sentinel node|CHandle|no fat|not a fat|not fat|not user-denotable|no raw pointer|no raw-pointer|compiler-internal|internal-only|pre-strip|below the witness boundary|backend leg'

# Files whose purpose is to record the retirement itself, or history that must stay verbatim.
ALLOW_FILES=(
  # the register and its plans: they name what is retired
  'clef/docs/fidelity/phg/Design_Supersession_Register.md'
  'clef/docs/fidelity/phg/Closure_Retooling_Plan.md'
  'clef/docs/fidelity/phg/PSG_to_PHG_Plan.md'
  'clef/docs/fidelity/phg/drift-gate.sh'
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
  # 'path-substring::pattern-substring' — the row applies only to lines matching that retired pattern;
  # an empty pattern applies to every retired pattern in that path.
  'clef/src/Compiler/PSGSaturation/SemanticGraph/Core.fs::'                 # SeqSaturation two-shape recognizer → suspension recipe (spec seq §6)
  'clef/src/Compiler/PSGSaturation/SemanticGraph/Types.fs::code_ptr'        # LambdaContext base indices → closure hyperedge in CCS
  'clef/src/Compiler/Nanopass/BakerSaturation.fs::code_ptr'                 # same
  'Composer/src/MiddleEnd/PSGElaboration/YieldStateIndices.fs::'            # recognizer, Composer side → retired with it
  'Composer/src/MiddleEnd/PSGElaboration/::'                                # ClosureLayout / closure-pair coeffects → Closure_Retooling_Plan steps 1–3
  'Composer/src/MiddleEnd/Alex/::'                                          # cast sites and memref<2xindex> closure pair → steps 4–5
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
ALLOW_DIRS=( '/archive/' '/history/' '/proof-trace/' '/bin/' '/obj/' '/intermediates/' '/node_modules/' '/.git/' '/build/' '/target/' )

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
if (( hits == 0 )); then
  echo "drift-gate: clean (no retired vocabulary in corpus)"
  exit 0
fi
echo "drift-gate: $hits line(s) of retired vocabulary — see Design_Supersession_Register.md"
(( WARN_ONLY )) && exit 0
exit 1
