#!/usr/bin/env bash
# clef #165 Increment B - leased analyzer entry point.
#
# Usage: RunClefAnalyzers.sh [--base <git-rev>]
#
# Builds the Clef-owned typed analyzer into a fresh per-invocation OutDir
# (immune to ambient OutDir/Configuration overrides or stale Debug DLLs), runs
# it over every Zone A compile item of src/Compiler/Clef.Compiler.Service.fsproj,
# writes a fresh SARIF report with AXD000 boundary-completion and dependency
# receipts, enforces base-vs-candidate baseline monotonicity against the
# accepted base revision (never comparing a committed candidate against itself;
# initial admission restricted strictly to the authorized bootstrap revision),
# and verifies exact equality + symmetric reference & ProjectReference closure
# against the checked-in ratchet baseline.
#
# Production verification never rewrites ratchet.tsv: baseline emission is an
# explicit, separate owner act via `VerifyReceipt.fsx --emit-baseline`.
set -euo pipefail

base_rev=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --base)
      [[ $# -ge 2 ]] || { printf 'Missing value for --base\n' >&2; exit 2; }
      base_rev="$2"
      shift 2
      ;;
    *)
      printf 'Unknown argument: %s (expected optional --base <git-rev>)\n' "$1" >&2
      exit 2
      ;;
  esac
done

tool_dir=$(cd -P "$(dirname "$0")" && pwd)
repo_dir=$(git -C "$tool_dir" rev-parse --show-toplevel)
project="$repo_dir/src/Compiler/Clef.Compiler.Service.fsproj"
dotnet=${DOTNET_HOST_PATH:-dotnet}
raw_out=${CLEF_ANALYZER_RECEIPTS:-$tool_dir/receipts}
mkdir -p "$raw_out"
out_dir=$(cd -P "$raw_out" && pwd)
baseline="$tool_dir/baseline/ratchet.tsv"

# Authorized Increment B bootstrap base revision (last commit before ratchet.tsv lands).
readonly BOOTSTRAP_BASE_SHA="2034d4bf25809c914658579bd5792f140ca950a1"

[[ "$project" == /* && -f "$project" ]] || { printf 'Compiler project not found: %s\n' "$project" >&2; exit 2; }
[[ -f "$baseline" ]] || { printf 'Ratchet baseline is missing: %s\n' "$baseline" >&2; exit 2; }

cd "$tool_dir"

stamp=$(date -u +%Y%m%dT%H%M%SZ)-$$
analyzer_dir="$out_dir/analyzer-bin-$stamp"
mkdir -p "$analyzer_dir"
report="$out_dir/report-$stamp.sarif"
analysis_log="$out_dir/analysis-$stamp.log"

"$dotnet" tool restore
"$dotnet" build Clef.Analyzers.fsproj --no-incremental -c Debug -m:1 \
  -p:BuildInParallel=false -p:OutDir="$analyzer_dir/"
analyzer_dll="$analyzer_dir/Clef.Analyzers.dll"
[[ -f "$analyzer_dll" ]] || { printf 'Analyzer assembly is not built in fresh OutDir: %s\n' "$analyzer_dll" >&2; exit 1; }

printf 'Analyzer assembly: %s sha256 %s\n' "$analyzer_dll" "$(sha256sum "$analyzer_dll" | awk '{print $1}')"
printf 'Checked-in baseline: %s sha256 %s\n' "$baseline" "$(sha256sum "$baseline" | awk '{print $1}')"

# Resolve accepted base revision for monotonic --ratchet-base comparison.
# If --base is omitted:
#   - When the working tree modifies ratchet.tsv (or adds it for bootstrap),
#     compare against HEAD.
#   - When ratchet.tsv is clean (committed candidate), compare against the
#     merge-base with origin/main, or HEAD~1 if HEAD is already at origin/main
#     so a committed candidate can never supply itself as its own base.
head_sha=$(git -C "$repo_dir" rev-parse HEAD)
if [[ -z "$base_rev" ]]; then
  if [[ -n "$(git -C "$repo_dir" status --porcelain -- tools/Clef.Analyzers/baseline/ratchet.tsv)" ]]; then
    base_rev="$head_sha"
  elif git -C "$repo_dir" rev-parse --verify origin/main >/dev/null 2>&1; then
    origin_sha=$(git -C "$repo_dir" rev-parse origin/main)
    if [[ "$head_sha" != "$origin_sha" ]]; then
      base_rev=$(git -C "$repo_dir" merge-base HEAD origin/main)
    elif git -C "$repo_dir" rev-parse --verify HEAD~1 >/dev/null 2>&1; then
      base_rev=$(git -C "$repo_dir" rev-parse HEAD~1)
    else
      base_rev="$head_sha"
    fi
  elif git -C "$repo_dir" rev-parse --verify HEAD~1 >/dev/null 2>&1; then
    base_rev=$(git -C "$repo_dir" rev-parse HEAD~1)
  else
    base_rev="$head_sha"
  fi
fi

resolved_base=$(git -C "$repo_dir" rev-parse --verify "${base_rev}^{commit}") || {
  printf 'RECEIPT FAIL: invalid --base revision: %s\n' "$base_rev" >&2
  exit 1
}

if git -C "$repo_dir" cat-file -e "${resolved_base}:tools/Clef.Analyzers/baseline/ratchet.tsv" 2>/dev/null; then
  base_baseline="$out_dir/base-ratchet-$stamp.tsv"
  git -C "$repo_dir" show "${resolved_base}:tools/Clef.Analyzers/baseline/ratchet.tsv" > "$base_baseline"
  printf 'Comparing candidate baseline against base revision %s\n' "$resolved_base"
  "$dotnet" fsi "$tool_dir/VerifyReceipt.fsx" --ratchet-base "$base_baseline" "$baseline"
elif [[ "$resolved_base" == "$BOOTSTRAP_BASE_SHA" ]]; then
  printf 'RECEIPT OK: initial baseline admission strictly at authorized bootstrap base %s.\n' "$resolved_base"
else
  printf 'RECEIPT FAIL: base revision %s lacks tools/Clef.Analyzers/baseline/ratchet.tsv and is not authorized bootstrap base %s.\n' \
    "$resolved_base" "$BOOTSTRAP_BASE_SHA" >&2
  exit 1
fi

"$dotnet" msbuild -noAutoResponse "$project" -property:Configuration=Debug \
  -getItem:Compile > "$out_dir/compile-items-$stamp.json"
"$dotnet" msbuild -noAutoResponse "$project" -property:Configuration=Debug \
  -property:BuildProjectReferences=false -target:FindReferenceAssembliesForReferences \
  -getItem:ReferencePathWithRefAssemblies > "$out_dir/references-$stamp.json"
"$dotnet" msbuild -noAutoResponse "$project" -property:Configuration=Debug \
  -getItem:ProjectReference > "$out_dir/project-refs-$stamp.json"

"$dotnet" fsi "$tool_dir/VerifyReceipt.fsx" --zone-a "$out_dir/compile-items-$stamp.json" > "$out_dir/zone-a-$stamp.txt"
mapfile -t zone_files < "$out_dir/zone-a-$stamp.txt"
[[ ${#zone_files[@]} -gt 0 ]] || { printf 'No Zone A files resolved.\n' >&2; exit 1; }
printf 'Analyzing %d Zone A compile items.\n' "${#zone_files[@]}"

set +e
"$dotnet" fsharp-analyzers --project "$project" --analyzers-path "$analyzer_dir" \
  --include-analyzers "Clef zone-A boundary" \
  --include-files "${zone_files[@]}" \
  --report "$report" > "$analysis_log" 2>&1
status=$?
set -e

if [[ ! -f "$report" ]]; then
  printf 'Analyzer run did not produce a report (exit %s); this is a tool failure, not a diagnostic.\n' "$status" >&2
  cat "$analysis_log" >&2
  exit 1
fi
if grep -qiE "failed to load|analyzer.*failed on|could not find analyzer" "$analysis_log"; then
  printf 'Analyzer load failure, not a diagnostic exit (exit %s).\n' "$status" >&2
  cat "$analysis_log" >&2
  exit 1
fi

printf 'Analyzer exit %s; diagnostics in %s sha256 %s\n' "$status" "$report" "$(sha256sum "$report" | awk '{print $1}')"

"$dotnet" fsi "$tool_dir/VerifyReceipt.fsx" --strict-typed-tree "$report"
"$dotnet" fsi "$tool_dir/VerifyReceipt.fsx" --verify \
  "$out_dir/compile-items-$stamp.json" "$out_dir/references-$stamp.json" \
  "$out_dir/project-refs-$stamp.json" "$report" "$baseline"
printf 'Receipt verification passed.\n'
