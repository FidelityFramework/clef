#!/usr/bin/env bash
# clef #165 Increment B - fault-injection negative control.
#
# Two separate probes against one live Zone A file, restored byte-identically:
#   probe A: System.Runtime.CompilerServices.ConditionalWeakTable (AXC010)
#   probe B: Microsoft.FSharp.Reflection.FSharpValue (AXC009)
#
# Asserts per probe:
#   1. Host build aborts before CoreCompile with CLEF001 (nonzero exit).
#   2. DesignTimeBuild=true alone STILL refuses with CLEF001 (no bypass).
#   3. SkipCompilerExecution=true alone STILL refuses with CLEF001 (no bypass).
#   4. DesignTimeBuild=true + SkipCompilerExecution=true skips the guard so
#      fsharp-analyzers can crack the project and inspect the typed AST.
#   5. Clef-owned analyzer reports exact code & reason at injected line (>= orig_lines + 1).
#   6. VerifyReceipt.fsx --ratchet refuses the injected site against ratchet.tsv.
set -euo pipefail

tool_dir=$(cd -P "$(dirname "$0")/.." && pwd)
repo_dir=$(git -C "$tool_dir" rev-parse --show-toplevel)
dotnet=${DOTNET_HOST_PATH:-dotnet}
raw_out=${CLEF_ANALYZER_RECEIPTS:-$tool_dir/receipts}
mkdir -p "$raw_out"
out_dir=$(cd -P "$raw_out" && pwd)
project="$repo_dir/src/Compiler/Clef.Compiler.Service.fsproj"
baseline="$tool_dir/baseline/ratchet.tsv"
target="$repo_dir/src/Compiler/PSGSaturation/SemanticGraph/BorrowedViews.fs"
stamp=$(date -u +%Y%m%dT%H%M%SZ)-$$
analyzer_dir="$out_dir/fault-analyzer-bin-$stamp"
mkdir -p "$analyzer_dir"

selected=${1:-AB}
case "$selected" in
  A|B|AB|BA) ;;
  *) printf 'Invalid probe selection: %s (expected A, B, or AB)\n' "$selected" >&2; exit 2 ;;
esac

cd "$tool_dir"
"$dotnet" tool restore > /dev/null
"$dotnet" build "$tool_dir/Clef.Analyzers.fsproj" --no-incremental -c Debug -m:1 \
  -p:BuildInParallel=false -p:OutDir="$analyzer_dir/"

[[ -f "$target" ]] || { printf 'Fault target missing: %s\n' "$target" >&2; exit 2; }
[[ -f "$baseline" ]] || { printf 'Ratchet baseline is missing: %s\n' "$baseline" >&2; exit 2; }

original_sha=$(sha256sum "$target" | awk '{print $1}')
orig_lines=$(wc -l < "$target")
cp "$target" "$out_dir/BorrowedViews.fs.original-$stamp"

restore() {
  cp "$out_dir/BorrowedViews.fs.original-$stamp" "$target"
  restored=$(sha256sum "$target" | awk '{print $1}')
  if [[ "$original_sha" != "$restored" ]]; then
    printf 'RESTORE FAILED: expected %s got %s\n' "$original_sha" "$restored" >&2
    exit 1
  fi
  printf 'RESTORED byte-identical: %s sha256 %s\n' "$target" "$restored"
}
trap restore EXIT

# Baseline guard run on the unmodified file.
set +e
"$dotnet" msbuild -noAutoResponse "$project" -property:Configuration=Debug \
  -property:SkipResolveProjectReferences=true -target:CheckClefCoreNominals \
  > "$out_dir/guard-clean-$stamp.log" 2>&1
clean_status=$?
set -e
printf 'Guard at HEAD: exit %s\n' "$clean_status"
[[ $clean_status -eq 0 ]] || { printf 'CONTROL FAIL: the guard refuses a clean Zone A file.\n' >&2; exit 1; }

pass=0
fail=0

probe() {
  local name="$1" line="$2" code="$3" reason="$4"
  local injected_min_line=$((orig_lines + 1))
  printf '\n// clef #165 fault-injection probe %s: refused before CoreCompile.\n%s\n' "$name" "$line" >> "$target"
  printf 'PROBE %s injected into %s at line >= %d\n' "$name" "$target" "$injected_min_line"

  # 1. Host build: the guard must abort with CLEF001 before CoreCompile.
  set +e
  "$dotnet" msbuild -noAutoResponse "$project" -property:Configuration=Debug \
    -property:SkipResolveProjectReferences=true \
    > "$out_dir/build-fault-$name-$stamp.log" 2>&1
  build_status=$?
  set -e
  if [[ $build_status -ne 0 ]] && grep -q "CLEF001" "$out_dir/build-fault-$name-$stamp.log"; then
    printf 'CONTROL PASS: host build refused probe %s (exit %s) with CLEF001.\n' "$name" "$build_status"
    pass=$((pass + 1))
  else
    printf 'CONTROL FAIL: probe %s was not refused by the host build (exit %s).\n' "$name" "$build_status" >&2
    fail=$((fail + 1))
  fi

  # 2a. DesignTimeBuild=true alone MUST STILL refuse with CLEF001 (no bypass).
  set +e
  "$dotnet" msbuild -noAutoResponse "$project" -property:Configuration=Debug \
    -property:SkipResolveProjectReferences=true -target:CheckClefCoreNominals \
    -property:DesignTimeBuild=true \
    > "$out_dir/guard-dtb-$name-$stamp.log" 2>&1
  dtb_status=$?
  set -e
  if [[ $dtb_status -ne 0 ]] && grep -q "CLEF001" "$out_dir/guard-dtb-$name-$stamp.log"; then
    printf 'CONTROL PASS: DesignTimeBuild=true alone still refused probe %s with CLEF001.\n' "$name"
    pass=$((pass + 1))
  else
    printf 'CONTROL FAIL: DesignTimeBuild=true bypassed the guard for probe %s (exit %s).\n' "$name" "$dtb_status" >&2
    fail=$((fail + 1))
  fi

  # 2b. SkipCompilerExecution=true alone MUST STILL refuse with CLEF001 (no bypass).
  set +e
  "$dotnet" msbuild -noAutoResponse "$project" -property:Configuration=Debug \
    -property:SkipResolveProjectReferences=true -target:CheckClefCoreNominals \
    -property:SkipCompilerExecution=true \
    > "$out_dir/guard-skiponly-$name-$stamp.log" 2>&1
  skiponly_status=$?
  set -e
  if [[ $skiponly_status -ne 0 ]] && grep -q "CLEF001" "$out_dir/guard-skiponly-$name-$stamp.log"; then
    printf 'CONTROL PASS: SkipCompilerExecution=true alone still refused probe %s with CLEF001.\n' "$name"
    pass=$((pass + 1))
  else
    printf 'CONTROL FAIL: SkipCompilerExecution=true alone bypassed the guard for probe %s (exit %s).\n' "$name" "$skiponly_status" >&2
    fail=$((fail + 1))
  fi

  # 2c. DesignTimeBuild=true + SkipCompilerExecution=true skips the guard for AST analysis.
  set +e
  "$dotnet" msbuild -noAutoResponse "$project" -property:Configuration=Debug \
    -property:SkipResolveProjectReferences=true -target:CheckClefCoreNominals \
    -property:DesignTimeBuild=true -property:SkipCompilerExecution=true \
    > "$out_dir/guard-skip-$name-$stamp.log" 2>&1
  skip_status=$?
  set -e
  if [[ $skip_status -eq 0 ]] && ! grep -q "CLEF001" "$out_dir/guard-skip-$name-$stamp.log"; then
    printf 'CONTROL PASS: DesignTimeBuild=true + SkipCompilerExecution=true skipped the guard for probe %s.\n' "$name"
    pass=$((pass + 1))
  else
    printf 'CONTROL FAIL: DesignTimeBuild=true + SkipCompilerExecution=true did not skip the guard for probe %s (exit %s).\n' "$name" "$skip_status" >&2
    fail=$((fail + 1))
  fi

  # 3. Typed analyzer reports exact code & reason at the injected line (>= orig_lines + 1).
  local probe_sarif="$out_dir/fault-report-$name-$stamp.sarif"
  set +e
  "$dotnet" fsharp-analyzers --project "$project" --analyzers-path "$analyzer_dir" \
    --include-analyzers "Clef zone-A boundary" --include-files "$target" \
    --report "$probe_sarif" \
    > "$out_dir/fault-analysis-$name-$stamp.log" 2>&1
  analyzer_status=$?
  set -e
  printf 'PROBE %s SARIF: %s\n' "$name" "$probe_sarif"
  if [[ -f "$probe_sarif" ]] && [[ $analyzer_status -ne 0 ]]; then
    printf 'CONTROL PASS: analyzer exited non-zero (%s) for probe %s.\n' "$analyzer_status" "$name"
    pass=$((pass + 1))
  else
    printf 'CONTROL FAIL: analyzer exit %s for probe %s.\n' "$analyzer_status" "$name" >&2
    fail=$((fail + 1))
  fi
  if "$dotnet" fsi "$tool_dir/VerifyReceipt.fsx" --expect \
       "$probe_sarif" "BorrowedViews.fs" "$code" "$reason" --min-line "$injected_min_line"; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
  fi

  # 4. Ratchet refuses the injected site (naming BorrowedViews.fs and exact code).
  set +e
  "$dotnet" fsi "$tool_dir/VerifyReceipt.fsx" --ratchet "$baseline" \
    "$probe_sarif" > "$out_dir/ratchet-fault-$name-$stamp.log" 2>&1
  ratchet_status=$?
  set -e
  if [[ $ratchet_status -ne 0 ]] && grep -q "BorrowedViews.fs $code" "$out_dir/ratchet-fault-$name-$stamp.log"; then
    printf 'CONTROL PASS: ratchet refused the injected %s site in BorrowedViews.fs.\n' "$code"
    pass=$((pass + 1))
  else
    printf 'CONTROL FAIL: ratchet did not refuse BorrowedViews.fs %s (exit %s).\n' "$code" "$ratchet_status" >&2
    cat "$out_dir/ratchet-fault-$name-$stamp.log" >&2
    fail=$((fail + 1))
  fi

  restore
}

if [[ "$selected" == *A* ]]; then
  probe A 'let private fiProbeWeakTable = System.Runtime.CompilerServices.ConditionalWeakTable<string, string>()' AXC010 "ambient or process-wide mutable state"
fi
if [[ "$selected" == *B* ]]; then
  probe B 'let private fiProbeReflect = Microsoft.FSharp.Reflection.FSharpValue.PreComputeTupleReader typeof<int * int>' AXC009 "reflection or structural formatting"
fi

src_diff=$(git -C "$repo_dir" diff -- src/ | wc -c)
printf 'src/ diff bytes after restore: %s\n' "$src_diff"
[[ $src_diff -eq 0 ]] || { printf 'CONTROL FAIL: src/ was left modified.\n' >&2; exit 1; }

set +e
"$dotnet" msbuild -noAutoResponse "$project" -property:Configuration=Debug \
  -property:SkipResolveProjectReferences=true -target:CheckClefCoreNominals \
  > "$out_dir/guard-clean-after-$stamp.log" 2>&1
final_status=$?
set -e
printf 'Guard after restore: exit %s\n' "$final_status"
[[ $final_status -eq 0 ]]

printf 'Fault-injection controls: %d pass, %d fail.\n' "$pass" "$fail"
[[ $fail -eq 0 ]]
