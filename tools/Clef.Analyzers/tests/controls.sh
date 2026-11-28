#!/usr/bin/env bash
# clef #165 Increment B - rule, provenance, completion, ProjectReference, and exact-ratchet controls.
set -euo pipefail

tool_dir=$(cd -P "$(dirname "$0")/.." && pwd)
repo_dir=$(git -C "$tool_dir" rev-parse --show-toplevel)
dotnet=${DOTNET_HOST_PATH:-dotnet}
raw_out=${CLEF_ANALYZER_RECEIPTS:-$tool_dir/receipts}
mkdir -p "$raw_out"
out_dir=$(cd -P "$raw_out" && pwd)
fixture="$tool_dir/tests/fixtures/Fixture.fsproj"
stamp=$(date -u +%Y%m%dT%H%M%SZ)-$$
analyzer_dir="$out_dir/fixture-analyzer-bin-$stamp"
mkdir -p "$analyzer_dir"
report="$out_dir/fixture-report-$stamp.sarif"
refs="$out_dir/fixture-references-$stamp.json"
proj_refs="$out_dir/fixture-project-refs-$stamp.json"
line="$out_dir/control-line-$stamp.txt"
zero=0000000000000000000000000000000000000000000000000000000000000000

cd "$tool_dir"
"$dotnet" tool restore > /dev/null

# Build analyzer into fresh invocation-specific OutDir (also verifying ambient
# OutDir env cannot redirect or substitute a stale Debug DLL).
OutDir="$out_dir/ignored-ambient-outdir/" "$dotnet" build "$tool_dir/Clef.Analyzers.fsproj" \
  --no-incremental -c Debug -m:1 -p:BuildInParallel=false -p:OutDir="$analyzer_dir/"
[[ -f "$analyzer_dir/Clef.Analyzers.dll" ]] || { printf 'Analyzer DLL missing from fresh OutDir: %s\n' "$analyzer_dir" >&2; exit 1; }
[[ ! -f "$out_dir/ignored-ambient-outdir/Clef.Analyzers.dll" ]] || { printf 'Ambient OutDir leaked into analyzer build\n' >&2; exit 1; }

"$dotnet" build "$fixture" --no-incremental -m:1 -p:BuildInParallel=false
"$dotnet" msbuild -noAutoResponse "$fixture" -property:Configuration=Debug \
  -property:BuildProjectReferences=false -target:FindReferenceAssembliesForReferences \
  -getItem:ReferencePathWithRefAssemblies > "$refs"
"$dotnet" msbuild -noAutoResponse "$fixture" -property:Configuration=Debug \
  -getItem:ProjectReference > "$proj_refs"

set +e
"$dotnet" fsharp-analyzers --project "$fixture" --analyzers-path "$analyzer_dir" \
  --include-analyzers "Clef zone-A boundary" \
  --report "$report" > "$out_dir/fixture-analysis-$stamp.log" 2>&1
status=$?
set -e
[[ -f "$report" ]] || { printf 'Fixture run produced no SARIF (exit %s).\n' "$status" >&2; exit 1; }

if grep -qiE "analyzer.*failed on|failed to load|could not find analyzer" \
     "$out_dir/fixture-analysis-$stamp.log"; then
  printf 'Fixture run: an analyzer failed to load, exit %s.\n' "$status" >&2
  exit 1
fi

pass=0
fail=0

run() {
  if "$dotnet" fsi "$tool_dir/VerifyReceipt.fsx" "$@" > "$line" 2>&1; then
    cat "$line"
    pass=$((pass + 1))
  else
    cat "$line"
    fail=$((fail + 1))
  fi
}

run_refusal() {
  local reason="$1"
  shift
  if "$dotnet" fsi "$tool_dir/VerifyReceipt.fsx" "$@" > "$line" 2>&1; then
    printf 'CONTROL FAIL: expected a refusal for %s, the verifier accepted it\n' "$reason"
    cat "$line"
    fail=$((fail + 1))
  elif grep -qiE "$reason" "$line"; then
    printf 'CONTROL PASS (refusal, exact reason: %s)\n' "$reason"
    cat "$line"
    pass=$((pass + 1))
  else
    printf 'CONTROL FAIL: refused, but not for the reason %s\n' "$reason"
    cat "$line"
    fail=$((fail + 1))
  fi
}

# Blocker 1: guard skips ONLY when BOTH DesignTimeBuild=true AND SkipCompilerExecution=true.
guard_target=$(sed -n '/Target Name="CheckClefCoreNominals"/,/>/p' "$repo_dir/build/ClefCore.targets")
expected_cond=$(cat <<'EOF'
'$(DesignTimeBuild)' != 'true' or '$(SkipCompilerExecution)' != 'true'
EOF
)
if printf '%s\n' "$guard_target" | grep -Fq "$expected_cond"; then
  printf 'CONTROL PASS: guard Condition requires BOTH DesignTimeBuild=true and SkipCompilerExecution=true to skip.\n'
  pass=$((pass + 1))
else
  printf 'CONTROL FAIL: guard Condition has wrong skip predicate: %s\n' "$guard_target"
  fail=$((fail + 1))
fi

# Blocker 4: build/ClefCore.targets must never emit or rewrite the ratchet baseline.
if grep -qiE "emit-baseline|ratchet\.tsv" "$repo_dir/build/ClefCore.targets"; then
  printf 'CONTROL FAIL: build/ClefCore.targets references emit-baseline or ratchet.tsv.\n'
  fail=$((fail + 1))
else
  printf 'CONTROL PASS: build/ClefCore.targets emits no baseline.\n'
  pass=$((pass + 1))
fi

# Production script must bind checked-in ratchet.tsv, fresh per-invocation OutDir, and --base check.
if grep -q 'CLEF_ANALYZER_BASELINE\|CLEF_ANALYZER_ASSEMBLY_DIR' "$tool_dir/RunClefAnalyzers.sh"; then
  printf 'CONTROL FAIL: RunClefAnalyzers.sh still allows baseline or assembly env override.\n'
  fail=$((fail + 1))
elif ! grep -Fq -- '-p:OutDir="$analyzer_dir/"' "$tool_dir/RunClefAnalyzers.sh"; then
  printf 'CONTROL FAIL: RunClefAnalyzers.sh does not pin invocation-specific OutDir.\n'
  fail=$((fail + 1))
else
  printf 'CONTROL PASS: RunClefAnalyzers.sh binds checked-in ratchet.tsv and fresh per-invocation OutDir DLL.\n'
  pass=$((pass + 1))
fi

# Unauthorized non-bootstrap --base without ratchet.tsv must be refused by RunClefAnalyzers.sh.
if prev_sha=$(git -C "$repo_dir" rev-parse --verify HEAD~1 2>/dev/null); then
  set +e
  CLEF_ANALYZER_RECEIPTS="$out_dir" bash "$tool_dir/RunClefAnalyzers.sh" --base "$prev_sha" > "$line" 2>&1
  unauth_status=$?
  set -e
  if [[ $unauth_status -ne 0 ]] && grep -qi "not authorized bootstrap base" "$line"; then
    printf 'CONTROL PASS (refusal, exact reason: unauthorized non-bootstrap --base %s refused)\n' "$prev_sha"
    pass=$((pass + 1))
  else
    printf 'CONTROL FAIL: RunClefAnalyzers.sh did not refuse unauthorized --base %s (exit %s)\n' "$prev_sha" "$unauth_status"
    cat "$line"
    fail=$((fail + 1))
  fi
fi

# Clean positive controls (including string/comment/type-var/interpolated lookalikes and keyed graph.Nodes lookups).
run --expect-none "$report" "ZoneAClean.fs"
run --expect-none "$report" "AdmittedCarrier.fs"
run --expect-none "$report" "InlineIlCase.fs"
run --expect-none "$report" "SegmentationCleanCase.fs"
run --expect "$report" "ZoneAClean.fs" "AXD000" "boundaryAnalyzerCompleted"
run --expect "$report" "AdmittedCarrier.fs" "AXD000" "referenceManifestSha256"
run --expect "$report" "InlineIlCase.fs" "AXD000" "sourceSha256"

# Positive AXD000 provenance & symmetric reference + project-reference equality on the real fixture run.
run --provenance "$report" "$refs" --project-refs "$proj_refs"

# Exact-reason negative controls (with exact --line assertions for lexer/AST edge cases).
run --expect "$report" "BoxCase.fs" "AXC001" "untyped obj escape hatch"
run --expect "$report" "ObjDeclCase.fs" "AXC005" "declared obj-typed value"
run --expect "$report" "BclCase.fs" "AXC002" "Zone A may not depend on the .NET base class library"
run --expect "$report" "StringMemberCase.fs" "AXC003" "direct BCL member on a primitive carrier"
run --expect "$report" "NullIdentityCase.fs" "AXC004" "null literal inside Zone A" --line 6
run --expect "$report" "NullIdentityCase.fs" "AXC004" "null literal inside Zone A" --line 12
run --expect "$report" "NullIdentityCase.fs" "AXC004" "null literal inside Zone A" --line 15
run --expect "$report" "NullIdentityCase.fs" "AXC004" "null literal inside Zone A" --line 18
run --expect "$report" "NullIdentityCase.fs" "AXC004" "reference identity or null" --line 21
run --expect "$report" "NullIdentityCase.fs" "AXC004" "reference identity or null" --line 24
run --expect "$report" "HostProcessCase.fs" "AXC006" "host, process or timing primitive"
run --expect "$report" "HostToolsCase.fs" "CLF002" "HostTools" --min-line 11
run --expect "$report" "LazyStateCase.fs" "AXC010" "branches on Lazy state" --min-line 5
run --expect "$report" "InlineIlFault.fs" "AXC007" "inline MSIL escape hatch" --line 6
run --expect "$report" "InlineIlFault.fs" "AXC007" "inline MSIL CLR throw" --line 8
run --expect "$report" "InlineIlFault.fs" "AXC007" "inline MSIL CLR throw" --line 10
run --expect "$report" "InlineIlFault.fs" "AXC007" "inline MSIL escape hatch" --line 12
run --expect "$report" "ExtendedInterpFault.fs" "AXC009" "extended interpolated string hole"
run --expect "$report" "ReflectionCase.fs" "AXC009" "reflection or structural formatting"
run --expect "$report" "ReflectionCase.fs" "AXC009" "resolved PrintfFormat contains %A" --line 21
run --expect "$report" "ReflectionCase.fs" "AXC009" "resolved PrintfFormat contains %*A" --line 24
run --expect "$report" "ReflectionCase.fs" "AXC009" "runtime PrintfFormat" --line 27
run --expect "$report" "ReflectionCase.fs" "AXC009" "%O format specifier" --line 31
run --expect "$report" "ReflectionCase.fs" "AXC009" "%T format specifier" --line 33
run --expect "$report" "FaultCase.fs" "AXC010" "ambient or process-wide mutable state"
run --expect "$report" "FaultCase.fs" "AXC009" "reflection or structural formatting"
run --expect "$report" "ConcurrentCase.fs" "AXC010" "ambient or process-wide mutable state"
run --expect "$report" "ConcurrentCase.fs" "AXC010" "Monitor lock" --line 11
run --expect "$report" "MutableCellCase.fs" "AXC011" "legacy mutable BCL collection"
run --expect "$report" "MutableCellCase.fs" "AXC010" "ambient mutable state"
run --expect "$report" "RefCellCase.fs" "AXC010" "module-level ref cell" --line 6
run --expect "$report" "RefCellCase.fs" "AXC010" "captures a ref cell" --line 8
run --expect "$report" "RefCellCase.fs" "AXC010" "captures a ref cell" --line 14
run --expect "$report" "RefCellCase.fs" "AXC011" "mutable ref cell" --line 18
run --expect "$report" "RefCellCase.fs" "AXC011" "mutable ref cell" --line 21
run --expect "$report" "RefCellCase.fs" "AXC011" "mutable ref cell" --line 24
run --expect "$report" "RefCellCase.fs" "AXC011" "mutable ref cell" --line 25
run --expect "$report" "RefCellCase.fs" "AXC011" "mutable ref cell" --line 26
run --expect "$report" "ThrowCase.fs" "AXC008" "'failwith' throws"
run --expect "$report" "ThrowCase.fs" "AXC008" "'failwithf' throws"
run --expect "$report" "ThrowCase.fs" "AXC008" "'head' throws"
run --expect "$report" "ThrowCase.fs" "AXC008" "'get' throws"
run --expect "$report" "ThrowCase.fs" "AXC008" "'nullArgCheck' throws" --line 13
run --expect "$report" "AliasResolutionCase.fs" "CLF001" "re-derives published state" --min-line 12
run --expect "$report" "AliasResolutionCase.fs" "CLF001" "readSharedBufferRegions" --min-line 15
run --expect "$report" "WitnessEmissionCase.fs" "CLF001" "WitnessEmission"
run --expect "$report" "PublicationProjectCase.fs" "CLF001" "Publication"
run --expect "$report" "ConsoleOutputCase.fs" "CLF002" "writes to the console"
run --expect "$report" "ConsoleWriteCase.fs" "CLF002" "touches the host"
run --expect "$report" "NativeTypedTree/NormalizeCase.fs" "CLF003" "re-normalizes the native typed tree" --min-line 7
run --expect "$report" "SegmentationUnionCase.fs" "CLF004" "segmentation node-keys-union ratchet"
run --expect "$report" "SegmentationEdgeUnionCase.fs" "CLF004" "segmentation unfiltered-edges ratchet"

# No Zone A item may be left unanalysed, and AXD001 is never a pass.
run --strict-typed-tree "$report"

axd001_report="$out_dir/axd001-negative-$stamp.sarif"
printf '{"runs":[{"results":[{"ruleId":"AXD001","message":{"text":"the typed tree is unavailable, so the Clef zone-A analyzer cannot run"},"locations":[{"physicalLocation":{"artifactLocation":{"uri":"NativeTypedTree/SyntheticGap.fs"}}}]}]}]}' > "$axd001_report"
run_refusal "not typed-tree analysed" --strict-typed-tree "$axd001_report"

clean_report="$out_dir/axd001-clean-$stamp.sarif"
printf '{"runs":[{"results":[]}]}' > "$clean_report"
run --strict-typed-tree "$clean_report"
run_refusal "zero AXD000" --provenance "$clean_report" "$refs"

# Adversarial provenance & boundary-completion tampered negatives.
tamper() {
  local pattern="$1" replacement="$2" output="$3"
  sed "s|$pattern|$replacement|" "$report" > "$output"
  if cmp -s "$report" "$output"; then
    printf 'CONTROL FAIL: the tamper pattern matched nothing, so the negative control is vacuous\n' >&2
    exit 1
  fi
}

esc='\\":\\"'

tamper "sourceSha256$esc[0-9a-f]*" "sourceSha256$esc$zero" "$out_dir/provenance-tampered-source-$stamp.sarif"
run_refusal "source hash.*stale or invented" --provenance "$out_dir/provenance-tampered-source-$stamp.sarif" "$refs"

tamper "sha256$esc[0-9a-f]*" "sha256$esc$zero" "$out_dir/provenance-tampered-assembly-$stamp.sarif"
run_refusal "assembly hash.*stale or invented" --provenance "$out_dir/provenance-tampered-assembly-$stamp.sarif" "$refs"

tamper "sha256$esc[0-9a-f]*" "sha256$esc" "$out_dir/provenance-missing-digest-$stamp.sarif"
run_refusal "has no SHA-256 digest" --provenance "$out_dir/provenance-missing-digest-$stamp.sarif" "$refs"

tamper "referenceManifestSha256$esc[0-9a-f]*" "referenceManifestSha256$esc$zero" "$out_dir/provenance-tampered-manifest-$stamp.sarif"
run_refusal "reference manifest digest" --provenance "$out_dir/provenance-tampered-manifest-$stamp.sarif" "$refs"

tamper 'assemblies\\":\[[^]]*]' 'assemblies\\":[]' "$out_dir/provenance-empty-closure-$stamp.sarif"
run_refusal "records no assemblies" --provenance "$out_dir/provenance-empty-closure-$stamp.sarif" "$refs"

tamper 'boundaryAnalyzerCompleted\\":true' 'boundaryAnalyzerCompleted\\":false' "$out_dir/provenance-uncompleted-boundary-$stamp.sarif"
run_refusal "lacks boundaryAnalyzerCompleted=true" --provenance "$out_dir/provenance-uncompleted-boundary-$stamp.sarif" "$refs"

# Stripping all boundary diagnostics while retaining AXD000 must fail boundaryDiagnosticCount check.
stripped_report="$out_dir/provenance-stripped-diags-$stamp.sarif"
jq '.runs[0].results |= map(select(.ruleId == "AXD000"))' "$report" > "$stripped_report"
run_refusal "boundary diagnostic count mismatch" --provenance "$stripped_report" "$refs"

# Duplicate AXD000 receipt must be refused.
dup_axd_report="$out_dir/provenance-dup-axd000-$stamp.sarif"
jq '.runs[0].results += [(.runs[0].results | map(select(.ruleId == "AXD000")) | .[0])]' "$report" > "$dup_axd_report"
run_refusal "duplicate dependency-context receipt" --provenance "$dup_axd_report" "$refs"

# Same-suffix different-root substitution must be refused by canonical path check.
other_root="$out_dir/other-checkout/tools/Clef.Analyzers/tests/fixtures"
mkdir -p "$other_root"
cp "$tool_dir/tests/fixtures/ZoneAClean.fs" "$other_root/ZoneAClean.fs"
sub_report="$out_dir/provenance-other-root-$stamp.sarif"
sed "s|$tool_dir/tests/fixtures/ZoneAClean.fs|$other_root/ZoneAClean.fs|g" "$report" > "$sub_report"
if cmp -s "$report" "$sub_report"; then
  printf 'CONTROL FAIL: same-suffix substitution matched nothing\n' >&2
  exit 1
fi
run_refusal "canonical path mismatch" --provenance "$sub_report" "$refs"

# Extra MSBuild ref not cited by analyzer -> refused.
probe_refs="$out_dir/provenance-extra-reference-$stamp.json"
awk 'BEGIN{inserted=0}
  /^    "ReferencePathWithRefAssemblies": \[$/ { print; print "      { \"FullPath\": \"does-not-exist-in-the-evaluated-set.dll\" },"; inserted=1; next }
  { print }' "$refs" > "$probe_refs"
run_refusal "omits .* evaluated reference path" --provenance "$report" "$probe_refs"

# Shortened MSBuild ref list (symmetric check) -> refused.
short_refs="$out_dir/provenance-short-reference-$stamp.json"
jq '.Items.ReferencePathWithRefAssemblies |= .[1:]' "$refs" > "$short_refs"
run_refusal "unexpected reference path" --provenance "$report" "$short_refs"

# Symmetric @(ProjectReference) refusal controls (omitted generator project & unexpected project while assemblies stay intact).
missing_proj_refs="$out_dir/provenance-missing-proj-$stamp.json"
printf '{"Items":{"ProjectReference":[{"FullPath":"%s/buildtools/fslex/fslex.fsproj"}]}}\n' "$repo_dir" > "$missing_proj_refs"
run_refusal "omits 1 evaluated project reference" --provenance "$report" "$refs" --project-refs "$missing_proj_refs"

extra_proj_report="$out_dir/provenance-extra-proj-$stamp.sarif"
jq --arg p "$repo_dir/buildtools/fslex/fslex.fsproj" \
  '.runs[0].results |= map(if .ruleId == "AXD000" then .message.text = ((.message.text | fromjson) | .context.referencedProjects = [$p] | tojson) else . end)' \
  "$report" > "$extra_proj_report"
run_refusal "unexpected project reference" --provenance "$extra_proj_report" "$refs" --project-refs "$proj_refs"

# Exact-equality ratchet (refuses stale slack 1->0->1) + monotonic --ratchet-base + strict parser controls.
synthetic_report() {
  local path="$1" code="$2" count="$3"
  local results=""
  for ((i = 0; i < count; i++)); do
    entry="{\"ruleId\":\"$code\",\"message\":{\"text\":\"synthetic site $i\"},\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"NativeTypedTree/SyntheticRatchet.fs\"}}}]}"
    if [[ -z "$results" ]]; then results="$entry"; else results="$results,$entry"; fi
  done
  printf '{"runs":[{"results":[%s]}]}' "$results" > "$path"
}

baseline_probe="$out_dir/ratchet-probe-$stamp.tsv"
printf 'NativeTypedTree/SyntheticRatchet.fs\tAXC011\t3\n' > "$baseline_probe"

synthetic_report "$out_dir/ratchet-equal-$stamp.sarif" AXC011 3
run --ratchet "$baseline_probe" "$out_dir/ratchet-equal-$stamp.sarif"
synthetic_report "$out_dir/ratchet-shrunk-$stamp.sarif" AXC011 2
run_refusal "ratchet refused 1 shrunk site" --ratchet "$baseline_probe" "$out_dir/ratchet-shrunk-$stamp.sarif"
synthetic_report "$out_dir/ratchet-increased-$stamp.sarif" AXC011 4
run_refusal "ratchet refused 1 increased site" --ratchet "$baseline_probe" "$out_dir/ratchet-increased-$stamp.sarif"
synthetic_report "$out_dir/ratchet-new-site-$stamp.sarif" AXC007 1
run_refusal "ratchet refused 1 new site" --ratchet "$baseline_probe" "$out_dir/ratchet-new-site-$stamp.sarif"

# 1 -> 0 -> 1 regrowth prevention + --ratchet-base monotonic comparison.
base_one="$out_dir/ratchet-base-one-$stamp.tsv"
cand_zero="$out_dir/ratchet-cand-zero-$stamp.tsv"
cand_raised="$out_dir/ratchet-cand-raised-$stamp.tsv"
cand_added="$out_dir/ratchet-cand-added-$stamp.tsv"
printf 'NativeTypedTree/SyntheticRatchet.fs\tAXC011\t1\n' > "$base_one"
printf '# retired row\n' > "$cand_zero"
printf 'NativeTypedTree/SyntheticRatchet.fs\tAXC011\t2\n' > "$cand_raised"
printf 'NativeTypedTree/SyntheticRatchet.fs\tAXC011\t1\nNativeTypedTree/NewFile.fs\tAXC010\t1\n' > "$cand_added"

run_refusal "ratchet refused 1 shrunk site" --ratchet "$base_one" "$clean_report"
run --ratchet-base "$base_one" "$cand_zero"
run --ratchet "$cand_zero" "$clean_report"
synthetic_report "$out_dir/ratchet-regrow-$stamp.sarif" AXC011 1
run_refusal "ratchet refused 1 new site" --ratchet "$cand_zero" "$out_dir/ratchet-regrow-$stamp.sarif"
run_refusal "ratchet-base refused 1 new baseline row" --ratchet-base "$cand_zero" "$base_one"
run_refusal "ratchet-base refused 1 raised baseline row" --ratchet-base "$base_one" "$cand_raised"
run_refusal "ratchet-base refused 1 new baseline row" --ratchet-base "$base_one" "$cand_added"

bad_baseline="$out_dir/ratchet-malformed-$stamp.tsv"
printf 'malformed-two-columns\tAXC011\n' > "$bad_baseline"
run_refusal "malformed baseline row" --ratchet "$bad_baseline" "$clean_report"

empty_rule_baseline="$out_dir/ratchet-empty-rule-$stamp.tsv"
printf 'NativeTypedTree/SyntheticRatchet.fs\t\t1\n' > "$empty_rule_baseline"
run_refusal "unrecognized or empty rule code" --ratchet "$empty_rule_baseline" "$clean_report"

unknown_rule_baseline="$out_dir/ratchet-unknown-rule-$stamp.tsv"
printf 'NativeTypedTree/SyntheticRatchet.fs\tBOGUS999\t1\n' > "$unknown_rule_baseline"
run_refusal "unrecognized or empty rule code" --ratchet "$unknown_rule_baseline" "$clean_report"

dup_baseline="$out_dir/ratchet-dup-$stamp.tsv"
printf 'NativeTypedTree/SyntheticRatchet.fs\tAXC011\t1\nNativeTypedTree/SyntheticRatchet.fs\tAXC011\t2\n' > "$dup_baseline"
run_refusal "duplicate baseline key" --ratchet "$dup_baseline" "$clean_report"

# Verification must not rewrite the checked-in baseline.
baseline="$tool_dir/baseline/ratchet.tsv"
before=$(sha256sum "$baseline" | awk '{print $1}')
"$dotnet" fsi "$tool_dir/VerifyReceipt.fsx" --ratchet "$baseline" "$report" > /dev/null 2>&1 || true
after=$(sha256sum "$baseline" | awk '{print $1}')
if [[ "$before" == "$after" ]]; then
  printf 'CONTROL PASS: verification did not rewrite the ratchet baseline (sha256 %s).\n' "$before"
  pass=$((pass + 1))
else
  printf 'CONTROL FAIL: verification rewrote the ratchet baseline (%s -> %s).\n' "$before" "$after"
  fail=$((fail + 1))
fi

printf 'Controls: %d pass, %d fail.\n' "$pass" "$fail"
[[ $fail -eq 0 ]]
