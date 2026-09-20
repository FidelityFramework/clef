# Functional surface inventory

These probes supply source evidence for Composer's
[language completion review](../../../Composer/docs/Clef_Language_Completion_Review_2026-09-19.md)
under its existing implementation roadmap.
They check small positive source forms and forbidden forms through CCS. Missing
operations are explicit completion gaps, not expected-success tests silently
skipped by the runner. Exit 1 means at least one expectation remains unmet.

From the sibling Composer checkout, build the current compiler:

```sh
dotnet build src/Composer.fsproj -c Debug
```

Then from clef:

```sh
dotnet fsi tests/LanguageSurface/Probe.fsx
```

The script reports the loaded CCS assembly path and hash. It uses `parseAndCheck` without
a platform and does not establish native behavior, complete CE translation, or
proof discharge. Rejection requires a located effective error; parse failures,
crashes and accepted graphs containing error nodes never count as successful
negative tests. Positive acceptance does not assert the inferred result type,
complete graph structure or presence/discharge of obligations. Dimension, null,
object-type and boxing rejections require their recorded located diagnostic
codes. Non-builder CE rejection requires a located effective error; the intended
admission diagnostic is still to be specified with that correction. All
rejection diagnostics are printed so the reason remains reviewable. The
ordinary function in the CE rejection probes deliberately
has no admitted builder protocol.

The Option/Result/List operation names are completion requirements for this
inventory. They do not claim that the entire F# library is implicitly available.
Negative/fractional syntax remains subject to the separate admission exercise;
the inventory does not manufacture an executable syntax for that draft.

Native function/capture behavior is exercised by Composer's
`tests/NativeCallbacks/NativeCallbacks.Tests.fsproj`; dimensional source and
solver correspondence by `tests/CCS.Editor.Tests/CCS.Editor.Tests.fsproj`.
Use those gates alongside this inventory. The recorded baseline is evidence
for its assembly hash, not an assertion that a later checkout has the same gaps.
Composer's `ClefCompilerServiceProject` property can select another CCS project;
record the resolved project and build inputs alongside any new baseline. The
assembly hash alone does not establish a correspondence to current source.
For this baseline, `dotnet msbuild src/Composer.fsproj
-getProperty:ClefCompilerServiceProject` resolved to the sibling
`clef/src/Compiler/Clef.Compiler.Service.fsproj`. The Composer build passed before
these probes; the [review](../../../Composer/docs/Clef_Language_Completion_Review_2026-09-19.md)
records the repository heads and working-tree qualification.
