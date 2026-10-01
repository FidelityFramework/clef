# CCS project workspace — 2026-10-01

CCS now owns a cold, shared **whole-project checking** coordinator through
`Fidelity.FSharp.Incremental.Hosting` **0.1.0-preview.5**. This is a compiler-host
integration boundary. It does not implement partial Baker rechecking, cross-edit
proof caching, or Clef's native `Incremental<'T>` lowering.

## Source and authority

- [ProjectWorkspace.fs](../src/Compiler/Project/ProjectWorkspace.fs) owns revisions,
  consumer demands, typed projected results, withdrawal and close.
- [ProjectChecker.fs](../src/Compiler/Project/ProjectChecker.fs) owns input capture,
  complete checking and the producer publication helper.
- [CheckExecution.fs](../src/Compiler/CheckExecution.fs) owns the process gate and
  restores phase configuration after checking and projection, including failure.
- [AGENTS.md](../AGENTS.md) remains authoritative: CCS/Baker settles semantics and
  complete proof premises; Publication copies settled rows into `Fidelity.PSG`;
  Alex consumes published authority. No recipe or inference moved into this host.

The package is pinned in [Clef.Compiler.Service.fsproj](../src/Compiler/Clef.Compiler.Service.fsproj)
and supplied by the [vendored feed](../vendor/Fidelity.FSharp.Incremental/README.md).
Preview.5 adds atomic state/watch observation used here to avoid missed wakeups.
Its graph transition rules are not a new compiler proof-validity rule.

The language alignment source is `spec/incremental-computation.md`, revision
`746ef16232164a5ad2620a535b9fb521705f4226`, especially
[§6.1 stabilization and §6.3 demand](https://forge.spkez.dev/FidelityFramework/clef-lang-spec/src/commit/746ef16232164a5ad2620a535b9fb521705f4226/spec/incremental-computation.md#L271-L370).
§6.1 permits reuse only after all relevant inputs are validated and preserves
independent invalidations. §6.3 gates work by observation demand. The present
host shares one immutable generation and fully rechecks each reserved generation;
it does not infer a smaller dependency census from matching query text or graph
fingerprints. The spec's §14.2 explicitly distinguishes graph traversal machinery
from evidence that incremental compiler rechecking has been implemented.

LAN retrieval provenance: snapshot
`30f3a9fe9c28e1757e757bf2b748d6d125869309093c1c5355087e7f53a547f7`,
generation 3; source chunk
`d45f4f5819b8820363eb0dcf7f954f89671adf7d67defe4db6592ab9da5e0e77`,
lines 271–370, untruncated. The source revision matches the local spec checkout.
Requests and responses are retained under
`/home/hhh/.codex/work/incremental-adoption-2026-10-01/lan/`.

## Capture and ownership

The loader and source resolver share one read-through capture of project,
dependency and binding metadata. Source bytes, ordering, platform membership,
options, linked libraries and selected platform target are fixed before parsing.
Disk reads are revalidated at the end of capture; an observed change or read error
refuses capture. Checking then reads the captured strings, not the live files.
This is not an atomic filesystem transaction; clients must reserve before edits.

`ProjectCheckResult.InputFiles` records the actual metadata and source text;
`SourceFiles` preserves checking order. `PlatformTarget` comes from the same
captured binding options, so downstream compatibility checks need not reread the
binding. Volatile source overrides are normalized and captured explicitly.
Malformed paths and conflicting overrides for one generation are typed refusals.
Conflicting normalized path aliases and different source/metadata views of the
same path are refused, so the input receipt cannot conceal a consumed text.
Parse failure produces diagnostics and an empty graph, never a silently shortened
project that could be published as complete.

`CheckExecution` serializes the NativeService entry points that reset global node
and solver counters, and the parser entry point. A workspace holds that ownership
through checking and its projector. Editor projectors must freeze their views
there. `ProjectChecker.publish` checks diagnostics and delegates to the existing
CCS Publication boundary; consumers need not invoke Publication directly.

## Lifecycle contract

| Operation | Contract |
| --- | --- |
| Construct workspace | No input capture, coordinator start or evaluation. |
| `BeginReserve` | Retain an operation immediately; hides old local availability and admits scope invalidation. |
| Reservation `ObserveAsync` | Repeatedly observe that exact acknowledgement. A successful receipt must precede edits. |
| `BeginDemand` | Admit a retained consumer of an immutable revision/override request. Equal overrides in the same generation share owned capture and the complete check. No file I/O runs under the control lock. |
| Demand `ObserveAsync` | Cold, repeatable observation. Cancelling an observer leaves its retained consumer demand owned. |
| Demand `ReleaseAsync` | Withdraw that consumer; repeated calls observe the same admitted release. Other consumers preserve their demand. |
| `BeginClose` / `CloseAsync` | Seal admission immediately / observe physical completion of all owned compiler work. |

Every reserved generation receives a fresh work identity. An old consumer cannot
drive a new generation. Results are offered only with current host eligibility
and a matching typed owner result token. No result crosses a reservation through
automatic hash equality, cached query equality or structural similarity.

The checker is synchronous and noninterruptible. Cancellation requests revoke
eligibility; they do not establish completion. Owned evaluation runs without an
ambient attempt token and returns only after checking, projection and restoration.
The evaluator owns input capture as well as checking; close joins paused capture
I/O without blocking admission of reservation or close itself. Capture failures
are observed through the retained demand. The first successful immutable capture
is retained even if its original attempt was withdrawn, so a later demand for
that same generation cannot silently reread different bytes. Close joins that work even when a
former observer has cancelled or a projector fails. `DrainDiagnostics` retains
failures from withdrawn attempts; successful close does not erase them. Release
acknowledgement alone is not a physical-drain receipt.

There are 256 command slots; admission reserves one withdrawal slot for every
live demand. `Busy` refuses additional admission without losing release capacity.
Protocol identities are never recycled: after 4,096 reservations or 65,536 demands,
`LifetimeLimitReached` requires closing and creating a new workspace. Consumers
must also bound their own retained handles and views.

## Validation status

Evidence directory: `/home/hhh/.codex/work/incremental-adoption-2026-10-01/validation/`.

- Initial build reported six diagnostics from two implementation mistakes: a
  missing record type annotation and an invalid one-line async branch. Both were
  corrected; the original `clef-workspace.log` remains evidence of that failure.
- The corrected focused gate passed **15/15**, zero skipped, in
  `clef-workspace-r2.log` / `clef-workspace.trx`: eight workspace lifecycle cases
  and seven existing project/link cases.
- Three subsequent cases cover malformed volatile paths, two actual workspaces
  contending for the process gate, and captured platform target metadata. The
  unfiltered `clef-full-r2.log` gate built and executed **2,220** cases:
  **2,121 passed, 99 failed**; all eleven new workspace cases passed. Failure
  identity comparison in `clef-exact-comparison.json` accounts for all 2,209
  previous test IDs plus the eleven additions: no missing tests, new failures or
  recovered failures. The same 99 compiler cases failed in that baseline; these
  are compiler diagnostics, not failures of the separately audited library.
- Follow-up review found capture blocking the control lock, hidden diagnostics
  for failed withdrawn attempts, and ambiguous normalized input views. Capture
  now runs inside the owned evaluator, failures remain host diagnostics, and
  ambiguous views fail closed. A same-generation demand after withdrawal also
  retains the first successful immutable capture. The final focused gate passed
  **22/22**: all fifteen workspace cases and seven existing project/link cases
  (`clef-workspace-final.log` / `clef-workspace-final.trx`). The final unfiltered
  gate executed **2,224** cases: **2,125 passed, 99 failed, zero skipped**
  (`clef-full-final.log` / `clef-full-final.trx`). Exact comparison by test ID and
  name retains all 2,209 baseline cases plus fifteen passing additions, with
  **zero missing tests, new failures or recoveries**
  (`clef-exact-comparison-final.json`). The 99 failures are the ongoing compiler
  backlog; this integration neither fixes them nor establishes a new library
  release restriction.
- The package's preview.5 watch gate passed **102/102** in
  `incremental-watch.log`. The independent preview.5
  [consumer observation audit](https://forge.spkez.dev/FidelityFramework/Fidelity.FSharp.Incremental/src/commit/deabc97/docs/Consumer_Observation_Auditor_Assessment_2026-10-01.md)
  separately passed **102/102** plus three observation controls and accepted the
  package for integration. Consumer results remain separately identified.

Focused lifecycle checks do not establish full compiler or F/C acceptance.
Preserve any unfiltered failures with their diagnostics and ownership; do not
weaken proof premises or substitute passing subsets for that gate.
