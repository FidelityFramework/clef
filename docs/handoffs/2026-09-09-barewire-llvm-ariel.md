# Handoff: BAREWire layout, direct LLVM/LLD, and Ariel

Recorded 2026-09-09. This is a continuation record, not a claim that all workspace
changes were authored in this chat. Implementation changes remain local and
uncommitted; nothing was pushed or published. Preserve existing changes.

## Start here in the next chat

Read this file, then `/home/hhh/repos/Composer/docs/multi-core-cpu.md` and
`/home/hhh/repos/BAREWire/docs/13 Dispatch Regions.md`. Inspect current status
before editing. Do not repeat the completed LLVM backend replacement or confuse
implemented static-storage proofs with the proposed dynamic dispatch contract.

**Current status: native pthread carrier support is implemented and tested.**
The user subsequently authorized implementation after the initial assessment
and handoff request. That implementation is now complete for the bounded CPU
rendering milestone:

- Ariel's scheduling layer has persistent pthread carriers, synchronous dispatch,
  participant retirement, startup cleanup and shutdown. Its native lifecycle
  tests pass with one/two/four carriers and 100 generations each.
- `HelloWayland.CpuCarriers.fidproj` runs the actual glyph calculation through
  those carriers. Native serial/parallel equivalence passes and the executable
  produces the rendered image.
- The original `HelloWayland.fidproj` window application still uses its serial
  adapter. Connecting the tested renderer to the Wayland/GBM mapped buffer and
  handling sustained-frame storage are the remaining integration work.

This implements the first bounded Ariel scheduling feature. Full actor/mailbox
integration, scheduler conformance and automatic Baker dispatch insertion remain
future work. The historical sections at the end record earlier checkpoints;
they do not describe the current implementation status.

## Repository map and Git state

| Location under `/home/hhh/repos` | Observed branch / HEAD | Purpose |
| --- | --- | --- |
| `Composer` | `main` / `ad1506f` | Actual Composer backend and middle-end changes |
| `BAREWire` | `main` / `14e46f6` | Concrete static-storage planner; new dispatch design |
| `clef.worktrees/clef-scope-integration` | detached / `09970a258` | Compiler service actually referenced by Composer |
| `clef.worktrees/clef-language-dimensions-plan-review` | `fidelity` / `09970a258` | Current workspace and this handoff; separate existing scope/type changes |
| `Fidelity.Platform` | `cleanup/dead-code` / `6baa850` | Target description and generated native bindings |
| `lattice-vscode` | `fidelity` / `a0eb5fb` | Local editor extension; `client/` is currently untracked |
| `HelloWayland` | `pre-light-mode` / `9a29d3b` | CPU/GPU application and multi-core design |

`Composer/Directory.Build.local.props` explicitly points to:
`/home/hhh/repos/clef.worktrees/clef-scope-integration/src/Compiler/Clef.Compiler.Service.fsproj`.
Do not assume that editing the current dimensions-plan-review checkout changes
the compiler used by Composer or Lattice.

The scope-integration worktree has a very large existing staged restructuring
(including thousands of deletions) plus unstaged/untracked additions. Do not
reset it or bulk-commit its index as if it were only this task. Other repositories
also contain earlier work. No Git staging or commits were done for this handoff.

## Completed: concrete static string storage integration

The earlier missing link from BAREWire layout through compiler obligations to
emitted storage was repaired for the static string pool:

- `BAREWire/src/Platform/StaticStorage.fs`: checked allocation planner consuming
  the declared memory space and storage requests. Tests are in
  `BAREWire/tests/StaticStorageTests.fs`; package/project source lists were wired.
- Compiler `src/Compiler/PSGSaturation/SemanticGraph/StaticStringLayout.fs` in the
  **scope-integration** worktree calls that planner. The graph carries the actual
  pool bytes and settled entries; layout obligations consume that plan.
- Composer literal emission uses the settled pool. Its
  `src/MiddleEnd/Alex/Traversal/StaticStorageValidation.fs` checks correspondence
  against structured emitted MLIR. Associated changes are in literal patterns,
  literal witnesses, dialect types/serialization, SMT transfer, MLIR generation,
  and project source ordering.
- `Composer/tests/StaticStorageRegression.fsx` and
  `Composer/tests/StaticStorageNativeRegression.py` exercise rejected mutations
  and the resulting ELF. `tests/SMTTransferRegression.fsx` covers solver transfer.

Scope: concrete static string placement and preservation, not whole-program
heap/stack/lifetime safety or already-implemented multi-worker memory safety.
The previously displayed assumed string adjacency theorem was insufficient;
do not describe it as a substitute for the concrete integration.

Earlier recorded validation: BAREWire 508 passing tests, compiler 114 passing
tests, Composer 50 solver cases and 10 storage mutation cases, plus a real
Lattice extension-host check. These are session results, not freshly rerun by
the handoff task. Native validation was repeated after the final LLVM/LLD relink.

## Completed: remove Clang from Composer's LLVM/ELF backend

The native pipeline is now:

```text
MLIR -> LLVM IR (.ll)
     -> opt -mtriple=... -passes=no-op-module -> target bitcode (.bc)
     -> ld.lld (LLVM LTO/code generation internally) -> ELF
```

Composer's generated textual IR lacked a target DataLayout. The target-aware
`opt` step supplies it; LLD cannot simply consume that original module without
target preparation. Explicit conflicting IR target triples are rejected.
This removes Clang and standalone llc from this CPU path; LLVM machine-code
generation remains inside LLD. The AIE backend still has its own Peano tools.

Key files in Composer:

- `src/BackEnd/LLVM/Codegen.fs`: target preparation, explicit runtime inputs,
  direct LLD invocation, process argument handling and failure reporting.
- `src/BackEnd/LLVM/Pipeline.fs`: pipeline wiring.
- `src/Core/Types/Pipeline.fs`: `NativeLinkOptions` and backend context.
- `src/Core/CompilationOrchestrator.fs`, `src/CLI/Program.fs`: option propagation.
- `src/CLI/Diagnostics/ToolChainVerification.fs`, `EnvironmentInfo.fs`,
  `src/CLI/Commands/DoctorCommand.fs`: doctor checks LLVM/LLD rather than C compilers.
- `docs/LLVM_Backend.md`: implementation, scope, CLI inputs, and validation.
- `tests/LLDBackendRegression.fsx`: native execution/linking and refusal tests.

CLI link inputs: `--sysroot`, repeatable `--link-library-path`,
`--link-start-file`, `--link-end-file`, plus `--dynamic-linker` and
`--linker-script`. These are not a newly implemented fidproj schema or automatic
Fidelity.Platform runtime-input projection.

Hosted Linux console mode resolves installed startup objects, loader and libc;
cross-hosted linking needs a sysroot or explicit inputs. Freestanding/embedded
mode adds no implicit CRT/libc. Shared-library mode is supported. The current
direct image profile covers ELF; PE/MachO/Wasm need separate profiles and are
explicitly rejected. Native Linux uses the native CPU LTO option; cross builds
use their target rather than inheriting the host CPU.

Composer was rebuilt locally. No global CLI install was performed. Run commands
from Composer so its .NET 10 SDK is selected, using the local assembly where
needed: `dotnet src/bin/Debug/net10.0/Composer.dll`.

### Validation and existing evidence

- Build passed with only the existing Fidelity.Data SourceLink warning.
- `dotnet fsi tests/LLDBackendRegression.fsx` passed hosted, shared and
  freestanding execution; a scripted ARM cross-link; and six refusal cases.
  The test prepends failing Clang/GCC/llc traps and verifies none were invoked.
- `composer doctor --verbose` passed LLVM/LLD checks. Its saved log predates a
  final help-text cleanup; stale F# usage text in that log was subsequently fixed.
- The real HelloDimensionsProof sample compiled and ran via LLD. Its final
  backend was relinked after the last codegen change, then storage validation
  passed: 4096-byte pool, 4096-byte alignment, exact bytes, read-only ELF section
  and load segment, all 43 source/native obligations UNSAT, and output
  `Enter your name: Hello, Ada!`.
- Final search found no `clang` in Composer `src/BackEnd` or `src/CLI`.
  Historical documentation/C binding references elsewhere were not erased.

Reproduction commands from Composer:

```sh
dotnet fsi tests/LLDBackendRegression.fsx
dotnet src/bin/Debug/net10.0/Composer.dll compile /tmp/composer-static-pool-6btqz6ob/HelloDimensionsProof.fidproj -k --no-color
python3 tests/StaticStorageNativeRegression.py /tmp/composer-static-pool-6btqz6ob/targets
```

Temporary evidence (may disappear; test source is the durable reproduction):

- `/tmp/composer-lld-build.log`
- `/tmp/composer-lld-tests.log`
- `/tmp/composer-lld-sample.log`
- `/tmp/composer-lld-doctor.log`
- `/tmp/composer-static-pool-6btqz6ob/targets/`
- `/tmp/lattice-ccs-host-tInjKq/result.json`
- `/tmp/lattice-ccs-host-tInjKq/entry-layout-proof.json`

## Completed: typed pthread implementation and native validation

The user explicitly requested running local Farscape over the needed libraries
and carrying the CPU path through native execution. Ariel is the **scheduling
layer**; refer to this implementation as its **pthread carrier support**, not as
an Ariel runtime. This terminology is an architectural requirement from the user.

Farscape now generates the production pthread surface from installed headers:
opaque `CHandle` objects, `FnPtr` callbacks, bounded scalar output arrays, measured
mutex/condition/affinity storage, allocator specializations and ownership metadata.
The generator's focused suite has 578 passing tests. `CallerOwns`/`CalleeOwns`
describe boundary intent; they do not by themselves implement lifetime checking.

The active compiler is the `clef-scope-integration` worktree selected by Composer's
local build props. Its typed handle/reference declaration changes and Composer's
foreign-call lowering have passed fresh LLVM/LLD executable checks for allocation,
callback entry, `pthread_create`/`pthread_join`, release, and rejection of an empty
output array before the foreign call. Native affinity discovery also passed with
inherited, three-CPU and single-CPU masks. The probes and a fresh-build runner are
tracked in `Fidelity.Platform/tests/Ariel/native/`.

The persistent carrier source is `Fidelity.Platform/CPU/Linux/x86_64/Ariel/Region.clef`.
It uses typed values throughout. Native lifecycle and HelloWayland's
serial/parallel equivalence gates pass. The accepted renderer lives in
`HelloWayland/src/Cpu/Typed/`, with tests in `HelloWayland/tests/ariel-typed/`.
Its pixel function is checked byte-for-byte against the shared source. Its serial
executable and BAREWire scalar-bounds executable also pass. The original Wayland
presentation loop has not yet been connected to this renderer.

Completed compiler work restores captured array extent/type, fixed-size capture
views and parent SSA scope, and covers first-class functions with no captures.
The existing closure environment allocator has no general reclamation for repeated
escaping closure creation; a synchronous carrier drain is not a reclamation proof.
Do not report bounded per-frame allocation or full display integration on the
strength of these boundary probes alone.

### Compiler fixes exercised by the typed carrier path

- Farscape declarations determine foreign argument/result widths and checked
  scalar-array output projection. Native callbacks use `FnPtr` plus opaque
  `CHandle` context.
- Closure placement and witnessing retain array extents, bounded record views,
  mutable cells and function pairs. Anonymous functions and compiler-generated
  pair wrappers have unique code symbols; function aliases retain snapshots.
- Range analysis reads the complete curried parameter chain before Curry
  normalization. A regression carries bounds 224 and 257 through a mutable
  callback slot and nested callback; unknown inputs retain Register width.
- Array indices use signed or unsigned extension according to the established
  range. `Array.zeroCreate` initializes scalar storage, including bool and float.
- Representation meets cover immutable bindings as well as mutable bindings,
  preserving the conversion from a uniform callback result to its selected slot.

Composer build 20 passes. All 136 compiler service tests, seven index-sign cases,
four native callback programs, and the native array test with poisoned allocator
storage pass. The callback and array runners are `Composer/tests/NativeCallbacks/run.py`
and `Composer/tests/MemoryArrays/run.py`; they compile fresh LLVM/LLD executables.

### Native acceptance checkpoint

All six final-build native gates pass: allocation, create/join, rejection of an
empty foreign output, partial-startup rollback, affinity discovery and lifecycle.
The lifecycle gate exercises one/two/four carriers for 100 generations each,
exact assignment/tails, nested admission rejection, callback failure/reuse,
zero-work and failed-work retirement, and shutdown/restart behavior. Artifacts:
`/tmp/ariel-native-xxjn13nl`; reproducible source and limits are recorded in
`Fidelity.Platform/tests/Ariel/native/STATUS.md`.

HelloWayland's final-build native serial/parallel equivalence gate passes with
actual `Trace.pixel` computation and a noncaller pthread completion witness.
The accepted typed renderer is now in `HelloWayland/src/Cpu/Typed/`, selected by
`HelloWayland.CpuCarriers.fidproj`. Its root entry renders a CPU image through
Ariel's pthread carriers. The original window/GPU manifests remain separate;
mapped display projection and host callback-state migration are still required
to put this adapter into the production Wayland presentation loop.

The standalone CPU image executable also passes: `HelloWayland/targets/CPU-CarrierDemo`
produces a validated 192 × 224 PPM with the actual orange shaded glyph. The
review image is `HelloWayland/targets/cpu-carrier-demo.png`. These generated
artifacts are ignored; source, manifests and test drivers are retained.

From `/home/hhh/repos/HelloWayland`:

```sh
../Composer/src/bin/Debug/net10.0/Composer compile HelloWayland.CpuCarriers.fidproj
./targets/CPU-CarrierDemo > targets/cpu-carrier-demo.ppm
```

The latest fresh typed renderer driver passes all three gates (bounds, serial,
equivalence) after promotion to `src/Cpu/Typed`. The completed carrier evidence
is in `Fidelity.Platform/tests/Ariel/native/STATUS.md`; renderer evidence and
source correspondence are in `HelloWayland/tests/ariel-typed/README.md`.

This is actual compiled Clef execution through LLVM/LLD and generated foreign
bindings. It does not claim full scheduler conformance, automatic Baker region
insertion, complete graph-derived lifetime proofs, or reclamation of arbitrary
escaping closure environments.

## User preferences and scope discipline

- Be concise and judicious with tokens. Complete concrete authorized work.
- Do not build the website merely for Markdown edits.
- Clef has its own identity; .NET is the current host, not a reason to revert to
  F# semantics or outsource compiler facts to optional analyzers.
- BAREWire is the layout mechanism; proof/type metadata need not tag final bytes.
- Keep proof display controls as currently agreed. The sidebar remains populated;
  inline proof links toggle independently, with expand/collapse controls.
- Source/numeric conversion experiments previously deferred remain deferred.
- The user explicitly authorized the native pthread implementation after the
  initial handoff request. Implementation and native validation are complete for
  the bounded CPU rendering milestone. No commits, pushes or global installs
  were performed.

## Historical assessment: before native implementation

This section records the initial assessment. Its binding and callback defects
were subsequently repaired in the typed implementation described above. Retain
the architectural findings; use the current acceptance results for status.

Read these local documents before proposing work:

1. `Composer/docs/multi-core-cpu.md` — current bounded implementation plan.
2. `BAREWire/docs/13 Dispatch Regions.md` — current common memory-contract design.
3. `HelloWayland/docs/multi-core-cpu.md` — application plan; modified since the
   initial assessment, so reread its current text.
4. `HelloWayland/docs/shadow-and-substrate.md` — the same shader saw different
   input bytes because shadow lists were outside the GPU upload's used extent.
5. `clef-lang-site/hugo/content/blog/surfacing-the-scheduler.md` and
   `hugo/content/docs/design/concurrency/ariel-under-prospero.md`.
6. `clef-lang-spec/spec/scheduler-contract.md`.

The Composer and BAREWire dispatch documents were discovered during handoff
capture; they were not created by this handoff task. They are currently
untracked and must be included when their owning changes are eventually committed.

**Use their narrower first milestone.** An earlier assessment suggested a full
simulated Ariel core first. The current written plan instead calls for one
synchronous bounded region at a time, a small participant-lifecycle harness,
persistent hosted CPU workers, and an explicit internal call from the CPU Fill
adapter. Full actor/mailbox integration, supervision trees, full scheduler
conformance, automatic Baker insertion, asynchronous UI suspension and GPU
federation are later work. Do not reintroduce those as prerequisites for the
first multi-core logo animation.

Concrete findings to preserve:

- `HelloWayland/src/Common/Trace.clef` computes pixels from a shared table with
  local arithmetic state. `src/Cpu/Fill.clef` writes one pixel per index.
  `src/Common/Host.clef` fills the table before dispatch and unmaps after
  `Fill.frame` returns. Preserve the common renderer and shadow quality.
- Read-only worker code alone does not establish input immutability through
  aliases. Carry complete input footprints, allocation identity, exclusive output
  slices, target environment layout and lifetime/publication/retirement facts.
- Work completion is distinct from participant release: the original pool
  sketch could decrement the last work counter, then access bookkeeping after
  the caller returned. Region retirement must wait for all such accesses.
- Buffer reuse must also respect the compositor's release. Neither worker join
  nor a frame callback alone proves the compositor has released its buffer.
- Generated pthread externs exist, but the bridge has unbound `__newthread` /
  `__attr`, an absent module reference and a hardcoded null environment. The base
  platform manifest does not include them. Convenience wrappers also use errno
  for pthread APIs that report errors directly. Repair generation/bindings and
  validate callback ABI, dependency closure, target mutex/condvar storage and
  error handling. Preserve compiler-owned callback reachability.
- Existing Composer closures use code/environment pointers; that does not alone
  prove foreign thread-entry ABI or capture lifetime. No Ariel dispatch recipe
  or CPU concurrency atomic emission was found in the assessment.
- BAREWire's current spatial validators and static planner are foundations.
  Dynamic native allocation identity, dispatch lifetimes and synchronization
  guarantees are proposed connections, not already proven by those APIs.
- Affinity/deployment budget determines usable workers; online processor count
  alone is insufficient. Row partitioning alone does not prove cache-line
  separation. Single-carrier behavior must work.
- Keep the existing Wayland owner thread initially. Wayland can support multiple
  queues/threads; the single-owner choice is this application's boundary.
- Test exact frame bytes at fixed inputs, zero/tail partitions, delayed workers,
  partial startup, rejected concurrent submission, resize and teardown. Measure
  table preparation, rendering, join and presentation separately. No frame-rate
  guarantee follows from the number of logical processors.

The intended proof path remains shared machinery: BAREWire/Platform facts ->
compiler-carried layout and boundary evidence -> Ariel scheduling realization ->
Composer preservation checks -> Lattice presentation. No per-demo fabricated
obligations, and no dependency/refinement annotations imposed on ordinary source.

## Historical checkpoint: foundations and the archived pointer attempt

The native admission failures below concern the earlier pointer-based attempt.
The later typed implementation passed its native gates; these failures are not
current blockers or evidence that implementation is still only a design.

Implemented locally on September 9; no commits or pushes. Existing dirty work
was preserved. New source work remains in the scope-integration compiler used
by Composer's `Directory.Build.local.props`.

Verified contributions:

- **BAREWire:** `src/Platform/DispatchRegions.fs` and registrations/tests. Shared
  allocation, input, partition, alias and capture-layout validation, plus
  overflow-safe scalar extent guards. 562 .NET checks, fresh Fable dispatch
  regressions and existing JS gates (including 22 cvc5 queries) pass. These are
  spatial checks, not native lifetime or whole-program safety proofs.
- **CCS/Composer:** `SemanticGraph/FunctionPointers.fs` settles named callback
  entries and fully applied invocations into `Codata.FunctionPointers`. Baker
  retains declaration references instead of eta-expanding them into closures;
  `Meets` carries call argument widths and `RangeAnalysis` recognizes the value
  call boundary. `FnPtr` annotations are registered. Alex has matching pattern
  and witness modules. Implicit closure erasure and partial native calls reject.
  Six compiler tests pass. `Composer/tests/NativeCallbacks` checks named callback
  selection, typed forwarding, signed arguments and results through fresh
  MLIR/LLVM/LLD/native execution; the initial two-argument probe also passed.
  A whole-function expression annotation (`let f : ... = fun ...`) exposed an
  existing native declaration/slot-classification gap. Such callback entries
  now reject explicitly with CCS8096 before emission; parameter annotations
  and typed `FnPtr` parameters/values pass. Do not mistake this limited admission
  for support for every function-value source form.
- **Diagnostics:** saturation recipe export now writes recipe summaries instead
  of traversing mutable inference cells/non-string measure keys. A regression
  covers the previously crashing JSON path. Composer prints exception detail
  with `-v` for actual compiler failures.
- **Farscape/Fidelity.Platform:** real-header anonymous-union/layout extraction,
  callback forwarding, direct pthread return codes, source indentation and
  identifier escaping repaired. FSharp.Core pin aligned with Fidelity.Data so
  a clean tracked build works without replacing output DLLs. 570 generator
  tests pass. Production pthread output follows typed `CHandle`/`FnPtr` and
  descriptor representations; its direct source list has no raw pointer
  spellings. The separate ctypes ABI probe passes storage sizes, environment
  roundtrip, direct error codes and current-process affinity.
- **Ariel lifecycle:** a bounded model explores 1,747 states. The native carrier implementation
  and renderer candidate are explicitly experimental and have not passed their
  native gates. Completion and participant release are separate. Partial
  startup cleanup and terminal failed shutdown were reviewed.

### Critical correction: do not restore the removed pointer surface

The first native pool attempt used the old `NativePtr`/`nativeint` surface from
the existing application and generated bindings. The current compiler rejected
it with 274 errors (last full build log `/tmp/ariel-native-debug3.log`). This is
intentional in `clef-lang-spec/spec/ffi-boundary.md` and the scope-integration
`docs/fidelity/phg/Dimensional_Range_Design.md` CS-11/CS-12 accounts. It is not a
reason to weaken the source rules or add an implicit compatibility fallback.

The required bridge is opaque handle marshalling, declared bounded-array out
parameters (not dereferencing `CHandle`), and compiler-owned typed callback
capture storage whose lifetime extends through carrier release. BAREWire's
native dependency source also needs its representation migration. The new
`FnPtr<int -> int -> int>` native gate proves callback plumbing only; it does
not prove that the POSIX pool or captured arrays compile or are safe.

The candidate is preserved at:

- `Fidelity.Platform/CPU/Linux/x86_64/Experimental/Ariel/STATUS.md`, with the
  carrier source, native harness and explicit unaccepted status.
- `Fidelity.Platform/CPU/Linux/x86_64/Experimental/Pthread`, the legacy ABI
  experiment, separate from production typed generation.
- `HelloWayland/tests/ariel-prototype`, the unchanged-pixel renderer candidate,
  equivalence harness and archived integration patch.

HelloWayland's production manifest, CPU Fill, Host and GPU compatibility source
were restored exactly to their original bytes; they were pristine before this
attempt. Its default CPU path remains serial. Existing dirty design documents
were retained and their current status updated.

The owner additionally clarified that broad Linux binding regeneration for
full-loop destruction is **not required for this initial step**. Only pthread
and narrowly necessary Libc source rendering repairs were made. Compositor
buffer release remains a documented later boundary: a frame callback is pacing,
not permission to reuse that buffer. No desktop teardown rewrite was made.

Platform predicates remain compile-time declarations; allowed process affinity
is a runtime resource input, bounded by deployment policy. Prototype capability
and address-ceiling declarations demonstrate that separation, but they are not
an integrated compiler capability-selection proof path.

Useful next references: Composer `docs/multi-core-cpu.md`, Farscape
`docs/Native_Carrier_Bindings.md`, and the experimental Ariel `STATUS.md`.
