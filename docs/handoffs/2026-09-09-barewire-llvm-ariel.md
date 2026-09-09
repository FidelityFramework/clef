# Ariel and native mapped storage: reconciled compiler integration

The compiler changes used by the live HelloWayland CPU window are integrated
with current `main`, including the dimensional and scope work from `fidelity`.
This record supersedes the temporary-checkout instructions previously at this
path. Main's PHG architecture, predicate propagation and backward range
refinement are retained.

The integration carries native ABI declarations, flat callback code/environment
pairs, scoped `BorrowedView<Schema>` values, actual representation and stride
facts, and graph-generated mapped-span obligations through CCS and Baker.
Composer consumes those facts when lowering native calls and mapped storage.
Ariel is the scheduling layer: participant accesses retire before a mapped
callback returns and its native owner releases the view.

## Normal checkout and validation

Build the compiler and its regression suite from the regular sibling checkout:

```sh
cd /home/hhh/repos/clef
dotnet test tests/Clef.Compiler.Service.Tests/Clef.Compiler.Service.Tests.fsproj
```

The reconciled checkout passes all **169 tests**. BAREWire and Fidelity.Data are
resolved through their normal sibling repository paths. Fidelity.Data's hosted
library and tests use `.fs` source filenames; its source bodies are unchanged
by that prerequisite repair.

Composer's normal project reference is `../clef/src/Compiler/Clef.Compiler.Service.fsproj`.
A local override selecting the retired temporary compiler checkout is unnecessary.
The [cross-repository integration record](../../../Composer/docs/Ariel_Integration_Changes.md)
records the dependent build, native window acceptance, commit identities and
worktree cleanup. Native observations and their scope are documented in
[Composer's Ariel design](../../../Composer/docs/multi-core-cpu.md).

## Proof scope

The shared mapped-span model establishes element containment, alignment and
nonwrapping address addition under the emitter's checked extent conditions.
It does not establish the native allocator contract, variable-stride
multiplication, worker disjointness or scheduler retirement by itself. Native
mapping gates, scope validation and Ariel lifecycle checks provide separate
coverage. The generated scoped callback metadata states a trusted library
retirement contract; it is not a general verified borrow checker.

## Recovery history

Before reconciliation, both the original index tree and the complete nonignored
working tree were preserved under the local Git ref
`refs/archive/ariel-scope-integration-20260909`. The working snapshot is
`b6893e6f484b9eb89d67d862f469b98e7d25dd83`; its parents preserve the staged
snapshot and original history. Raw index and merge metadata are held under
`.git/reconciliation-backups/ariel-scope-20260909` in the main repository.
This is recovery history, not an active build checkout or dependency.
