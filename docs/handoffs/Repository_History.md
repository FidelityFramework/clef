# Clef repository history and scope

Migration date: 2026-09-20. The repository's default and maintained branch is
`main`. This is repository maintenance, not a change to Clef language semantics.

## History boundary

The new root is the retained-content snapshot of the first CCS rename/migration,
original commit `3e39442be` dated 2026-02-18. Subsequent Clef commits retain their
authorship, dates and ordering, including merge structure. Commits whose only
changes concerned removed files are retained as historical waypoints.

History is restricted to the maintained files after the cleanup. Files already
deleted from the current repository are not carried back into the new root or
intermediate snapshots. Therefore older snapshots document the development
sequence but are not promised to build independently after filtering.

The generated `commit-map.tsv` beside this document maps full old commit IDs to
new IDs. Use it when resolving older Composer/library waypoint references;
those recorded test results still describe their original artifacts. Rewriting
a commit ID is not a new execution or proof result. Pre-root ancestry belongs
only to the external recovery archive, not to clone-visible refs.

## Retained and removed material

The maintained tree keeps the Clef compiler, Baker nanopasses, native type
universe, graph infrastructure, current tests, inherited lexer/parser and
parser-generation tools. F#/.NET dependencies needed to run the bootstrap
compiler remain. They do not define Clef's source semantics or target runtime.
MIT licensing and upstream attribution remain intact.

Removed material includes the unused inherited language server and protocol
proxy, F# Interactive settings and text resources, unused .NET assembly resolver
and compiler-location code, upstream localization inputs and coordinator,
unused assembly/package auditing projects, signing/manifest assets, and the
checked-in NuGet package. The ignore list now describes current generated output.

The remote ref inventory contained 210 branches and 143 tags. The four
Clef-specific side branches, including the dimensions work, were ancestors of
`main`; the other remote branch tips were inherited upstream work. Retire all
209 non-main remote branches and all inherited tags in the same publication as
the rewritten `main`. Do not leave a backup branch or tag retaining the old
history in this repository. The external recovery bundle retains the original
refs without enlarging new clones.

## Validation and recovery

The cleaned source passed all 1,006 CCS tests, a Composer build and the native
formatter/UTF-8 snapshot gate (stock MLIR verification, native exit zero, empty
stderr and all 22 expected lines). These checks validate the cleaned current
tree, not every filtered historical snapshot.

An external recovery archive at
`/home/hhh/repo-archives/clef-thinning-2026-09-20/` holds the verified original
Git bundle, ref/deletion inventories and migration evidence. It is not part of
the repository or required to build it. Old server objects may remain until
Forgejo performs garbage collection; absence of clone-visible old refs and a
fresh clone's contents/size are separate checks from server disk reclamation.

After publication, existing clones should be replaced with fresh clones after
preserving any local work. A normal merge/pull of the old and new histories can
restore the retired ancestry. Reapply needed unpublished work against the new
history and use the commit map to reconcile old references.
