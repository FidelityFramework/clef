# Clef predicates at platform boundaries

The implemented path is the static MMIO fragment of the
[platform-predicates specification](../../../clef-lang-spec/spec/platform-predicates.md).
Its [Contracts vocabulary and acceptance limits](../../../Fidelity.Platform/docs/MMIO_CONTRACTS.md)
are shared by the RA6M5 and the restricted 64-bit guest design probe.

`ClefPredicate` holds a name, a typed `Expr<bool>` condition and provenance.
[Predicates.fs](../../src/Compiler/PSGSaturation/SemanticGraph/Predicates.fs)
evaluates closed integer/Boolean relations over immutable declaration data,
retaining expression and dependency identities. Mutable/runtime facts, unsupported
expressions and missing information remain pending.

[DeviceAccess.fs](../../src/Compiler/PSGSaturation/SemanticGraph/DeviceAccess.fs)
requires these conditions at a used MMIO binding, alongside mandatory region,
mapping, width, permission and value-range checks. The settled access evidence
is graph codata. Composer consumes it without reevaluating the quotation.

This file supersedes the earlier F★-inspired capability-matrix proposal. The
useful connection is preservation of propositions, premises and validity scope
through Clef's existing deferred-inference model. The legacy
`PlatformContext.Predicates` Boolean map is not the implemented consumer.
Automatic vector/capability dispatch, runtime mapping guards and general symbolic
predicate proofs remain separate work.

Compiler evidence establishes a relation between declarations. Hardware/boot
assertions are recorded separately as external premises; no physical capability
or solver certificate follows merely from a quoted Boolean.
