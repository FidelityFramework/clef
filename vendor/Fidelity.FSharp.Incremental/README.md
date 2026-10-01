# Fidelity.FSharp.Incremental package input

These MIT packages are the explicit preview.5 dependency for the first compiler
and provider integration. They were packed from implementation commit
`87c77d91ab24c8e4d065e4e726f8c06abc3180c4` in
[Fidelity.FSharp.Incremental](https://forge.spkez.dev/FidelityFramework/Fidelity.FSharp.Incremental).
`SHA256SUMS` identifies the exact archives; their nuspecs identify the source.
The identical archives are retained in each consumer's local feed so restoring
one checkout does not silently choose another developer's mutable library build.
No FDA or IcedTasks dependency is added.

Validate with `sha256sum -c SHA256SUMS` in this directory. Refresh by packing a
reviewed, tested library commit into external scratch, then updating both package
pins, archives and checksums together. Never overwrite an already published
version with different bytes. Consumer validation must identify its actual
compiler, library and provider closure; package restoration alone is not proof,
artifact or lifetime acceptance.
