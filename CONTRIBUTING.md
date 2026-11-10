# CCS contributor tooling

Composer is the toolchain entry point. Its `tools/Dev.fsx` bootstraps sibling
repositories and builds the managed toolchain. CCS can also be built from this
checkout with a stable .NET 10 SDK:

```text
dotnet build src/Compiler/Clef.Compiler.Service.fsproj -p:FSharpCoreImplicitPackageVersion=10.1.401
dotnet fsi tests/HostTooling/Discovery.fsx
dotnet fsi tools/InstallSolver.fsx
dotnet test tests/Clef.Compiler.Service.Tests/Clef.Compiler.Service.Tests.fsproj -p:FSharpCoreImplicitPackageVersion=10.1.401 --filter FullyQualifiedName~Solver
```

The build property applies the same FSharp.Core version throughout the sibling
project graph. Use separate build directories for Windows and Linux.

The root `nuget.config` is the sole package configuration. It retains nuget.org
and `vendor/Fidelity.FSharp.Incremental`. The obsolete Arcade `NuGet.config`
must not be restored: case-sensitive Git trees containing both names cannot be
checked out reliably on Windows. No Arcade SDK is used by this build.

`InstallSolver.fsx` downloads the official cvc5 1.3.0 static release for Windows
x64 or Linux x64 and checks its published SHA-256 before extraction. It installs
under `%LOCALAPPDATA%/Clef/toolchains/cvc5-1.3.0` or
`~/.local/toolchains/cvc5-1.3.0`, preserving existing installations. Other hosts
can provide their own solver through `CLEF_CVC5`.

Solver selection is explicit `CLEF_CVC5`, then the exact executable found on
PATH, then the current user's installation. Linux parity mounts and the Linux
temporary toolchain location remain Linux-only fallbacks. An explicit missing
solver fails; it is never replaced. `CLEF_PROOF_TEMP_DIR` selects query scratch.
Host-discovery checks use `artifacts/scratch/`; solver tests use portable directory names.
Source fixture checkouts are LF so multiline source replacements behave identically
on both hosts. Generated TOML fixture paths use quoted string encoding, and path
assertions follow the checker's normalized slash representation.

These checks concern the compiler host and solver transport. They do not add a
Windows output target or establish full language/proof acceptance.
