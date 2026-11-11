# Target-specific compiler regressions

`Windows/SourcePlatformTests.fs` belongs to the Windows source-platform suite.
These are compiler-service tests, so run them on either Windows or Linux:

```text
dotnet test tests/Clef.Compiler.Service.Tests/Clef.Compiler.Service.Tests.fsproj -p:FSharpCoreImplicitPackageVersion=10.1.401 --filter FullyQualifiedName~Platform.Windows
```

They check source-owned loading publication with and without optional runtime
metadata, and retain invalid-contract controls. Host discovery and installation
tests are separate under `tests/HostTooling/Windows` and `tests/HostTooling/Linux`.
