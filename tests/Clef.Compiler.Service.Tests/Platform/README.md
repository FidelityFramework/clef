# Target-specific compiler regressions

`Windows/SourcePlatformTests.fs` belongs to the Windows source-platform suite.
These are compiler-service tests, so run them on either Windows or Linux through
the Composer contributor harness (from the sibling Composer checkout):

```text
dotnet fsi tools/Dev.fsx -- compiler-regressions
```

The harness builds the test project, configures cvc5 for its children and includes
shared array, loop and initialization regressions. `ccs-tests` runs the full CCS
suite instead. These Windows cases check source-owned loading publication with and without optional runtime
metadata, and retain invalid-contract controls. Host discovery and installation
tests are separate under `tests/HostTooling/Windows` and `tests/HostTooling/Linux`.
