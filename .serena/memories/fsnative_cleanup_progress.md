# fsnative Cleanup Progress - December 2025

## Build Status: SUCCEEDS (0 errors, 0 warnings)

## Summary

The fsnative codebase was cleaned to remove BCL-dependent infrastructure, creating a foundation for the native type checker rebuild.

## Files Removed (BCL-dependent, not needed for native)

### Driver/
- `CompilerImports.fs/fsi` - .NET assembly imports
- `CompilerDiagnostics.fs/fsi` - depends on deleted type checking modules
- `ParseAndCheckInputs.fs/fsi` - old type checking orchestration
- `CompilerOptions.fs/fsi` - depends on Optimizer
- `fsc.fs/fsi` - old compiler driver
- `CompilerConfig.fs/fsi` - BCL-dependent configuration (orphaned after other removals)

### Symbols/
- All files removed - FCS public API depending on deleted infrastructure

### Service/
- All files removed (~57 files) - FCS service layer

### Interactive/
- All files removed - FSI not needed for native compilation

## Functions Stubbed (IL behavior neutralized)

In `TypedTreeOps.fs`:
- `TryDecodeILAttribute` - returns None (no IL attribute decoding)
- `TryFindAutoOpenAttr` - returns None
- `TryFindInternalsVisibleToAttr` - returns None
- `IsMatchingSignatureDataVersionAttr` - returns false
- `metadataOfTy` / `metadataOfTycon` - return FSharpOrArrayOrByrefOrTupleOrExnTypeMetadata

In `TcGlobals.fs`:
- `addMethodGeneratedAttrs` - returns input unchanged
- `addPropertyGeneratedAttrs` - returns input unchanged
- `addFieldGeneratedAttrs` - returns input unchanged
- `addPropertyNeverAttrs` - returns input unchanged
- `addFieldNeverAttrs` - returns input unchanged
- `mkDebuggerTypeProxyAttribute` - empty attribute
- `isArrayEmptyAvailable` - always false

In `ParseHelpers.fs`:
- `ParseAssemblyCodeInstructions` - returns empty array (inline IL not supported)
- `ParseAssemblyCodeType` - returns typ_Object fallback

## What Remains

The foundation for native type checking:
- `Utilities/` - common utilities
- `Facilities/` - ranges, logging, XML docs
- `AbstractIL/` - IL type representations (simplified, no BCL)
- `SyntaxTree/` - parsing (syntax tree structures)
- `TypedTree/` - type representations (TcGlobals, TypedTreeOps, etc.)
- `DependencyManager/` - dependency resolution

## Next Steps

Build the native type checker in `Checking.Native/`:
1. `NativeGlobals.fs` - Built-in types with native semantics
2. `NativeTypes.fs` - Type representation
3. `UnionFind.fs` - Efficient substitution
4. `CheckExpr.fs` - Unified construction
5. `SRTPResolution.fs` - SRTP during type checking
6. `Reachability.fs` - Hard prune before handoff
