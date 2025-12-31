# Type Provider Architecture in FNCS

## Current Status: Disabled via NO_TYPEPROVIDERS

Traditional .NET type providers are disabled in FNCS because they fundamentally depend on BCL reflection:

- `Assembly.UnsafeLoadFrom` - Dynamic assembly loading
- `Activator.CreateInstance` - Runtime object instantiation
- `System.Type` reflection - Type introspection
- `MaybeNull<'T>` patterns - BCL nullable semantics

These are incompatible with native compilation.

## Pre-existing Guards

The FCS codebase already has `#if !NO_TYPEPROVIDERS` guards throughout:
- TypeProviders.fs/fsi
- tainted.fs/fsi
- 200+ locations across the compiler

Enabling `NO_TYPEPROVIDERS` in DefineConstants cleanly disables all type provider code.

## Future: Native Type Providers

The metaprogramming capability can be restored via native-first approach:

1. **Static metadata files** (TOML/JSON schemas instead of assemblies)
2. **Quotation-based generation** (compile-time evaluation)
3. **Active pattern providers** (pattern-based discovery)
4. **Staged metaprogramming** (MetaOCaml-style)

Key difference: Zero runtime reflection, zero BCL dependency.

## Documentation

Full analysis in: `/home/hhh/repos/Firefly/docs/FNCS_Native_Type_Providers.md`

## Files Modified

- `FSharpNative.Compiler.Service.fsproj` - Added NO_TYPEPROVIDERS define
