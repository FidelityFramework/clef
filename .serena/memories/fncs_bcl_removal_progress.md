# FNCS BCL Removal Progress

## Status: In Progress (~50 errors remaining, down from ~200)

## Completed Work

### IL Layer (IL.fs/IL.fsi)
- ✅ Removed BCL types from ILGlobals (typ_Type, typ_Array, etc.)
- ✅ Removed P/Invoke machinery (ILNativeType, PInvokeMethod)
- ✅ Fixed ILInstr union cases (AI_* naming)
- ✅ Added IL instruction helpers (mkNormalCall, mkNormalCallvirt, etc.)
- ✅ Fixed ILBoxity accessibility (made public)
- ✅ Fixed mkILTy, mkILNamedTy accessibility
- ✅ Deleted unused IL construction helpers:
  - typesOfILParams
  - mkILFieldsLazy, emptyILFields
  - mkILMethodsFromArray, mkILMethods, emptyILMethods
  - emptyILProperties
  - emptyILEvents
  - emptyILMethodImpls
  - mkILNestedTyRef
- ✅ Disabled type providers (NO_TYPEPROVIDERS)
- ✅ Prefixed unused _namedArgs parameter in mkILCustomAttribute

### TypedTreeOps
- ✅ Removed BCL-dependent IL code gen helpers
- ✅ Kept native string helpers (mspec_String_Length, etc.)

## Remaining Work (~50 errors)

### Category 1: Missing IL Type Members
Files affected: TcGlobals.fs, import.fs, TypeHierarchy.fs
- ILMethodDef.With
- ILPropertyDef.With
- ILFieldDef.With
- ILTypeDef.Methods
- ILTypeDef.GenericParams
- ILTypeDef.Extends
- ILTypeDef.Implements
- ILTypeDef.MetadataIndex
- ILTypeDef.CustomAttrsStored
- ILAttributesStored.GetCustomAttrs
- ILToken.ILType

### Category 2: Missing IL Helper Functions
Files affected: TypedTreeOps.fs, TypedTreePickle.fs, import.fs
- decodeILAttribData (attribute reading)
- computeILEnumInfo (enum analysis)
- getTyOfILEnumInfo
- rescopeILScopeRef
- rescopeILType
- mkILBoxedType (need to export)
- mkLdarg
- splitILTypeNameWithPossibleStaticArguments

### Category 3: Missing IL Instructions
Files affected: TypedTreePickle.fs
- I_ldvirtftn
- I_ldarg
- I_ldstr
- I_unbox
- AI_ckfinite

### Category 4: Missing IL Types
Files affected: import.fs, import.fsi, TypedTreeOps.fsi
- ILGenericParameterDef
- ILGenericParameterDefs
- ILReadonly (→ ILReadonlyPrefix?)
- ILPreTypeDef
- ILNestedExportedTypes

### Category 5: TcGlobals BCL References
- typ_Type still referenced (line 966)
- primaryAssemblyRef on ILGlobals

### Category 6: Other
- isFeatureSupported (ParseHelpers.fs)
- ReadonlyAddress, NormalAddress (TypedTreeOps.fs)
- Given DU case (import.fs)

## Strategy Notes

These missing items are for **reading IL metadata** from referenced assemblies, which FNCS needs. The IL layer must support:
1. Reading type definitions from .NET assemblies
2. Understanding method/property/field signatures
3. Generic parameter constraints
4. Custom attributes

## Key Insight: FSNI Architecture

FSNI (F# Native Interactive) was analyzed. Key finding:
- FSNI does NOT use IL - it goes F# → FNCS → Alex → MLIR → ORC JIT
- The unused IL helpers were correctly deleted
- The Interactive module (fsi.fs) is kept as scaffold but will be rewritten
- Current fsi.fs IL usage will be replaced with MLIR generation

## Files Modified

- `/src/Compiler/AbstractIL/IL.fs`
- `/src/Compiler/AbstractIL/IL.fsi`
- `/src/Compiler/TypedTree/TypedTreeOps.fs`
- `/src/Compiler/TypedTree/TypedTreeOps.fsi`
- `/src/Compiler/FSharpNative.Compiler.Service.fsproj` (defines)

## Next Steps

1. Add missing IL type members (.With methods, etc.)
2. Add missing IL helper functions from upstream
3. Handle TcGlobals typ_Type references
4. Address remaining ~50 build errors systematically
