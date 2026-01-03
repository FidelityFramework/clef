# IL → Native Type Migration Progress (January 2, 2026)

## Completed Work

### TcGlobals.fsi/fs
- Removed `ilg: ILGlobals` constructor parameter
- Added `splitTypeName` and `mkNativeTypeRef` helper functions
- `BuiltinAttribInfo.TypeRef` now returns `TypeConRef`
- Renamed `FindSysILTypeRef` → `FindSysTypeRef`
- Removed all IL attribute generation functions
- Removed `iltyp_*` members

### TypedTreeOps.fsi/fs
- Removed `mkAsmExpr` (creates TOp.ILAsm)
- Removed box/isinst/unbox IL instructions
- Removed `mspec_String_*` IL method specs
- Removed `mkStaticCall_String_Concat*` functions
- Removed IL attribute functions (TryDecodeILAttribute, IsILAttrib, etc.)
- Removed `ConstToILFieldInit` active pattern
- Simplified `mkArrayElemAddress` and `mkGetTupleItemN` signatures
- Updated `TryBindTyconRefAttribute` to remove IL callback

## Remaining Work

### Phase 4: Remove TypedTree IL DU Cases
These DU cases still exist in TypedTree and are pattern-matched throughout:
- `TOp.ILAsm` - IL assembly expression
- `TOp.ILCall` - IL method call  
- `TILObjectRepr` - IL object representation
- `TAsmRepr` - Assembly representation
- `CompiledTypeRepr.ILAsmNamed/ILAsmOpen`

### Entity Properties to Remove
- `IsILTycon`
- `ILTyconRawMetadata`
- `CompiledRepresentation`
- `CompiledRepresentationForNamedType`

### Files Needing Updates After DU Removal
- TypedTreeOps.fs: ~40+ pattern matches on IL DU cases
- TypeHashing.fs: Uses ILTypeRef, ILArrayShape, ILType, ILCallingSignature
- Many callers of removed functions need stubs or native equivalents

## Build Status
Build fails with ~90 errors, mostly:
1. Pattern matches on removed/nonexistent IL DU cases
2. Calls to removed IL functions (mkAsmExpr, mkILAsmCeq, etc.)
3. References to removed Entity properties
