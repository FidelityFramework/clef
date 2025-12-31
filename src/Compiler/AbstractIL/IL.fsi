// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.
// Copyright (c) SpeakEZ, Inc.  All Rights Reserved.  Native scaffolding for FNCS.

/// Native scaffolding for the Abstract IL type system.
///
/// This module provides types with the same API surface as the original FCS AbstractIL.IL module,
/// but with semantics appropriate for native-first compilation in FNCS.
///
/// DESIGN PRINCIPLES:
/// 1. Types that represent imported .NET metadata are scaffolded minimally
/// 2. Types used for IL code emission are empty scaffolding (FNCS doesn't emit IL)
/// 3. Types representing native concepts have meaningful implementations
///
/// FUTURE DIRECTION:
/// This scaffolding enables TypedTree to compile. Over time, it should evolve into
/// a proper native type metadata layer (NativeTypeDef, NativeScopeRef, etc.)

module FSharp.Compiler.AbstractIL.IL

open System
open System.Collections.Generic
open System.Reflection

// ============================================================================
// ASSEMBLY AND MODULE REFERENCES
// In FNCS, these represent native module provenance rather than .NET assemblies
// ============================================================================

/// Represents a reference to a primary assembly.
/// In native compilation, this concept may map to "core library" (Alloy).
[<RequireQualifiedAccess>]
type internal PrimaryAssembly =
    | Mscorlib
    | System_Runtime
    | NetStandard

    member Name: string
    static member IsPossiblePrimaryAssembly: fileName: string -> bool

/// Represents guids (used for debugging info)
type ILGuid = byte[]

/// Platform target
[<StructuralEquality; StructuralComparison>]
type ILPlatform =
    internal
    | X86
    | AMD64
    | IA64
    | ARM
    | ARM64

/// Public key for assembly identity
[<StructuralEquality; StructuralComparison>]
type PublicKey =
    | PublicKey of byte[]
    | PublicKeyToken of byte[]

    member IsKey: bool
    member IsKeyToken: bool
    member Key: byte[]
    member KeyToken: byte[]
    static member KeyAsToken: byte[] -> PublicKey

/// Version information
[<Struct>]
type ILVersionInfo =
    val Major: uint16
    val Minor: uint16
    val Build: uint16
    val Revision: uint16
    new: major: uint16 * minor: uint16 * build: uint16 * revision: uint16 -> ILVersionInfo

/// Assembly reference - in FNCS, represents a native library reference
[<Sealed>]
type ILAssemblyRef =
    static member Create:
        name: string *
        hash: byte[] option *
        publicKey: PublicKey option *
        retargetable: bool *
        version: ILVersionInfo option *
        locale: string option ->
            ILAssemblyRef

    static member FromAssemblyName: AssemblyName -> ILAssemblyRef
    member Name: string
    member QualifiedName: string
    member Hash: byte[] option
    member PublicKey: PublicKey option
    member Retargetable: bool
    member Version: ILVersionInfo option
    member Locale: string option
    member EqualsIgnoringVersion: ILAssemblyRef -> bool
    interface System.IComparable

/// Module reference
[<Sealed>]
type ILModuleRef =
    static member Create: name: string * hasMetadata: bool * hash: byte[] option -> ILModuleRef
    member Name: string
    member HasMetadata: bool
    member Hash: byte[] option
    interface System.IComparable

/// Scope reference - where does a type come from?
/// In FNCS, this represents native module provenance.
[<StructuralEquality; StructuralComparison; RequireQualifiedAccess>]
type ILScopeRef =
    /// A reference to the type in the current module
    | Local
    /// A reference to a type in another module in the same assembly
    | Module of ILModuleRef
    /// A reference to a type in another assembly (in FNCS: native library)
    | Assembly of ILAssemblyRef
    /// A reference to a type in the primary assembly (in FNCS: core library)
    | PrimaryAssembly

    member IsLocalRef: bool
    member QualifiedName: string

// ============================================================================
// CALLING CONVENTIONS
// ============================================================================

[<StructuralEquality; StructuralComparison; RequireQualifiedAccess>]
type ILArgConvention =
    | Default
    | CDecl
    | StdCall
    | ThisCall
    | FastCall
    | VarArg

[<StructuralEquality; StructuralComparison; RequireQualifiedAccess>]
type ILThisConvention =
    | Instance
    | InstanceExplicit
    | Static

[<StructuralEquality; StructuralComparison>]
type ILCallingConv =
    | Callconv of ILThisConvention * ILArgConvention

    member internal IsInstance: bool
    member internal IsInstanceExplicit: bool
    member internal IsStatic: bool
    member internal ThisConv: ILThisConvention
    member internal BasicConv: ILArgConvention

    static member Instance: ILCallingConv
    static member Static: ILCallingConv

// ============================================================================
// ARRAY SHAPES
// ============================================================================

type internal ILArrayBound = int32 option
type internal ILArrayBounds = ILArrayBound * ILArrayBound

type ILArrayShape =
    internal
    | ILArrayShape of ILArrayBounds list

    member Rank: int
    static member SingleDimensional: ILArrayShape
    static member FromRank: int -> ILArrayShape

// ============================================================================
// TYPE REFERENCES AND TYPES
// ============================================================================

/// Boxity - value vs reference type
type ILBoxity =
    | AsObject
    | AsValue

/// Generic variance
type ILGenericVariance =
    | NonVariant
    | CoVariant
    | ContraVariant

/// Type reference - in FNCS, represents a native type path
[<Sealed>]
type ILTypeRef =
    static member Create: scope: ILScopeRef * enclosing: string list * name: string -> ILTypeRef
    member Scope: ILScopeRef
    member Enclosing: string list
    member Name: string
    member FullName: string
    member BasicQualifiedName: string
    member QualifiedName: string
    member internal EqualsWithPrimaryScopeRef: ILScopeRef * obj -> bool
    override ToString: unit -> string
    interface System.IComparable

/// Type specification with generic args
[<Sealed>]
type ILTypeSpec =
    static member Create: typeRef: ILTypeRef * instantiation: ILGenericArgs -> ILTypeSpec
    member TypeRef: ILTypeRef
    member GenericArgs: ILGenericArgs
    member Scope: ILScopeRef
    member Enclosing: string list
    member Name: string
    member FullName: string
    member internal EqualsWithPrimaryScopeRef: ILScopeRef * obj -> bool
    interface System.IComparable

/// Type representation - the core IL type in FNCS
and [<RequireQualifiedAccess; StructuralEquality; StructuralComparison>]
    ILType =
    | Void
    | Array of ILArrayShape * ILType
    | Value of ILTypeSpec
    | Boxed of ILTypeSpec
    | Ptr of ILType
    | Byref of ILType
    | FunctionPointer of ILCallingSignature
    | TypeVar of uint16
    | Modified of bool * ILTypeRef * ILType

    member TypeSpec: ILTypeSpec
    member internal Boxity: ILBoxity
    member TypeRef: ILTypeRef
    member IsNominal: bool
    member GenericArgs: ILGenericArgs
    member IsTyvar: bool
    member BasicQualifiedName: string
    member QualifiedName: string

/// Calling signature
and [<StructuralEquality; StructuralComparison>]
    ILCallingSignature =
    { CallingConv: ILCallingConv
      ArgTypes: ILTypes
      ReturnType: ILType }

/// Generic args and types
and ILGenericArgs = ILType list
and ILTypes = ILType list

// ============================================================================
// METHOD AND FIELD REFERENCES
// ============================================================================

/// Method reference
[<Sealed>]
type ILMethodRef =
    static member Create:
        enclosingTypeRef: ILTypeRef *
        callingConv: ILCallingConv *
        name: string *
        genericArity: int *
        argTypes: ILTypes *
        returnType: ILType ->
            ILMethodRef

    member DeclaringTypeRef: ILTypeRef
    member CallingConv: ILCallingConv
    member Name: string
    member GenericArity: int
    member ArgCount: int
    member ArgTypes: ILTypes
    member ReturnType: ILType
    member GetCallingSignature: unit -> ILCallingSignature
    interface System.IComparable

/// Field initializer value
type ILFieldInit =
    | String of string
    | Bool of bool
    | Char of uint16
    | Int8 of int8
    | Int16 of int16
    | Int32 of int32
    | Int64 of int64
    | UInt8 of uint8
    | UInt16 of uint16
    | UInt32 of uint32
    | UInt64 of uint64
    | Single of single
    | Double of double
    | Null

/// Field reference
type ILFieldRef =
    { DeclaringTypeRef: ILTypeRef
      Name: string
      Type: ILType }

/// Method specification (with instantiation)
[<Sealed>]
type ILMethodSpec =
    static member Create: ILType * ILMethodRef * ILGenericArgs -> ILMethodSpec
    member MethodRef: ILMethodRef
    member DeclaringType: ILType
    member GenericArgs: ILGenericArgs
    member CallingConv: ILCallingConv
    member GenericArity: int
    member Name: string
    member FormalArgTypes: ILTypes
    member FormalReturnType: ILType

/// Field specification
type ILFieldSpec =
    { FieldRef: ILFieldRef
      DeclaringType: ILType }

    member DeclaringTypeRef: ILTypeRef
    member Name: string
    member FormalType: ILType
    member ActualType: ILType

// ============================================================================
// IL INSTRUCTIONS - SCAFFOLDING ONLY
// FNCS does not emit IL. These are empty scaffolding to satisfy type definitions.
// ============================================================================

/// Code labels - used for state machine compilation (just an int alias)
type internal ILCodeLabel = int

/// Basic IL types (minimal scaffolding)
[<StructuralEquality; StructuralComparison>]
type internal ILBasicType =
    | DT_R
    | DT_I1
    | DT_U1
    | DT_I2
    | DT_U2
    | DT_I4
    | DT_U4
    | DT_I8
    | DT_U8
    | DT_R4
    | DT_R8
    | DT_I
    | DT_U
    | DT_REF

/// Readonly prefix for array element access
[<RequireQualifiedAccess>]
type internal ILReadonlyPrefix =
    | ReadOnly
    | NormalAddress

/// Memory volatility
type internal ILVolatility = | Volatile | Nonvolatile

/// Memory alignment
type internal ILAlignment = | Aligned | Unaligned1 | Unaligned2 | Unaligned4

/// Call tail prefix
type internal ILTailcall = | Tailcall | Normalcall

/// IL token for ldtoken instruction
type ILToken =
    | ILToken_type of ILType
    | ILToken_method of ILMethodSpec
    | ILToken_field of ILFieldSpec

/// IL constant values
type ILConstValue = | I4 of int32 | I8 of int64 | R4 of single | R8 of double

/// IL instruction - scaffolding for type checker
/// FNCS does not support inline IL assembly but the type checker needs these types.
[<StructuralEquality; NoComparison>]
type internal ILInstr =
    | AI_nop
    | AI_add | AI_sub | AI_mul | AI_div | AI_rem | AI_neg | AI_pop | AI_dup
    | AI_ldarg of uint16 | AI_ldloc of uint16 | AI_starg of uint16 | AI_stloc of uint16
    | AI_ret | AI_br of ILCodeLabel | AI_ldc of ILBasicType * ILConstValue | AI_ldnull
    | I_box of ILType | I_unbox_any of ILType | I_isinst of ILType | I_castclass of ILType
    | I_ldobj of ILAlignment * ILVolatility * ILType
    | I_stobj of ILAlignment * ILVolatility * ILType
    | I_cpobj of ILType | I_initobj of ILType
    | I_ldelem_any of ILArrayShape * ILType | I_stelem_any of ILArrayShape * ILType
    | I_newarr of ILArrayShape * ILType | I_ldlen
    | I_ldelema of ILReadonlyPrefix * bool * ILArrayShape * ILType
    | I_call of ILTailcall * ILMethodSpec * ILTypes option
    | I_callvirt of ILTailcall * ILMethodSpec * ILTypes option
    | I_callconstraint of ILTailcall * ILType * ILMethodSpec * ILTypes option
    | I_newobj of ILMethodSpec * ILTypes option
    | I_ldfld of ILAlignment * ILVolatility * ILFieldSpec
    | I_stfld of ILAlignment * ILVolatility * ILFieldSpec
    | I_ldsfld of ILVolatility * ILFieldSpec | I_stsfld of ILVolatility * ILFieldSpec
    | I_ldflda of ILFieldSpec | I_ldsflda of ILFieldSpec
    | I_ldtoken of ILToken | I_leave of ILCodeLabel | I_throw | I_rethrow
    | I_endfinally | I_endfilter
    | AI_conv of ILBasicType | AI_conv_ovf of ILBasicType | AI_conv_ovf_un of ILBasicType
    | AI_ceq | AI_cgt | AI_cgt_un | AI_clt | AI_clt_un
    | AI_and | AI_or | AI_xor | AI_not | AI_shl | AI_shr | AI_shr_un
    | AI_add_ovf | AI_add_ovf_un | AI_sub_ovf | AI_sub_ovf_un
    | AI_mul_ovf | AI_mul_ovf_un | AI_div_un | AI_rem_un
    | AI_ckfinite
    | I_ldloca of uint16 | I_ldarga of uint16 | I_sizeof of ILType | I_localloc
    | I_cpblk of ILAlignment * ILVolatility | I_initblk of ILAlignment * ILVolatility
    | I_ldvirtftn of ILMethodSpec
    | I_ldstr of string
    | I_unbox of ILType
    | EI_ldlen_multi of int32 * int32 | EI_ilzero of ILType

// ============================================================================
// MEMBER ACCESS
// ============================================================================

[<RequireQualifiedAccess>]
type ILMemberAccess =
    | Assembly
    | CompilerControlled
    | FamilyAndAssembly
    | FamilyOrAssembly
    | Family
    | Private
    | Public

[<RequireQualifiedAccess>]
type ILTypeDefAccess =
    | Public
    | Private
    | Nested of ILMemberAccess

// ============================================================================
// TYPE DEFINITIONS - SCAFFOLDING
// ============================================================================

/// Attribute element
[<RequireQualifiedAccess>]
type ILAttribElem =
    | String of string option
    | Bool of bool
    | Char of char
    | SByte of int8
    | Int16 of int16
    | Int32 of int32
    | Int64 of int64
    | Byte of uint8
    | UInt16 of uint16
    | UInt32 of uint32
    | UInt64 of uint64
    | Single of single
    | Double of double
    | Null
    | Type of ILType option
    | TypeRef of ILTypeRef option
    | Array of ILType * ILAttribElem list

/// Named argument for attributes
type ILAttributeNamedArg = string * ILType * bool * ILAttribElem

/// Attribute
[<Sealed>]
type ILAttribute =
    member Method: ILMethodSpec
    member Elements: ILAttribElem list
    member WithMethod: method': ILMethodSpec -> ILAttribute

/// Attributes collection (placeholder)
[<Sealed>]
type ILAttributes =
    member AsArray: unit -> ILAttribute[]
    member AsList: unit -> ILAttribute list

/// Stored attributes (placeholder for lazy loading)
[<NoEquality; NoComparison>]
type ILAttributesStored

/// Empty IL custom attributes
val emptyILCustomAttrs: ILAttributes

/// Create IL custom attributes from array
val mkILCustomAttrsFromArray: ILAttribute[] -> ILAttributes

/// Create IL custom attributes from list
val mkILCustomAttrs: ILAttribute list -> ILAttributes

/// Empty IL custom attrs stored
val emptyILCustomAttrsStored: ILAttributesStored

/// Store IL custom attributes
val storeILCustomAttrs: ILAttributes -> ILAttributesStored

/// Type definition layout
[<RequireQualifiedAccess>]
type ILTypeDefLayout =
    | Auto
    | Sequential of ILTypeDefLayoutInfo
    | Explicit of ILTypeDefLayoutInfo

and ILTypeDefLayoutInfo =
    { Size: int32 option
      Pack: uint16 option }

/// Type definition - minimal scaffolding
/// In FNCS, this should evolve into NativeTypeDef with layout information.
[<Sealed>]
type ILTypeDef =
    member Name: string
    member Access: ILTypeDefAccess
    member IsClass: bool
    member IsInterface: bool
    member IsStruct: bool
    member IsEnum: bool
    member IsDelegate: bool
    member IsSealed: bool
    member IsAbstract: bool
    member IsSerializable: bool
    member IsStructOrEnum: bool
    member Layout: ILTypeDefLayout
    member NestedTypes: ILTypeDefs
    member CustomAttrs: ILAttributes

/// Collection of type definitions
and [<Sealed>] ILTypeDefs =
    new: defs: ILTypeDef[] -> ILTypeDefs
    interface IEnumerable<ILTypeDef>
    member AsArray: unit -> ILTypeDef[]
    member AsList: unit -> ILTypeDef list
    member FindByName: string -> ILTypeDef

/// Create type defs from a list
val mkILTypeDefs: ILTypeDef list -> ILTypeDefs

/// Create type defs from an array
val mkILTypeDefsFromArray: ILTypeDef[] -> ILTypeDefs

/// Empty type defs
val emptyILTypeDefs: ILTypeDefs

// ============================================================================
// FIELD, METHOD, PROPERTY DEFINITIONS - Required by TcGlobals
// ============================================================================

/// Field definition
[<Sealed; NoComparison; NoEquality>]
type ILFieldDef =
    member Name: string
    member FieldType: ILType
    member IsStatic: bool
    member IsLiteral: bool
    member Access: ILMemberAccess
    member CustomAttrs: ILAttributes

/// Method definition
[<Sealed; NoComparison; NoEquality>]
type ILMethodDef =
    member Name: string
    member CallingConv: ILCallingConv
    member IsStatic: bool
    member IsAbstract: bool
    member IsFinal: bool
    member IsVirtual: bool
    member Access: ILMemberAccess
    member CustomAttrs: ILAttributes
    member ParameterTypes: ILTypes
    member GetCallingSignature: unit -> ILCallingSignature

/// Property definition
[<Sealed; NoComparison; NoEquality>]
type ILPropertyDef =
    member Name: string
    member PropertyType: ILType
    member CustomAttrs: ILAttributes

// ============================================================================
// SECURITY DECLARATIONS - SCAFFOLDING
// ============================================================================

/// Security declaration (scaffolding)
type ILSecurityDecl = ILSecurityDecl of int32 * byte[]

/// Security declarations
type ILSecurityDecls =
    | ILSecurityDecls of ILSecurityDecl list
    member AsList: unit -> ILSecurityDecl list

/// Stored security declarations (lazy loading scaffolding)
[<NoEquality; NoComparison>]
type ILSecurityDeclsStored =
    | GivenSecurityDecls of ILSecurityDecl[]
    | ReaderSecurityDecls of (int32 -> ILSecurityDecl[])
    member GetSecurityDecls: int32 -> ILSecurityDecls

val storeILSecurityDecls: ILSecurityDecls -> ILSecurityDeclsStored
val emptyILSecurityDecls: ILSecurityDecls
val emptyILSecurityDeclsStored: ILSecurityDeclsStored

// ============================================================================
// EXPORTED TYPES AND FORWARDERS - SCAFFOLDING
// ============================================================================

/// Exported type or forwarder entry
type ILExportedTypeOrForwarder =
    { ScopeRef: ILScopeRef
      Name: string
      Attributes: System.Reflection.TypeAttributes
      Nested: ILNestedExportedTypesAndForwarders
      CustomAttrsStored: ILAttributesStored
      MetadataIndex: int32 }
    member Access: ILTypeDefAccess
    member CustomAttrs: ILAttributes
    member IsForwarder: bool

/// Nested exported types
and [<Sealed>] ILNestedExportedTypesAndForwarders =
    member AsList: unit -> ILExportedTypeOrForwarder list

/// Exported types and forwarders collection
and [<Sealed>] ILExportedTypesAndForwarders =
    member AsList: unit -> ILExportedTypeOrForwarder list
    member TryFindByName: string -> ILExportedTypeOrForwarder option

// ============================================================================
// RESOURCES - SCAFFOLDING
// ============================================================================

/// Resource access
type ILResourceAccess =
    | Public
    | Private

/// Byte storage (lazy loading)
type ByteStorage = unit -> byte[]

/// Resource location
type ILResourceLocation =
    | Local of ByteStorage
    | File of ILModuleRef * int32
    | Assembly of ILAssemblyRef

/// Resource entry
type ILResource =
    { Name: string
      Location: ILResourceLocation
      Access: ILResourceAccess
      CustomAttrsStored: ILAttributesStored
      MetadataIndex: int32 }
    member CustomAttrs: ILAttributes

/// Resources collection
[<Sealed>]
type ILResources =
    new: resources: ILResource[] -> ILResources
    member AsList: unit -> ILResource list

// ============================================================================
// ASSEMBLY MANIFEST - SCAFFOLDING
// ============================================================================

/// Assembly longevity
type ILAssemblyLongevity =
    | Unset
    | Library
    | PlatformAppDomain
    | PlatformProcess
    | PlatformSystem

/// Assembly manifest - metadata for an assembly
type ILAssemblyManifest =
    { Name: string
      AuxModuleHashAlgorithm: int32
      SecurityDeclsStored: ILSecurityDeclsStored
      PublicKey: byte[] option
      Version: ILVersionInfo option
      Locale: string option
      CustomAttrsStored: ILAttributesStored
      AssemblyLongevity: ILAssemblyLongevity
      DisableJitOptimizations: bool
      JitTracking: bool
      IgnoreSymbolStoreSequencePoints: bool
      Retargetable: bool
      ExportedTypes: ILExportedTypesAndForwarders
      EntrypointElsewhere: ILModuleRef option
      MetadataIndex: int32 }
    member SecurityDecls: ILSecurityDecls
    member CustomAttrs: ILAttributes

/// Native resource (for embedding resources in native binaries - scaffolding)
[<RequireQualifiedAccess>]
type ILNativeResource =
    | In of fileName: string * linkedResourceBase: int * linkedResourceStart: int * linkedResourceLength: int
    | Out of unlinkedResources: byte[]

// ============================================================================
// MODULE DEFINITIONS - SCAFFOLDING
// ============================================================================

/// Module definition - scaffolding for FNCS
/// FNCS uses this for type resolution, not IL code generation
[<Sealed>]
type ILModuleDef =
    member Name: string
    member Manifest: ILAssemblyManifest option
    member TypeDefs: ILTypeDefs
    member IsDLL: bool
    member Platform: ILPlatform option
    member MetadataVersion: string
    member Resources: ILResources
    member HasManifest: bool
    member ManifestOfAssembly: ILAssemblyManifest
    /// Create an empty module (scaffolding for FNCS)
    static member Empty: name: string * typeDefs: ILTypeDefs -> ILModuleDef

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/// Split a namespace string into parts
val splitNamespace: string -> string list

/// Split a namespace string into an array
val splitNamespaceToArray: string -> string[]

/// Split an IL type name into namespace parts and type name
val splitILTypeName: string -> string list * string

/// SHA1 hash as int64 (for type identity)
val sha1HashInt64: byte[] -> int64

/// Create a simple assembly reference
val mkSimpleAssemblyRef: string -> ILAssemblyRef

/// Create a type reference
val mkILTyRef: ILScopeRef * string -> ILTypeRef

/// Create a nested type reference within an enclosing type
val mkILTyRefInTyRef: ILTypeRef * string -> ILTypeRef

/// Create a type spec
val mkILTySpec: ILTypeRef * ILGenericArgs -> ILTypeSpec

/// Create a non-generic type spec
val mkILNonGenericTySpec: ILTypeRef -> ILTypeSpec

/// Create a type with boxity
val mkILTy: ILBoxity -> ILTypeSpec -> ILType

/// Create a named type with boxity
val mkILNamedTy: ILBoxity -> ILTypeRef -> ILGenericArgs -> ILType

/// Create a type variable type
val mkILTyvarTy: uint16 -> ILType

/// Create a non-generic boxed type
val mkILNonGenericBoxedTy: ILTypeRef -> ILType

/// Create a non-generic value type
val mkILNonGenericValueTy: ILTypeRef -> ILType

/// Create a boxed type from a type spec
val mkILBoxedType: ILTypeSpec -> ILType

/// Create a value type from a type spec
val mkILValueType: ILTypeSpec -> ILType

/// Create a custom attribute
val mkILCustomAttribute:
    ILTypeRef * ILType list * ILAttribElem list * ILAttributeNamedArg list -> ILAttribute

/// Create a reference to a nested type within enclosing type definitions
val mkRefForNestedILTypeDef: ILScopeRef -> ILTypeDef list * ILTypeDef -> ILTypeRef

/// Create a field spec within a type
val mkILFieldSpecInTy: ILType * string * ILType -> ILFieldSpec

/// Create a method spec within a type
val internal mkILMethSpecInTy: ILType * ILCallingConv * string * ILTypes * ILType * ILGenericArgs -> ILMethodSpec

/// Create a non-generic method spec within a type
val mkILNonGenericMethSpecInTy: ILType * ILCallingConv * string * ILTypes * ILType -> ILMethodSpec

/// Create a non-generic instance method spec within a type
val mkILNonGenericInstanceMethSpecInTy: ILType * string * ILTypes * ILType -> ILMethodSpec

/// Create a non-generic static method spec within a type
val mkILNonGenericStaticMethSpecInTy: ILType * string * ILTypes * ILType -> ILMethodSpec

// ============================================================================
// IL INSTRUCTION HELPERS
// ============================================================================
// Helpers for creating IL instructions. Used by type checking to represent
// operations in the typed tree (mkAsmExpr).

/// Create a normal call instruction
val internal mkNormalCall: ILMethodSpec -> ILInstr

/// Create a normal callvirt instruction
val internal mkNormalCallvirt: ILMethodSpec -> ILInstr

/// Create a normal newobj instruction
val internal mkNormalNewobj: ILMethodSpec -> ILInstr

/// Create a normal stfld instruction
val internal mkNormalStfld: ILFieldSpec -> ILInstr

/// Create a normal stsfld instruction
val internal mkNormalStsfld: ILFieldSpec -> ILInstr

/// Create a normal ldsfld instruction
val internal mkNormalLdsfld: ILFieldSpec -> ILInstr

/// Create a normal ldfld instruction
val internal mkNormalLdfld: ILFieldSpec -> ILInstr

/// Create a normal ldflda instruction
val internal mkNormalLdflda: ILFieldSpec -> ILInstr

/// Create a normal ldobj instruction
val internal mkNormalLdobj: ILType -> ILInstr

/// Create a normal stobj instruction
val internal mkNormalStobj: ILType -> ILInstr

/// Load argument 0 (ldarg.0)
val internal mkLdarg0: ILInstr

/// Load argument n (ldarg n)
val internal mkLdarg: uint16 -> ILInstr

// ============================================================================
// SOURCE DOCUMENT (for debugging info)
// ============================================================================

[<Sealed>]
type ILSourceDocument =
    static member Create:
        language: ILGuid option * vendor: ILGuid option * documentType: ILGuid option * file: string -> ILSourceDocument
    member Language: ILGuid option
    member Vendor: ILGuid option
    member DocumentType: ILGuid option
    member File: string

[<Sealed>]
type internal ILDebugPoint =
    static member Create:
        document: ILSourceDocument * line: int * column: int * endLine: int * endColumn: int -> ILDebugPoint
    member Document: ILSourceDocument
    member Line: int
    member Column: int
    member EndLine: int
    member EndColumn: int

// ============================================================================
// INTERFACE IMPLEMENTATION
// ============================================================================

type InterfaceImpl =
    { Idx: int
      Type: ILType
      mutable CustomAttrsStored: ILAttributesStored }

    member CustomAttrs: ILAttributes
    static member Create: ilType: ILType * customAttrsStored: ILAttributesStored -> InterfaceImpl
    static member Create: ilType: ILType -> InterfaceImpl

// ============================================================================
// NATIVE TYPE GLOBALS
// ============================================================================
// FNCS defines the native type universe. Standard F# type names, native semantics.
// No BCL. No obj. No boxing.

[<Sealed>]
type internal ILGlobals =
    member primaryAssemblyName: string
    member fsharpCoreAssemblyScopeRef: ILScopeRef

    // Native primitive types
    member typ_String: ILType
    member typ_Bool: ILType
    member typ_Char: ILType
    member typ_SByte: ILType
    member typ_Int16: ILType
    member typ_Int32: ILType
    member typ_Int64: ILType
    member typ_Byte: ILType
    member typ_UInt16: ILType
    member typ_UInt32: ILType
    member typ_UInt64: ILType
    member typ_Single: ILType
    member typ_Double: ILType
    member typ_IntPtr: ILType
    member typ_UIntPtr: ILType

    // Fallback type for inline IL error handling (returns Void since inline IL not supported)
    member typ_Object: ILType

    static member Create: primaryAssemblyName: string * fsharpCoreAssemblyScopeRef: ILScopeRef -> ILGlobals

/// Global instance for error fallbacks (inline IL parsing errors)
/// In native compilation, inline IL is not supported, so this provides a fallback type.
val internal PrimaryAssemblyILGlobals: ILGlobals
