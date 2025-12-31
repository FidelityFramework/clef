// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.
// Copyright (c) SpeakEZ, Inc.  All Rights Reserved.  Native scaffolding for FNCS.

/// Native scaffolding implementation for the Abstract IL type system.
/// See IL.fsi for design principles and documentation.

module FSharp.Native.Compiler.AbstractIL.IL

open System
open System.Collections.Concurrent
open System.Collections.Generic
open System.Reflection

// ============================================================================
// STRING UTILITIES
// ============================================================================

let splitNameAt (nm: string) idx =
    if idx < 0 then failwith "splitNameAt: idx < 0"
    let s1 = nm.Substring(0, idx)
    let s2 = nm.Substring(idx + 1, nm.Length - idx - 1)
    s1, s2

let rec splitNamespaceAux (nm: string) =
    match nm.IndexOf '.' with
    | -1 -> [nm]
    | idx ->
        let s1, s2 = splitNameAt nm idx
        s1 :: splitNamespaceAux s2

let memoizeNamespaceTable = ConcurrentDictionary<string, string list>()
let splitNamespaceAuxDelegate = Func<string, string list> splitNamespaceAux

let splitNamespace nm =
    memoizeNamespaceTable.GetOrAdd(nm, splitNamespaceAuxDelegate)

let memoizeNamespaceArrayTable = ConcurrentDictionary<string, string[]>()

let splitNamespaceToArrayDelegate =
    Func<string, string array>(splitNamespace >> Array.ofList)

let splitNamespaceToArray nm =
    memoizeNamespaceArrayTable.GetOrAdd(nm, splitNamespaceToArrayDelegate)

let splitILTypeName (nm: string) =
    match nm.LastIndexOf '.' with
    | -1 -> [], nm
    | idx ->
        let s1, s2 = splitNameAt nm idx
        splitNamespace s1, s2

let _splitILTypeNameWithPossibleStaticArguments (nm: string) =
    let nm, suffix =
        match nm.IndexOf ',' with
        | -1 -> nm, None
        | idx -> let s1, s2 = splitNameAt nm idx in s1, Some s2
    let nsp, nm = splitILTypeName nm
    nsp, (match suffix with None -> nm | Some s -> nm + "," + s)

// ============================================================================
// SHA1 HASH - Required for type identity
// ============================================================================

module internal SHA1 =
    let inline (>>>&) (x: int) (y: int) = int32 (uint32 x >>> y)

    let f (t, b, c, d) =
        if t < 20 then (b &&& c) ||| ((~~~b) &&& d)
        elif t < 40 then b ^^^ c ^^^ d
        elif t < 60 then (b &&& c) ||| (b &&& d) ||| (c &&& d)
        else b ^^^ c ^^^ d

    let k t =
        if t < 20 then 0x5A827999
        elif t < 40 then 0x6ED9EBA1
        elif t < 60 then 0x8F1BBCDC
        else 0xCA62C1D6

    type SHAStream =
        { mutable stream: byte[]
          mutable pos: int
          mutable eof: bool }

    let rotl32 x n = (x <<< n) ||| (x >>>& (32 - n))

    let sha1Hash (s: SHAStream) =
        let mutable h0 = 0x67452301
        let mutable h1 = 0xEFCDAB89
        let mutable h2 = 0x98BADCFE
        let mutable h3 = 0x10325476
        let mutable h4 = 0xC3D2E1F0
        let w = Array.create 80 0

        let readByte() =
            let stream = s.stream
            let pos = s.pos
            if pos >= stream.Length then
                s.eof <- true
                0
            else
                s.pos <- pos + 1
                int stream[pos]

        let readUInt32() =
            let b0 = readByte()
            let b1 = readByte()
            let b2 = readByte()
            let b3 = readByte()
            (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

        let msgLen = s.stream.Length * 8
        let mutable loop = true
        let mutable padded = false

        while loop do
            let mutable padReq = false
            for i = 0 to 15 do
                if s.eof then
                    if not padded then
                        padded <- true
                        w[i] <- 0x80000000
                    else
                        w[i] <- 0
                    padReq <- true
                else
                    w[i] <- readUInt32()

            if padReq then
                if s.pos > s.stream.Length + 56 then ()
                else
                    w[15] <- msgLen
                    loop <- false
            else
                if s.eof then loop <- false

            for t = 16 to 79 do
                w[t] <- rotl32 (w[t - 3] ^^^ w[t - 8] ^^^ w[t - 14] ^^^ w[t - 16]) 1

            let mutable a = h0
            let mutable b = h1
            let mutable c = h2
            let mutable d = h3
            let mutable e = h4

            for t = 0 to 79 do
                let temp = (rotl32 a 5) + f (t, b, c, d) + e + k t + w[t]
                e <- d
                d <- c
                c <- rotl32 b 30
                b <- a
                a <- temp

            h0 <- h0 + a
            h1 <- h1 + b
            h2 <- h2 + c
            h3 <- h3 + d
            h4 <- h4 + e

        (h0, h1, h2, h3, h4)

    let sha1HashBytes (bytes: byte[]) =
        let h0, h1, h2, h3, h4 = sha1Hash { stream = bytes; pos = 0; eof = false }
        [| byte (h0 >>> 24); byte (h0 >>> 16); byte (h0 >>> 8); byte h0
           byte (h1 >>> 24); byte (h1 >>> 16); byte (h1 >>> 8); byte h1
           byte (h2 >>> 24); byte (h2 >>> 16); byte (h2 >>> 8); byte h2
           byte (h3 >>> 24); byte (h3 >>> 16); byte (h3 >>> 8); byte h3
           byte (h4 >>> 24); byte (h4 >>> 16); byte (h4 >>> 8); byte h4 |]

    let sha1HashInt64 (bytes: byte[]) =
        let _h0, _h1, _h2, h3, h4 = sha1Hash { stream = bytes; pos = 0; eof = false }
        (int64 h3 <<< 32) ||| int64 (uint32 h4)

let _sha1HashBytes s = SHA1.sha1HashBytes s
let sha1HashInt64 s = SHA1.sha1HashInt64 s

// ============================================================================
// ASSEMBLY AND MODULE REFERENCES
// ============================================================================

[<RequireQualifiedAccess>]
type internal PrimaryAssembly =
    | Mscorlib
    | System_Runtime
    | NetStandard

    member x.Name =
        match x with
        | Mscorlib -> "mscorlib"
        | System_Runtime -> "System.Runtime"
        | NetStandard -> "netstandard"

    static member IsPossiblePrimaryAssembly(fileName: string) =
        let name = System.IO.Path.GetFileNameWithoutExtension(fileName).ToLowerInvariant()
        name = "mscorlib" || name = "system.runtime" || name = "netstandard"

type ILGuid = byte[]

[<StructuralEquality; StructuralComparison>]
type ILPlatform =
    | X86
    | AMD64
    | IA64
    | ARM
    | ARM64

[<StructuralEquality; StructuralComparison>]
type PublicKey =
    | PublicKey of byte[]
    | PublicKeyToken of byte[]

    member x.IsKey = match x with PublicKey _ -> true | _ -> false
    member x.IsKeyToken = match x with PublicKeyToken _ -> true | _ -> false
    member x.Key = match x with PublicKey k -> k | PublicKeyToken k -> k
    member x.KeyToken = match x with PublicKeyToken k -> k | PublicKey k -> k
    static member KeyAsToken(key: byte[]) = PublicKeyToken key

[<Struct>]
type ILVersionInfo =
    val Major: uint16
    val Minor: uint16
    val Build: uint16
    val Revision: uint16
    new(major, minor, build, revision) =
        { Major = major; Minor = minor; Build = build; Revision = revision }

let _parseILVersion (vstr: string) =
    let parts = vstr.Split('.')
    let parse i = if i < parts.Length then UInt16.Parse(parts[i]) else 0us
    ILVersionInfo(parse 0, parse 1, parse 2, parse 3)

let _formatILVersion (v: ILVersionInfo) =
    sprintf "%d.%d.%d.%d" v.Major v.Minor v.Build v.Revision

let _compareILVersions (v1: ILVersionInfo) (v2: ILVersionInfo) =
    let c = compare v1.Major v2.Major
    if c <> 0 then c
    else
        let c = compare v1.Minor v2.Minor
        if c <> 0 then c
        else
            let c = compare v1.Build v2.Build
            if c <> 0 then c
            else compare v1.Revision v2.Revision

[<Sealed>]
type ILAssemblyRef(name: string, hash: byte[] option, publicKey: PublicKey option,
                   retargetable: bool, version: ILVersionInfo option, locale: string option) =

    static member Create(name, hash, publicKey, retargetable, version, locale) =
        ILAssemblyRef(name, hash, publicKey, retargetable, version, locale)

    static member FromAssemblyName(aname: AssemblyName) =
        let publicKey =
            match aname.GetPublicKeyToken() with
            | null | [||] -> None
            | token -> Some (PublicKeyToken token)
        let version =
            match aname.Version with
            | null -> None
            | v -> Some (ILVersionInfo(uint16 v.Major, uint16 v.Minor, uint16 v.Build, uint16 v.Revision))
        ILAssemblyRef(aname.Name, None, publicKey, false, version, None)

    member _.Name = name
    member _.QualifiedName = name
    member _.Hash = hash
    member _.PublicKey = publicKey
    member _.Retargetable = retargetable
    member _.Version = version
    member _.Locale = locale
    member x.EqualsIgnoringVersion(other: ILAssemblyRef) = x.Name = other.Name

    interface System.IComparable with
        member x.CompareTo(obj) =
            match obj with
            | :? ILAssemblyRef as other -> compare x.Name other.Name
            | _ -> 1

[<Sealed>]
type ILModuleRef(name: string, hasMetadata: bool, hash: byte[] option) =
    static member Create(name, hasMetadata, hash) = ILModuleRef(name, hasMetadata, hash)
    member _.Name = name
    member _.HasMetadata = hasMetadata
    member _.Hash = hash

    interface System.IComparable with
        member x.CompareTo(obj) =
            match obj with
            | :? ILModuleRef as other -> compare x.Name other.Name
            | _ -> 1

[<StructuralEquality; StructuralComparison; RequireQualifiedAccess>]
type ILScopeRef =
    | Local
    | Module of ILModuleRef
    | Assembly of ILAssemblyRef
    | PrimaryAssembly

    member x.IsLocalRef = match x with Local -> true | _ -> false

    member x.QualifiedName =
        match x with
        | Local -> ""
        | Module m -> m.Name
        | Assembly a -> a.QualifiedName
        | PrimaryAssembly -> "PrimaryAssembly"

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

    member x.IsInstance = match x with Callconv(ILThisConvention.Instance, _) -> true | _ -> false
    member x.IsInstanceExplicit = match x with Callconv(ILThisConvention.InstanceExplicit, _) -> true | _ -> false
    member x.IsStatic = match x with Callconv(ILThisConvention.Static, _) -> true | _ -> false
    member x.ThisConv = match x with Callconv(t, _) -> t
    member x.BasicConv = match x with Callconv(_, c) -> c

    static member Instance = Callconv(ILThisConvention.Instance, ILArgConvention.Default)
    static member Static = Callconv(ILThisConvention.Static, ILArgConvention.Default)

// ============================================================================
// ARRAY SHAPES
// ============================================================================

type internal ILArrayBound = int32 option
type internal ILArrayBounds = ILArrayBound * ILArrayBound

type ILArrayShape =
    | ILArrayShape of ILArrayBounds list

    member x.Rank = match x with ILArrayShape l -> l.Length
    static member SingleDimensional = ILArrayShape [(None, None)]
    static member FromRank(n: int) = ILArrayShape (List.init n (fun _ -> (None, None)))

// ============================================================================
// TYPE REFERENCES AND TYPES
// ============================================================================

type ILBoxity =
    | AsObject
    | AsValue

type ILGenericVariance =
    | NonVariant
    | CoVariant
    | ContraVariant

[<Sealed>]
type ILTypeRef(scope: ILScopeRef, enclosing: string list, name: string) =
    static member Create(scope, enclosing, name) = ILTypeRef(scope, enclosing, name)

    member _.Scope = scope
    member _.Enclosing = enclosing
    member _.Name = name

    member x.FullName =
        match enclosing with
        | [] -> name
        | _ -> String.concat "." enclosing + "." + name

    member x.BasicQualifiedName =
        match enclosing with
        | [] -> name
        | _ -> String.concat "+" enclosing + "+" + name

    member x.QualifiedName =
        let basic = x.BasicQualifiedName
        match scope with
        | ILScopeRef.Local -> basic
        | _ -> basic + ", " + scope.QualifiedName

    member internal x.EqualsWithPrimaryScopeRef(primaryScopeRef: ILScopeRef, obj: obj) =
        match obj with
        | :? ILTypeRef as other ->
            x.Name = other.Name &&
            x.Enclosing = other.Enclosing &&
            (x.Scope = other.Scope ||
             (x.Scope = ILScopeRef.PrimaryAssembly && other.Scope = primaryScopeRef) ||
             (other.Scope = ILScopeRef.PrimaryAssembly && x.Scope = primaryScopeRef))
        | _ -> false

    override x.ToString() = x.QualifiedName

    interface System.IComparable with
        member x.CompareTo(obj) =
            match obj with
            | :? ILTypeRef as other ->
                let c = compare x.Name other.Name
                if c <> 0 then c
                else
                    let c = compare x.Enclosing other.Enclosing
                    if c <> 0 then c
                    else compare x.Scope other.Scope
            | _ -> 1

// Forward declarations handled via recursion
type ILGenericArgs = ILType list
and ILTypes = ILType list

and [<StructuralEquality; StructuralComparison>] ILCallingSignature =
    { CallingConv: ILCallingConv
      ArgTypes: ILTypes
      ReturnType: ILType }

and [<Sealed>] ILTypeSpec(typeRef: ILTypeRef, genericArgs: ILGenericArgs) =
    static member Create(typeRef, genericArgs) = ILTypeSpec(typeRef, genericArgs)

    member _.TypeRef = typeRef
    member _.GenericArgs = genericArgs
    member _.Scope = typeRef.Scope
    member _.Enclosing = typeRef.Enclosing
    member _.Name = typeRef.Name
    member _.FullName = typeRef.FullName

    member internal x.EqualsWithPrimaryScopeRef(primaryScopeRef: ILScopeRef, obj: obj) =
        match obj with
        | :? ILTypeSpec as other ->
            typeRef.EqualsWithPrimaryScopeRef(primaryScopeRef, other.TypeRef) &&
            x.GenericArgs = other.GenericArgs
        | _ -> false

    interface System.IComparable with
        member x.CompareTo(obj) =
            match obj with
            | :? ILTypeSpec as other ->
                let c = compare typeRef other.TypeRef
                if c <> 0 then c
                else compare x.GenericArgs other.GenericArgs
            | _ -> 1

and [<RequireQualifiedAccess; StructuralEquality; StructuralComparison>] ILType =
    | Void
    | Array of ILArrayShape * ILType
    | Value of ILTypeSpec
    | Boxed of ILTypeSpec
    | Ptr of ILType
    | Byref of ILType
    | FunctionPointer of ILCallingSignature
    | TypeVar of uint16
    | Modified of bool * ILTypeRef * ILType

    member x.TypeSpec =
        match x with
        | Value ts | Boxed ts -> ts
        | _ -> failwith "TypeSpec: not a nominal type"

    member internal x.Boxity =
        match x with
        | Value _ -> AsValue
        | Boxed _ -> AsObject
        | _ -> AsObject

    member x.TypeRef =
        match x with
        | Value ts | Boxed ts -> ts.TypeRef
        | _ -> failwith "TypeRef: not a nominal type"

    member x.IsNominal =
        match x with
        | Value _ | Boxed _ -> true
        | _ -> false

    member x.GenericArgs =
        match x with
        | Value ts | Boxed ts -> ts.GenericArgs
        | _ -> []

    member x.IsTyvar =
        match x with
        | TypeVar _ -> true
        | _ -> false

    member x.BasicQualifiedName =
        match x with
        | Value ts | Boxed ts -> ts.TypeRef.BasicQualifiedName
        | Array(shape, ety) -> ety.BasicQualifiedName + "[" + String.replicate (shape.Rank - 1) "," + "]"
        | Ptr ety -> ety.BasicQualifiedName + "*"
        | Byref ety -> ety.BasicQualifiedName + "&"
        | _ -> "?"

    member x.QualifiedName =
        match x with
        | Value ts | Boxed ts -> ts.TypeRef.QualifiedName
        | _ -> x.BasicQualifiedName

// ============================================================================
// METHOD AND FIELD REFERENCES
// ============================================================================

[<Sealed>]
type ILMethodRef(declaringTypeRef: ILTypeRef, callingConv: ILCallingConv, name: string,
                 genericArity: int, argTypes: ILTypes, returnType: ILType) =

    static member Create(declaringTypeRef, callingConv, name, genericArity, argTypes, returnType) =
        ILMethodRef(declaringTypeRef, callingConv, name, genericArity, argTypes, returnType)

    member _.DeclaringTypeRef = declaringTypeRef
    member _.CallingConv = callingConv
    member _.Name = name
    member _.GenericArity = genericArity
    member _.ArgCount = argTypes.Length
    member _.ArgTypes = argTypes
    member _.ReturnType = returnType

    member x.GetCallingSignature() =
        { CallingConv = callingConv; ArgTypes = argTypes; ReturnType = returnType }

    interface System.IComparable with
        member x.CompareTo(obj) =
            match obj with
            | :? ILMethodRef as other ->
                let c = compare name other.Name
                if c <> 0 then c
                else compare declaringTypeRef other.DeclaringTypeRef
            | _ -> 1

[<StructuralEquality; StructuralComparison>]
type ILFieldRef =
    { DeclaringTypeRef: ILTypeRef
      Name: string
      Type: ILType }

[<Sealed>]
type ILMethodSpec(declaringType: ILType, methodRef: ILMethodRef, genericArgs: ILGenericArgs) =
    static member Create(declaringType, methodRef, genericArgs) =
        ILMethodSpec(declaringType, methodRef, genericArgs)

    member _.MethodRef = methodRef
    member _.DeclaringType = declaringType
    member _.GenericArgs = genericArgs
    member _.CallingConv = methodRef.CallingConv
    member _.GenericArity = methodRef.GenericArity
    member _.Name = methodRef.Name
    member _.FormalArgTypes = methodRef.ArgTypes
    member _.FormalReturnType = methodRef.ReturnType

type ILFieldSpec =
    { FieldRef: ILFieldRef
      DeclaringType: ILType }

    member x.DeclaringTypeRef = x.FieldRef.DeclaringTypeRef
    member x.Name = x.FieldRef.Name
    member x.FormalType = x.FieldRef.Type
    member x.ActualType = x.FieldRef.Type

// ============================================================================
// IL INSTRUCTIONS - SCAFFOLDING ONLY
// ============================================================================

type internal ILCodeLabel = int

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

[<RequireQualifiedAccess>]
type internal ILReadonlyPrefix =
    | ReadOnly
    | NormalAddress

type internal ILVolatility = | Volatile | Nonvolatile
type internal ILAlignment = | Aligned | Unaligned1 | Unaligned2 | Unaligned4
type internal ILTailcall = | Tailcall | Normalcall

[<RequireQualifiedAccess>]
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

[<RequireQualifiedAccess>]
type ILNativeType =
    | Empty
    | Custom of ILGuid * nativeTypeName: string * custMarshallerName: string * cookieString: byte[]
    | FixedSysString of int32
    | FixedArray of int32
    | Currency
    | LPSTR
    | LPWSTR
    | LPTSTR
    | LPUTF8STR
    | ByValStr
    | TBSTR
    | LPSTRUCT
    | Struct
    | Void
    | Bool
    | Int8
    | Int16
    | Int32
    | Int64
    | Float32
    | Float64
    | UInt8
    | UInt16
    | UInt32
    | UInt64
    | Array of ILNativeType option * (int32 * int32 option) option
    | Int
    | UInt
    | Method
    | AsAny
    | BSTR
    | IUnknown
    | IDispatch
    | Interface
    | Error
    | SafeArray of ILNativeVariant * string option
    | ANSIBSTR
    | VariantBool

and [<RequireQualifiedAccess>] ILNativeVariant =
    | Empty | Null | Variant | Currency | Decimal | Date | BSTR | LPSTR | LPWSTR
    | IUnknown | IDispatch | SafeArray | Error | HRESULT | CArray | UserDefined
    | Record | FileTime | Blob | Stream | Storage | StreamedObject | StoredObject
    | BlobObject | CF | CLSID | Void | Bool | Int8 | Int16 | Int32 | Int64
    | Float32 | Float64 | UInt8 | UInt16 | UInt32 | UInt64 | PTR
    | Array of ILNativeVariant | Vector of ILNativeVariant | Byref of ILNativeVariant
    | Int | UInt

type ILToken =
    | ILToken_type of ILType
    | ILToken_method of ILMethodSpec
    | ILToken_field of ILFieldSpec

type ILConstValue = | I4 of int32 | I8 of int64 | R4 of single | R8 of double

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
// OVERRIDES SPEC
// ============================================================================

[<Sealed>]
type ILOverridesSpec(methodRef: ILMethodRef, declaringType: ILType) =
    member _.MethodRef = methodRef
    member _.DeclaringType = declaringType

// ============================================================================
// MEMBER ACCESS
// ============================================================================

[<RequireQualifiedAccess>]
type ILMemberAccess =
    | Assembly | CompilerControlled | FamilyAndAssembly | FamilyOrAssembly
    | Family | Private | Public

[<RequireQualifiedAccess>]
type ILTypeDefAccess =
    | Public | Private | Nested of ILMemberAccess

// ============================================================================
// STORED ATTRIBUTES - Scaffolding for lazy loading
// ============================================================================

let internal NoMetadataIdx = -1

[<NoEquality; NoComparison>]
type ILAttributesStored =
    | Given of ILAttribute[]
    | Reader of (int32 -> ILAttribute[])

    member x.GetCustomAttrs(idx: int32) =
        match x with
        | Given attrs -> ILAttributes(attrs)
        | Reader f -> ILAttributes(f idx)

and [<Sealed>] ILAttribute(method': ILMethodSpec, data: byte[], elements: ILAttribElem list) =
    new(method', elements) = ILAttribute(method', [||], elements)
    member _.Method = method'
    member _.Data = data
    member _.Elements = elements
    member x.WithMethod(m) = ILAttribute(m, data, elements)

and [<Sealed>] ILAttributes(attrs: ILAttribute[]) =
    static member Empty = ILAttributes([||])
    member _.AsArray() = attrs
    member _.AsList() = Array.toList attrs

and [<RequireQualifiedAccess; StructuralEquality; StructuralComparison>] ILAttribElem =
    | String of string option | Bool of bool | Char of char
    | SByte of int8 | Int16 of int16 | Int32 of int32 | Int64 of int64
    | Byte of uint8 | UInt16 of uint16 | UInt32 of uint32 | UInt64 of uint64
    | Single of single | Double of double | Null
    | Type of ILType option | TypeRef of ILTypeRef option
    | Array of ILType * ILAttribElem list

type ILAttributeNamedArg = string * ILType * bool * ILAttribElem

let storeILCustomAttrs (attrs: ILAttributes) = Given (attrs.AsArray())
let emptyILCustomAttrs = ILAttributes([||])
let mkILCustomAttrsFromArray arr = ILAttributes(arr)
let mkILCustomAttrs l = mkILCustomAttrsFromArray (Array.ofList l)
let emptyILCustomAttrsStored = Given [||]

// ============================================================================
// SECURITY DECLARATIONS - Scaffolding
// ============================================================================

type ILSecurityDecl = ILSecurityDecl of int32 * byte[]

type ILSecurityDecls =
    | ILSecurityDecls of ILSecurityDecl list
    member x.AsList() = match x with ILSecurityDecls l -> l

[<NoEquality; NoComparison>]
type ILSecurityDeclsStored =
    | GivenSecurityDecls of ILSecurityDecl[]
    | ReaderSecurityDecls of (int32 -> ILSecurityDecl[])

    member x.GetSecurityDecls(idx: int32) =
        match x with
        | GivenSecurityDecls decls -> ILSecurityDecls(Array.toList decls)
        | ReaderSecurityDecls f -> ILSecurityDecls(Array.toList (f idx))

let storeILSecurityDecls (decls: ILSecurityDecls) =
    GivenSecurityDecls (Array.ofList (decls.AsList()))

let emptyILSecurityDecls = ILSecurityDecls []
let emptyILSecurityDeclsStored = GivenSecurityDecls [||]

// ============================================================================
// GENERIC PARAMETERS
// ============================================================================

type ILGenericParameterDef =
    { Name: string
      Constraints: ILTypes
      Variance: ILGenericVariance
      HasReferenceTypeConstraint: bool
      HasNotNullableValueTypeConstraint: bool
      HasDefaultConstructorConstraint: bool
      CustomAttrsStored: ILAttributesStored
      MetadataIndex: int32 }

    member x.CustomAttrs = x.CustomAttrsStored.GetCustomAttrs x.MetadataIndex

type ILGenericParameterDefs = ILGenericParameterDef list

// ============================================================================
// PARAMETERS AND RETURNS
// ============================================================================

[<NoEquality; NoComparison>]
type ILParameter =
    { Name: string option
      Type: ILType
      Default: ILFieldInit option
      Marshal: ILNativeType option
      IsIn: bool
      IsOut: bool
      IsOptional: bool
      CustomAttrsStored: ILAttributesStored
      MetadataIndex: int32 }

    member x.CustomAttrs = x.CustomAttrsStored.GetCustomAttrs x.MetadataIndex

type ILParameters = ILParameter list

[<NoEquality; NoComparison>]
type ILReturn =
    { Marshal: ILNativeType option
      Type: ILType
      CustomAttrsStored: ILAttributesStored
      MetadataIndex: int32 }

    member x.CustomAttrs = x.CustomAttrsStored.GetCustomAttrs x.MetadataIndex
    member x.WithCustomAttrs(customAttrs: ILAttributes) =
        { x with CustomAttrsStored = storeILCustomAttrs customAttrs }

// ============================================================================
// METHOD BODY - Scaffolding
// ============================================================================

type InterruptibleLazy<'T> = Lazy<'T>
let notlazy v = lazy v

type ILLocal = { Type: ILType; IsPinned: bool; DebugInfo: (string * int * int) option }
type ILLocals = ILLocal list

type ILExceptionClause =
    | Finally of int * int | Fault of int * int
    | FilterCatch of (int * int) * (int * int) | TypeCatch of ILType * (int * int)

type ILExceptionSpec = { Range: int * int; Clause: ILExceptionClause }
type ILLocalDebugInfo = { Range: int * int; Local: ILLocal }

type ILCode =
    { Labels: Dictionary<ILCodeLabel, int>
      Instrs: ILInstr[]
      Exceptions: ILExceptionSpec list
      Locals: ILLocalDebugInfo list }

type ILSourceMarker =
    { Document: ILSourceDocument
      Line: int; Column: int; EndLine: int; EndColumn: int }

and [<Sealed>] ILSourceDocument(language: ILGuid option, vendor: ILGuid option, documentType: ILGuid option, file: string) =
    static member Create(language, vendor, documentType, file) =
        ILSourceDocument(language, vendor, documentType, file)
    member _.Language = language
    member _.Vendor = vendor
    member _.DocumentType = documentType
    member _.File = file

type ILMethodBody =
    { IsZeroInit: bool; MaxStack: int32; NoInlining: bool; AggressiveInlining: bool
      Locals: ILLocals; Code: ILCode; SourceMarker: ILSourceMarker option }

// NOTE: P/Invoke types removed from FNCS
// FNCS uses Platform.Bindings module pattern (BCL-free), not DllImport/P/Invoke
// See Firefly's native_binding_architecture and platform_conduit_architecture memories

[<RequireQualifiedAccess; StructuralEquality; NoComparison>]
type MethodBody =
    | IL of InterruptibleLazy<ILMethodBody>
    | Abstract | Native | NotAvailable

// ============================================================================
// FIELD DEFINITION
// ============================================================================

[<Sealed; NoComparison; NoEquality>]
type ILFieldDef(name: string, fieldType: ILType, attributes: FieldAttributes,
                data: byte[] option, literalValue: ILFieldInit option,
                offset: int32 option, marshal: ILNativeType option,
                customAttrsStored: ILAttributesStored, metadataIndex: int32) =

    new(name, fieldType, attributes, data, literalValue, offset, marshal, customAttrs) =
        ILFieldDef(name, fieldType, attributes, data, literalValue, offset, marshal, storeILCustomAttrs customAttrs, NoMetadataIdx)

    member _.Name = name
    member _.FieldType = fieldType
    member _.Attributes = attributes
    member _.Data = data
    member _.LiteralValue = literalValue
    member _.Offset = offset
    member _.Marshal = marshal
    member _.CustomAttrsStored = customAttrsStored
    member x.CustomAttrs = customAttrsStored.GetCustomAttrs x.MetadataIndex
    member _.MetadataIndex = metadataIndex

    member x.IsStatic = x.Attributes &&& FieldAttributes.Static <> enum 0
    member x.IsSpecialName = x.Attributes &&& FieldAttributes.SpecialName <> enum 0
    member x.IsLiteral = x.Attributes &&& FieldAttributes.Literal <> enum 0
    member x.NotSerialized = x.Attributes &&& FieldAttributes.NotSerialized <> enum 0
    member x.IsInitOnly = x.Attributes &&& FieldAttributes.InitOnly <> enum 0

    member x.Access =
        let a = x.Attributes &&& FieldAttributes.FieldAccessMask
        if a = FieldAttributes.Public then ILMemberAccess.Public
        elif a = FieldAttributes.Private then ILMemberAccess.Private
        elif a = FieldAttributes.Family then ILMemberAccess.Family
        elif a = FieldAttributes.Assembly then ILMemberAccess.Assembly
        elif a = FieldAttributes.FamORAssem then ILMemberAccess.FamilyOrAssembly
        elif a = FieldAttributes.FamANDAssem then ILMemberAccess.FamilyAndAssembly
        else ILMemberAccess.CompilerControlled

    member x.With(?name, ?fieldType, ?attributes, ?data, ?literalValue, ?offset, ?marshal, ?customAttrs) =
        ILFieldDef(
            defaultArg name x.Name, defaultArg fieldType x.FieldType, defaultArg attributes x.Attributes,
            defaultArg data x.Data, defaultArg literalValue x.LiteralValue, defaultArg offset x.Offset,
            defaultArg marshal x.Marshal, defaultArg customAttrs x.CustomAttrs)

[<NoEquality; NoComparison>]
type ILFieldDefs(fields: ILFieldDef[]) =
    member _.AsList() = Array.toList fields
    member _.LookupByName(s: string) = fields |> Array.filter (fun f -> f.Name = s) |> Array.toList

// ============================================================================
// METHOD DEFINITION
// ============================================================================

[<Sealed; NoComparison; NoEquality>]
type ILMethodDef(name: string, attributes: MethodAttributes, implAttributes: MethodImplAttributes,
                 callingConv: ILCallingConv, parameters: ILParameters, ret: ILReturn,
                 body: InterruptibleLazy<MethodBody>, isEntryPoint: bool,
                 genericParams: ILGenericParameterDefs, securityDeclsStored: ILSecurityDeclsStored,
                 customAttrsStored: ILAttributesStored, metadataIndex: int32) =

    new(name, attributes, implAttributes, callingConv, parameters, ret, body, isEntryPoint, genericParams, securityDecls, customAttrs) =
        ILMethodDef(name, attributes, implAttributes, callingConv, parameters, ret, body, isEntryPoint, genericParams,
            storeILSecurityDecls securityDecls, storeILCustomAttrs customAttrs, NoMetadataIdx)

    member _.Name = name
    member _.Attributes = attributes
    member _.ImplAttributes = implAttributes
    member _.CallingConv = callingConv
    member _.Parameters = parameters
    member _.Return = ret
    member _.Body = body.Value
    member _.IsEntryPoint = isEntryPoint
    member _.GenericParams = genericParams
    member _.SecurityDeclsStored = securityDeclsStored
    member x.SecurityDecls = securityDeclsStored.GetSecurityDecls(x.MetadataIndex)
    member _.CustomAttrsStored = customAttrsStored
    member x.CustomAttrs = customAttrsStored.GetCustomAttrs(x.MetadataIndex)
    member _.MetadataIndex = metadataIndex

    member x.IsStatic = x.Attributes &&& MethodAttributes.Static <> enum 0
    member x.IsAbstract = x.Attributes &&& MethodAttributes.Abstract <> enum 0
    member x.IsFinal = x.Attributes &&& MethodAttributes.Final <> enum 0
    member x.IsVirtual = x.Attributes &&& MethodAttributes.Virtual <> enum 0
    member x.IsHideBySig = x.Attributes &&& MethodAttributes.HideBySig <> enum 0
    member x.IsSpecialName = x.Attributes &&& MethodAttributes.SpecialName <> enum 0
    member x.IsNewSlot = x.Attributes &&& MethodAttributes.NewSlot <> enum 0

    member x.Access =
        let a = x.Attributes &&& MethodAttributes.MemberAccessMask
        if a = MethodAttributes.Public then ILMemberAccess.Public
        elif a = MethodAttributes.Private then ILMemberAccess.Private
        elif a = MethodAttributes.Family then ILMemberAccess.Family
        elif a = MethodAttributes.Assembly then ILMemberAccess.Assembly
        elif a = MethodAttributes.FamORAssem then ILMemberAccess.FamilyOrAssembly
        elif a = MethodAttributes.FamANDAssem then ILMemberAccess.FamilyAndAssembly
        else ILMemberAccess.CompilerControlled

    member x.ParameterTypes = x.Parameters |> List.map (fun p -> p.Type)
    member x.GetCallingSignature() =
        { CallingConv = callingConv; ArgTypes = x.ParameterTypes; ReturnType = ret.Type }

    member x.With(?name, ?attributes, ?implAttributes, ?callingConv, ?parameters, ?ret, ?body, ?isEntryPoint, ?genericParams, ?securityDecls, ?customAttrs) =
        ILMethodDef(
            defaultArg name x.Name, defaultArg attributes x.Attributes, defaultArg implAttributes x.ImplAttributes,
            defaultArg callingConv x.CallingConv, defaultArg parameters x.Parameters, defaultArg ret x.Return,
            defaultArg body (notlazy x.Body), defaultArg isEntryPoint x.IsEntryPoint, defaultArg genericParams x.GenericParams,
            defaultArg securityDecls x.SecurityDecls, defaultArg customAttrs x.CustomAttrs)

[<NoEquality; NoComparison>]
type ILMethodDefs(methods: ILMethodDef[]) =
    member _.AsArray() = methods
    member _.AsList() = Array.toList methods
    member _.FindByName(nm: string) = methods |> Array.filter (fun m -> m.Name = nm) |> Array.toList
    member x.FindByNameAndArity(nm: string, arity: int) =
        x.FindByName nm |> List.filter (fun m -> m.Parameters.Length = arity)

    interface IEnumerable<ILMethodDef> with
        member _.GetEnumerator() = (methods :> IEnumerable<ILMethodDef>).GetEnumerator()
    interface System.Collections.IEnumerable with
        member _.GetEnumerator() = (methods :> System.Collections.IEnumerable).GetEnumerator()

// ============================================================================
// PROPERTY DEFINITION
// ============================================================================

[<Sealed; NoComparison; NoEquality>]
type ILPropertyDef(name: string, attributes: PropertyAttributes, setMethod: ILMethodRef option,
                   getMethod: ILMethodRef option, callingConv: ILThisConvention, propertyType: ILType,
                   init: ILFieldInit option, args: ILTypes, customAttrsStored: ILAttributesStored, metadataIndex: int32) =

    new(name, attributes, setMethod, getMethod, callingConv, propertyType, init, args, customAttrs) =
        ILPropertyDef(name, attributes, setMethod, getMethod, callingConv, propertyType, init, args, storeILCustomAttrs customAttrs, NoMetadataIdx)

    member _.Name = name
    member _.Attributes = attributes
    member _.GetMethod = getMethod
    member _.SetMethod = setMethod
    member _.CallingConv = callingConv
    member _.PropertyType = propertyType
    member _.Init = init
    member _.Args = args
    member _.CustomAttrsStored = customAttrsStored
    member x.CustomAttrs = customAttrsStored.GetCustomAttrs(x.MetadataIndex)
    member _.MetadataIndex = metadataIndex

    member x.IsSpecialName = x.Attributes &&& PropertyAttributes.SpecialName <> enum 0
    member x.IsRTSpecialName = x.Attributes &&& PropertyAttributes.RTSpecialName <> enum 0

    member x.With(?name, ?attributes, ?setMethod, ?getMethod, ?callingConv, ?propertyType, ?init, ?args, ?customAttrs) =
        ILPropertyDef(
            defaultArg name x.Name, defaultArg attributes x.Attributes, defaultArg setMethod x.SetMethod,
            defaultArg getMethod x.GetMethod, defaultArg callingConv x.CallingConv, defaultArg propertyType x.PropertyType,
            defaultArg init x.Init, defaultArg args x.Args, defaultArg customAttrs x.CustomAttrs)

[<NoEquality; NoComparison>]
type ILPropertyDefs(properties: ILPropertyDef[]) =
    member _.AsList() = Array.toList properties
    member _.LookupByName(s: string) = properties |> Array.filter (fun p -> p.Name = s) |> Array.toList

// ============================================================================
// EVENT DEFINITION
// ============================================================================

[<NoComparison; NoEquality>]
type ILEventDef(eventType: ILType option, name: string, attributes: EventAttributes,
                addMethod: ILMethodRef, removeMethod: ILMethodRef, fireMethod: ILMethodRef option,
                otherMethods: ILMethodRef list, customAttrsStored: ILAttributesStored, metadataIndex: int32) =

    new(eventType, name, attributes, addMethod, removeMethod, fireMethod, otherMethods, customAttrs) =
        ILEventDef(eventType, name, attributes, addMethod, removeMethod, fireMethod, otherMethods, storeILCustomAttrs customAttrs, NoMetadataIdx)

    member _.EventType = eventType
    member _.Name = name
    member _.Attributes = attributes
    member _.AddMethod = addMethod
    member _.RemoveMethod = removeMethod
    member _.FireMethod = fireMethod
    member _.OtherMethods = otherMethods
    member _.CustomAttrsStored = customAttrsStored
    member x.CustomAttrs = customAttrsStored.GetCustomAttrs(x.MetadataIndex)
    member _.MetadataIndex = metadataIndex

    member x.IsSpecialName = x.Attributes &&& EventAttributes.SpecialName <> enum 0
    member x.IsRTSpecialName = x.Attributes &&& EventAttributes.RTSpecialName <> enum 0

[<NoEquality; NoComparison>]
type ILEventDefs(events: ILEventDef[]) =
    member _.AsList() = Array.toList events
    member _.LookupByName(s: string) = events |> Array.filter (fun e -> e.Name = s) |> Array.toList

// ============================================================================
// METHOD IMPL
// ============================================================================

type ILMethodImplDef = { Overrides: ILOverridesSpec; OverrideBy: ILMethodSpec }

type ILMethodImplDefs(impls: ILMethodImplDef list) =
    member _.AsList() = impls

// ============================================================================
// TYPE DEF LAYOUT
// ============================================================================

[<RequireQualifiedAccess>]
type ILTypeDefLayout =
    | Auto | Sequential of ILTypeDefLayoutInfo | Explicit of ILTypeDefLayoutInfo

and ILTypeDefLayoutInfo = { Size: int32 option; Pack: uint16 option }

[<RequireQualifiedAccess>]
type ILTypeInit = | BeforeField | OnAny

// ============================================================================
// TYPE DEFINITION
// ============================================================================

[<Sealed>]
type ILTypeDef(name: string, attributes: TypeAttributes, layout: ILTypeDefLayout,
               implements: ILTypes, genericParams: ILGenericParameterDefs, extends: ILType option,
               methods: ILMethodDefs, nestedTypes: ILTypeDefs, fields: ILFieldDefs,
               methodImpls: ILMethodImplDefs, events: ILEventDefs, properties: ILPropertyDefs,
               isKnownToBeAttribute: bool, securityDeclsStored: ILSecurityDeclsStored,
               customAttrsStored: ILAttributesStored, metadataIndex: int32) =

    new(name, attributes, layout, implements, genericParams, extends, methods, nestedTypes, fields, methodImpls, events, properties, isKnownToBeAttribute, securityDecls, customAttrs) =
        ILTypeDef(name, attributes, layout, implements, genericParams, extends, methods, nestedTypes, fields, methodImpls, events, properties, isKnownToBeAttribute, storeILSecurityDecls securityDecls, storeILCustomAttrs customAttrs, NoMetadataIdx)

    member _.Name = name
    member _.Attributes = attributes
    member _.Layout = layout
    member _.Implements = implements
    member _.GenericParams = genericParams
    member _.Extends = extends
    member _.Methods = methods
    member _.NestedTypes = nestedTypes
    member _.Fields = fields
    member _.MethodImpls = methodImpls
    member _.Events = events
    member _.Properties = properties
    member _.IsKnownToBeAttribute = isKnownToBeAttribute
    member _.SecurityDeclsStored = securityDeclsStored
    member x.SecurityDecls = securityDeclsStored.GetSecurityDecls(x.MetadataIndex)
    member _.CustomAttrsStored = customAttrsStored
    member x.CustomAttrs = customAttrsStored.GetCustomAttrs(x.MetadataIndex)
    member _.MetadataIndex = metadataIndex

    member x.IsClass = x.Attributes &&& TypeAttributes.ClassSemanticsMask = TypeAttributes.Class
    member x.IsInterface = x.Attributes &&& TypeAttributes.ClassSemanticsMask = TypeAttributes.Interface
    member x.IsStruct = x.IsClass && x.IsSealed && x.Extends.IsSome
    member x.IsEnum = x.IsClass && x.IsSealed
    member x.IsDelegate = x.IsClass && x.Extends.IsSome
    member x.IsSealed = x.Attributes &&& TypeAttributes.Sealed <> enum 0
    member x.IsAbstract = x.Attributes &&& TypeAttributes.Abstract <> enum 0
    member x.IsSerializable = x.Attributes &&& TypeAttributes.Serializable <> enum 0
    member x.IsStructOrEnum = x.IsStruct || x.IsEnum

    member x.Access =
        let a = x.Attributes &&& TypeAttributes.VisibilityMask
        if a = TypeAttributes.Public then ILTypeDefAccess.Public
        elif a = TypeAttributes.NotPublic then ILTypeDefAccess.Private
        elif a = TypeAttributes.NestedPublic then ILTypeDefAccess.Nested ILMemberAccess.Public
        elif a = TypeAttributes.NestedPrivate then ILTypeDefAccess.Nested ILMemberAccess.Private
        elif a = TypeAttributes.NestedFamily then ILTypeDefAccess.Nested ILMemberAccess.Family
        elif a = TypeAttributes.NestedAssembly then ILTypeDefAccess.Nested ILMemberAccess.Assembly
        elif a = TypeAttributes.NestedFamORAssem then ILTypeDefAccess.Nested ILMemberAccess.FamilyOrAssembly
        elif a = TypeAttributes.NestedFamANDAssem then ILTypeDefAccess.Nested ILMemberAccess.FamilyAndAssembly
        else ILTypeDefAccess.Private

    member x.With(?name, ?attributes, ?layout, ?implements, ?genericParams, ?extends, ?methods, ?nestedTypes, ?fields, ?methodImpls, ?events, ?properties, ?customAttrs, ?securityDecls) =
        ILTypeDef(
            defaultArg name x.Name, defaultArg attributes x.Attributes, defaultArg layout x.Layout,
            defaultArg implements x.Implements, defaultArg genericParams x.GenericParams, defaultArg extends x.Extends,
            defaultArg methods x.Methods, defaultArg nestedTypes x.NestedTypes, defaultArg fields x.Fields,
            defaultArg methodImpls x.MethodImpls, defaultArg events x.Events, defaultArg properties x.Properties,
            x.IsKnownToBeAttribute, defaultArg securityDecls x.SecurityDecls, defaultArg customAttrs x.CustomAttrs)

and [<Sealed>] ILTypeDefs(defs: ILTypeDef[]) =
    member _.AsArray() = defs
    member _.AsList() = Array.toList defs
    member _.FindByName(name: string) = defs |> Array.find (fun d -> d.Name = name)
    member _.TryFindByName(name: string) = defs |> Array.tryFind (fun d -> d.Name = name)

    interface IEnumerable<ILTypeDef> with
        member _.GetEnumerator() = (defs :> IEnumerable<ILTypeDef>).GetEnumerator()
    interface System.Collections.IEnumerable with
        member _.GetEnumerator() = (defs :> System.Collections.IEnumerable).GetEnumerator()

let mkILTypeDefs l = ILTypeDefs(Array.ofList l)
let mkILTypeDefsFromArray arr = ILTypeDefs(arr)
let emptyILTypeDefs = ILTypeDefs([||])

// ============================================================================
// MODULE AND ASSEMBLY DEFINITIONS
// ============================================================================

type ILExportedTypeOrForwarder =
    { ScopeRef: ILScopeRef; Name: string; Attributes: TypeAttributes
      Nested: ILNestedExportedTypesAndForwarders; CustomAttrsStored: ILAttributesStored; MetadataIndex: int32 }
    member x.Access =
        let a = x.Attributes &&& TypeAttributes.VisibilityMask
        if a = TypeAttributes.Public then ILTypeDefAccess.Public else ILTypeDefAccess.Private
    member x.CustomAttrs = x.CustomAttrsStored.GetCustomAttrs x.MetadataIndex
    member x.IsForwarder = x.Attributes &&& enum 0x00200000 <> enum 0

and [<Sealed>] ILNestedExportedTypesAndForwarders(nested: ILExportedTypeOrForwarder[]) =
    member _.AsList() = Array.toList nested

and [<Sealed>] ILExportedTypesAndForwarders(entries: ILExportedTypeOrForwarder[]) =
    member _.AsList() = Array.toList entries
    member _.TryFindByName(nm: string) = entries |> Array.tryFind (fun e -> e.Name = nm)

type ILResourceAccess = | Public | Private
type ByteStorage = unit -> byte[]
type ILResourceLocation = | Local of ByteStorage | File of ILModuleRef * int32 | Assembly of ILAssemblyRef

type ILResource =
    { Name: string; Location: ILResourceLocation; Access: ILResourceAccess
      CustomAttrsStored: ILAttributesStored; MetadataIndex: int32 }
    member x.CustomAttrs = x.CustomAttrsStored.GetCustomAttrs x.MetadataIndex

[<Sealed>]
type ILResources(resources: ILResource[]) =
    member _.AsList() = Array.toList resources

type ILAssemblyLongevity = | Unset | Library | PlatformAppDomain | PlatformProcess | PlatformSystem

type ILAssemblyManifest =
    { Name: string; AuxModuleHashAlgorithm: int32; SecurityDeclsStored: ILSecurityDeclsStored
      PublicKey: byte[] option; Version: ILVersionInfo option; Locale: string option
      CustomAttrsStored: ILAttributesStored; AssemblyLongevity: ILAssemblyLongevity
      DisableJitOptimizations: bool; JitTracking: bool; IgnoreSymbolStoreSequencePoints: bool
      Retargetable: bool; ExportedTypes: ILExportedTypesAndForwarders
      EntrypointElsewhere: ILModuleRef option; MetadataIndex: int32 }

    member x.SecurityDecls = x.SecurityDeclsStored.GetSecurityDecls x.MetadataIndex
    member x.CustomAttrs = x.CustomAttrsStored.GetCustomAttrs x.MetadataIndex

[<RequireQualifiedAccess>]
type ILNativeResource =
    | In of fileName: string * linkedResourceBase: int * linkedResourceStart: int * linkedResourceLength: int
    | Out of unlinkedResources: byte[]

[<Sealed>]
type ILModuleDef(moduleName: string, manifest: ILAssemblyManifest option, typeDefs: ILTypeDefs,
                 subsystemVersion: int * int, useHighEntropyVA: bool, subSystemFlags: int32,
                 isDLL: bool, isILOnly: bool, platform: ILPlatform option, stackReserveSize: int32 option,
                 is32bit: bool, is32bitPreferred: bool, is64bit: bool, virtualAlignment: int32,
                 physicalAlignment: int32, imageBase: int32, metadataVersion: string,
                 resources: ILResources, nativeResources: ILNativeResource list,
                 customAttrsStored: ILAttributesStored, metadataIndex: int32) =

    new(moduleName, manifest, typeDefs, subsystemVersion, useHighEntropyVA, subSystemFlags, isDLL, isILOnly, platform, stackReserveSize, is32bit, is32bitPreferred, is64bit, virtualAlignment, physicalAlignment, imageBase, metadataVersion, resources, nativeResources, customAttrs) =
        ILModuleDef(moduleName, manifest, typeDefs, subsystemVersion, useHighEntropyVA, subSystemFlags, isDLL, isILOnly, platform, stackReserveSize, is32bit, is32bitPreferred, is64bit, virtualAlignment, physicalAlignment, imageBase, metadataVersion, resources, nativeResources, storeILCustomAttrs customAttrs, NoMetadataIdx)

    member _.Name = moduleName
    member _.Manifest = manifest
    member _.TypeDefs = typeDefs
    member _.SubsystemVersion = subsystemVersion
    member _.UseHighEntropyVA = useHighEntropyVA
    member _.SubSystemFlags = subSystemFlags
    member _.IsDLL = isDLL
    member _.IsILOnly = isILOnly
    member _.Platform = platform
    member _.StackReserveSize = stackReserveSize
    member _.Is32Bit = is32bit
    member _.Is32BitPreferred = is32bitPreferred
    member _.Is64Bit = is64bit
    member _.VirtualAlignment = virtualAlignment
    member _.PhysicalAlignment = physicalAlignment
    member _.ImageBase = imageBase
    member _.MetadataVersion = metadataVersion
    member _.Resources = resources
    member _.NativeResources = nativeResources
    member _.CustomAttrsStored = customAttrsStored
    member x.CustomAttrs = customAttrsStored.GetCustomAttrs(x.MetadataIndex)
    member _.MetadataIndex = metadataIndex

    member x.ManifestOfAssembly = match manifest with | Some m -> m | None -> failwith "no manifest"
    member x.HasManifest = manifest.IsSome

    /// Create an empty module (scaffolding for FNCS)
    static member Empty(name: string, typeDefs: ILTypeDefs) =
        ILModuleDef(name, None, typeDefs, (0, 0), false, 0, false, true, None, None,
                    false, false, false, 0, 0, 0, "", ILResources([||]), [],
                    emptyILCustomAttrsStored, NoMetadataIdx)

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

let mkSimpleAssemblyRef (name: string) =
    ILAssemblyRef.Create(name, None, None, false, None, None)

let mkILTyRef (scope: ILScopeRef, name: string) =
    let parts = name.Split('.')
    let enclosing = if parts.Length > 1 then Array.toList parts.[0..parts.Length-2] else []
    let typeName = parts.[parts.Length - 1]
    ILTypeRef.Create(scope, enclosing, typeName)

let mkILTyRefInTyRef (tref: ILTypeRef, name: string) =
    ILTypeRef.Create(tref.Scope, tref.Enclosing @ [tref.Name], name)

let mkILTySpec (tref: ILTypeRef, inst: ILGenericArgs) = ILTypeSpec.Create(tref, inst)
let mkILNonGenericTySpec tref = mkILTySpec(tref, [])
let mkILBoxedType (tspec: ILTypeSpec) = ILType.Boxed tspec
let mkILValueType (tspec: ILTypeSpec) = ILType.Value tspec
let mkILNonGenericBoxedTy (tref: ILTypeRef) = ILType.Boxed(ILTypeSpec.Create(tref, []))
let mkILNonGenericValueTy (tref: ILTypeRef) = ILType.Value(ILTypeSpec.Create(tref, []))

let mkILTy boxed tspec =
    match boxed with
    | AsObject -> mkILBoxedType tspec
    | AsValue -> mkILValueType tspec

let mkILNamedTy boxed tref inst = mkILTy boxed (ILTypeSpec.Create(tref, inst))
let mkILTyvarTy (tv: uint16) = ILType.TypeVar tv

let mkILCustomAttribute (tref: ILTypeRef, argTypes: ILType list, elements: ILAttribElem list, _namedArgs: ILAttributeNamedArg list) =
    let mref = ILMethodRef.Create(tref, ILCallingConv.Instance, ".ctor", 0, argTypes, ILType.Void)
    let mspec = ILMethodSpec.Create(ILType.Boxed(ILTypeSpec.Create(tref, [])), mref, [])
    ILAttribute(mspec, elements)

let mkRefForNestedILTypeDef (scope: ILScopeRef) (enc: ILTypeDef list, tdef: ILTypeDef) =
    let enclosing = enc |> List.map (fun td -> td.Name)
    ILTypeRef.Create(scope, enclosing, tdef.Name)

let mkILFieldSpec (tref: ILFieldRef, dt: ILType) = { FieldRef = tref; DeclaringType = dt }
let mkILFieldSpecInTy (ty: ILType, nm: string, fty: ILType) =
    mkILFieldSpec ({ DeclaringTypeRef = ty.TypeRef; Name = nm; Type = fty }, ty)

let mkILMethRef (tref: ILTypeRef, cc: ILCallingConv, nm: string, garity: int, args: ILTypes, ret: ILType) =
    ILMethodRef.Create(tref, cc, nm, garity, args, ret)

let mkILMethSpecInTy (ty: ILType, cc: ILCallingConv, nm: string, args: ILTypes, ret: ILType, inst: ILGenericArgs) =
    let mref = mkILMethRef(ty.TypeRef, cc, nm, inst.Length, args, ret)
    ILMethodSpec.Create(ty, mref, inst)

let mkILNonGenericMethSpecInTy (ty: ILType, cc: ILCallingConv, nm: string, args: ILTypes, ret: ILType) =
    mkILMethSpecInTy(ty, cc, nm, args, ret, [])

let mkILInstanceMethSpecInTy (ty: ILType, nm: string, args: ILTypes, ret: ILType, inst: ILGenericArgs) =
    mkILMethSpecInTy(ty, ILCallingConv.Instance, nm, args, ret, inst)

let mkILNonGenericInstanceMethSpecInTy (ty: ILType, nm: string, args: ILTypes, ret: ILType) =
    mkILInstanceMethSpecInTy(ty, nm, args, ret, [])

let mkILStaticMethSpecInTy (ty: ILType, nm: string, args: ILTypes, ret: ILType, inst: ILGenericArgs) =
    mkILMethSpecInTy(ty, ILCallingConv.Static, nm, args, ret, inst)

let mkILNonGenericStaticMethSpecInTy (ty: ILType, nm: string, args: ILTypes, ret: ILType) =
    mkILStaticMethSpecInTy(ty, nm, args, ret, [])

// ============================================================================
// DEBUG INFO
// ============================================================================

[<Sealed>]
type internal ILDebugPoint(document: ILSourceDocument, line: int, column: int, endLine: int, endColumn: int) =
    static member Create(document, line, column, endLine, endColumn) =
        ILDebugPoint(document, line, column, endLine, endColumn)
    member _.Document = document
    member _.Line = line
    member _.Column = column
    member _.EndLine = endLine
    member _.EndColumn = endColumn

// ============================================================================
// INTERFACE IMPLEMENTATION
// ============================================================================

type InterfaceImpl =
    { Idx: int
      Type: ILType
      mutable CustomAttrsStored: ILAttributesStored }

    member x.CustomAttrs = x.CustomAttrsStored.GetCustomAttrs x.Idx

    static member Create(ilType: ILType, customAttrsStored: ILAttributesStored) =
        { Idx = 0; Type = ilType; CustomAttrsStored = customAttrsStored }

    static member Create(ilType: ILType) =
        { Idx = 0; Type = ilType; CustomAttrsStored = emptyILCustomAttrsStored }

// ============================================================================
// IL INSTRUCTION HELPERS
// ============================================================================
// Helpers for creating IL instructions. Used by type checking to represent
// operations in the typed tree (mkAsmExpr). These are NOT BCL dependencies -
// they're IL instruction constructors.

let internal mkNormalCall mspec = I_call(Normalcall, mspec, None)
let internal mkNormalCallvirt mspec = I_callvirt(Normalcall, mspec, None)
let internal mkNormalNewobj mspec = I_newobj(mspec, None)
let internal mkNormalStfld fspec = I_stfld(Aligned, Nonvolatile, fspec)
let internal mkNormalStsfld fspec = I_stsfld(Nonvolatile, fspec)
let internal mkNormalLdsfld fspec = I_ldsfld(Nonvolatile, fspec)
let internal mkNormalLdfld fspec = I_ldfld(Aligned, Nonvolatile, fspec)
let internal mkNormalLdflda fspec = I_ldflda fspec
let internal mkNormalLdobj dt = I_ldobj(Aligned, Nonvolatile, dt)
let internal mkNormalStobj dt = I_stobj(Aligned, Nonvolatile, dt)

let internal mkLdarg0 = AI_ldarg 0us
let internal mkLdarg (n: uint16) = AI_ldarg n

// ============================================================================
// NATIVE TYPE GLOBALS
// ============================================================================
// FNCS defines the native type universe. Standard F# type names, native semantics.
// No BCL. No obj. No boxing.

[<Sealed>]
type internal ILGlobals(primaryAssemblyName: string, fsharpCoreAssemblyScopeRef: ILScopeRef) =
    let scope = ILScopeRef.Assembly (mkSimpleAssemblyRef primaryAssemblyName)
    let mkValTy name = mkILNonGenericValueTy (mkILTyRef(scope, name))

    member _.primaryAssemblyName = primaryAssemblyName
    member _.fsharpCoreAssemblyScopeRef = fsharpCoreAssemblyScopeRef

    // Native primitive types
    member _.typ_String = mkValTy "string"
    member _.typ_Bool = mkValTy "bool"
    member _.typ_Char = mkValTy "char"
    member _.typ_SByte = mkValTy "sbyte"
    member _.typ_Int16 = mkValTy "int16"
    member _.typ_Int32 = mkValTy "int32"
    member _.typ_Int64 = mkValTy "int64"
    member _.typ_Byte = mkValTy "byte"
    member _.typ_UInt16 = mkValTy "uint16"
    member _.typ_UInt32 = mkValTy "uint32"
    member _.typ_UInt64 = mkValTy "uint64"
    member _.typ_Single = mkValTy "float32"
    member _.typ_Double = mkValTy "float"
    member _.typ_IntPtr = mkValTy "nativeint"
    member _.typ_UIntPtr = mkValTy "unativeint"

    // Fallback type for inline IL error handling (inline IL not supported in native compilation)
    // Returns unit type as a safe fallback
    member _.typ_Object = ILType.Void

    static member Create(primaryAssemblyName, fsharpCoreAssemblyScopeRef) =
        ILGlobals(primaryAssemblyName, fsharpCoreAssemblyScopeRef)

// Global instance for error fallbacks (used by ParseHelpers for inline IL errors)
let internal PrimaryAssemblyILGlobals =
    ILGlobals.Create("native", ILScopeRef.Local)
