// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.
// Copyright (c) SpeakEZ, Inc.  All Rights Reserved.  Native scaffolding for FNCS.

/// ILX Types scaffolding for FNCS.
/// ILX was an extended IL representation for F#-specific constructs.
/// FNCS provides minimal scaffolding since we don't emit IL.

module FSharp.Native.Compiler.AbstractIL.ILX.Types

open FSharp.Native.Compiler.AbstractIL.IL

/// Reference to an ILX union representation.
/// In FCS, this held information about how to compile discriminated unions to IL.
/// In FNCS, this is scaffolding only - native compilation handles unions differently.
[<Sealed>]
type IlxUnionRef(boxity: ILBoxity, typeRef: ILTypeRef, alternatives: string[], nullPermitted: bool) =
    member _.Boxity = boxity
    member _.TypeRef = typeRef
    member _.Alternatives = alternatives
    member _.NullPermitted = nullPermitted

    static member Create(boxity, typeRef, alternatives, nullPermitted) =
        IlxUnionRef(boxity, typeRef, alternatives, nullPermitted)
