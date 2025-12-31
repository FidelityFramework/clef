// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.
// Copyright (c) SpeakEZ, Inc.  All Rights Reserved.  Native scaffolding for FNCS.

/// IL Binary Reader scaffolding for FNCS.
/// In FCS, this reads .NET assemblies. In FNCS, this is minimal scaffolding.
/// Native compilation uses different metadata sources.

module FSharp.Compiler.AbstractIL.ILBinaryReader

open System
open System.IO
open FSharp.Compiler.AbstractIL.IL

/// Metadata snapshot for incremental checking
type ILReaderMetadataSnapshot = obj * nativeint * int

/// Try to get a metadata snapshot
type ILReaderTryGetMetadataSnapshot = string * DateTime -> ILReaderMetadataSnapshot option

/// Options for reading IL modules
type ILReaderOptions =
    { metadataOnly: bool
      reduceMemoryUsage: bool
      pdbDirPath: string option
      tryGetMetadataSnapshot: ILReaderTryGetMetadataSnapshot }

/// IL module reader - scaffolding for FNCS
/// Native compilation doesn't read .NET assemblies in the same way.
[<Sealed>]
type ILModuleReader(moduleDef: ILModuleDef, assemblyRefs: ILAssemblyRef list) =
    member _.ILModuleDef = moduleDef
    member _.ILAssemblyRefs = assemblyRefs

    interface IDisposable with
        member _.Dispose() = ()

/// Create a module reader (scaffolding - returns empty module)
let OpenILModuleReader (_fileName: string) (_options: ILReaderOptions) : ILModuleReader =
    // In FNCS, we don't actually read .NET assemblies
    // This scaffolding returns an empty module
    let emptyModule = ILModuleDef.Empty("empty", ILTypeDefs([||]))
    ILModuleReader(emptyModule, [])

/// Default metadata snapshot getter (always returns None)
let defaultTryGetMetadataSnapshot : ILReaderTryGetMetadataSnapshot =
    fun _ -> None
