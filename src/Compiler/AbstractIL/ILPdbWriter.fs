// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.
// Copyright (c) SpeakEZ, Inc.  All Rights Reserved.  Native scaffolding for FNCS.

/// PDB Writer scaffolding for FNCS.
/// Native compilation uses DWARF debug info, not PDB.
/// This is minimal scaffolding.

module FSharp.Compiler.AbstractIL.ILPdbWriter

/// PDB document data (scaffolding)
type PdbDocumentData =
    { File: string
      Guid: byte[]
      Vendor: byte[]
      Type: byte[] }

/// Get an empty PDB data representation
let getEmptyPdbData() = None
