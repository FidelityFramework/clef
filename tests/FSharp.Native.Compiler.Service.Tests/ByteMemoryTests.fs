// Copyright (c) Microsoft Corporation.  All Rights Reserved.  See License.txt in the project root for license information.
namespace FSharp.Native.Compiler.Service.Tests

open Xunit
open FSharp.Test

module ByteMemoryTests =
    open FSharp.Native.Compiler.IO

    [<Fact>]
    let ``ByteMemory.CreateMemoryMappedFile succeeds with byte length of zero`` () =

        let memory = ByteMemory.Empty.AsReadOnly()
        let newMemory = ByteStorage.FromByteMemoryAndCopy(memory, useBackingMemoryMappedFile = true).GetByteMemory()
        Assert.shouldBe 0 newMemory.Length
