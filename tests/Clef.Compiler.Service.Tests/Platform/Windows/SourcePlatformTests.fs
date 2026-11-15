namespace Clef.Compiler.Service.Tests.Platform.Windows

open Xunit
open Clef.Compiler.Service.Tests
open Clef.Compiler.NativeService
open Clef.Compiler.NativeTypedTree.NativeTypes
open Clef.Compiler.PSGSaturation.SemanticGraph

module private SourceLoading =
    let check metadata library =
        let authority =
            SourcePlatformFixture.authority
                .Replace("Os = \"linux\"", "Os = \"windows\"")
                .Replace("Runtime = \"freestanding\"", "Runtime = \"win32\"")
                .Replace("x86_64-unknown-linux-gnu", "x86_64-pc-windows-msvc")
                .Replace("Surfaces = [| { Endpoints = [| write |] } |]", "Surfaces = [||]")
        let contract = """
type ProcessLinkContract = { Identity: string; Version: string; Source: string; Library: string; Runtime: string; Os: string; Arch: string; LoadAt: string; LiveUntil: string; Unloading: string; ExportedLibrary: string }
let loading: ProcessLinkContract = {
    Identity = "windows-source-loading-test"; Version = "1"; Source = "WriteAuthority.loading"
    Library = "LIBRARY"; Runtime = "win32"; Os = "windows"; Arch = "x86_64"
    LoadAt = "ProcessStartup"; LiveUntil = "ProcessTermination"
    Unloading = "Forbidden"; ExportedLibrary = "Forbidden"
}
"""
        let parse source file =
            match parseStringWithDefaults source file with
            | ParseSuccess value -> value
            | ParseError errors -> failwithf "%A" errors
        let context =
            { SourcePlatformFixture.platform with
                RuntimeModel = if metadata then Some RuntimeModel.Win32 else None
                PlatformLoading = Some "WriteAuthority.loading" }
        checkParsedInputsWithPlatform
            [parse (authority + contract.Replace("LIBRARY",library)) "write-authority.clef"; parse "module App\n[<EntryPoint>]\nlet main _ = 37\n" "windows-loading.clef"]
            (Some context)

type SourcePlatformTests() =
    [<Theory>]
    [<InlineData(true)>]
    [<InlineData(false)>]
    member _.``Windows startup keeps validated source loading without redundant runtime metadata``(metadata: bool) =
        let result = SourceLoading.check metadata "kernel32"
        DimensionalCases.noErrors result
        let loading = PlatformResolution.readLoading result.Graph |> Result.defaultWith (failwithf "%A") |> Option.get
        Assert.Equal("win32", loading.Contract.Runtime)
        let revision = Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish result.Graph |> Result.defaultWith (failwithf "%A")
        Assert.True(revision.Emission.Storage.Startup.IsSome)
        Assert.True(revision.Emission.Boundary.Loading.IsSome, "Validated source loading was lost during publication.")
        Assert.Equal("kernel32", revision.Emission.Boundary.Loading.Value.Contract.Library)

    [<Theory>]
    [<InlineData(true)>]
    [<InlineData(false)>]
    member _.``Windows loading still rejects a non-kernel32 contract``(metadata: bool) =
        let result = SourceLoading.check metadata "c"
        Assert.True(PlatformResolution.readLoading result.Graph |> Result.isError)
        let boundary = BoundaryEmission.project result.Graph |> Result.defaultWith (failwithf "%A")
        Assert.True(boundary.Loading.IsNone)

    [<Fact>]
    member _.``Windows Console profile settles HostApiSymbol WriteFile and IEEE float representations``() =
        let profile = System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__, "../../../../../Fidelity.Platform/Profiles/Windows_x86_64_Console/Fidelity.Platform.fidproj"))
        Assert.True(System.IO.File.Exists profile)
        let scratch = System.IO.Path.Combine(System.IO.Path.GetTempPath(), "clef-win-console-" + System.Guid.NewGuid().ToString("N"))
        System.IO.Directory.CreateDirectory scratch |> ignore
        try
            let source = System.IO.Path.Combine(scratch, "Program.clef")
            let project = System.IO.Path.Combine(scratch, "Program.fidproj")
            let code =
                [ "module WindowsConsoleTest"
                  "let mutable position = 1"
                  "let main () ="
                  "    let values = [| 11; 37; 19 |]"
                  "    values.[position] <- 300"
                  "    let ratio = 3.5 + 0.25"
                  "    Console.write \"alpha:\""
                  "    Console.writeln \"λ\""
                  "    Console.error \"warn:\""
                  "    Console.errorln \"ok\""
                  "    if ratio > 3.7 && values.[position] = 300 then 37 else 1" ]
                |> String.concat "\n"
            System.IO.File.WriteAllText(source, code)
            let escapedProfile = profile.Replace("\\", "\\\\")
            System.IO.File.WriteAllText(project, sprintf "[package]\nname=\"WindowsConsoleTest\"\nversion=\"0.1.0\"\n[compilation]\ntarget=\"cpu\"\n[dependencies]\nplatform={path=\"%s\"}\n[build]\nsources=[\"Program.clef\"]\noutput_kind=\"console\"\n[link]\nlibraries=[\"kernel32\"]\n" escapedProfile)
            let checkedProject = Clef.Compiler.Project.ProjectChecker.checkProject project |> Result.defaultWith (failwithf "%A")
            Assert.False(Clef.Compiler.Project.ProjectChecker.hasErrors checkedProject, System.String.Join("\n", Clef.Compiler.Project.ProjectChecker.getErrorMessages checkedProject))
            let revision = Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish checkedProject.CheckResult.Graph |> Result.defaultWith (failwithf "%A")
            Assert.NotEmpty(revision.Emission.Boundary.IntrinsicWrites)
            let imported = revision.Emission.Boundary.IntrinsicWriteImports.Values |> Assert.Single
            Assert.Equal(Fidelity.PSG.IntrinsicWriteEndpoint.HostApiSymbol "WriteFile", imported.Target)
            Assert.NotEmpty(revision.Emission.Boundary.IntrinsicWriteProofs)
        finally
            System.IO.Directory.Delete(scratch, true)

    [<Theory>]
    [<InlineData("ffi", "WriteFile")>]
    [<InlineData("syscall", "WriteFile")>]
    [<InlineData("host-api", "")>]
    [<InlineData("host-api", "Write File")>]
    member _.``Windows symbol write endpoint requires an explicit host-api surface and identifier address``(surfaceKind: string, address: string) =
        let authority =
            SourcePlatformFixture.authority
                .Replace("Os = \"linux\"", "Os = \"windows\"")
                .Replace("Runtime = \"freestanding\"", "Runtime = \"win32\"")
                .Replace("x86_64-unknown-linux-gnu", "x86_64-pc-windows-msvc")
                .Replace("type BoundarySurface = { Endpoints: Endpoint array }", "type BoundarySurface = { Kind: string; Endpoints: Endpoint array }")
                .Replace("Location = \"syscall-number\"; Address = \"1\"", sprintf "Location = \"symbol\"; Address = \"%s\"" address)
                .Replace("Surfaces = [| { Endpoints = [| write |] } |]", sprintf "Surfaces = [| { Kind = \"%s\"; Endpoints = [| write |] } |]" surfaceKind)
        let parse source file =
            match parseStringWithDefaults source file with
            | ParseSuccess value -> value
            | ParseError errors -> failwithf "%A" errors
        let result =
            checkParsedInputsWithPlatform
                [parse authority "write-authority.clef"; parse "module App\nlet main () =\n    let s = \"hi\"\n    let _ = Sys.write 1 s.Bytes s.Length\n    0\n" "app.clef"]
                (Some { SourcePlatformFixture.platform with RuntimeModel = Some RuntimeModel.Win32 })
        Assert.True(hasErrors result)

    [<Fact>]
    member _.``Windows Console profile settles kernel32 foreign imports and native entry slots while refusing implicit libc``() =
        let profile = System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__, "../../../../../Fidelity.Platform/Profiles/Windows_x86_64_Console/Fidelity.Platform.fidproj"))
        let bareWire = System.IO.Path.GetFullPath(System.IO.Path.Combine(__SOURCE_DIRECTORY__, "../../../../../BAREWire/src/BAREWire.BindingMetadata.fidproj"))
        Assert.True(System.IO.File.Exists profile)
        Assert.True(System.IO.File.Exists bareWire)
        let scratch = System.IO.Path.Combine(System.IO.Path.GetTempPath(), "clef-win-boundary-" + System.Guid.NewGuid().ToString("N"))
        System.IO.Directory.CreateDirectory scratch |> ignore
        try
            let source = System.IO.Path.Combine(scratch, "Program.clef")
            let project = System.IO.Path.Combine(scratch, "Program.fidproj")
            let escapedProfile = profile.Replace("\\", "\\\\")
            let escapedBareWire = bareWire.Replace("\\", "\\\\")
            System.IO.File.WriteAllText(project, sprintf "[package]\nname=\"WindowsBoundaryTest\"\nversion=\"0.1.0\"\n[compilation]\ntarget=\"cpu\"\n[dependencies]\nplatform={path=\"%s\"}\nbarewire={path=\"%s\"}\n[build]\nsources=[\"Program.clef\"]\noutput_kind=\"console\"\n[link]\nlibraries=[\"kernel32\"]\n" escapedProfile escapedBareWire)
            let validCode =
                [ "module WindowsBoundaryTest"
                  "open BAREWire.Descriptors"
                  "type CleanupGroup = private | OpaqueCleanupGroup"
                  "[<FidelityExtern(\"kernel32\", \"GetCurrentProcessId\")>]"
                  "let GetCurrentProcessId () : int = NativeDefault.zeroed ()"
                  "let GetCurrentProcessIdDescriptor : Expr<FunctionDescriptor> ="
                  "    <@ { CName = \"GetCurrentProcessId\"; Parameters = [||]; ReturnType = Integer(Unsigned, 32); CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>"
                  "[<FidelityExtern(\"kernel32\", \"CreateThreadpoolCleanupGroup\")>]"
                  "let CreateThreadpoolCleanupGroup () : option<CHandle<CleanupGroup>> = NativeDefault.zeroed ()"
                  "let CreateThreadpoolCleanupGroupDescriptor : Expr<FunctionDescriptor> ="
                  "    <@ { CName = \"CreateThreadpoolCleanupGroup\"; Parameters = [||]; ReturnType = Pointer 64; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>"
                  "let CreateThreadpoolCleanupGroupResourceDescriptor : Expr<ResourceDescriptor> ="
                  "    <@ { Resource = OwnedNullableReturn { Binding = \"WindowsBoundaryTest.CloseThreadpoolCleanupGroup\"; Parameter = 0 }"
                  "         Hypothesis = { Identity = \"win32.tp.cleanup\"; Version = \"1\"; Source = \"test\" } } @>"
                  "[<FidelityExtern(\"kernel32\", \"CloseThreadpoolCleanupGroup\")>]"
                  "let CloseThreadpoolCleanupGroup (g: CHandle<CleanupGroup>) : unit = NativeDefault.zeroed ()"
                  "let CloseThreadpoolCleanupGroupDescriptor : Expr<FunctionDescriptor> ="
                  "    <@ { CName = \"CloseThreadpoolCleanupGroup\"; Parameters = [| { Name = \"g\"; Type = Pointer 64; PassBy = Value } |]; ReturnType = Void; CallingConvention = CDecl; OwnershipTransfer = Undeclared } @>"
                  "let private pidSlot = FnPtr.ofExtern GetCurrentProcessId"
                  "let private checkResource () ="
                  "    match CreateThreadpoolCleanupGroup () with"
                  "    | None -> 9"
                  "    | Some g ->"
                  "        CloseThreadpoolCleanupGroup g"
                  "        37"
                  "let main () ="
                  "    let a = GetCurrentProcessId ()"
                  "    let b = FnPtr.invoke pidSlot ()"
                  "    let r = checkResource ()"
                  "    if a = b && a <> 0 && r = 37 then 37 else 1" ]
                |> String.concat "\n"
            System.IO.File.WriteAllText(source, validCode)
            let checkedValid = Clef.Compiler.Project.ProjectChecker.checkProject project |> Result.defaultWith (failwithf "%A")
            Assert.False(Clef.Compiler.Project.ProjectChecker.hasErrors checkedValid, System.String.Join("\n", Clef.Compiler.Project.ProjectChecker.getErrorMessages checkedValid))
            let revision = Clef.Compiler.PSGSaturation.Publication.RevisionPublication.publish checkedValid.CheckResult.Graph |> Result.defaultWith (failwithf "%A")
            Assert.Equal(3, revision.Emission.Boundary.Imports.Count)
            Assert.All(revision.Emission.Boundary.Imports.Values, fun imported -> Assert.Equal("kernel32", imported.Library))
            Assert.Single(revision.Emission.Boundary.Entries.Values) |> ignore
            Assert.Single(revision.Emission.Boundary.ResourceDeclarations.Values) |> ignore

            let libcCode = validCode.Replace("[<FidelityExtern(\"kernel32\", \"GetCurrentProcessId\")>]", "[<FidelityExtern(\"c\", \"GetCurrentProcessId\")>]")
            System.IO.File.WriteAllText(source, libcCode)
            let checkedLibc = Clef.Compiler.Project.ProjectChecker.checkProject project |> Result.defaultWith (failwithf "%A")
            Assert.True(Clef.Compiler.Project.ProjectChecker.hasErrors checkedLibc)
        finally
            System.IO.Directory.Delete(scratch, true)
