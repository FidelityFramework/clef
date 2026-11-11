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
