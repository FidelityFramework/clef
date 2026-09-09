namespace Clef.Compiler.Service.Tests

open System
open System.IO
open Xunit
open Clef.Compiler.Project

type private ProjectFiles() =
    let directory = Path.Combine(Path.GetTempPath(), "clef-link-tests-" + Guid.NewGuid().ToString("N"))
    do Directory.CreateDirectory directory |> ignore
    member _.Write(name: string, extra: string) =
        File.WriteAllText(Path.Combine(directory, name + ".clef"), "module " + name + "\nlet value = 1\n")
        let path = Path.Combine(directory, name + ".fidproj")
        File.WriteAllText(path,
            "[package]\nname = \"" + name + "\"\n[compilation]\ntarget = \"library\"\n"
            + "[build]\noutput_kind = \"library\"\nsources = [\"" + name + ".clef\"]\n" + extra)
        path
    interface IDisposable with
        member _.Dispose() = Directory.Delete(directory, true)

module private LinkCases =
    let loaded path =
        match FidprojLoader.load path with
        | Ok options -> options
        | Error error -> failwith error

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "ProjectLinks")>]
type ProjectLinkTests() =
    [<Fact>]
    member _.``Link declarations are optional and preserve distinct explicit identities``() =
        use files = new ProjectFiles()
        let absent = files.Write("Absent", "") |> LinkCases.loaded
        Assert.Empty(absent.LinkedLibraries)
        let declared = files.Write("Declared", "[link]\nlibraries = [\"gbm\", \"resvg\", \"gbm\"]\n") |> LinkCases.loaded
        Assert.Equal<string list>(["gbm"; "resvg"], declared.LinkedLibraries)
        let empty = files.Write("Empty", "[link]\nlibraries = []\n") |> LinkCases.loaded
        Assert.Empty(empty.LinkedLibraries)

    [<Theory>]
    [<InlineData("\"gbm\"")>]
    [<InlineData("[\"gbm\", 42]")>]
    [<InlineData("[\"\"]")>]
    [<InlineData("[\"  \"]")>]
    member _.``Malformed link declarations are errors``(value: string) =
        use files = new ProjectFiles()
        let path = files.Write("Invalid", "[link]\nlibraries = " + value + "\n")
        match FidprojLoader.load path with
        | Error _ -> ()
        | Ok _ -> failwith "Malformed libraries were silently accepted"

    [<Fact>]
    member _.``Dependency link identities survive diamond resolution and project checking``() =
        use files = new ProjectFiles()
        files.Write("Shared", "[link]\nlibraries = [\"c\", \"gbm\"]\n") |> ignore
        files.Write("A", "[dependencies]\nshared = { path = \"Shared.fidproj\" }\n[link]\nlibraries = [\"gbm\"]\n") |> ignore
        files.Write("B", "[dependencies]\nshared = { path = \"Shared.fidproj\" }\n[link]\nlibraries = [\"resvg\"]\n") |> ignore
        let path = files.Write("App", "[dependencies]\na = { path = \"A.fidproj\" }\nb = { path = \"B.fidproj\" }\n[link]\nlibraries = [\"pthread\", \"gbm\"]\n")
        let expected = ["pthread"; "gbm"; "c"; "resvg"]
        match SourceResolver.getSourcesAndLibraries (LinkCases.loaded path) with
        | Error error -> failwith (SourceResolutionError.format error)
        | Ok resolved ->
            Assert.Equal<string list>(expected, resolved.LinkedLibraries)
            let sourceNames = resolved.SourcePaths |> List.map (fun path ->
                match Path.GetFileName path with
                | null -> failwith "Resolved source has no filename"
                | name -> name)
            Assert.Equal<string list>(["Shared.clef"; "A.clef"; "B.clef"; "App.clef"], sourceNames)
        for checkedProject in [ ProjectChecker.checkProject path; ProjectChecker.checkProjectWithVolatile path Map.empty ] do
            match checkedProject with
            | Error error -> failwith error
            | Ok project -> Assert.Equal<string list>(expected, project.Options.LinkedLibraries)

    [<Fact>]
    member _.``Invalid transitive link metadata is reported with dependency identity``() =
        use files = new ProjectFiles()
        files.Write("Broken", "[link]\nlibraries = false\n") |> ignore
        let path = files.Write("App", "[dependencies]\nbroken = { path = \"Broken.fidproj\" }\n")
        match SourceResolver.getSourcesAndLibraries (LinkCases.loaded path) with
        | Error (DependencyFidprojLoadError ("broken", _, message)) -> Assert.Contains("libraries", message)
        | other -> failwithf "Expected the transitive declaration error, got %A" other
