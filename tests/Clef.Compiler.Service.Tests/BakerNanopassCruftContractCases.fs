namespace Clef.Compiler.Service.Tests

open System
open System.IO
open Xunit
open Fidelity.Data.XML

module private BakerNanopassCruftAnalyzer =
    type Diagnostic = {
        Code: string
        File: string
        Line: int
        Column: int
        Message: string
    }

    let hasReflectionFormat (text: string) =
        let length = text.Length
        let rec scan i =
            if i >= length then false
            elif text[i] <> '%' then scan (i + 1)
            elif i + 1 < length && text[i + 1] = '%' then scan (i + 2)
            else
                let mutable j = i + 1
                while j < length && (text[j] = '-' || text[j] = '+' || text[j] = '0' || text[j] = '#') do
                    j <- j + 1
                if j < length && text[j] = '*' then
                    j <- j + 1
                else
                    while j < length && text[j] >= '0' && text[j] <= '9' do
                        j <- j + 1
                if j < length && text[j] = '.' then
                    j <- j + 1
                    if j < length && text[j] = '*' then
                        j <- j + 1
                    else
                        while j < length && text[j] >= '0' && text[j] <= '9' do
                            j <- j + 1
                if j < length && text[j] = 'A' then true
                else scan (i + 1)
        scan 0

    let private isIdentStart (c: char) =
        Char.IsLetter c || c = '_'

    let private isIdentPart (c: char) =
        Char.IsLetterOrDigit c || c = '_' || c = '\''

    let private isClrThrowIdent (ident: string) =
        match ident with
        | "failwith"
        | "failwithf"
        | "invalidArg"
        | "invalidOp"
        | "nullArg"
        | "raise"
        | "reraise" -> true
        | _ -> false

    let analyzeSource (checkThrows: bool) (fileName: string) (source: string) : Diagnostic list =
        let diagnostics = ResizeArray<Diagnostic>()
        let length = source.Length
        let mutable i = 0
        let mutable line = 1
        let mutable lineStart = 0

        let currentColumn pos = (pos - lineStart) + 1

        let advanceChar () =
            if i < length then
                if source[i] = '\n' then
                    line <- line + 1
                    lineStart <- i + 1
                i <- i + 1

        let addDiagnostic code ln col message =
            diagnostics.Add {
                Code = code
                File = fileName
                Line = ln
                Column = col
                Message = message
            }

        let rejectReferenceIdentity ln col =
            addDiagnostic
                "AXC006"
                ln
                col
                "Clef Baker and Nanopass code must not use reference identity (PhysicalEquality or ReferenceEquals)."

        let rejectReflectionFormat ln col =
            addDiagnostic
                "AXC007"
                ln
                col
                "Clef Baker and Nanopass code must not use %A reflection formatting."

        let rejectClrThrow ident ln col =
            addDiagnostic
                "AXC008"
                ln
                col
                (sprintf "Clef Baker and Nanopass code must not throw CLR exceptions (%s)." ident)

        while i < length do
            let c = source[i]
            if c = '/' && i + 1 < length && source[i + 1] = '/' then
                while i < length && source[i] <> '\n' do
                    advanceChar ()
            elif c = '(' && i + 1 < length && source[i + 1] = '*' then
                let mutable depth = 1
                advanceChar ()
                advanceChar ()
                while i < length && depth > 0 do
                    if source[i] = '(' && i + 1 < length && source[i + 1] = '*' then
                        depth <- depth + 1
                        advanceChar ()
                        advanceChar ()
                    elif source[i] = '*' && i + 1 < length && source[i + 1] = ')' then
                        depth <- depth - 1
                        advanceChar ()
                        advanceChar ()
                    else
                        advanceChar ()
            elif c = '"' && i + 2 < length && source[i + 1] = '"' && source[i + 2] = '"' then
                let startLine = line
                let startCol = currentColumn i
                advanceChar ()
                advanceChar ()
                advanceChar ()
                let contentStart = i
                let mutable closed = false
                while i < length && not closed do
                    if source[i] = '"' && i + 2 < length && source[i + 1] = '"' && source[i + 2] = '"' then
                        let text = source.Substring(contentStart, i - contentStart)
                        if hasReflectionFormat text then
                            rejectReflectionFormat startLine startCol
                        advanceChar ()
                        advanceChar ()
                        advanceChar ()
                        closed <- true
                    else
                        advanceChar ()
            elif c = '@' && i + 1 < length && source[i + 1] = '"' then
                let startLine = line
                let startCol = currentColumn i
                advanceChar ()
                advanceChar ()
                let sb = System.Text.StringBuilder()
                let mutable closed = false
                while i < length && not closed do
                    if source[i] = '"' then
                        if i + 1 < length && source[i + 1] = '"' then
                            sb.Append('"') |> ignore
                            advanceChar ()
                            advanceChar ()
                        else
                            advanceChar ()
                            closed <- true
                    else
                        sb.Append(source[i]) |> ignore
                        advanceChar ()
                if hasReflectionFormat (sb.ToString()) then
                    rejectReflectionFormat startLine startCol
            elif c = '"' then
                let startLine = line
                let startCol = currentColumn i
                advanceChar ()
                let sb = System.Text.StringBuilder()
                let mutable closed = false
                while i < length && not closed do
                    if source[i] = '\\' && i + 1 < length then
                        sb.Append(source[i]) |> ignore
                        advanceChar ()
                        sb.Append(source[i]) |> ignore
                        advanceChar ()
                    elif source[i] = '"' then
                        advanceChar ()
                        closed <- true
                    else
                        sb.Append(source[i]) |> ignore
                        advanceChar ()
                if hasReflectionFormat (sb.ToString()) then
                    rejectReflectionFormat startLine startCol
            elif c = '\'' then
                if i + 2 < length && source[i + 1] <> '\\' && source[i + 2] = '\'' then
                    advanceChar ()
                    advanceChar ()
                    advanceChar ()
                elif i + 3 < length && source[i + 1] = '\\' && source[i + 3] = '\'' then
                    advanceChar ()
                    advanceChar ()
                    advanceChar ()
                    advanceChar ()
                else
                    advanceChar ()
            elif isIdentStart c then
                let startPos = i
                let startLine = line
                let startCol = currentColumn i
                while i < length && isIdentPart source[i] do
                    advanceChar ()
                let ident = source.Substring(startPos, i - startPos)
                if ident = "PhysicalEquality" || ident = "ReferenceEquals" then
                    rejectReferenceIdentity startLine startCol
                elif checkThrows && isClrThrowIdent ident then
                    rejectClrThrow ident startLine startCol
            else
                advanceChar ()

        diagnostics
        |> Seq.distinctBy (fun d -> d.Code, d.File, d.Line, d.Column)
        |> Seq.toList

    let repoRoot () =
        Path.GetFullPath(Path.Combine(__SOURCE_DIRECTORY__, "..", ".."))

    let bakerAndNanopassFiles () =
        let compilerDir = Path.Combine(repoRoot (), "src", "Compiler")
        let fsprojPath = Path.Combine(compilerDir, "Clef.Compiler.Service.fsproj")
        let xmlText = File.ReadAllText(fsprojPath)
        match Xml.parse xmlText with
        | Error err ->
            failwithf "Failed to parse Clef.Compiler.Service.fsproj via Fidelity.Data.XML: %s" (string err)
        | Ok doc ->
            let rec collectIncludes (node: XmlNode) =
                match node with
                | XmlNode.Element(name, _, children) ->
                    let current =
                        if name = "Compile" then
                            XmlNode.attr "Include" node |> Option.toList
                        else
                            []
                    current @ (children |> List.collect collectIncludes)
                | _ -> []
            collectIncludes doc.Root
            |> List.choose (fun (inc: string) ->
                let normalized = inc.Replace('\\', Path.DirectorySeparatorChar)
                if normalized.StartsWith("Baker" + string Path.DirectorySeparatorChar, StringComparison.Ordinal)
                   || normalized.StartsWith("Nanopass" + string Path.DirectorySeparatorChar, StringComparison.Ordinal) then
                    Some(normalized, Path.Combine(compilerDir, normalized))
                else
                    None)

    let throwFreeRecipeFiles =
        let sep = string Path.DirectorySeparatorChar
        Set.ofList [
            "Baker" + sep + "Recipes" + sep + "HardwareModuleRecipes.fs"
            "Baker" + sep + "Recipes" + sep + "ArrayMemoryRecipes.fs"
            "Baker" + sep + "Recipes" + sep + "MemoryAccessRecipes.fs"
            "Baker" + sep + "Recipes" + sep + "KernelModuleRecipes.fs"
            "Baker" + sep + "Recipes" + sep + "KernelDeclarations.fs"
            "Baker" + sep + "Recipes" + sep + "StringViewRecipes.fs"
        ]

[<Trait("Category", "Compiler.Service"); Trait("Subcategory", "BakerNanopassCruftContract")>]
type BakerNanopassCruftContractCases() =
    [<Fact>]
    member _.``All Baker and Nanopass compile items satisfy AXC006 AXC007 and migrated AXC008``() =
        let files = BakerNanopassCruftAnalyzer.bakerAndNanopassFiles ()
        Assert.True(files.Length >= 103, sprintf "Expected at least 103 Baker and Nanopass compile items, found %d" files.Length)

        let matchedThrowFree =
            files
            |> List.filter (fun (relativePath, _) -> BakerNanopassCruftAnalyzer.throwFreeRecipeFiles.Contains relativePath)
        Assert.Equal(6, matchedThrowFree.Length)

        let violations =
            files
            |> List.collect (fun (relativePath, fullPath) ->
                let source = File.ReadAllText(fullPath)
                let checkThrows = BakerNanopassCruftAnalyzer.throwFreeRecipeFiles.Contains relativePath
                BakerNanopassCruftAnalyzer.analyzeSource checkThrows relativePath source)

        if not violations.IsEmpty then
            let summary =
                violations
                |> List.map (fun v -> sprintf "%s:%d:%d [%s] %s" v.File v.Line v.Column v.Code v.Message)
                |> String.concat "\n"
            Assert.Fail(sprintf "Found %d AXC006/AXC007/AXC008 violations in Baker/Nanopass:\n%s" violations.Length summary)

    [<Fact>]
    member _.``AXC006 AXC007 and AXC008 analyzer detects ReferenceEquals PhysicalEquality percent-A and CLR throws``() =
        let sample =
            String.concat "\n" [
                "module Sample"
                "let a x y = obj.ReferenceEquals(x, y)"
                "let b x y = LanguagePrimitives.PhysicalEquality x y"
                "let c x = sprintf \"%A\" x"
                "let d x = failwithf \"%+A\" x"
                "let e x = $\"val={x:%A}\""
                "let f x = invalidOp \"bad\""
                "let ok x = sprintf \"%s %%A %d\" x 1"
            ]
        let diagnostics = BakerNanopassCruftAnalyzer.analyzeSource true "Sample.fs" sample
        let codes = diagnostics |> List.map (fun d -> d.Code, d.Line)
        Assert.Equal<(string * int) list>(
            [
                ("AXC006", 2)
                ("AXC006", 3)
                ("AXC007", 4)
                ("AXC008", 5)
                ("AXC007", 5)
                ("AXC007", 6)
                ("AXC008", 7)
            ],
            codes
        )
