// Host build tool. FSI loads the tokenizer from the selected SDK.
open System
open System.IO
open FSharp.Compiler.Tokenization

type Site = { File: string; Name: string; Line: int; Column: int }

let roots = set ["NativeTypedTree"; "PSGSaturation"; "Baker"; "Nanopass"]
let names = set ["FSharpValue"; "FSharpType"; "ConditionalWeakTable"; "ConcurrentDictionary"; "ProcessStartInfo"]
let prefixes = set ["System.Reflection"; "Microsoft.FSharp.Reflection"]
let normalize (path: string) = path.Replace('\\','/')
let inZone (path: string) =
    let slash = path.IndexOf('/')
    slash > 0 && roots.Contains(path.Substring(0, slash))

let inputs manifest =
    let rows = File.ReadAllLines(manifest) |> Array.map (fun row -> row.Split('\t'))
    let projectDir = rows |> Array.choose (function [|"P"; p|] -> Some p | _ -> None) |> Array.exactlyOne
    let defines = rows |> Array.choose (function [|"D"; d|] -> Some d | _ -> None) |> Array.toList
    let files = rows |> Array.choose (fun row ->
        match row with
        | [|"P"; _|] | [|"D"; _|] -> None
        | [|"F"; path; identity|] | [|"F"; path; identity; _|] ->
            let physical = normalize (Path.GetRelativePath(projectDir, path))
            let logical = normalize (if row.Length = 4 && row[3] <> "" then row[3] else identity)
            if inZone physical then Some (physical, path)
            elif inZone logical then Some (logical, path)
            else None
        | _ -> invalidOp "Invalid evaluated Compile row.")
    if files.Length = 0 then invalidOp "No evaluated Zone A compiler inputs."
    if (files |> Array.distinctBy fst).Length <> files.Length then invalidOp "Duplicate Zone A compile path."
    defines, files

let scan defines (file, path) =
    let tokenizer = FSharpSourceTokenizer("COMPILED" :: defines, Some path, None, None)
    let mutable state = FSharpTokenizerLexState.Initial
    let mutable previous : (string * int * int) list = []
    [ for lineNumber, line in File.ReadLines(path) |> Seq.indexed do
        let lexer = tokenizer.CreateLineTokenizer(line)
        let mutable reading = true
        while reading do
            let token, next = lexer.ScanToken(state)
            state <- next
            match token with
            | None -> reading <- false
            | Some t when t.ColorClass = FSharpTokenColorKind.Comment || t.TokenName = "WHITESPACE" -> ()
            | Some t when t.TokenName = "IDENT" || t.TokenName = "DOT" ->
                let raw = line.Substring(t.LeftColumn, t.RightColumn - t.LeftColumn + 1)
                let name =
                    if raw.Length >= 4 && raw.StartsWith("``", StringComparison.Ordinal) && raw.EndsWith("``", StringComparison.Ordinal)
                    then raw.Substring(2, raw.Length - 4) else raw
                let row, column = lineNumber + 1, t.LeftColumn + 1
                let site symbol r c = { File=file; Name=symbol; Line=r; Column=c }
                if names.Contains name then yield site name row column
                if name = "Reflection" then
                    match previous with
                    | (".",_,_) :: ("System",r,c) :: _ -> yield site "System.Reflection" r c
                    | (".",_,_) :: ("FSharp",_,_) :: (".",_,_) :: ("Microsoft",r,c) :: _ ->
                        yield site "Microsoft.FSharp.Reflection" r c
                    | _ -> ()
                previous <- (name,row,column) :: List.truncate 3 previous
            | Some _ -> previous <- [] ]

let allowance path =
    File.ReadLines(path) |> Seq.fold (fun rows (line: string) ->
        match line.Split('\t') with
        | [|file; name; count|] when inZone file && (names.Contains name || prefixes.Contains name) ->
            let n = Int32.Parse(count, Globalization.CultureInfo.InvariantCulture)
            let key = file, name
            if n < 1 || Map.containsKey key rows then invalidOp ("Invalid or duplicate allowance: " + line)
            Map.add key n rows
        | _ -> invalidOp ("Malformed allowance: " + line)) Map.empty

let maximum key counts = Map.tryFind key counts |> Option.defaultValue 0

let ratchet accepted proposed =
    proposed |> Map.forall (fun ((file,name) as key) n ->
        let limit = maximum key accepted
        if n <= limit then true else
            eprintfn "%s: error CLEF001: allowance expansion for %s (accepted %d, proposed %d)." file name limit n
            false)

let run args =
    match args with
    | [|"ratchet"; stable; proposed|] -> ratchet (allowance stable) (allowance proposed)
    | [|"check"; manifest; _; "--emit-scope"|]
    | [|"check"; manifest; _|] | [|"census"; manifest|] ->
        let defines, files = inputs manifest
        let groups =
            files |> Seq.collect (scan defines) |> Seq.groupBy (fun s -> s.File,s.Name)
            |> Seq.map (fun (key,sites) -> key, Seq.toArray sites) |> Map.ofSeq
        if args[0] = "census" then
            for KeyValue((file,name),sites) in groups do printfn "%s\t%s\t%d" file name sites.Length
            true
        else
            let limits = allowance args[2]
            let mutable valid = true
            for KeyValue((file,name) as key,sites) in groups do
                let limit = maximum key limits
                if sites.Length > limit then
                    let site = sites[limit]
                    eprintfn "%s(%d,%d): error CLEF001: %s allowance=%d actual=%d" file site.Line site.Column name limit sites.Length
                    valid <- false
            if valid && args.Length = 4 then
                for _, path in files do printfn "%s" path
            valid
    | _ -> invalidArg "args" "check <compile-inputs> <allowances> | census <compile-inputs> | ratchet <accepted> <proposed>"

try exit (if run fsi.CommandLineArgs[1..] then 0 else 1)
with e -> eprintfn "error CLEF001: %s" e.Message; exit 2
